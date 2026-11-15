// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Baseline (non-LSE, armv8.0) LL/SC atomics, end to end.
//!
//! AtomicRmw and CmpXchg on a profile without FEAT_LSE select opaque LL/SC
//! pseudos that register allocation sees as one instruction; after allocation
//! they expand into LDXR/LDAXR{B,H} .. STXR/STLXR{B,H} + CBNZ retry loops.
//! These tests force `AArch64IsaProfile::BASELINE` and compile for the host
//! triple (aarch64-apple-darwin or aarch64-unknown-linux-gnu), so the same
//! file is a native control on both hosts; LL/SC is baseline armv8.0 and runs
//! on LSE hardware too. Every emitted word is decoded independently of the
//! compiler (field masks from the Arm ARM), and native execution is compared
//! with C11 <stdatomic.h> oracles:
//!
//! * every RMW operation at 8/16/32/64 bits and every ordering, with guard
//!   bytes around the atomic object, at O0-O3;
//! * compare-exchange at Bool/8/16/32/64 bits for all fifteen valid Rust
//!   (success, failure) ordering pairs, returning the old value and the
//!   success flag, at O0-O3;
//! * multi-threaded contention (fetch_add counters at every width, a
//!   CAS-loop counter and an acquire/release spinlock guarding a plain
//!   counter) with exact final counts at O0-O3;
//! * a register-pressure function whose spills are load-bearing, decoded to
//!   prove that no load or store sits inside any exclusive window.
//!
//! This is differential and structural testing evidence. It is not an
//! exclusive-monitor, memory-model, linearizability or progress proof, and
//! the LL/SC opcodes remain RED rows in the opcode evidence inventory.

#[path = "common/rosetta.rs"]
mod process;

#[path = "common/fresh_dir.rs"]
mod fresh_dir;

use std::fmt::Write as _;
use std::fs;
use std::process::Command;

use trust_cg_codegen::pipeline::{OptLevel, Pipeline, PipelineConfig};
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};
use trust_cg_codegen::{Compiler, CompilerConfig};

use trust_ir::{
    AtomicRMWOp, BinOp, Block, BlockId, CastOp, Constant, Endianness, FuncId, FuncTy, Function,
    Inst, InstrNode, Module, Ordering, StructPassingPolicy, TargetInfo, Ty, ValueId,
};

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const ORDERINGS: [Ordering; 5] = [
    Ordering::Relaxed,
    Ordering::Acquire,
    Ordering::Release,
    Ordering::AcqRel,
    Ordering::SeqCst,
];
/// Every valid Rust compare-exchange (success, failure) pair: the failure
/// ordering is never Release/AcqRel and may be stronger than success.
const CAS_PAIRS: [(Ordering, Ordering); 15] = [
    (Ordering::Relaxed, Ordering::Relaxed),
    (Ordering::Relaxed, Ordering::Acquire),
    (Ordering::Relaxed, Ordering::SeqCst),
    (Ordering::Acquire, Ordering::Relaxed),
    (Ordering::Acquire, Ordering::Acquire),
    (Ordering::Acquire, Ordering::SeqCst),
    (Ordering::Release, Ordering::Relaxed),
    (Ordering::Release, Ordering::Acquire),
    (Ordering::Release, Ordering::SeqCst),
    (Ordering::AcqRel, Ordering::Relaxed),
    (Ordering::AcqRel, Ordering::Acquire),
    (Ordering::AcqRel, Ordering::SeqCst),
    (Ordering::SeqCst, Ordering::Relaxed),
    (Ordering::SeqCst, Ordering::Acquire),
    (Ordering::SeqCst, Ordering::SeqCst),
];

/// `(C type, trust_ir type, width in bits)` for the RMW matrix.
#[derive(Clone, Copy)]
struct Width {
    signed: &'static str,
    unsigned: &'static str,
    bits: u32,
}

const WIDTHS: [Width; 4] = [
    Width {
        signed: "i8",
        unsigned: "u8",
        bits: 8,
    },
    Width {
        signed: "i16",
        unsigned: "u16",
        bits: 16,
    },
    Width {
        signed: "i32",
        unsigned: "u32",
        bits: 32,
    },
    Width {
        signed: "i64",
        unsigned: "u64",
        bits: 64,
    },
];

fn ty_for(c_type: &str) -> Ty {
    match c_type {
        "i8" => Ty::I8,
        "u8" => Ty::U8,
        "i16" => Ty::I16,
        "u16" => Ty::U16,
        "i32" => Ty::I32,
        "u32" => Ty::U32,
        "i64" => Ty::I64,
        "u64" => Ty::U64,
        "b1" => Ty::Bool,
        "u128" => Ty::U128,
        "i128" => Ty::I128,
        other => panic!("unknown C type {other}"),
    }
}

/// `(name, trust_ir op, uses signed C type, C11 oracle expression)`.
const RMW_OPS: [(&str, AtomicRMWOp, bool, &str); 10] = [
    ("add", AtomicRMWOp::Add, false, "atomic_fetch_add_explicit"),
    ("sub", AtomicRMWOp::Sub, false, "atomic_fetch_sub_explicit"),
    ("and", AtomicRMWOp::And, false, "atomic_fetch_and_explicit"),
    ("or", AtomicRMWOp::Or, false, "atomic_fetch_or_explicit"),
    ("xor", AtomicRMWOp::Xor, false, "atomic_fetch_xor_explicit"),
    ("xchg", AtomicRMWOp::Xchg, false, "atomic_exchange_explicit"),
    ("smax", AtomicRMWOp::Max, true, "fetch_max"),
    ("smin", AtomicRMWOp::Min, true, "fetch_min"),
    ("umax", AtomicRMWOp::UMax, false, "fetch_max"),
    ("umin", AtomicRMWOp::UMin, false, "fetch_min"),
];

/// Host triple for native execution, or `None` on a host that cannot run
/// AArch64 Mach-O or Linux GNU ELF code.
fn native_triple() -> Option<&'static str> {
    if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
        Some("aarch64-apple-darwin")
    } else if cfg!(all(
        target_arch = "aarch64",
        target_os = "linux",
        target_env = "gnu"
    )) {
        Some("aarch64-unknown-linux-gnu")
    } else {
        None
    }
}

/// Object-only triple on hosts without native execution.
fn compile_triple() -> &'static str {
    native_triple().unwrap_or("aarch64-apple-darwin")
}

fn module(triple: &str, name: &str) -> Module {
    let mut module = Module::new(name);
    module.target_info = Some(TargetInfo {
        triple: triple.into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: Some("aapcs64".into()),
        struct_passing: StructPassingPolicy::NativeC,
    });
    module
}

fn add_function(
    module: &mut Module,
    name: &str,
    params: Vec<Ty>,
    returns: Vec<Ty>,
    body: Vec<InstrNode>,
) {
    let sig = module
        .add_func_type(FuncTy {
            params: params.clone(),
            returns,
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(module.functions.len() as u32),
        name,
        sig,
        BlockId::new(0),
    );
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(id, ty)| (ValueId::new(id as u32), ty))
            .collect(),
        body,
    }];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
}

fn add_rmw(module: &mut Module, name: &str, op: AtomicRMWOp, ty: Ty, ordering: Ordering) {
    add_function(
        module,
        name,
        vec![Ty::PtrMut(Box::new(ty.clone())), ty.clone()],
        vec![ty.clone()],
        vec![
            InstrNode::new(Inst::AtomicRMW {
                op,
                ty,
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                ordering,
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    );
}

fn add_cas(
    module: &mut Module,
    name: &str,
    ty: Ty,
    success: Ordering,
    failure: Ordering,
    return_success: bool,
) {
    let mut body = vec![
        InstrNode::new(Inst::CmpXchg {
            ty: ty.clone(),
            ptr: ValueId::new(0),
            expected: ValueId::new(1),
            desired: ValueId::new(2),
            success,
            failure,
            weak: false,
        })
        .with_results(vec![ValueId::new(3), ValueId::new(4)]),
    ];
    let result = if return_success {
        body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::U64,
                operand: ValueId::new(4),
            })
            .with_result(ValueId::new(5)),
        );
        ValueId::new(5)
    } else {
        ValueId::new(3)
    };
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));
    add_function(
        module,
        name,
        vec![Ty::PtrMut(Box::new(ty.clone())), ty.clone(), ty.clone()],
        vec![if return_success { Ty::U64 } else { ty }],
        body,
    );
}

fn baseline_pipeline(triple: &str, opt_level: OptLevel) -> Pipeline {
    Pipeline::new(PipelineConfig {
        opt_level,
        target_triple: triple.into(),
        ..PipelineConfig::default()
    })
    .with_aarch64_isa_profile(AArch64IsaProfile::BASELINE)
}

/// Compile every function of `module` separately through a BASELINE pipeline.
fn compile_baseline(module: &Module, triple: &str, opt_level: OptLevel) -> Vec<Vec<u8>> {
    assert!(trust_ir_build::validate::validate_module(module).is_empty());
    let lowered = permit_translate_module(module).expect("fixture must translate");
    let pipeline = baseline_pipeline(triple, opt_level);
    lowered
        .iter()
        .map(|(function, _)| {
            pipeline
                .compile_function(function)
                .unwrap_or_else(|error| panic!("{} at {opt_level:?}: {error}", function.name))
        })
        .collect()
}

// ---------------------------------------------------------------------------
// Independent object readers and A64 field decoding
// ---------------------------------------------------------------------------

fn u16_at(bytes: &[u8], at: usize) -> usize {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap()) as usize
}

fn u32_at(bytes: &[u8], at: usize) -> usize {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize
}

fn u64_at(bytes: &[u8], at: usize) -> usize {
    u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap()) as usize
}

fn words(text: &[u8]) -> Vec<u32> {
    assert_eq!(text.len() % 4, 0);
    text.as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect()
}

/// `.text` / `__TEXT,__text` words, read without the compiler's writers.
fn text_words(object: &[u8]) -> Vec<u32> {
    if object.starts_with(b"\x7fELF") {
        assert_eq!(u16_at(object, 18), 183, "EM_AARCH64");
        let table = u64_at(object, 40);
        let entry_size = u16_at(object, 58);
        let strings = table + u16_at(object, 62) * entry_size;
        let names = &object[u64_at(object, strings + 24)..][..u64_at(object, strings + 32)];
        for index in 0..u16_at(object, 60) {
            let entry = table + index * entry_size;
            let name = &names[u32_at(object, entry)..];
            let end = name.iter().position(|b| *b == 0).unwrap();
            if &name[..end] == b".text" {
                return words(&object[u64_at(object, entry + 24)..][..u64_at(object, entry + 32)]);
            }
        }
        panic!("ELF .text missing");
    }
    assert_eq!(u32_at(object, 0), 0xfeed_facf, "MH_MAGIC_64");
    assert_eq!(u32_at(object, 4), 0x0100_000c, "CPU_TYPE_ARM64");
    let commands = u32_at(object, 16);
    let mut at = 32;
    for _ in 0..commands {
        let (command, size) = (u32_at(object, at), u32_at(object, at + 4));
        if command == 0x19 {
            let sections = u32_at(object, at + 64);
            for index in 0..sections {
                let section = at + 72 + index * 80;
                let name = &object[section..section + 16];
                let segment = &object[section + 16..section + 32];
                if name.starts_with(b"__text\0") && segment.starts_with(b"__TEXT\0") {
                    let size = u64_at(object, section + 40);
                    let offset = u32_at(object, section + 48);
                    return words(&object[offset..offset + size]);
                }
            }
        }
        at += size;
    }
    panic!("Mach-O __TEXT,__text missing");
}

/// Load/store exclusive (Arm ARM C4.1.94). Single register: size 001000
/// o2=0 L o1=0 Rs o0 Rt2=11111 Rn Rt. X-register pair: 1 sz=1 001000 o2=0 L
/// o1=1 Rs o0 Rt2 Rn Rt, reported with `size == 4` (128 bits).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Exclusive {
    size: u32,
    pair: bool,
    load: bool,
    ordered: bool,
    rs: u32,
    rn: u32,
    rt: u32,
    rt2: u32,
}

fn exclusive(word: u32) -> Option<Exclusive> {
    let common = |size, pair, rt2| Exclusive {
        size,
        pair,
        load: word >> 22 & 1 == 1,
        ordered: word >> 15 & 1 == 1,
        rs: word >> 16 & 31,
        rn: word >> 5 & 31,
        rt: word & 31,
        rt2,
    };
    if word & 0x3fa0_7c00 == 0x0800_7c00 {
        return Some(common(word >> 30, false, 31));
    }
    if word & 0xbfa0_0000 == 0x8820_0000 {
        assert_eq!(
            word >> 30 & 1,
            1,
            "only X-register pairs are emitted: {word:#010x}"
        );
        return Some(common(4, true, word >> 10 & 31));
    }
    None
}

/// Any LSE single-instruction atomic (LD<op>/SWP or CAS/CASP) — never legal
/// on a baseline profile, and never used for 128-bit atomics.
fn is_lse(word: u32) -> bool {
    word & 0x3f20_0c00 == 0x3820_0000
        || word & 0x3fa0_7c00 == 0x08a0_7c00
        || word & 0xbfa0_7c00 == 0x0820_7c00
}

/// Every load/store-class word (op0 = x1x0).
fn is_load_store(word: u32) -> bool {
    word & 0x0a00_0000 == 0x0800_0000
}

const CLREX: u32 = 0xd503_3f5f;

fn is_cbnz_w(word: u32) -> Option<(u32, i32)> {
    (word & 0xff00_0000 == 0x3500_0000)
        .then_some((word & 31, ((word >> 5 & 0x7ffff) as i32) << 13 >> 13))
}

fn is_bcond(word: u32) -> Option<(u32, i32)> {
    (word & 0xff00_0010 == 0x5400_0000)
        .then_some((word & 15, ((word >> 5 & 0x7ffff) as i32) << 13 >> 13))
}

/// One decoded LL/SC loop: its exclusive pair and whether it is a CAS loop.
#[derive(Debug)]
struct Window {
    load: Exclusive,
    store: Exclusive,
    cas: bool,
}

fn check_status(store: &Exclusive) {
    assert!(
        store.rs != store.rt
            && (!store.pair || store.rs != store.rt2)
            && (store.rs != store.rn || store.rn == 31),
        "constrained-unpredictable store-exclusive status overlap: {store:?}"
    );
}

fn check_retry(words: &[u32], at: usize, status: u32, head: usize) {
    let (tested, back) = is_cbnz_w(words[at]).expect("store-exclusive must feed CBNZ");
    assert_eq!(tested, status, "CBNZ must test the store-exclusive status");
    assert_eq!(
        at as i64 + i64::from(back),
        head as i64,
        "CBNZ must retry at the load-exclusive"
    );
}

/// Find every exclusive window and check its structure independently: the
/// window holds no other load/store word and no branch except the CAS
/// compare-failure `B.NE`s; the store's status feeds a `CBNZ` back to the
/// load; a single-register CAS ends `B.EQ +2 ; CLREX`, and a pair CAS ends
/// `B.EQ +3 ; ST{L}XP status, <loaded pair> ; CBNZ` (the write-back that
/// makes the 128-bit read single-copy atomic).
fn exclusive_windows(words: &[u32]) -> Vec<Window> {
    let mut windows = Vec::new();
    let mut index = 0;
    while index < words.len() {
        let Some(load) = exclusive(words[index]).filter(|e| e.load) else {
            index += 1;
            continue;
        };
        assert_eq!(load.rs, 31, "load-exclusive Rs must be 11111");
        assert!(!load.pair || load.rt != load.rt2, "LDXP names Rt twice");
        let mut cursor = index + 1;
        let mut exits = Vec::new();
        let store = loop {
            let word = *words.get(cursor).expect("load-exclusive without store");
            if let Some(store) = exclusive(word) {
                assert!(
                    !store.load,
                    "two load-exclusives without a store at {cursor}"
                );
                break store;
            }
            assert!(
                !is_load_store(word),
                "memory access {word:#010x} inside the exclusive window at {cursor}"
            );
            if let Some((cond, offset)) = is_bcond(word) {
                assert_eq!(cond, 1, "only B.NE may leave the exclusive window");
                exits.push((cursor, offset));
            } else {
                assert!(
                    word >> 26 & 0b111 != 0b101 && word >> 25 & 0b1111 != 0b1010,
                    "branch {word:#010x} inside the exclusive window"
                );
            }
            cursor += 1;
            assert!(cursor - index <= 8, "exclusive window too long");
        };
        assert_eq!(store.size, load.size, "exclusive pair width mismatch");
        assert_eq!(store.pair, load.pair);
        assert_eq!(store.rn, load.rn, "exclusive pair base mismatch");
        check_status(&store);
        check_retry(words, cursor + 1, store.rs, index);
        let next = match (load.pair, exits.as_slice()) {
            (_, []) => cursor + 2,
            (false, [(bne, 4)]) => {
                assert_eq!(bne + 1, cursor, "B.NE must sit just before the store");
                assert_eq!(
                    is_bcond(words[cursor + 2]),
                    Some((0, 2)),
                    "B.EQ +2 success exit"
                );
                assert_eq!(words[cursor + 3], CLREX, "compare-failure CLREX");
                cursor + 4
            }
            (true, [(first, 6), (second, 4)]) => {
                assert_eq!((*first, *second, cursor), (index + 2, index + 4, index + 5));
                assert_eq!(
                    is_bcond(words[cursor + 2]),
                    Some((0, 3)),
                    "B.EQ +3 success exit"
                );
                let write_back = exclusive(words[cursor + 3]).expect("failure write-back store");
                assert!(write_back.pair && !write_back.load);
                assert_eq!(
                    (write_back.rs, write_back.rt, write_back.rt2, write_back.rn),
                    (store.rs, load.rt, load.rt2, load.rn),
                    "the failure path must store back the loaded pair"
                );
                assert_eq!(write_back.ordered, store.ordered);
                check_status(&write_back);
                check_retry(words, cursor + 4, write_back.rs, index);
                cursor + 5
            }
            (pair, other) => panic!("unexpected exits {other:?} (pair={pair})"),
        };
        windows.push(Window {
            load,
            store,
            cas: !exits.is_empty(),
        });
        index = next;
    }
    windows
}

fn acquire(ordering: Ordering) -> bool {
    matches!(
        ordering,
        Ordering::Acquire | Ordering::AcqRel | Ordering::SeqCst
    )
}

fn release(ordering: Ordering) -> bool {
    matches!(
        ordering,
        Ordering::Release | Ordering::AcqRel | Ordering::SeqCst
    )
}

fn size_field(bits: u32) -> u32 {
    match bits {
        8 => 0,
        16 => 1,
        32 => 2,
        64 => 3,
        _ => 4,
    }
}

/// Check one function object: exactly one LL/SC window of the expected
/// width, kind and acquire/release bits, and no LSE word at all.
/// True when an object names an `__aarch64_*` outline-atomics helper (as an
/// undefined symbol or anywhere else in its string tables).
fn names_outline_atomics_helper(object: &[u8]) -> bool {
    object.windows(10).any(|name| name == b"__aarch64_")
}

fn check_single_window(
    object: &[u8],
    bits: u32,
    cas: bool,
    load_acquire: bool,
    store_release: bool,
) {
    assert!(
        !names_outline_atomics_helper(object),
        "a CG atomic must not depend on __aarch64_* outline helpers"
    );
    let words = text_words(object);
    assert!(
        !words.iter().any(|&w| is_lse(w)),
        "baseline object contains an LSE atomic"
    );
    let windows = exclusive_windows(&words);
    assert_eq!(
        windows.len(),
        1,
        "exactly one exclusive window: {windows:?}"
    );
    let window = &windows[0];
    assert_eq!(window.cas, cas);
    assert_eq!(window.load.size, size_field(bits));
    assert_eq!(
        window.load.ordered, load_acquire,
        "load-exclusive acquire bit"
    );
    assert_eq!(
        window.store.ordered, store_release,
        "store-exclusive release bit"
    );
}

// ---------------------------------------------------------------------------
// Native execution
// ---------------------------------------------------------------------------

fn scratch(tag: &str) -> fresh_dir::ScratchDir {
    fresh_dir::create(&format!("trust-cg-llsc-{tag}-"))
}

/// Link `objects` with `driver` and run it natively; returns stdout.
fn link_and_run(tag: &str, objects: &[Vec<u8>], driver: &str, extra: &[&str]) -> String {
    link_run_inspect(tag, objects, driver, extra, &|_| {})
}

/// [`link_and_run`], also handing the linked executable's bytes to
/// `inspect` before the scratch directory is removed.
fn link_run_inspect(
    tag: &str,
    objects: &[Vec<u8>],
    driver: &str,
    extra: &[&str],
    inspect: &dyn Fn(&[u8]),
) -> String {
    link_run_inspect_outcome(tag, objects, driver, extra, inspect, None)
}

fn link_run_inspect_outcome(
    tag: &str,
    objects: &[Vec<u8>],
    driver: &str,
    extra: &[&str],
    inspect: &dyn Fn(&[u8]),
    expected_signal: Option<i32>,
) -> String {
    let root = scratch(tag);
    let driver_path = root.join("driver.c");
    fs::write(&driver_path, driver).unwrap();
    let mut link = Command::new("cc");
    link.args(["-O2", "-std=c11"]).arg(&driver_path);
    for (index, object) in objects.iter().enumerate() {
        let path = root.join(format!("f{index}.o"));
        fs::write(&path, object).unwrap();
        link.arg(path);
    }
    let executable = root.join("driver");
    link.args(extra).arg("-o").arg(&executable);
    let linked =
        process::command_output_with_timeout(&mut link, process::codegen_link_timeout()).unwrap();
    assert!(
        !linked.timed_out && linked.output.status.success(),
        "{tag}: link failed in {}: {}",
        root.display(),
        String::from_utf8_lossy(&linked.output.stderr)
    );
    inspect(&fs::read(&executable).unwrap());
    let run = if expected_signal.is_some() {
        // Observe the actual signal, rather than accepting an arbitrary
        // nonzero exit or the shell's 128+signal normalization.
        let mut command = process::aarch64_emulation::configured_command(&executable)
            .unwrap()
            .unwrap_or_else(|| Command::new(&executable));
        process::command_output_with_timeout(&mut command, process::codegen_run_timeout()).unwrap()
    } else {
        process::run_executable_with_timeout(&executable, process::codegen_run_timeout()).unwrap()
    };
    let stdout = String::from_utf8_lossy(&run.output.stdout).into_owned();
    assert!(
        !run.timed_out,
        "{tag}: execution timed out in {}",
        root.display()
    );
    if let Some(signal) = expected_signal {
        #[cfg(unix)]
        {
            use std::os::unix::process::ExitStatusExt;
            assert_eq!(
                run.output.status.signal(),
                Some(signal),
                "{tag}: the unsupported instruction must signal; files={}",
                root.display()
            );
        }
        #[cfg(not(unix))]
        panic!("unsupported-instruction signal controls require Unix: {signal}");
    } else {
        assert!(
            run.output.status.success(),
            "{tag}: native run failed in {}: {stdout}{}",
            root.display(),
            String::from_utf8_lossy(&run.output.stderr)
        );
    }
    fs::remove_dir_all(root).unwrap();
    stdout
}

const C_PRELUDE: &str = r#"
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef int8_t i8; typedef uint8_t u8; typedef int16_t i16; typedef uint16_t u16;
typedef int32_t i32; typedef uint32_t u32; typedef int64_t i64; typedef uint64_t u64;
static const i8 V_i8[] = {0, 1, -1, 127, -128, -2, 0x5a, -0x5b};
static const u8 V_u8[] = {0, 1, 2, 0x7f, 0x80, 0xfe, 0xff, 0x5a};
static const i16 V_i16[] = {0, 1, -1, 32767, -32768, -2, 0x5a5a, -0x5a5b};
static const u16 V_u16[] = {0, 1, 2, 0x7fff, 0x8000, 0xfffe, 0xffff, 0x5aa5};
static const i32 V_i32[] = {0, 1, -1, INT32_MAX, INT32_MIN, -2, 0x5a5aa5a5, -0x5a5aa5a6};
static const u32 V_u32[] = {0, 1, 2, 0x7fffffffu, 0x80000000u, 0xfffffffeu, 0xffffffffu, 0xa5a55a5au};
static const i64 V_i64[] = {0, 1, -1, INT64_MAX, INT64_MIN, -2, 0x5a5aa5a55a5aa5a5LL, -0x123456789abcdefLL};
static const u64 V_u64[] = {0, 1, 2, 0x7fffffffffffffffULL, 0x8000000000000000ULL, 0xfffffffffffffffeULL, 0xffffffffffffffffULL, 0xa5a55a5a0f0ff0f0ULL};
typedef bool b1;
static const b1 V_b1[] = {false, true};
#define NV(T) (sizeof(V_##T) / sizeof(V_##T[0]))
#define DEF_MINMAX(T) \
  static T fetch_max_##T(_Atomic(T) *o, T v, memory_order m) { T old = atomic_load_explicit(o, m == memory_order_release ? memory_order_relaxed : m == memory_order_acq_rel ? memory_order_acquire : m); \
    while (!atomic_compare_exchange_weak(o, &old, old > v ? old : v)) {} return old; } \
  static T fetch_min_##T(_Atomic(T) *o, T v, memory_order m) { T old = atomic_load_explicit(o, m == memory_order_release ? memory_order_relaxed : m == memory_order_acq_rel ? memory_order_acquire : m); \
    while (!atomic_compare_exchange_weak(o, &old, old < v ? old : v)) {} return old; }
DEF_MINMAX(i8) DEF_MINMAX(u8) DEF_MINMAX(i16) DEF_MINMAX(u16)
DEF_MINMAX(i32) DEF_MINMAX(u32) DEF_MINMAX(i64) DEF_MINMAX(u64)
static unsigned long cases;
#define GUARD 0xa5
/* The atomic object sits at byte 8 of a 32-byte buffer of guard bytes. */
#define GUARDS_INTACT(T) guards_intact(buf, sizeof(T))
static int guards_intact(const unsigned char *buf, unsigned width) {
  for (unsigned k = 0; k < 32; k++) if ((k < 8 || k >= 8 + width) && buf[k] != GUARD) return 0;
  return 1;
}
#define CHECK_RMW(T, FN, ORACLE, ORDER) do { \
  for (unsigned i = 0; i < NV(T); i++) for (unsigned j = 0; j < NV(T); j++) { \
    T init = V_##T[i], val = V_##T[j]; \
    _Alignas(16) unsigned char buf[32]; memset(buf, GUARD, sizeof buf); \
    T *p = (T *)(buf + 8); memcpy(p, &init, sizeof(T)); \
    _Atomic(T) oracle = init; T want_old = ORACLE(&oracle, val, ORDER); T want = atomic_load(&oracle); \
    T got = FN(p, val); cases++; \
    if (got != want_old || *p != want) { \
      printf(#FN " i=%u j=%u old=%llx/%llx mem=%llx/%llx\n", i, j, (unsigned long long)got, \
        (unsigned long long)want_old, (unsigned long long)*p, (unsigned long long)want); return 1; } \
    if (!GUARDS_INTACT(T)) { printf(#FN " adjacent-byte mutation i=%u j=%u\n", i, j); return 1; } \
  } } while (0)
#define CHECK_CAS(T, OLD, OK) do { \
  for (unsigned i = 0; i < NV(T); i++) for (unsigned e = 0; e < NV(T); e++) \
  for (unsigned d = 0; d < NV(T); d++) { \
    T init = V_##T[i], expected = V_##T[e], desired = V_##T[d]; \
    _Atomic(T) oracle = init; T seen = expected; \
    bool want_ok = atomic_compare_exchange_strong(&oracle, &seen, desired); \
    T want = atomic_load(&oracle); \
    _Alignas(16) unsigned char buf[32]; memset(buf, GUARD, sizeof buf); \
    T *p = (T *)(buf + 8); memcpy(p, &init, sizeof(T)); \
    T old = OLD(p, expected, desired); cases++; \
    if (old != seen || *p != want || !GUARDS_INTACT(T)) { \
      printf(#OLD " i=%u e=%u d=%u\n", i, e, d); return 1; } \
    memcpy(p, &init, sizeof(T)); u64 ok = OK(p, expected, desired); cases++; \
    if (ok != (u64)want_ok || *p != want || !GUARDS_INTACT(T)) { \
      printf(#OK " i=%u e=%u d=%u ok=%llu want=%d\n", i, e, d, (unsigned long long)ok, want_ok); return 1; } \
  } } while (0)
"#;

fn memory_order(ordering: Ordering) -> &'static str {
    match ordering {
        Ordering::Relaxed => "memory_order_relaxed",
        Ordering::Acquire => "memory_order_acquire",
        Ordering::Release => "memory_order_release",
        Ordering::AcqRel => "memory_order_acq_rel",
        Ordering::SeqCst => "memory_order_seq_cst",
    }
}

/// The RMW matrix: module, C driver, and per-function expected window.
struct Matrix {
    module: Module,
    driver: String,
    expected_cases: u64,
    /// `(bits, cas, load acquire, store release)` per function, in order.
    windows: Vec<(u32, bool, bool, bool)>,
}

fn rmw_matrix(triple: &str) -> Matrix {
    let mut module = module(triple, "llsc_rmw_matrix");
    let mut declarations = String::new();
    let mut calls = String::new();
    let mut windows = Vec::new();
    let mut expected_cases = 0u64;
    for (name, op, signed, oracle) in RMW_OPS {
        for width in WIDTHS {
            let c_type = if signed { width.signed } else { width.unsigned };
            for (index, ordering) in ORDERINGS.into_iter().enumerate() {
                let function = format!("rmw_{name}_{c_type}_{index}");
                add_rmw(&mut module, &function, op, ty_for(c_type), ordering);
                windows.push((width.bits, false, acquire(ordering), release(ordering)));
                writeln!(
                    declarations,
                    "extern {c_type} {function}({c_type}*, {c_type});"
                )
                .unwrap();
                let oracle = if oracle.starts_with("fetch_") {
                    format!("{oracle}_{c_type}")
                } else {
                    oracle.to_string()
                };
                writeln!(
                    calls,
                    "CHECK_RMW({c_type}, {function}, {oracle}, {});",
                    memory_order(ordering)
                )
                .unwrap();
                expected_cases += 64;
            }
        }
    }
    let driver = format!(
        "{C_PRELUDE}{declarations}int main(void) {{\n{calls}if (cases != {expected_cases}UL) return 2;\n\
         printf(\"llsc_rmw_cases=%lu\\n\", cases); return 0; }}\n"
    );
    Matrix {
        module,
        driver,
        expected_cases,
        windows,
    }
}

fn cas_matrix(triple: &str) -> Matrix {
    let mut module = module(triple, "llsc_cas_matrix");
    let mut declarations = String::new();
    let mut calls = String::new();
    let mut windows = Vec::new();
    let mut expected_cases = 0u64;
    for (c_type, bits, values) in [
        ("b1", 8, 2u64),
        ("u8", 8, 8),
        ("u16", 16, 8),
        ("u32", 32, 8),
        ("u64", 64, 8),
    ] {
        for (index, (success, failure)) in CAS_PAIRS.into_iter().enumerate() {
            let load_acquire = acquire(success) || acquire(failure);
            // The success ordering is lifted to cover the failure ordering:
            // an acquiring failure needs an acquiring load, and a SeqCst
            // failure lifts the whole operation to SeqCst.
            let store_release = release(success) || failure == Ordering::SeqCst;
            let old = format!("cas_old_{c_type}_{index}");
            let ok = format!("cas_ok_{c_type}_{index}");
            add_cas(&mut module, &old, ty_for(c_type), success, failure, false);
            add_cas(&mut module, &ok, ty_for(c_type), success, failure, true);
            windows.push((bits, true, load_acquire, store_release));
            windows.push((bits, true, load_acquire, store_release));
            writeln!(
                declarations,
                "extern {c_type} {old}({c_type}*, {c_type}, {c_type});\n\
                 extern u64 {ok}({c_type}*, {c_type}, {c_type});"
            )
            .unwrap();
            writeln!(calls, "CHECK_CAS({c_type}, {old}, {ok});").unwrap();
            expected_cases += 2 * values * values * values;
        }
    }
    let driver = format!(
        "{C_PRELUDE}{declarations}int main(void) {{\n{calls}if (cases != {expected_cases}UL) return 2;\n\
         printf(\"llsc_cas_cases=%lu\\n\", cases); return 0; }}\n"
    );
    Matrix {
        module,
        driver,
        expected_cases,
        windows,
    }
}

fn run_matrix(tag: &str, matrix: &Matrix, marker: &str) -> u64 {
    let triple = compile_triple();
    let mut executed = 0;
    for opt_level in OPT_LEVELS {
        let objects = compile_baseline(&matrix.module, triple, opt_level);
        assert_eq!(objects.len(), matrix.windows.len());
        for (object, &(bits, cas, load_acquire, store_release)) in
            objects.iter().zip(&matrix.windows)
        {
            check_single_window(object, bits, cas, load_acquire, store_release);
        }
        if native_triple().is_none() {
            continue;
        }
        let stdout = link_and_run(
            &format!("{tag}-{opt_level:?}"),
            &objects,
            &matrix.driver,
            &[],
        );
        assert_eq!(
            stdout.trim(),
            format!("{marker}={}", matrix.expected_cases),
            "{tag} {opt_level:?}"
        );
        executed += matrix.expected_cases;
    }
    executed
}

#[test]
fn baseline_llsc_rmw_matches_c11_for_every_op_width_and_ordering_o0_through_o3() {
    let matrix = rmw_matrix(compile_triple());
    assert_eq!(matrix.windows.len(), 10 * 4 * 5);
    let executed = run_matrix("rmw", &matrix, "llsc_rmw_cases");
    if native_triple().is_some() {
        assert_eq!(executed, 4 * 12_800);
        println!(
            "{executed} native LL/SC RMW checks (10 ops x 4 widths x 5 orderings x 64 pairs, O0-O3)"
        );
    }
}

#[test]
fn baseline_llsc_cmpxchg_matches_c11_for_every_width_and_ordering_pair_o0_through_o3() {
    let matrix = cas_matrix(compile_triple());
    assert_eq!(matrix.windows.len(), 5 * 15 * 2);
    assert_eq!(
        matrix.expected_cases,
        15 * (2 * 2 * 2 * 2 + 4 * 2 * 8 * 8 * 8)
    );
    let executed = run_matrix("cas", &matrix, "llsc_cas_cases");
    if native_triple().is_some() {
        assert_eq!(executed, 4 * 61_680);
        println!("{executed} native LL/SC compare-exchange checks (5 widths x 15 pairs, O0-O3)");
    }
}

// ---------------------------------------------------------------------------
// Sub-word operands whose registers carry bits above the access width
// ---------------------------------------------------------------------------

/// `Trunc` of a 32-bit parameter `operand` to `narrow`, as `result`.
fn trunc_node(narrow: &Ty, operand: u32, result: u32) -> InstrNode {
    InstrNode::new(Inst::Cast {
        op: CastOp::Trunc,
        src_ty: Ty::U32,
        dst_ty: narrow.clone(),
        operand: ValueId::new(operand),
    })
    .with_result(ValueId::new(result))
}

/// `fn(p: *T, expected: u32, desired: u32)`: compare-exchange on the
/// truncated operands, returning the old value or the success flag.
fn add_dirty_cas(module: &mut Module, name: &str, ty: Ty, return_success: bool) {
    let mut body = vec![
        trunc_node(&ty, 1, 3),
        trunc_node(&ty, 2, 4),
        InstrNode::new(Inst::CmpXchg {
            ty: ty.clone(),
            ptr: ValueId::new(0),
            expected: ValueId::new(3),
            desired: ValueId::new(4),
            success: Ordering::SeqCst,
            failure: Ordering::Acquire,
            weak: false,
        })
        .with_results(vec![ValueId::new(5), ValueId::new(6)]),
    ];
    let result = if return_success {
        body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::Bool,
                dst_ty: Ty::U64,
                operand: ValueId::new(6),
            })
            .with_result(ValueId::new(7)),
        );
        ValueId::new(7)
    } else {
        ValueId::new(5)
    };
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));
    add_function(
        module,
        name,
        vec![Ty::PtrMut(Box::new(ty.clone())), Ty::U32, Ty::U32],
        vec![if return_success { Ty::U64 } else { ty }],
        body,
    );
}

/// `fn(p: *T, value: u32) -> T`: RMW `op` on the truncated value.
fn add_dirty_rmw(module: &mut Module, name: &str, op: AtomicRMWOp, ty: Ty) {
    add_function(
        module,
        name,
        vec![Ty::PtrMut(Box::new(ty.clone())), Ty::U32],
        vec![ty.clone()],
        vec![
            trunc_node(&ty, 1, 2),
            InstrNode::new(Inst::AtomicRMW {
                op,
                ty,
                ptr: ValueId::new(0),
                value: ValueId::new(2),
                ordering: Ordering::AcqRel,
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(3)],
            }),
        ],
    );
}

const DIRTY_DRIVER_MACROS: &str = r#"
/* Bits above the access width that the truncated operand registers carry. */
static const u32 JUNK[] = {0u, 0xa5a5a5a5u, 0xffffffffu};
#define NJ (sizeof(JUNK) / sizeof(JUNK[0]))
#define WIDTH_MASK(T) ((u32)((1ull << (8 * sizeof(T))) - 1))
#define DIRTY(T, X, J) (((u32)(X) & WIDTH_MASK(T)) | (JUNK[J] & ~WIDTH_MASK(T)))
#define CHECK_DIRTY_RMW(T, FN, ORACLE) do { \
  for (unsigned i = 0; i < NV(T); i++) for (unsigned j = 0; j < NV(T); j++) for (unsigned k = 0; k < NJ; k++) { \
    T init = V_##T[i], val = V_##T[j]; \
    _Alignas(16) unsigned char buf[32]; memset(buf, GUARD, sizeof buf); \
    T *p = (T *)(buf + 8); memcpy(p, &init, sizeof(T)); \
    _Atomic(T) oracle = init; T want_old = ORACLE(&oracle, val, memory_order_acq_rel); T want = atomic_load(&oracle); \
    T got = FN(p, DIRTY(T, val, k)); cases++; \
    if (got != want_old || *p != want || !GUARDS_INTACT(T)) { \
      printf(#FN " i=%u j=%u k=%u old=%llx/%llx mem=%llx/%llx\n", i, j, k, (unsigned long long)got, \
        (unsigned long long)want_old, (unsigned long long)*p, (unsigned long long)want); return 1; } \
  } } while (0)
#define CHECK_SEXT_UNSIGNED_RMW(S, U, FN, ORACLE) do { \
  for (unsigned i = 0; i < NV(S); i++) for (unsigned j = 0; j < NV(S); j++) { \
    S init = V_##S[i], val = V_##S[j]; \
    _Alignas(16) unsigned char buf[32]; memset(buf, GUARD, sizeof buf); \
    S *p = (S *)(buf + 8); memcpy(p, &init, sizeof(S)); \
    _Atomic(U) oracle = (U)init; U want_old = ORACLE(&oracle, (U)val, memory_order_acq_rel); U want = atomic_load(&oracle); \
    U got = (U)FN(p, val); cases++; \
    if (got != want_old || (U)*p != want || !GUARDS_INTACT(S)) { \
      printf(#FN " i=%u j=%u old=%llx/%llx mem=%llx/%llx\n", i, j, (unsigned long long)got, \
        (unsigned long long)want_old, (unsigned long long)(U)*p, (unsigned long long)want); return 1; } \
  } } while (0)
#define CHECK_DIRTY_CAS(T, OLD, OK) do { \
  for (unsigned i = 0; i < NV(T); i++) for (unsigned e = 0; e < NV(T); e++) \
  for (unsigned d = 0; d < NV(T); d++) for (unsigned k = 0; k < NJ; k++) { \
    T init = V_##T[i], expected = V_##T[e], desired = V_##T[d]; \
    _Atomic(T) oracle = init; T seen = expected; \
    bool want_ok = atomic_compare_exchange_strong(&oracle, &seen, desired); \
    T want = atomic_load(&oracle); \
    _Alignas(16) unsigned char buf[32]; memset(buf, GUARD, sizeof buf); \
    T *p = (T *)(buf + 8); memcpy(p, &init, sizeof(T)); \
    T old = OLD(p, DIRTY(T, expected, k), DIRTY(T, desired, (k + 1) % NJ)); cases++; \
    if (old != seen || *p != want || !GUARDS_INTACT(T)) { \
      printf(#OLD " i=%u e=%u d=%u k=%u\n", i, e, d, k); return 1; } \
    memcpy(p, &init, sizeof(T)); u64 ok = OK(p, DIRTY(T, expected, k), DIRTY(T, desired, (k + 1) % NJ)); cases++; \
    if (ok != (u64)want_ok || *p != want || !GUARDS_INTACT(T)) { \
      printf(#OK " i=%u e=%u d=%u k=%u ok=%llu want=%d\n", i, e, d, k, (unsigned long long)ok, want_ok); return 1; } \
  } } while (0)
"#;

/// Adversarial control for the sub-word operand normalization inside the
/// expanded loops. LDXR{B,H} zero-extends the loaded value, but a narrow
/// operand produced by `Trunc` (or passed sign-extended) may carry arbitrary
/// bits above the access width. The byte/halfword CAS must compare against
/// the zero-extended expected value, and min/max must extend `value` by the
/// operation's signedness before comparing. Every other matrix passes clean
/// (ABI-extended) operands, so dropping any of those extensions would go
/// unnoticed there; here the operand registers reach the pseudo dirty.
#[test]
fn baseline_llsc_subword_operands_with_dirty_high_bits_match_c11_o0_through_o3() {
    let triple = compile_triple();
    let mut source = module(triple, "llsc_dirty_subword");
    let mut declarations = String::new();
    let mut calls = String::new();
    let mut windows = Vec::new();
    let mut expected_cases = 0u64;
    for (c_type, bits) in [("u8", 8), ("u16", 16), ("i8", 8), ("i16", 16)] {
        let old = format!("dirty_cas_old_{c_type}");
        let ok = format!("dirty_cas_ok_{c_type}");
        add_dirty_cas(&mut source, &old, ty_for(c_type), false);
        add_dirty_cas(&mut source, &ok, ty_for(c_type), true);
        windows.push((bits, true));
        windows.push((bits, true));
        writeln!(
            declarations,
            "extern {c_type} {old}({c_type}*, u32, u32);\nextern u64 {ok}({c_type}*, u32, u32);"
        )
        .unwrap();
        writeln!(calls, "CHECK_DIRTY_CAS({c_type}, {old}, {ok});").unwrap();
        expected_cases += 2 * 8 * 8 * 8 * 3;
    }
    // Signed narrow parameters arrive sign-extended by the caller: negative
    // expected values carry ones above the access width, while LDXR{B,H}
    // zero-extends the loaded value.
    for (c_type, bits) in [("i8", 8), ("i16", 16)] {
        let old = format!("sext_cas_old_{c_type}");
        let ok = format!("sext_cas_ok_{c_type}");
        add_cas(
            &mut source,
            &old,
            ty_for(c_type),
            Ordering::SeqCst,
            Ordering::Acquire,
            false,
        );
        add_cas(
            &mut source,
            &ok,
            ty_for(c_type),
            Ordering::SeqCst,
            Ordering::Acquire,
            true,
        );
        windows.push((bits, true));
        windows.push((bits, true));
        writeln!(
            declarations,
            "extern {c_type} {old}({c_type}*, {c_type}, {c_type});\nextern u64 {ok}({c_type}*, {c_type}, {c_type});"
        )
        .unwrap();
        writeln!(calls, "CHECK_CAS({c_type}, {old}, {ok});").unwrap();
        expected_cases += 2 * 8 * 8 * 8;
    }
    for (name, op, signed) in [
        ("smax", AtomicRMWOp::Max, true),
        ("smin", AtomicRMWOp::Min, true),
        ("umax", AtomicRMWOp::UMax, false),
        ("umin", AtomicRMWOp::UMin, false),
    ] {
        for (width, bits) in [(("i8", "u8"), 8), (("i16", "u16"), 16)] {
            let c_type = if signed { width.0 } else { width.1 };
            let function = format!("dirty_{name}_{c_type}");
            add_dirty_rmw(&mut source, &function, op, ty_for(c_type));
            windows.push((bits, false));
            writeln!(declarations, "extern {c_type} {function}({c_type}*, u32);").unwrap();
            let oracle = if name.ends_with("max") {
                "fetch_max"
            } else {
                "fetch_min"
            };
            writeln!(
                calls,
                "CHECK_DIRTY_RMW({c_type}, {function}, {oracle}_{c_type});"
            )
            .unwrap();
            expected_cases += 8 * 8 * 3;
        }
    }
    // Unsigned min/max over a signed-typed narrow value: the caller
    // sign-extends it, so the comparison must zero-extend it first.
    for (name, op, signed, unsigned, bits) in [
        ("umax", AtomicRMWOp::UMax, "i8", "u8", 8),
        ("umin", AtomicRMWOp::UMin, "i8", "u8", 8),
        ("umax", AtomicRMWOp::UMax, "i16", "u16", 16),
        ("umin", AtomicRMWOp::UMin, "i16", "u16", 16),
    ] {
        let function = format!("sext_{name}_{signed}");
        add_rmw(&mut source, &function, op, ty_for(signed), Ordering::AcqRel);
        windows.push((bits, false));
        writeln!(
            declarations,
            "extern {signed} {function}({signed}*, {signed});"
        )
        .unwrap();
        let oracle = if name == "umax" {
            "fetch_max"
        } else {
            "fetch_min"
        };
        writeln!(
            calls,
            "CHECK_SEXT_UNSIGNED_RMW({signed}, {unsigned}, {function}, {oracle}_{unsigned});"
        )
        .unwrap();
        expected_cases += 8 * 8;
    }
    assert_eq!(windows.len(), 24);
    assert_eq!(expected_cases, 4 * 3072 + 2 * 1024 + 8 * 192 + 4 * 64);
    let driver = format!(
        "{C_PRELUDE}{DIRTY_DRIVER_MACROS}{declarations}int main(void) {{\n{calls}\
         if (cases != {expected_cases}UL) return 2;\n\
         printf(\"llsc_dirty_cases=%lu\\n\", cases); return 0; }}\n"
    );
    let mut executed = 0;
    for opt_level in OPT_LEVELS {
        let objects = compile_baseline(&source, triple, opt_level);
        assert_eq!(objects.len(), windows.len());
        for (object, &(bits, cas)) in objects.iter().zip(&windows) {
            check_single_window(object, bits, cas, true, true);
        }
        if native_triple().is_none() {
            continue;
        }
        let stdout = link_and_run(&format!("dirty-{opt_level:?}"), &objects, &driver, &[]);
        assert_eq!(
            stdout.trim(),
            format!("llsc_dirty_cases={expected_cases}"),
            "{opt_level:?}"
        );
        executed += expected_cases;
    }
    if native_triple().is_some() {
        assert_eq!(executed, 4 * expected_cases);
        println!("{executed} native dirty-operand sub-word LL/SC checks (O0-O3)");
    }
}

// ---------------------------------------------------------------------------
// Multi-threaded contention
// ---------------------------------------------------------------------------

const CONTENTION_DRIVER: &str = r#"
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#define THREADS 8
#define ITERS 25000
extern uint8_t fetch_add_u8(uint8_t *, uint8_t);
extern uint16_t fetch_add_u16(uint16_t *, uint16_t);
extern uint32_t fetch_add_u32(uint32_t *, uint32_t);
extern uint64_t fetch_add_u64(uint64_t *, uint64_t);
extern uint64_t fetch_sub_u64(uint64_t *, uint64_t);
extern uint64_t cas_u64(uint64_t *, uint64_t, uint64_t);
extern uint8_t cas_u8(uint8_t *, uint8_t, uint8_t);
extern uint32_t swap_acquire_u32(uint32_t *, uint32_t);
extern uint32_t swap_release_u32(uint32_t *, uint32_t);
extern uint64_t fetch_umax_u64(uint64_t *, uint64_t);
static _Alignas(64) uint8_t c8;
static _Alignas(64) uint16_t c16;
static _Alignas(64) uint32_t c32;
static _Alignas(64) uint64_t c64;
static _Alignas(64) uint64_t down = (uint64_t)THREADS * ITERS;
static _Alignas(64) uint64_t cas_counter;
static _Alignas(64) uint8_t cas8_counter;
static _Alignas(64) uint32_t lock;
static _Alignas(64) unsigned long plain;
static _Alignas(64) uint64_t high;
static void *worker(void *arg) {
  uint64_t id = (uint64_t)(uintptr_t)arg;
  for (int i = 0; i < ITERS; i++) {
    fetch_add_u8(&c8, 1); fetch_add_u16(&c16, 1); fetch_add_u32(&c32, 1); fetch_add_u64(&c64, 1);
    /* Mixed codegen: the C compiler's own atomics (inline LSE on Apple
       arm64; __aarch64_* outline helpers under -moutline-atomics on Linux)
       race the CG LL/SC loops on the same words. */
    __atomic_fetch_add(&c64, 1, __ATOMIC_SEQ_CST);
    fetch_sub_u64(&down, 1);
    uint64_t old = __atomic_load_n(&cas_counter, __ATOMIC_RELAXED);
    for (;;) { uint64_t seen = cas_u64(&cas_counter, old, old + 1); if (seen == old) break; old = seen; }
    uint64_t c_old = __atomic_load_n(&cas_counter, __ATOMIC_RELAXED);
    while (!__atomic_compare_exchange_n(&cas_counter, &c_old, c_old + 1, 0, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED)) {}
    uint8_t old8 = __atomic_load_n(&cas8_counter, __ATOMIC_RELAXED);
    for (;;) { uint8_t seen = cas_u8(&cas8_counter, old8, (uint8_t)(old8 + 1)); if (seen == old8) break; old8 = seen; }
    /* Test-and-test-and-set: spin on a plain relaxed load and attempt the
       acquiring LL/SC exchange only when the lock looks free, so waiters do
       not keep breaking the holder's exclusive monitor on release. */
    for (;;) {
      while (__atomic_load_n(&lock, __ATOMIC_RELAXED) != 0) {}
      if (swap_acquire_u32(&lock, 1) == 0) break;
    }
    plain++;
    swap_release_u32(&lock, 0);
    fetch_umax_u64(&high, id * ITERS + (uint64_t)i);
  }
  return 0;
}
int main(void) {
  pthread_t threads[THREADS];
  for (uintptr_t t = 0; t < THREADS; t++) if (pthread_create(&threads[t], 0, worker, (void *)t)) return 3;
  for (int t = 0; t < THREADS; t++) pthread_join(threads[t], 0);
  const uint64_t total = (uint64_t)THREADS * ITERS;
  if (c8 != (uint8_t)total || c16 != (uint16_t)total || c32 != (uint32_t)total || c64 != 2 * total) {
    printf("fetch_add lost updates: %u %u %u %llu\n", c8, c16, c32, (unsigned long long)c64); return 1; }
  if (down != 0) { printf("fetch_sub lost updates: %llu\n", (unsigned long long)down); return 1; }
  if (cas_counter != 2 * total || cas8_counter != (uint8_t)total) {
    printf("CAS loop lost updates: %llu %u\n", (unsigned long long)cas_counter, cas8_counter); return 1; }
  if (plain != total) { printf("spinlock lost updates: %lu\n", plain); return 1; }
  if (high != total - 1) { printf("fetch_umax: %llu\n", (unsigned long long)high); return 1; }
  printf("contention_total=%llu\n", (unsigned long long)total);
  return 0;
}
"#;

fn contention_module(triple: &str) -> Module {
    let mut module = module(triple, "llsc_contention");
    for (name, op, ty, ordering) in [
        ("fetch_add_u8", AtomicRMWOp::Add, Ty::U8, Ordering::Relaxed),
        ("fetch_add_u16", AtomicRMWOp::Add, Ty::U16, Ordering::AcqRel),
        ("fetch_add_u32", AtomicRMWOp::Add, Ty::U32, Ordering::SeqCst),
        (
            "fetch_add_u64",
            AtomicRMWOp::Add,
            Ty::U64,
            Ordering::Relaxed,
        ),
        (
            "fetch_sub_u64",
            AtomicRMWOp::Sub,
            Ty::U64,
            Ordering::Release,
        ),
        (
            "swap_acquire_u32",
            AtomicRMWOp::Xchg,
            Ty::U32,
            Ordering::Acquire,
        ),
        (
            "swap_release_u32",
            AtomicRMWOp::Xchg,
            Ty::U32,
            Ordering::Release,
        ),
        (
            "fetch_umax_u64",
            AtomicRMWOp::UMax,
            Ty::U64,
            Ordering::SeqCst,
        ),
    ] {
        add_rmw(&mut module, name, op, ty, ordering);
    }
    add_cas(
        &mut module,
        "cas_u64",
        Ty::U64,
        Ordering::AcqRel,
        Ordering::Acquire,
        false,
    );
    add_cas(
        &mut module,
        "cas_u8",
        Ty::U8,
        Ordering::SeqCst,
        Ordering::Relaxed,
        false,
    );
    module
}

#[test]
fn baseline_llsc_multithreaded_contention_counts_exactly_o0_through_o3() {
    let triple = compile_triple();
    let module = contention_module(triple);
    let mut runs = 0;
    for opt_level in OPT_LEVELS {
        let objects = compile_baseline(&module, triple, opt_level);
        for object in &objects {
            let words = text_words(object);
            assert!(!words.iter().any(|&w| is_lse(w)));
            assert_eq!(exclusive_windows(&words).len(), 1);
        }
        if native_triple().is_none() {
            continue;
        }
        // On Linux, force the outline-atomics helpers for the C side so the
        // mixed-codegen race is LL/SC against libgcc's __aarch64_* routines;
        // on Apple arm64 the C side is inline LSE.
        let extra: &[&str] = if cfg!(target_os = "linux") {
            &["-pthread", "-moutline-atomics"]
        } else {
            &[]
        };
        let stdout = link_run_inspect(
            &format!("contention-{opt_level:?}"),
            &objects,
            CONTENTION_DRIVER,
            extra,
            &|executable| {
                if cfg!(target_os = "linux") {
                    assert!(
                        executable
                            .windows(b"__aarch64_ldadd8_acq_rel".len())
                            .any(|name| name == b"__aarch64_ldadd8_acq_rel"),
                        "the C side must use the outline-atomics helper"
                    );
                } else {
                    let words = text_words(executable);
                    assert!(
                        words.iter().any(|&w| is_lse(w)),
                        "the C side must use inline LSE on Apple arm64"
                    );
                }
            },
        );
        assert_eq!(stdout.trim(), "contention_total=200000", "{opt_level:?}");
        runs += 1;
    }
    if native_triple().is_some() {
        assert_eq!(runs, 4);
        println!(
            "8 threads x 25000 iterations, 10 LL/SC functions racing C-compiler atomics, \
             exact counts at O0-O3"
        );
    }
}

// ---------------------------------------------------------------------------
// Register pressure: spills stay outside every exclusive window
// ---------------------------------------------------------------------------

const PRESSURE_VALUES: u32 = 40;

/// `pressure(u64 *src, u64 *atom, u8 *byte, u64 v) -> u64`: loads
/// `PRESSURE_VALUES` words, keeps all of them live across a 64-bit fetch_add,
/// a 64-bit compare-exchange and an 8-bit fetch_umax, then folds them.
fn pressure_module(triple: &str) -> Module {
    let mut module = module(triple, "llsc_pressure");
    let mut body = Vec::new();
    let mut next = 5u32;
    let mut fresh = || {
        let id = ValueId::new(next);
        next += 1;
        id
    };
    let mut loaded = Vec::new();
    for index in 0..PRESSURE_VALUES {
        let offset = fresh();
        body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(i128::from(index)),
            })
            .with_result(offset),
        );
        let address = fresh();
        body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U64,
                base: ValueId::new(0),
                indices: vec![offset],
                inbounds: true,
            })
            .with_result(address),
        );
        let value = fresh();
        body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr: address,
                volatile: false,
                align: Some(8),
            })
            .with_result(value),
        );
        loaded.push(value);
    }
    let added = fresh();
    body.push(
        InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty: Ty::U64,
            ptr: ValueId::new(1),
            value: ValueId::new(3),
            ordering: Ordering::SeqCst,
        })
        .with_result(added),
    );
    let swapped = fresh();
    let swapped_ok = fresh();
    body.push(
        InstrNode::new(Inst::CmpXchg {
            ty: Ty::U64,
            ptr: ValueId::new(1),
            expected: loaded[0],
            desired: loaded[1],
            success: Ordering::AcqRel,
            failure: Ordering::Acquire,
            weak: false,
        })
        .with_results(vec![swapped, swapped_ok]),
    );
    let byte_value = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U64,
            dst_ty: Ty::U8,
            operand: loaded[2],
        })
        .with_result(byte_value),
    );
    let byte_old = fresh();
    body.push(
        InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::UMax,
            ty: Ty::U8,
            ptr: ValueId::new(2),
            value: byte_value,
            ordering: Ordering::Relaxed,
        })
        .with_result(byte_old),
    );
    let byte_wide = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U8,
            dst_ty: Ty::U64,
            operand: byte_old,
        })
        .with_result(byte_wide),
    );
    // A 128-bit fetch_add (five defs and three uses on one pair pseudo)
    // under the same pressure.
    let wide_value = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::U64,
            dst_ty: Ty::U128,
            operand: ValueId::new(3),
        })
        .with_result(wide_value),
    );
    let wide_old = fresh();
    body.push(
        InstrNode::new(Inst::AtomicRMW {
            op: AtomicRMWOp::Add,
            ty: Ty::U128,
            ptr: ValueId::new(4),
            value: wide_value,
            ordering: Ordering::SeqCst,
        })
        .with_result(wide_old),
    );
    let wide_lo = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U128,
            dst_ty: Ty::U64,
            operand: wide_old,
        })
        .with_result(wide_lo),
    );
    let shift = fresh();
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U128,
            value: Constant::Int(64),
        })
        .with_result(shift),
    );
    let wide_shifted = fresh();
    body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::LShr,
            ty: Ty::U128,
            lhs: wide_old,
            rhs: shift,
        })
        .with_result(wide_shifted),
    );
    let wide_hi = fresh();
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::Trunc,
            src_ty: Ty::U128,
            dst_ty: Ty::U64,
            operand: wide_shifted,
        })
        .with_result(wide_hi),
    );
    let mut accumulator = added;
    for &value in [swapped, byte_wide, wide_lo, wide_hi]
        .iter()
        .chain(loaded.iter())
    {
        let multiplied = fresh();
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: Ty::U64,
                lhs: accumulator,
                rhs: ValueId::new(3),
            })
            .with_result(multiplied),
        );
        let summed = fresh();
        body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Xor,
                ty: Ty::U64,
                lhs: multiplied,
                rhs: value,
            })
            .with_result(summed),
        );
        accumulator = summed;
    }
    body.push(InstrNode::new(Inst::Return {
        values: vec![accumulator],
    }));
    add_function(
        &mut module,
        "pressure",
        vec![
            Ty::PtrMut(Box::new(Ty::U64)),
            Ty::PtrMut(Box::new(Ty::U64)),
            Ty::PtrMut(Box::new(Ty::U8)),
            Ty::U64,
            Ty::PtrMut(Box::new(Ty::U128)),
        ],
        vec![Ty::U64],
        body,
    );
    module
}

const PRESSURE_DRIVER: &str = r#"
#include <stdint.h>
#include <stdio.h>
#define N 40
typedef unsigned __int128 u128;
extern uint64_t pressure(uint64_t *src, uint64_t *atom, uint8_t *byte, uint64_t v, u128 *wide);
static uint64_t model(uint64_t *src, uint64_t *atom, uint8_t *byte, uint64_t v, u128 *wide) {
  uint64_t added = *atom; *atom += v;
  uint64_t swapped = *atom; if (*atom == src[0]) *atom = src[1];
  uint8_t b = (uint8_t)src[2]; uint64_t byte_old = *byte; if (b > *byte) *byte = b;
  u128 wide_old = *wide; *wide += v;
  uint64_t acc = added;
  acc = (acc * v) ^ swapped;
  acc = (acc * v) ^ byte_old;
  acc = (acc * v) ^ (uint64_t)wide_old;
  acc = (acc * v) ^ (uint64_t)(wide_old >> 64);
  for (int i = 0; i < N; i++) acc = (acc * v) ^ src[i];
  return acc;
}
int main(void) {
  uint64_t src[N];
  unsigned checks = 0;
  for (uint64_t round = 0; round < 64; round++) {
    for (int i = 0; i < N; i++) src[i] = 0x9e3779b97f4a7c15ULL * (uint64_t)(i + 1) ^ round;
    uint64_t v = 3 + round * 2;
    uint64_t atom_a = round & 1 ? src[0] - v : round * 7, atom_b = atom_a;
    uint8_t byte_a = (uint8_t)(round * 13), byte_b = byte_a;
    _Alignas(16) u128 wide_a = ((u128)(round * 5) << 64) | (uint64_t)~round;
    _Alignas(16) u128 wide_b = wide_a;
    uint64_t want = model(src, &atom_b, &byte_b, v, &wide_b);
    uint64_t got = pressure(src, &atom_a, &byte_a, v, &wide_a);
    if (got != want || atom_a != atom_b || byte_a != byte_b || wide_a != wide_b) {
      printf("round %llu: got %llx want %llx atom %llx/%llx byte %u/%u\n", (unsigned long long)round,
        (unsigned long long)got, (unsigned long long)want, (unsigned long long)atom_a,
        (unsigned long long)atom_b, byte_a, byte_b);
      return 1;
    }
    checks++;
  }
  printf("pressure_checks=%u\n", checks);
  return 0;
}
"#;

/// Single-register SP/X29-based loads and stores (unsigned-offset or
/// unscaled forms): spill and reload traffic. Callee-saved register saves use
/// the pair forms and are not counted.
fn spill_words(words: &[u32]) -> usize {
    words
        .iter()
        .filter(|&&w| {
            (w & 0x3b00_0000 == 0x3900_0000 || w & 0x3b20_0c00 == 0x3800_0000)
                && matches!(w >> 5 & 31, 29 | 31)
        })
        .count()
}

#[test]
fn baseline_llsc_register_pressure_keeps_every_exclusive_window_spill_free() {
    let triple = compile_triple();
    let module = pressure_module(triple);
    let mut decoded = 0;
    for opt_level in OPT_LEVELS {
        let objects = compile_baseline(&module, triple, opt_level);
        assert_eq!(objects.len(), 1);
        let words = text_words(&objects[0]);
        assert!(!words.iter().any(|&w| is_lse(w)));
        // Pressure is load-bearing: more live values than allocatable GPRs
        // forces spill traffic somewhere in the function.
        assert!(
            spill_words(&words) >= 8,
            "{opt_level:?}: expected spill traffic, found {}",
            spill_words(&words)
        );
        let windows = exclusive_windows(&words);
        assert_eq!(windows.len(), 4, "{opt_level:?}: {windows:?}");
        assert_eq!(windows.iter().filter(|w| w.cas).count(), 1);
        assert_eq!(windows.iter().filter(|w| w.load.pair).count(), 1);
        decoded += windows.len();
        if native_triple().is_some() {
            let stdout = link_and_run(
                &format!("pressure-{opt_level:?}"),
                &objects,
                PRESSURE_DRIVER,
                &[],
            );
            assert_eq!(stdout.trim(), "pressure_checks=64", "{opt_level:?}");
        }
    }
    assert_eq!(decoded, 16);
}

// ---------------------------------------------------------------------------
// Production Linux path and closed forms
// ---------------------------------------------------------------------------

/// The generic Linux AOT profile is BASELINE: the production compiler
/// (`Compiler::new_for_target_spec(aarch64-unknown-linux-gnu)`, no profile
/// override) must emit LL/SC loops for every RMW op/width/ordering and every
/// CAS width/ordering pair instead of refusing. Every host decodes the ELF
/// words; an aarch64 Linux GNU host also links the production object with
/// the same C11 oracle drivers and runs them natively.
#[test]
fn generic_linux_production_compiler_emits_llsc_loops_and_matches_c11() {
    let triple = "aarch64-unknown-linux-gnu";
    let linux_native = native_triple() == Some(triple);
    let mut executed = 0;
    for (matrix, marker) in [
        (rmw_matrix(triple), "llsc_rmw_cases"),
        (cas_matrix(triple), "llsc_cas_cases"),
    ] {
        let expected_cas = matrix.windows.iter().filter(|window| window.1).count();
        for opt_level in OPT_LEVELS {
            let compiler = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    ..CompilerConfig::default()
                },
                TargetSpec::parse(triple).unwrap(),
            )
            .with_codegen_license(permit_unlicensed());
            let object = compiler
                .compile(&matrix.module)
                .unwrap_or_else(|error| panic!("{marker} {opt_level:?}: {error}"))
                .object_code;
            assert!(
                !names_outline_atomics_helper(&object),
                "{opt_level:?}: generic Linux atomics must not need __aarch64_* helpers"
            );
            let words = text_words(&object);
            assert!(
                !words.iter().any(|&w| is_lse(w)),
                "{opt_level:?}: LSE on generic Linux"
            );
            let windows = exclusive_windows(&words);
            assert_eq!(
                windows.len(),
                matrix.windows.len(),
                "{marker} {opt_level:?}"
            );
            assert_eq!(windows.iter().filter(|w| w.cas).count(), expected_cas);
            // Acquire/release multiset agrees with the per-function selection.
            let mut want: Vec<_> = matrix
                .windows
                .iter()
                .map(|&(bits, cas, load, store)| (size_field(bits), cas, load, store))
                .collect();
            let mut got: Vec<_> = windows
                .iter()
                .map(|w| (w.load.size, w.cas, w.load.ordered, w.store.ordered))
                .collect();
            want.sort_unstable();
            got.sort_unstable();
            assert_eq!(got, want, "{marker} {opt_level:?}");
            if linux_native {
                let stdout = link_and_run(
                    &format!("linux-production-{marker}-{opt_level:?}"),
                    &[object],
                    &matrix.driver,
                    &[],
                );
                assert_eq!(stdout.trim(), format!("{marker}={}", matrix.expected_cases));
                executed += matrix.expected_cases;
            }
        }
    }
    if linux_native {
        assert_eq!(executed, 4 * (12_800 + 61_680));
        println!("{executed} native checks of production generic-Linux LL/SC atomics at O0-O3");
    }
}

/// An explicitly admitted LSE profile keeps the single-instruction LSE
/// lowering; LL/SC is selected only when LSE is not admitted.
#[test]
fn lse_profile_keeps_lse_and_emits_no_exclusive_loop() {
    let triple = compile_triple();
    let mut source = module(triple, "lse_atomics");
    add_rmw(
        &mut source,
        "lse_add",
        AtomicRMWOp::Add,
        Ty::U32,
        Ordering::SeqCst,
    );
    add_cas(
        &mut source,
        "lse_cas",
        Ty::U64,
        Ordering::SeqCst,
        Ordering::SeqCst,
        false,
    );
    let lowered = permit_translate_module(&source).unwrap();
    for opt_level in OPT_LEVELS {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level,
            target_triple: triple.into(),
            ..PipelineConfig::default()
        })
        .with_aarch64_isa_profile(AArch64IsaProfile::LSE);
        for (function, _) in &lowered {
            let words = text_words(&pipeline.compile_function(function).unwrap());
            assert_eq!(words.iter().filter(|&&w| is_lse(w)).count(), 1);
            assert!(words.iter().all(|&w| exclusive(w).is_none()));
        }
    }
}

const BOOL_DRIVER_PRELUDE: &str = r#"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
static unsigned long cases;
#define GUARD 0xc3
static bool model(unsigned op, bool old, bool v) {
  switch (op) { case 0: return v; case 1: return old & v; case 2: return old | v; default: return old ^ v; }
}
#define CHECK_BOOL_RMW(FN, OP) do { for (unsigned i = 0; i < 2; i++) for (unsigned j = 0; j < 2; j++) { \
    _Alignas(8) unsigned char buf[16]; memset(buf, GUARD, sizeof buf); buf[8] = (unsigned char)i; \
    bool got = FN((bool *)(buf + 8), (bool)j); cases++; \
    if (got != (bool)i || buf[8] != (unsigned char)model(OP, i, j)) { \
      printf(#FN " i=%u j=%u got=%d mem=%u\n", i, j, got, buf[8]); return 1; } \
    for (unsigned k = 0; k < 16; k++) if (k != 8 && buf[k] != GUARD) { printf(#FN " guard %u\n", k); return 1; } \
  } } while (0)
"#;

/// Bool read-modify-write admits exactly exchange and the bitwise ops (the
/// Rust `AtomicBool` surface): byte-sized LL/SC loops on the baseline
/// profile and byte LSE ops when LSE is admitted, checked against a C model
/// with guard bytes at O0-O3. Arithmetic and min/max stay named refusals.
#[test]
fn bool_rmw_logical_ops_match_c_model_and_arithmetic_stays_closed() {
    let triple = compile_triple();
    let mut source = module(triple, "bool_rmw");
    let mut declarations = String::new();
    let mut calls = String::new();
    let ops = [
        ("xchg", AtomicRMWOp::Xchg),
        ("and", AtomicRMWOp::And),
        ("or", AtomicRMWOp::Or),
        ("xor", AtomicRMWOp::Xor),
    ];
    let mut expected = Vec::new();
    for (op_index, (name, op)) in ops.into_iter().enumerate() {
        for (index, ordering) in ORDERINGS.into_iter().enumerate() {
            let function = format!("bool_{name}_{index}");
            add_rmw(&mut source, &function, op, Ty::Bool, ordering);
            expected.push((acquire(ordering), release(ordering)));
            writeln!(declarations, "extern bool {function}(bool*, bool);").unwrap();
            writeln!(calls, "CHECK_BOOL_RMW({function}, {op_index});").unwrap();
        }
    }
    let driver = format!(
        "{BOOL_DRIVER_PRELUDE}{declarations}int main(void) {{\n{calls}if (cases != 80UL) return 2;\n\
         printf(\"bool_rmw_cases=%lu\\n\", cases); return 0; }}\n"
    );
    let lowered = permit_translate_module(&source).unwrap();
    let mut runs = 0;
    let mut unsupported_lse_signals = 0;
    for profile in [AArch64IsaProfile::BASELINE, AArch64IsaProfile::LSE] {
        for opt_level in OPT_LEVELS {
            let pipeline = Pipeline::new(PipelineConfig {
                opt_level,
                target_triple: triple.into(),
                ..PipelineConfig::default()
            })
            .with_aarch64_isa_profile(profile);
            let objects: Vec<_> = lowered
                .iter()
                .map(|(function, _)| pipeline.compile_function(function).unwrap())
                .collect();
            for (object, &(load_acquire, store_release)) in objects.iter().zip(&expected) {
                if profile == AArch64IsaProfile::BASELINE {
                    check_single_window(object, 8, false, load_acquire, store_release);
                } else {
                    let words = text_words(object);
                    let lse: Vec<_> = words.iter().filter(|&&w| is_lse(w)).collect();
                    assert_eq!(lse.len(), 1, "one byte LSE op");
                    assert_eq!(*lse[0] >> 30, 0, "Bool LSE RMW must be a byte access");
                    assert!(words.iter().all(|&w| exclusive(w).is_none()));
                }
            }
            if native_triple().is_some() {
                if profile.is_supported_by_host() {
                    let stdout = link_and_run(
                        &format!("bool-{profile}-{opt_level:?}"),
                        &objects,
                        &driver,
                        &[],
                    );
                    assert_eq!(stdout.trim(), "bool_rmw_cases=80");
                    runs += 1;
                } else {
                    assert_eq!(profile, AArch64IsaProfile::LSE);
                    let stdout = link_run_inspect_outcome(
                        &format!("bool-unsupported-{profile}-{opt_level:?}"),
                        &objects,
                        &driver,
                        &[],
                        &|_| {},
                        Some(4), // SIGILL: forced LSE on a CPU that does not implement it.
                    );
                    assert!(stdout.is_empty());
                    unsupported_lse_signals += 1;
                }
            }
        }
    }
    if native_triple().is_some() {
        let lse_supported = AArch64IsaProfile::LSE.is_supported_by_host();
        assert_eq!(runs, if lse_supported { 8 } else { 4 });
        assert_eq!(unsupported_lse_signals, if lse_supported { 0 } else { 4 });
        assert_eq!(runs + unsupported_lse_signals, 8);
        eprintln!(
            "AARCH64_BOOL_CPU_PROFILE cells=8 matched={runs} unsupported_lse_sigill={unsupported_lse_signals}"
        );
    }

    let mut refusals = 0;
    for op in [
        AtomicRMWOp::Add,
        AtomicRMWOp::Sub,
        AtomicRMWOp::Max,
        AtomicRMWOp::Min,
        AtomicRMWOp::UMax,
        AtomicRMWOp::UMin,
    ] {
        let mut closed = module(triple, "bool_closed");
        add_rmw(&mut closed, "bool_closed", op, Ty::Bool, Ordering::SeqCst);
        let lowered = permit_translate_module(&closed).unwrap();
        for profile in [AArch64IsaProfile::BASELINE, AArch64IsaProfile::LSE] {
            let error = Pipeline::new(PipelineConfig {
                target_triple: triple.into(),
                ..PipelineConfig::default()
            })
            .with_aarch64_isa_profile(profile)
            .compile_function(&lowered[0].0)
            .unwrap_err()
            .to_string();
            assert!(
                error.contains("Bool AtomicRmw admits only xchg/and/or/xor"),
                "{op:?} {profile}: {error}"
            );
            refusals += 1;
        }
    }
    assert_eq!(refusals, 12);
}

// ---------------------------------------------------------------------------
// 128-bit atomics: LDXP/STXP pair loops on every profile
// ---------------------------------------------------------------------------

fn add_load(module: &mut Module, name: &str, ty: Ty, ordering: Ordering) {
    add_function(
        module,
        name,
        vec![Ty::PtrMut(Box::new(ty.clone()))],
        vec![ty.clone()],
        vec![
            InstrNode::new(Inst::AtomicLoad {
                ty,
                ptr: ValueId::new(0),
                ordering,
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    );
}

fn add_store(module: &mut Module, name: &str, ty: Ty, ordering: Ordering) {
    add_function(
        module,
        name,
        vec![Ty::PtrMut(Box::new(ty.clone())), ty.clone()],
        vec![],
        vec![
            InstrNode::new(Inst::AtomicStore {
                ty,
                ptr: ValueId::new(0),
                value: ValueId::new(1),
                ordering,
            }),
            InstrNode::new(Inst::Return { values: vec![] }),
        ],
    );
}

const C128_PRELUDE: &str = r#"
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
typedef unsigned __int128 u128; typedef __int128 i128;
#define P(HI, LO) (((u128)(HI) << 64) | (u128)(LO))
static const u128 V_u128[] = {
  0, 1, ~(u128)0, P(1, 0), P(0, UINT64_MAX), P(0x8000000000000000ULL, 0),
  P(0x7fffffffffffffffULL, UINT64_MAX), P(0x0123456789abcdefULL, 0xfedcba9876543210ULL)
};
#define NV (sizeof(V_u128) / sizeof(V_u128[0]))
static unsigned long cases;
#define GUARD 0x5a
static int guards_intact(const unsigned char *buf) {
  for (unsigned k = 0; k < 48; k++) if ((k < 16 || k >= 32) && buf[k] != GUARD) return 0;
  return 1;
}
static u128 model(unsigned op, u128 old, u128 v) {
  switch (op) {
    case 0: return old + v; case 1: return old - v; case 2: return old & v;
    case 3: return old | v; case 4: return old ^ v; case 5: return v;
    case 6: return (i128)old > (i128)v ? old : v; case 7: return (i128)old < (i128)v ? old : v;
    case 8: return old > v ? old : v; default: return old < v ? old : v;
  }
}
#define HL(X) (unsigned long long)((X) >> 64), (unsigned long long)(X)
#define BUFFER(INIT) _Alignas(16) unsigned char buf[48]; memset(buf, GUARD, sizeof buf); \
  u128 *p = (u128 *)(buf + 16); { u128 init_ = (INIT); memcpy(p, &init_, 16); }
#define CHECK_RMW(FN, OP, T) do { for (unsigned i = 0; i < NV; i++) for (unsigned j = 0; j < NV; j++) { \
    BUFFER(V_u128[i]); u128 want = model(OP, V_u128[i], V_u128[j]); \
    u128 got = (u128)FN((T *)p, (T)V_u128[j]); cases++; \
    if (got != V_u128[i] || *p != want || !guards_intact(buf)) { \
      printf(#FN " i=%u j=%u old=%016llx%016llx mem=%016llx%016llx want=%016llx%016llx\n", i, j, \
        HL(got), HL(*p), HL(want)); return 1; } } } while (0)
#define CHECK_CAS(OLD, OK) do { for (unsigned i = 0; i < NV; i++) for (unsigned e = 0; e < NV; e++) \
  for (unsigned d = 0; d < NV; d++) { \
    u128 init = V_u128[i], expected = V_u128[e], desired = V_u128[d]; \
    bool ok_want = init == expected; u128 want = ok_want ? desired : init; \
    { BUFFER(init); u128 old = OLD(p, expected, desired); cases++; \
      if (old != init || *p != want || !guards_intact(buf)) { printf(#OLD " i=%u e=%u d=%u\n", i, e, d); return 1; } } \
    { BUFFER(init); uint64_t ok = OK(p, expected, desired); cases++; \
      if (ok != ok_want || *p != want || !guards_intact(buf)) { printf(#OK " i=%u e=%u d=%u\n", i, e, d); return 1; } } \
  } } while (0)
#define CHECK_LOAD(FN) do { for (unsigned i = 0; i < NV; i++) { BUFFER(V_u128[i]); \
    u128 got = FN(p); cases++; \
    if (got != V_u128[i] || *p != V_u128[i] || !guards_intact(buf)) { printf(#FN " i=%u\n", i); return 1; } } } while (0)
#define CHECK_STORE(FN) do { for (unsigned i = 0; i < NV; i++) for (unsigned j = 0; j < NV; j++) { \
    BUFFER(V_u128[i]); FN(p, V_u128[j]); cases++; \
    if (*p != V_u128[j] || !guards_intact(buf)) { printf(#FN " i=%u j=%u\n", i, j); return 1; } } } while (0)
"#;

/// The 128-bit matrix: every RMW op x ordering, every CAS ordering pair
/// (old and success variants), and every valid load/store ordering.
fn matrix128(triple: &str) -> Matrix {
    let mut module = module(triple, "llsc_i128_matrix");
    let mut declarations = String::new();
    let mut calls = String::new();
    let mut windows = Vec::new();
    let mut expected_cases = 0u64;
    for (op_index, (name, op, signed, _)) in RMW_OPS.into_iter().enumerate() {
        let c_type = if signed { "i128" } else { "u128" };
        for (index, ordering) in ORDERINGS.into_iter().enumerate() {
            let function = format!("rmw128_{name}_{index}");
            add_rmw(&mut module, &function, op, ty_for(c_type), ordering);
            windows.push((128, false, acquire(ordering), release(ordering)));
            writeln!(
                declarations,
                "extern {c_type} {function}({c_type}*, {c_type});"
            )
            .unwrap();
            writeln!(calls, "CHECK_RMW({function}, {op_index}, {c_type});").unwrap();
            expected_cases += 64;
        }
    }
    for (index, (success, failure)) in CAS_PAIRS.into_iter().enumerate() {
        let old = format!("cas128_old_{index}");
        let ok = format!("cas128_ok_{index}");
        add_cas(&mut module, &old, Ty::U128, success, failure, false);
        add_cas(&mut module, &ok, Ty::U128, success, failure, true);
        let load_acquire = acquire(success) || acquire(failure);
        let store_release = release(success) || failure == Ordering::SeqCst;
        windows.push((128, true, load_acquire, store_release));
        windows.push((128, true, load_acquire, store_release));
        writeln!(
            declarations,
            "extern u128 {old}(u128*, u128, u128);\nextern uint64_t {ok}(u128*, u128, u128);"
        )
        .unwrap();
        writeln!(calls, "CHECK_CAS({old}, {ok});").unwrap();
        expected_cases += 2 * 512;
    }
    for (index, (ordering, acquire_bit, release_bit)) in [
        (Ordering::Relaxed, false, false),
        (Ordering::Acquire, true, false),
        (Ordering::SeqCst, true, true),
    ]
    .into_iter()
    .enumerate()
    {
        let function = format!("load128_{index}");
        add_load(&mut module, &function, Ty::U128, ordering);
        windows.push((128, false, acquire_bit, release_bit));
        writeln!(declarations, "extern u128 {function}(u128*);").unwrap();
        writeln!(calls, "CHECK_LOAD({function});").unwrap();
        expected_cases += 8;
    }
    for (index, (ordering, acquire_bit, release_bit)) in [
        (Ordering::Relaxed, false, false),
        (Ordering::Release, false, true),
        (Ordering::SeqCst, true, true),
    ]
    .into_iter()
    .enumerate()
    {
        let function = format!("store128_{index}");
        add_store(&mut module, &function, Ty::U128, ordering);
        windows.push((128, false, acquire_bit, release_bit));
        writeln!(declarations, "extern void {function}(u128*, u128);").unwrap();
        writeln!(calls, "CHECK_STORE({function});").unwrap();
        expected_cases += 64;
    }
    let driver = format!(
        "{C128_PRELUDE}{declarations}int main(void) {{\n{calls}if (cases != {expected_cases}UL) return 2;\n\
         printf(\"llsc_i128_cases=%lu\\n\", cases); return 0; }}\n"
    );
    Matrix {
        module,
        driver,
        expected_cases,
        windows,
    }
}

/// 128-bit atomics use LDXP/STXP pair loops on the baseline AND on the LSE
/// profile (no CASP or LSE2 form is admitted), checked against a C model
/// with guard bytes at O0-O3.
#[test]
fn llsc_i128_atomics_match_c_model_on_baseline_and_lse_profiles_o0_through_o3() {
    let triple = compile_triple();
    let matrix = matrix128(triple);
    assert_eq!(matrix.windows.len(), 50 + 30 + 3 + 3);
    assert_eq!(matrix.expected_cases, 50 * 64 + 15 * 1024 + 3 * 8 + 3 * 64);
    let lowered = {
        assert!(trust_ir_build::validate::validate_module(&matrix.module).is_empty());
        permit_translate_module(&matrix.module).expect("fixture must translate")
    };
    let mut executed = 0;
    for profile in [AArch64IsaProfile::BASELINE, AArch64IsaProfile::LSE] {
        for opt_level in OPT_LEVELS {
            let pipeline = Pipeline::new(PipelineConfig {
                opt_level,
                target_triple: triple.into(),
                ..PipelineConfig::default()
            })
            .with_aarch64_isa_profile(profile);
            let objects: Vec<_> = lowered
                .iter()
                .map(|(function, _)| {
                    pipeline.compile_function(function).unwrap_or_else(|error| {
                        panic!("{} {profile} {opt_level:?}: {error}", function.name)
                    })
                })
                .collect();
            for (object, &(bits, cas, load_acquire, store_release)) in
                objects.iter().zip(&matrix.windows)
            {
                check_single_window(object, bits, cas, load_acquire, store_release);
            }
            if native_triple().is_none() {
                continue;
            }
            let stdout = link_and_run(
                &format!("i128-{profile}-{opt_level:?}"),
                &objects,
                &matrix.driver,
                &[],
            );
            assert_eq!(
                stdout.trim(),
                format!("llsc_i128_cases={}", matrix.expected_cases)
            );
            executed += matrix.expected_cases;
        }
    }
    if native_triple().is_some() {
        assert_eq!(executed, 8 * matrix.expected_cases);
        println!(
            "{executed} native 128-bit LL/SC checks (RMW, CAS, load, store; 2 profiles, O0-O3)"
        );
    }
}

const CONTENTION128_DRIVER: &str = r#"
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
typedef unsigned __int128 u128;
#define THREADS 8
#define ITERS 20000
#define STEP ((((u128)1) << 64) + 1)
extern u128 fetch_add_u128(u128 *, u128);
extern u128 cas_u128(u128 *, u128, u128);
extern u128 load_u128(u128 *);
extern void store_u128(u128 *, u128);
static _Alignas(64) u128 sum;
static _Alignas(64) u128 counter;
static _Alignas(64) u128 shared;
static _Alignas(64) unsigned long torn;
static void *worker(void *arg) {
  uint64_t id = (uint64_t)(uintptr_t)arg;
  for (uint64_t i = 0; i < ITERS; i++) {
    fetch_add_u128(&sum, STEP);
    u128 old = load_u128(&counter);
    for (;;) { u128 seen = cas_u128(&counter, old, old + STEP); if (seen == old) break; old = seen; }
    uint64_t k = id * ITERS + i;
    store_u128(&shared, (((u128)k) << 64) | k);
    u128 v = load_u128(&shared);
    if ((uint64_t)(v >> 64) != (uint64_t)v) __atomic_fetch_add(&torn, 1, __ATOMIC_RELAXED);
  }
  return 0;
}
int main(void) {
  pthread_t threads[THREADS];
  for (uintptr_t t = 0; t < THREADS; t++) if (pthread_create(&threads[t], 0, worker, (void *)t)) return 3;
  for (int t = 0; t < THREADS; t++) pthread_join(threads[t], 0);
  const u128 want = (u128)THREADS * ITERS * STEP;
  if (sum != want || counter != want) {
    printf("lost 128-bit updates: sum %016llx%016llx counter %016llx%016llx\n",
      (unsigned long long)(sum >> 64), (unsigned long long)sum,
      (unsigned long long)(counter >> 64), (unsigned long long)counter);
    return 1;
  }
  if (torn) { printf("torn 128-bit reads: %lu\n", torn); return 1; }
  printf("contention128_total=%llu\n", (unsigned long long)(THREADS * ITERS));
  return 0;
}
"#;

/// Eight threads hammer 128-bit fetch_add (carry into the high half on
/// every step), a 128-bit CAS-loop counter, and paired store/load of values
/// whose halves must match (a torn read would split them).
#[test]
fn llsc_i128_multithreaded_contention_counts_exactly_and_never_tears_o0_through_o3() {
    let triple = compile_triple();
    let mut source = module(triple, "llsc_i128_contention");
    add_rmw(
        &mut source,
        "fetch_add_u128",
        AtomicRMWOp::Add,
        Ty::U128,
        Ordering::AcqRel,
    );
    add_cas(
        &mut source,
        "cas_u128",
        Ty::U128,
        Ordering::SeqCst,
        Ordering::Acquire,
        false,
    );
    add_load(&mut source, "load_u128", Ty::U128, Ordering::Acquire);
    add_store(&mut source, "store_u128", Ty::U128, Ordering::Release);
    let mut runs = 0;
    for opt_level in OPT_LEVELS {
        let objects = compile_baseline(&source, triple, opt_level);
        for object in &objects {
            assert_eq!(exclusive_windows(&text_words(object)).len(), 1);
        }
        if native_triple().is_none() {
            continue;
        }
        let extra: &[&str] = if cfg!(target_os = "linux") {
            &["-pthread"]
        } else {
            &[]
        };
        let stdout = link_and_run(
            &format!("contention128-{opt_level:?}"),
            &objects,
            CONTENTION128_DRIVER,
            extra,
        );
        assert_eq!(stdout.trim(), "contention128_total=160000", "{opt_level:?}");
        runs += 1;
    }
    if native_triple().is_some() {
        assert_eq!(runs, 4);
    }
}

/// Debug-info emission walks register-debug provenance keyed by instruction
/// ids; the expansion reuses the pseudo's id for the defining load-exclusive
/// and adds unattributed loop instructions. Every LL/SC family must still
/// compile, with intact windows, when debug info is requested.
#[test]
fn llsc_expansion_survives_debug_info_emission() {
    let triple = compile_triple();
    let mut source = module(triple, "llsc_debug");
    add_rmw(
        &mut source,
        "dbg_add_u32",
        AtomicRMWOp::Add,
        Ty::U32,
        Ordering::SeqCst,
    );
    add_rmw(
        &mut source,
        "dbg_smax_i8",
        AtomicRMWOp::Max,
        Ty::I8,
        Ordering::Relaxed,
    );
    add_cas(
        &mut source,
        "dbg_cas_u16",
        Ty::U16,
        Ordering::AcqRel,
        Ordering::Acquire,
        true,
    );
    add_rmw(
        &mut source,
        "dbg_xor_u128",
        AtomicRMWOp::Xor,
        Ty::U128,
        Ordering::Release,
    );
    add_cas(
        &mut source,
        "dbg_cas_u128",
        Ty::U128,
        Ordering::SeqCst,
        Ordering::SeqCst,
        false,
    );
    add_load(&mut source, "dbg_load_u128", Ty::U128, Ordering::Acquire);
    let lowered = permit_translate_module(&source).unwrap();
    for opt_level in OPT_LEVELS {
        let pipeline = Pipeline::new(PipelineConfig {
            opt_level,
            emit_debug: true,
            target_triple: triple.into(),
            ..PipelineConfig::default()
        })
        .with_aarch64_isa_profile(AArch64IsaProfile::BASELINE);
        for (function, _) in &lowered {
            let object = pipeline
                .compile_function(function)
                .unwrap_or_else(|error| panic!("{} {opt_level:?}: {error}", function.name));
            assert_eq!(
                exclusive_windows(&text_words(&object)).len(),
                1,
                "{}",
                function.name
            );
            if triple.ends_with("darwin") {
                assert!(
                    object.windows(12).any(|name| name == b"__debug_line"),
                    "{}: Mach-O debug line table requested but absent",
                    function.name
                );
            }
        }
    }
}

/// The LL/SC pseudos and the exclusives/CLREX their expansion emits have no
/// accepted evidence obligation: each one blocks per-compile promotion, so a
/// proof-required consumer refuses baseline atomics instead of crediting them.
#[test]
#[cfg(feature = "verify")]
fn llsc_pseudos_and_exclusives_block_proof_promotion() {
    use trust_cg_ir::function::{MachFunction, Signature, Type};
    use trust_cg_ir::inst::{AArch64Opcode as O, MachInst};
    use trust_cg_ir::operand::MachOperand as A;
    use trust_cg_ir::regs::{W0, W1, W2, W3, X4};
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(|| {
            let cases: Vec<(O, Vec<A>)> = vec![
                (
                    O::LlscRmw32,
                    vec![
                        A::PReg(W0),
                        A::PReg(W1),
                        A::PReg(W2),
                        A::PReg(W3),
                        A::PReg(X4),
                        A::Imm(0),
                        A::Imm(3),
                    ],
                ),
                (
                    O::LlscCmpSwap32,
                    vec![
                        A::PReg(W0),
                        A::PReg(W1),
                        A::PReg(W2),
                        A::PReg(W3),
                        A::PReg(X4),
                        A::Imm(3),
                    ],
                ),
                (O::Ldxrb, vec![A::PReg(W0), A::PReg(X4)]),
                (O::Stxrh, vec![A::PReg(W2), A::PReg(W1), A::PReg(X4)]),
                (O::Clrex, vec![]),
            ];
            for (opcode, operands) in cases {
                let mut function = MachFunction::new(
                    format!("unproven_{opcode:?}"),
                    Signature::new(vec![Type::I64], vec![]),
                );
                let id = function.push_inst(MachInst::new(opcode, operands));
                function.append_inst(function.entry, id);
                let ret = function.push_inst(MachInst::new(O::Ret, vec![]));
                function.append_inst(function.entry, ret);
                let report = trust_cg_verify::verify_function(&function);
                let inventory = report.emitted_opcode_inventory();
                assert!(!inventory.is_promotable(), "{opcode:?}: {inventory:?}");
                assert!(
                    inventory.uncovered_non_pseudo_opcodes().iter().any(
                        |row| row.opcode == trust_cg_verify::InstructionOpcode::AArch64(opcode)
                    ),
                    "{opcode:?} itself must block promotion: {inventory:?}"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}

/// `translate_module` under [`permit_unlicensed`].
fn permit_translate_module(
    module: &trust_ir::Module,
) -> Result<
    Vec<(trust_cg_lower::Function, trust_cg_lower::ProofContext)>,
    trust_cg_lower::AdapterError,
> {
    trust_cg_lower::translate_module_for_arch_with_tls_with_license(
        module,
        trust_cg_lower::GuardCarrierArch::default(),
        trust_cg_lower::TlsDialect::default(),
        &permit_unlicensed(),
    )
}
