// trust-cg-codegen/tests/e2e_aarch64_concurrency.rs - contended multi-thread
// atomics, ordering litmus tests and thread-local initialization.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Native concurrency controls for trust-cg AArch64 atomics and TLS on the
//! two hosts that execute AArch64 objects (macOS arm64 Mach-O, Linux GNU
//! ELF), through `tests/common/native_host.rs`.
//!
//! Atomics (LSE lanes: the Darwin AOT `Compiler` and the explicit-LSE
//! pipeline profile on Darwin; the explicit-LSE profile on Linux, whose
//! generic AOT refuses LSE by design; O0-O3): eight threads released by a
//! barrier contend on every read-modify-write op (add, sub, and, or, xor,
//! xchg, smax, smin, umax, umin) at 8/16/32/64 bits and on a
//! compare-exchange loop counter. The driver
//! (`tests/fixtures/concurrency/atomics_driver.c`) checks linearizability
//! invariants of the returned old values (a fetch-add histogram, per-thread
//! bit ownership, exchange token accounting, monotone max/min) and exact
//! finals, and runs the identical workloads through the C compiler's
//! `__atomic` builtins. This test compares both lanes' finals with a Rust
//! `std::sync::atomic` oracle under the same contention. A spinlock built
//! from a CG compare-exchange and a CG store-release must keep its critical
//! section exclusive. A streaming message-passing litmus (CG
//! store-release/load-acquire, and seq-cst, around plain relaxed data
//! accesses), a perpetual store-buffering litmus (CG seq-cst) and a perpetual
//! load-buffering litmus (CG release/acquire, and seq-cst) must never show
//! their forbidden outcome over 2^20, 2^18 and 2^18 iterations. Their C relaxed
//! controls (plain LDR/STR) report how often the ARMv8-permitted weak outcome
//! appeared, and the store-buffering control must see it at least once across
//! the run, showing the harness overlaps the two threads closely enough to
//! detect it (the load-buffering weak outcome is architecturally allowed but
//! rarely produced by hardware, so its control is informational). CG lowers
//! its relaxed atomic loads and stores to LDAR/STLR, so its relaxed-API lines
//! are informational. A non-atomic load/add/store mutation must lose updates
//! under the same harness, showing the harness can see a broken RMW.
//!
//! The harness alone does not discriminate a lost ordering. On Apple M-series
//! hardware the message-passing relaxed control, like the load-buffering one,
//! shows its weak outcome in almost no run, and no native workload observes
//! the acquire/release bits of an LSE read-modify-write or compare-exchange.
//! A per-function decode of every executed object (both lanes, O0-O3) pins
//! each function's LSE op, access size and ordering form (`AL` RMW, `CASAL`,
//! `LDAR`, `STLR`), with mutation controls that strip one ordering at a time.
//!
//! The litmus results are testing evidence over a finite number of runs on
//! one host, not a memory-model proof: no obligation here connects the
//! selected LDAR/STLR/LSE forms to the C11/Rust ordering semantics.
//!
//! TLS (every opt level): three waves of eight threads read `cg_tls`'s
//! initial value and zero-initialized `cg_tls_zero` after the main thread
//! mutated its own copy (and after earlier waves exited), agree with the C
//! driver's `extern __thread` view of the same variables, keep distinct stable
//! addresses while all are alive, and never observe another thread's bumps
//! (`tests/fixtures/concurrency/tls_driver.c`). Darwin lowers these through
//! TLV descriptors; Linux executables through local-exec.
//!
//! The baseline (no-LSE) profile's refusal of every atomic family is pinned
//! by name on every host: there is no LL/SC fallback to exercise.

use std::collections::BTreeMap;

use trust_cg_codegen::compiler::{Compiler, CompilerConfig};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::{AArch64IsaProfile, TargetSpec};
use trust_ir::value::GlobalId;
use trust_ir::{
    AtomicRMWOp, BinOp, Block, BlockId, Constant, FuncId, FuncTy, Function, Global, Inst,
    InstrNode, Linkage, Module, Ordering, TlsModel, Ty, ValueId, Visibility,
};

#[path = "common/native_host.rs"]
mod native_host;

const OPT_LEVELS: [OptLevel; 4] = [OptLevel::O0, OptLevel::O1, OptLevel::O2, OptLevel::O3];
const TRIPLES: [&str; 2] = ["aarch64-apple-darwin", "aarch64-unknown-linux-gnu"];
const WIDTHS: [(u32, Ty); 4] = [(8, Ty::I8), (16, Ty::I16), (32, Ty::I32), (64, Ty::I64)];
const RMW_OPS: [(AtomicRMWOp, &str); 10] = [
    (AtomicRMWOp::Add, "add"),
    (AtomicRMWOp::Sub, "sub"),
    (AtomicRMWOp::And, "and"),
    (AtomicRMWOp::Or, "or"),
    (AtomicRMWOp::Xor, "xor"),
    (AtomicRMWOp::Xchg, "xchg"),
    (AtomicRMWOp::Max, "smax"),
    (AtomicRMWOp::Min, "smin"),
    (AtomicRMWOp::UMax, "umax"),
    (AtomicRMWOp::UMin, "umin"),
];
/// Driver constants (`atomics_driver.c`).
const THREADS: u64 = 8;
const ITERS: u64 = 16384;
const NM: u64 = THREADS * ITERS;
const TLS_INIT: i128 = 24301;

// =============================================================================
// CG modules
// =============================================================================

fn ptr(ty: &Ty) -> Ty {
    Ty::PtrMut(Box::new(ty.clone()))
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
    let id = FuncId::new(module.functions.len() as u32);
    let mut function = Function::new(id, name, sig, BlockId::new(0));
    function.linkage = Linkage::External;
    function.blocks = vec![Block {
        id: BlockId::new(0),
        params: params
            .into_iter()
            .enumerate()
            .map(|(index, ty)| (ValueId::new(index as u32), ty))
            .collect(),
        body,
    }];
    module.functions.push(function);
}

fn ret(value: u32) -> InstrNode {
    InstrNode::new(Inst::Return {
        values: vec![ValueId::new(value)],
    })
}

/// Every contended function the atomics driver calls.
fn atomics_module() -> Module {
    let mut module = Module::new("concurrency_atomics");
    for (bits, ty) in WIDTHS {
        for (op, name) in RMW_OPS {
            add_function(
                &mut module,
                &format!("rmw_{name}_{bits}"),
                vec![ptr(&ty), ty.clone()],
                vec![ty.clone()],
                vec![
                    InstrNode::new(Inst::AtomicRMW {
                        op,
                        ty: ty.clone(),
                        ptr: ValueId::new(0),
                        value: ValueId::new(1),
                        ordering: Ordering::SeqCst,
                    })
                    .with_result(ValueId::new(2)),
                    ret(2),
                ],
            );
        }
        add_function(
            &mut module,
            &format!("cas_{bits}"),
            vec![ptr(&ty), ty.clone(), ty.clone()],
            vec![ty.clone()],
            vec![
                InstrNode::new(Inst::CmpXchg {
                    ty: ty.clone(),
                    ptr: ValueId::new(0),
                    expected: ValueId::new(1),
                    desired: ValueId::new(2),
                    success: Ordering::SeqCst,
                    failure: Ordering::SeqCst,
                    weak: false,
                })
                .with_results(vec![ValueId::new(3), ValueId::new(4)]),
                ret(3),
            ],
        );
    }
    for (name, ordering) in [
        ("acquire", Ordering::Acquire),
        ("relaxed", Ordering::Relaxed),
        ("seqcst", Ordering::SeqCst),
    ] {
        add_function(
            &mut module,
            &format!("load_{name}_64"),
            vec![ptr(&Ty::I64)],
            vec![Ty::I64],
            vec![
                InstrNode::new(Inst::AtomicLoad {
                    ty: Ty::I64,
                    ptr: ValueId::new(0),
                    ordering,
                })
                .with_result(ValueId::new(1)),
                ret(1),
            ],
        );
    }
    for (name, ordering) in [
        ("release", Ordering::Release),
        ("relaxed", Ordering::Relaxed),
        ("seqcst", Ordering::SeqCst),
    ] {
        add_function(
            &mut module,
            &format!("store_{name}_64"),
            vec![ptr(&Ty::I64), Ty::I64],
            vec![],
            vec![
                InstrNode::new(Inst::AtomicStore {
                    ty: Ty::I64,
                    ptr: ValueId::new(0),
                    value: ValueId::new(1),
                    ordering,
                }),
                InstrNode::new(Inst::Return { values: vec![] }),
            ],
        );
    }
    // Mutation control: a deliberately NON-atomic read-modify-write.
    add_function(
        &mut module,
        "nonatomic_add_64",
        vec![ptr(&Ty::I64), Ty::I64],
        vec![Ty::I64],
        vec![
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                volatile: true,
                align: Some(8),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(1),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(0),
                value: ValueId::new(3),
                volatile: true,
                align: Some(8),
            }),
            ret(2),
        ],
    );
    module
}

fn tls_global(name: &str, value: i128) -> Global {
    Global {
        name: name.into(),
        ty: Ty::I64,
        mutable: true,
        initializer: Some(Constant::Int(value)),
        linkage: Linkage::External,
        // Any dynamic model: Darwin selects TLV, an ELF executable local-exec.
        tls: Some(TlsModel::GeneralDynamic),
        align: Some(8),
        section: None,
        visibility: Visibility::Default,
        retained: false,
    }
}

/// `cg_tls` (TLS_INIT), zero-initialized `cg_tls_zero`, their addresses and a
/// bump of this thread's `cg_tls`.
fn tls_module() -> Module {
    let mut module = Module::new("concurrency_tls");
    module.globals = vec![tls_global("cg_tls", TLS_INIT), tls_global("cg_tls_zero", 0)];
    for (name, global) in [("cg_tls_addr", 0), ("cg_tls_zero_addr", 1)] {
        add_function(
            &mut module,
            name,
            vec![],
            vec![Ty::Ptr],
            vec![
                InstrNode::new(Inst::GlobalAddr {
                    global: GlobalId::new(global),
                })
                .with_result(ValueId::new(0)),
                ret(0),
            ],
        );
    }
    add_function(
        &mut module,
        "cg_tls_bump",
        vec![Ty::I64],
        vec![Ty::I64],
        vec![
            InstrNode::new(Inst::GlobalAddr {
                global: GlobalId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Load {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                volatile: false,
                align: Some(8),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: ValueId::new(2),
                rhs: ValueId::new(0),
            })
            .with_result(ValueId::new(3)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(1),
                value: ValueId::new(3),
                volatile: false,
                align: Some(8),
            }),
            ret(3),
        ],
    );
    module
}

fn compiler(triple: &str, opt_level: OptLevel) -> Compiler {
    Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
            ..CompilerConfig::default()
        },
        TargetSpec::parse(triple).expect("triple parses"),
    )
    .with_codegen_license(permit_unlicensed())
}

/// The LSE lanes this host links: the Darwin AOT `Compiler` (Darwin only)
/// and the explicit-LSE pipeline profile (every native host).
// Used only by the AArch64-native module below; gated the same way so an
// x86-64 host build does not refuse the target for a dead helper.
#[cfg(any(
    all(target_arch = "aarch64", target_os = "macos"),
    all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")
))]
fn atomics_objects(module: &Module, opt_level: OptLevel) -> Vec<(&'static str, Vec<u8>)> {
    let mut objects = Vec::new();
    if native_host::DARWIN {
        let object = compiler(native_host::TRIPLE, opt_level)
            .compile(module)
            .unwrap_or_else(|error| panic!("darwin-aot {opt_level:?}: {error}"))
            .object_code;
        objects.push(("darwin-aot", object));
    }
    assert!(
        AArch64IsaProfile::LSE.is_supported_by_host(),
        "the explicit LSE native lane requires host LSE"
    );
    let object = native_host::compile_with_isa_profile(module, opt_level, AArch64IsaProfile::LSE)
        .unwrap_or_else(|error| panic!("explicit-lse {opt_level:?}: {error}"));
    objects.push(("explicit-lse", object));
    objects
}

// =============================================================================
// Object-level evidence (every host)
// =============================================================================

/// LSE atomic memory operation (`LDADD`..`SWP` family): size in bits 31:30.
fn lse_rmw_size(word: u32) -> Option<u32> {
    (word & 0x3F20_0C00 == 0x3820_0000).then_some(word >> 30)
}

/// LSE compare-and-swap (`CAS{A,L,AL}{B,H,}`): size in bits 31:30.
fn lse_cas_size(word: u32) -> Option<u32> {
    (word & 0x3FA0_7C00 == 0x08A0_7C00).then_some(word >> 30)
}

#[test]
fn every_width_and_ordering_selects_lse_and_acquire_release_forms() {
    for triple in TRIPLES {
        for opt_level in OPT_LEVELS {
            let object = native_host::compile_with_isa_profile_for(
                triple,
                &atomics_module(),
                opt_level,
                AArch64IsaProfile::LSE,
            )
            .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: {error}"));
            let words = native_host::text_words(&object);
            for size in 0..4 {
                assert!(
                    words.iter().any(|&w| lse_rmw_size(w) == Some(size)),
                    "{triple} {opt_level:?}: no LSE RMW of size {size}"
                );
                assert!(
                    words.iter().any(|&w| lse_cas_size(w) == Some(size)),
                    "{triple} {opt_level:?}: no LSE CAS of size {size}"
                );
            }
            // 64-bit LDAR and STLR (acquire load, release store).
            assert!(
                words.iter().any(|&w| w & 0xFFFF_FC00 == 0xC8DF_FC00),
                "{triple} {opt_level:?}: no LDAR"
            );
            assert!(
                words.iter().any(|&w| w & 0xFFFF_FC00 == 0xC89F_FC00),
                "{triple} {opt_level:?}: no STLR"
            );
        }
    }
}

// -----------------------------------------------------------------------------
// Per-function ordering decode
// -----------------------------------------------------------------------------
//
// The native litmus lines cannot stand in for this check. On Apple M-series
// hardware the message-passing and load-buffering relaxed C controls show
// their weak outcome in almost no run, so a CG load-acquire that lost its
// acquire (LDAR -> LDR) passes the message-passing litmus in nearly every run.
// Nothing native observes the ordering bits of an LSE read-modify-write at
// all: the contended workloads check atomicity and values, which an LDADD
// without A/R still satisfies. So the ordering of every executed function is
// pinned here by decoding its own words.

fn le16(bytes: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap())
}

fn le32(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn le64(bytes: &[u8], at: usize) -> usize {
    usize::try_from(u64::from_le_bytes(bytes[at..at + 8].try_into().unwrap())).unwrap()
}

/// The NUL-terminated string at `at`, or the rest of `bytes` (a full-width
/// Mach-O segment or section name has no NUL).
fn cstr(bytes: &[u8], at: usize) -> &str {
    let len = bytes[at..]
        .iter()
        .position(|&b| b == 0)
        .unwrap_or(bytes.len() - at);
    std::str::from_utf8(&bytes[at..at + len]).unwrap()
}

fn code_words(code: &[u8]) -> Vec<u32> {
    assert_eq!(code.len() % 4, 0, "function extent is not word sized");
    code.as_chunks::<4>()
        .0
        .iter()
        .map(|word| u32::from_le_bytes(*word))
        .collect()
}

/// The code of every function a relocatable CG object defines, keyed by its
/// C-level name, read from the object's own symbol table by this parser
/// rather than the emitter: ELF `STT_FUNC` extents, or Mach-O external
/// `__TEXT,__text` symbols, each extending to the next one.
fn function_words(object: &[u8]) -> BTreeMap<String, Vec<u32>> {
    let mut functions = BTreeMap::new();
    if object.starts_with(b"\x7fELF") {
        let (shoff, shentsize, shnum) = (
            le64(object, 40),
            usize::from(le16(object, 58)),
            usize::from(le16(object, 60)),
        );
        let header = |index: usize| {
            assert!(index < shnum, "section index {index} out of range");
            shoff + index * shentsize
        };
        for index in 0..shnum {
            let symtab = header(index);
            if le32(object, symtab + 4) != 2 {
                continue; // not SHT_SYMTAB
            }
            let strtab = le64(object, header(le32(object, symtab + 40) as usize) + 24);
            let (offset, size, entsize) = (
                le64(object, symtab + 24),
                le64(object, symtab + 32),
                le64(object, symtab + 56),
            );
            for entry in (offset..offset + size).step_by(entsize) {
                if object[entry + 4] & 0xF != 2 {
                    continue; // not STT_FUNC
                }
                let section = header(usize::from(le16(object, entry + 6)));
                let start = le64(object, section + 24) + le64(object, entry + 8);
                let name = cstr(object, strtab + le32(object, entry) as usize).to_string();
                let code = code_words(&object[start..start + le64(object, entry + 16)]);
                assert!(
                    functions.insert(name, code).is_none(),
                    "duplicate ELF function"
                );
            }
        }
        return functions;
    }
    assert_eq!(le32(object, 0), 0xFEED_FACF, "MH_MAGIC_64");
    let (mut text, mut symtab, mut ordinal, mut at) = (None, None, 0u8, 32);
    for _ in 0..le32(object, 16) {
        match le32(object, at) {
            0x19 => {
                for index in 0..le32(object, at + 64) as usize {
                    let section = at + 72 + index * 80;
                    ordinal += 1;
                    if cstr(&object[section..section + 16], 0) == "__text"
                        && cstr(&object[section + 16..section + 32], 0) == "__TEXT"
                    {
                        text = Some((
                            ordinal,
                            le64(object, section + 32),
                            le64(object, section + 40),
                            le32(object, section + 48) as usize,
                        ));
                    }
                }
            }
            0x2 => {
                symtab = Some((
                    le32(object, at + 8) as usize,
                    le32(object, at + 12) as usize,
                    le32(object, at + 16) as usize,
                ));
            }
            _ => {}
        }
        at += le32(object, at + 4) as usize;
    }
    let (text_ordinal, text_addr, text_size, text_offset) = text.expect("__TEXT,__text");
    let (symoff, nsyms, stroff) = symtab.expect("LC_SYMTAB");
    // Every N_SECT symbol in __text (no stabs) bounds an extent; only the
    // external ones name a function.
    let mut starts: Vec<(usize, bool, String)> = (0..nsyms)
        .filter_map(|index| {
            let entry = symoff + index * 16;
            let n_type = object[entry + 4];
            (n_type & 0xE0 == 0 && n_type & 0x0E == 0x0E && object[entry + 5] == text_ordinal).then(
                || {
                    let name = cstr(object, stroff + le32(object, entry) as usize);
                    (
                        le64(object, entry + 8) - text_addr,
                        n_type & 0x01 != 0,
                        name.strip_prefix('_').unwrap_or(name).to_string(),
                    )
                },
            )
        })
        .collect();
    starts.sort();
    for (index, (start, external, name)) in starts.iter().enumerate() {
        if !external {
            continue;
        }
        let end = starts.get(index + 1).map_or(text_size, |(next, ..)| *next);
        let code = code_words(&object[text_offset + start..text_offset + end]);
        assert!(
            functions.insert(name.clone(), code).is_none(),
            "duplicate Mach-O function"
        );
    }
    functions
}

/// LSE atomic memory operation other than `LDAPR` (which shares its class).
fn is_lse_rmw(word: u32) -> bool {
    lse_rmw_size(word).is_some() && !is_ldapr(word)
}

/// `LDAPR{B,H,}` (load-acquire RCpc).
fn is_ldapr(word: u32) -> bool {
    word & 0x3FFF_FC00 == 0x38BF_C000
}

/// `LDAR{B,H,}` (load-acquire RCsc).
fn is_ldar(word: u32) -> bool {
    word & 0x3FFF_FC00 == 0x08DF_FC00
}

/// `STLR{B,H,}` (store-release).
fn is_stlr(word: u32) -> bool {
    word & 0x3FFF_FC00 == 0x089F_FC00
}

/// Plain `LDR{B,H,}` / `STR{B,H,}` (unsigned offset 0) of an acquire load or
/// release store's size and registers: the ordering-loss mutation.
fn unordered(word: u32) -> u32 {
    let base = if is_ldar(word) {
        [0x3940_0000, 0x7940_0000, 0xB940_0000, 0xF940_0000]
    } else if is_stlr(word) {
        [0x3900_0000, 0x7900_0000, 0xB900_0000, 0xF900_0000]
    } else {
        return word;
    };
    base[(word >> 30) as usize] | (word & 0x3FF)
}

/// `(o3, opc)` of the LSE operation each RMW op selects: `sub` is `LDADD` of
/// the negated operand and `and` is `LDCLR` of the inverted one.
fn lse_op_fields(op: &str) -> (u32, u32) {
    match op {
        "add" | "sub" => (0, 0b000),
        "and" => (0, 0b001),
        "xor" => (0, 0b010),
        "or" => (0, 0b011),
        "smax" => (0, 0b100),
        "smin" => (0, 0b101),
        "umax" => (0, 0b110),
        "umin" => (0, 0b111),
        "xchg" => (1, 0b000),
        other => panic!("unknown RMW op {other}"),
    }
}

/// What is wrong with one [`atomics_module`] function's words: each RMW must be
/// exactly one LSE operation of its op and width in the acquire-release (`AL`)
/// form its `SeqCst` request needs, each compare-exchange one `CASAL` of its
/// width, each 64-bit load one `LDAR` and each store one `STLR`, and the
/// mutation control must carry no atomic or ordered access at all.
fn ordering_violations(name: &str, words: &[u32]) -> Vec<String> {
    let count = |class: fn(u32) -> bool| words.iter().filter(|&&word| class(word)).count();
    let single = |class: fn(u32) -> bool| match words
        .iter()
        .copied()
        .filter(|&w| class(w))
        .collect::<Vec<_>>()[..]
    {
        [word] => Some(word),
        _ => None,
    };
    let (rmw, cas) = (count(is_lse_rmw), count(|w| lse_cas_size(w).is_some()));
    let (ldar, ldapr, stlr) = (count(is_ldar), count(is_ldapr), count(is_stlr));
    let mut problems = Vec::new();
    let mut expect = |ok: bool, what: &str| {
        if !ok {
            problems.push(format!("{name}: {what}"));
        }
    };
    let size_of = |bits: &str| bits.parse::<u32>().unwrap().trailing_zeros() - 3;
    if let Some((op, bits)) = name
        .strip_prefix("rmw_")
        .and_then(|rest| rest.rsplit_once('_'))
    {
        expect(
            rmw == 1 && cas + ldar + ldapr + stlr == 0,
            "one LSE RMW and no other atomic",
        );
        if let Some(word) = single(is_lse_rmw) {
            expect(word >> 30 == size_of(bits), "LSE access size");
            expect(
                ((word >> 15) & 1, (word >> 12) & 7) == lse_op_fields(op),
                "LSE operation",
            );
            expect(
                word & 0x00C0_0000 == 0x00C0_0000,
                "SeqCst RMW is not the AL form",
            );
        }
    } else if let Some(bits) = name.strip_prefix("cas_") {
        expect(
            cas == 1 && rmw + ldar + ldapr + stlr == 0,
            "one CAS and no other atomic",
        );
        if let Some(word) = single(|w| lse_cas_size(w).is_some()) {
            expect(word >> 30 == size_of(bits), "CAS access size");
            expect(
                word & 0x0040_8000 == 0x0040_8000,
                "SeqCst/SeqCst CAS is not CASAL",
            );
        }
    } else if name.starts_with("load_") {
        // Relaxed is pinned too: LIMITATIONS.md documents that CG strengthens
        // it to LDAR. SeqCst needs LDAR (RCsc), never LDAPR.
        expect(
            ldar == 1 && rmw + cas + ldapr + stlr == 0,
            "one LDAR and no other atomic",
        );
        expect(
            single(is_ldar).is_some_and(|word| word >> 30 == 3),
            "64-bit LDAR",
        );
    } else if name.starts_with("store_") {
        expect(
            stlr == 1 && rmw + cas + ldar + ldapr == 0,
            "one STLR and no other atomic",
        );
        expect(
            single(is_stlr).is_some_and(|word| word >> 30 == 3),
            "64-bit STLR",
        );
    } else if name == "nonatomic_add_64" {
        expect(
            rmw + cas + ldar + ldapr + stlr == 0,
            "the mutation control must stay non-atomic",
        );
    } else {
        expect(false, "not a function of atomics_module");
    }
    problems
}

/// Every function of the objects the native lanes link (explicit LSE on both
/// formats, and the Darwin AOT `Compiler`) decodes to its requested op, width
/// and ordering at O0-O3; each plausible ordering loss is rejected by name.
#[test]
fn each_atomic_function_decodes_to_its_requested_op_width_and_ordering() {
    let module = atomics_module();
    let expected: std::collections::BTreeSet<String> = module
        .functions
        .iter()
        .map(|function| function.name.clone())
        .collect();
    let mut checked = 0;
    for triple in TRIPLES {
        for opt_level in OPT_LEVELS {
            let mut lanes = vec![(
                "explicit-lse",
                native_host::compile_with_isa_profile_for(
                    triple,
                    &module,
                    opt_level,
                    AArch64IsaProfile::LSE,
                )
                .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: {error}")),
            )];
            if triple.contains("apple") {
                let object = compiler(triple, opt_level)
                    .compile(&module)
                    .unwrap_or_else(|error| panic!("darwin-aot {opt_level:?}: {error}"))
                    .object_code;
                lanes.push(("darwin-aot", object));
            }
            for (lane, object) in lanes {
                let functions = function_words(&object);
                assert_eq!(
                    functions
                        .keys()
                        .cloned()
                        .collect::<std::collections::BTreeSet<_>>(),
                    expected,
                    "{triple} {lane} {opt_level:?}: defined functions"
                );
                let problems: Vec<String> = functions
                    .iter()
                    .flat_map(|(name, words)| ordering_violations(name, words))
                    .collect();
                assert!(
                    problems.is_empty(),
                    "{triple} {lane} {opt_level:?}: {problems:#?}"
                );
                checked += 1;

                // Mutation controls on this object's own words: each loses an
                // ordering (or changes the op) without breaking atomicity, which
                // the native harness does not reliably notice.
                let rmw = |mask: u32| move |w: u32| if is_lse_rmw(w) { w & !mask } else { w };
                type WordMutation = Box<dyn Fn(u32) -> u32>;
                let mutations: [(&str, &str, WordMutation); 7] = [
                    ("rmw_add_64", "LDADDAL -> LDADD", Box::new(rmw(0x00C0_0000))),
                    ("rmw_xchg_8", "SWPALB -> SWPAB", Box::new(rmw(0x0040_0000))),
                    (
                        "rmw_umax_16",
                        "LDUMAXALH -> LDSMAXALH",
                        Box::new(rmw(0x2000)),
                    ),
                    (
                        "cas_32",
                        "CASAL -> CASA",
                        Box::new(|w| {
                            if lse_cas_size(w).is_some() {
                                w & !0x8000
                            } else {
                                w
                            }
                        }),
                    ),
                    ("load_acquire_64", "LDAR -> LDR", Box::new(unordered)),
                    (
                        "load_seqcst_64",
                        "LDAR -> LDAPR",
                        Box::new(|w| {
                            if is_ldar(w) {
                                0x38BF_C000 | (w & 0xC000_03FF)
                            } else {
                                w
                            }
                        }),
                    ),
                    ("store_release_64", "STLR -> STR", Box::new(unordered)),
                ];
                for (name, mutation, mutate) in &mutations {
                    let words: Vec<u32> = functions[*name].iter().map(|&w| mutate(w)).collect();
                    assert_ne!(
                        words, functions[*name],
                        "{name}: {mutation} changed nothing"
                    );
                    assert!(
                        !ordering_violations(name, &words).is_empty(),
                        "{triple} {lane} {opt_level:?}: {mutation} in {name} went undetected"
                    );
                }
            }
        }
    }
    assert_eq!(checked, OPT_LEVELS.len() * 3);
}

/// LDXR/LDAXR/LDXP/LDAXP: `sz 001000 o2=0 L=1 o1 Rs=11111 o0 Rt2 Rn Rt`,
/// with `o1` (pair) and `o0` (acquire) masked out.
fn is_load_exclusive(word: u32) -> bool {
    word & 0x3FDF_0000 == 0x085F_0000
}

/// Without LSE, atomics are not refused: the baseline profile lowers every
/// RMW and CAS through post-RA load/store-exclusive retry loops, on both
/// object formats and on generic Linux AOT (which keeps the baseline profile
/// by design), and emits no LSE word.
#[test]
fn baseline_profile_lowers_atomics_through_llsc_loops_on_both_formats() {
    let mut objects: Vec<(String, Vec<u8>)> = TRIPLES
        .iter()
        .map(|triple| {
            let object = native_host::compile_with_isa_profile_for(
                triple,
                &atomics_module(),
                OptLevel::O0,
                AArch64IsaProfile::BASELINE,
            )
            .unwrap_or_else(|error| panic!("{triple}: {error}"));
            (format!("{triple} baseline"), object)
        })
        .collect();
    objects.push((
        "aarch64-unknown-linux-gnu generic AOT".to_string(),
        compiler("aarch64-unknown-linux-gnu", OptLevel::O0)
            .compile(&atomics_module())
            .unwrap_or_else(|error| panic!("generic Linux AOT: {error}"))
            .object_code,
    ));
    for (lane, object) in &objects {
        let functions = function_words(object);
        assert!(!functions.is_empty(), "{lane}: no functions decoded");
        for (name, words) in &functions {
            assert!(
                !words
                    .iter()
                    .any(|&w| is_lse_rmw(w) || lse_cas_size(w).is_some()),
                "{lane}: {name} emitted an LSE word under the baseline profile"
            );
            if name.starts_with("rmw_") || name.starts_with("cas_") {
                assert!(
                    words.iter().any(|&w| is_load_exclusive(w)),
                    "{lane}: {name} has no load-exclusive loop head"
                );
            } else if name.starts_with("load_") {
                assert!(
                    words.iter().any(|&w| is_ldar(w) || is_ldapr(w)),
                    "{lane}: {name} has no acquire load"
                );
            } else if name.starts_with("store_") {
                assert!(
                    words.iter().any(|&w| is_stlr(w)),
                    "{lane}: {name} has no release store"
                );
            }
        }
    }
}

#[test]
fn tls_objects_compile_for_both_formats_at_every_opt_level() {
    for triple in TRIPLES {
        for opt_level in OPT_LEVELS {
            let object = compiler(triple, opt_level)
                .compile(&tls_module())
                .unwrap_or_else(|error| panic!("{triple} {opt_level:?}: {error}"))
                .object_code;
            if triple.contains("linux") {
                native_host::assert_elf_aarch64_object(&object);
            } else {
                native_host::assert_macho_arm64_object(&object);
            }
        }
    }
}

// =============================================================================
// Rust std::sync::atomic oracle
// =============================================================================

fn mask_of(bits: u32) -> u64 {
    if bits == 64 {
        u64::MAX
    } else {
        (1 << bits) - 1
    }
}

/// `extreme_operand` of the driver: per-thread monotone max/min operands.
fn extreme_operand(op: &str, k: u64, bits: u32) -> u64 {
    let mask = mask_of(bits);
    let sign = 1u64 << (bits - 1);
    let step = (mask / (NM - 1)).max(1);
    let magnitude = if k > mask / step { mask } else { k * step };
    match op {
        "umax" => magnitude,
        "umin" => mask - magnitude,
        "smax" => sign.wrapping_add(magnitude) & mask,
        _ => (sign - 1).wrapping_sub(magnitude) & mask,
    }
}

fn extreme_initial(op: &str, bits: u32) -> u64 {
    let sign = 1u64 << (bits - 1);
    match op {
        "umax" => 0,
        "umin" => mask_of(bits),
        "smax" => sign,
        _ => sign - 1,
    }
}

/// Finals of the deterministic workloads, computed by running the same
/// contended operations on `std::sync::atomic` types in `THREADS` threads.
fn rust_oracle(bits: u32) -> BTreeMap<&'static str, u64> {
    macro_rules! run {
        ($atomic:ty, $unsigned:ty, $signed:ty, $signed_atomic:ty) => {{
            use std::sync::atomic::Ordering::SeqCst;
            use std::sync::{Arc, Barrier};
            let mut finals = BTreeMap::new();
            let contend = |op: &'static str| -> u64 {
                let barrier = Arc::new(Barrier::new(THREADS as usize));
                if matches!(op, "smax" | "smin") {
                    let cell = Arc::new(<$signed_atomic>::new(
                        extreme_initial(op, bits) as $unsigned as $signed,
                    ));
                    std::thread::scope(|scope| {
                        for t in 0..THREADS {
                            let (cell, barrier) = (cell.clone(), barrier.clone());
                            scope.spawn(move || {
                                barrier.wait();
                                for i in 0..ITERS {
                                    let v = extreme_operand(op, i * THREADS + t, bits) as $unsigned
                                        as $signed;
                                    if op == "smax" {
                                        cell.fetch_max(v, SeqCst);
                                    } else {
                                        cell.fetch_min(v, SeqCst);
                                    }
                                }
                            });
                        }
                    });
                    return cell.load(SeqCst) as $unsigned as u64;
                }
                let initial = match op {
                    "umax" | "umin" => extreme_initial(op, bits),
                    _ => 0,
                };
                let cell = Arc::new(<$atomic>::new(initial as $unsigned));
                std::thread::scope(|scope| {
                    for t in 0..THREADS {
                        let (cell, barrier) = (cell.clone(), barrier.clone());
                        scope.spawn(move || {
                            barrier.wait();
                            for i in 0..ITERS {
                                match op {
                                    "add" => {
                                        cell.fetch_add(1, SeqCst);
                                    }
                                    "sub" => {
                                        cell.fetch_sub(1, SeqCst);
                                    }
                                    "umax" => {
                                        cell.fetch_max(
                                            extreme_operand(op, i * THREADS + t, bits) as $unsigned,
                                            SeqCst,
                                        );
                                    }
                                    "umin" => {
                                        cell.fetch_min(
                                            extreme_operand(op, i * THREADS + t, bits) as $unsigned,
                                            SeqCst,
                                        );
                                    }
                                    _ => {
                                        // cas_loop
                                        let mut expected = cell.load(SeqCst);
                                        loop {
                                            match cell.compare_exchange(
                                                expected,
                                                expected.wrapping_add(1),
                                                SeqCst,
                                                SeqCst,
                                            ) {
                                                Ok(_) => break,
                                                Err(seen) => expected = seen,
                                            }
                                        }
                                    }
                                }
                            }
                        });
                    }
                });
                cell.load(SeqCst) as u64
            };
            for op in ["add", "sub", "smax", "smin", "umax", "umin", "cas_loop"] {
                finals.insert(op, contend(op));
            }
            finals
        }};
    }
    use std::sync::atomic::{
        AtomicI8, AtomicI16, AtomicI32, AtomicI64, AtomicU8, AtomicU16, AtomicU32, AtomicU64,
    };
    match bits {
        8 => run!(AtomicU8, u8, i8, AtomicI8),
        16 => run!(AtomicU16, u16, i16, AtomicI16),
        32 => run!(AtomicU32, u32, i32, AtomicI32),
        _ => run!(AtomicU64, u64, i64, AtomicI64),
    }
}

#[test]
fn rust_oracle_matches_the_analytic_finals() {
    for (bits, _) in WIDTHS {
        let mask = mask_of(bits);
        let finals = rust_oracle(bits);
        assert_eq!(finals["add"], NM & mask, "{bits}");
        assert_eq!(finals["sub"], NM.wrapping_neg() & mask, "{bits}");
        assert_eq!(finals["cas_loop"], NM & mask, "{bits}");
        for op in ["smax", "smin", "umax", "umin"] {
            assert_eq!(finals[op], extreme_operand(op, NM - 1, bits), "{bits} {op}");
        }
    }
}

// =============================================================================
// Native execution (AArch64 Linux GNU and macOS)
// =============================================================================

#[cfg(any(
    all(target_arch = "aarch64", target_os = "macos"),
    all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")
))]
#[path = "common/rosetta.rs"]
mod rosetta;

#[cfg(any(
    all(target_arch = "aarch64", target_os = "macos"),
    all(target_arch = "aarch64", target_os = "linux", target_env = "gnu")
))]
mod native {
    use super::*;
    use std::path::Path;
    use std::process::Command;
    use std::time::Duration;

    const ATOMICS_DRIVER: &str = include_str!("fixtures/concurrency/atomics_driver.c");
    const TLS_DRIVER: &str = include_str!("fixtures/concurrency/tls_driver.c");

    #[derive(Debug)]
    struct Line {
        ok: bool,
        final_value: u64,
        detail: String,
    }

    /// Compile `driver` with the host C compiler, link it with `object`, run
    /// it under a watchdog and return its stdout.
    fn link_and_run(label: &str, driver: &str, object: &[u8]) -> String {
        let directory = tempfile::Builder::new()
            .prefix("trust-cg-concurrency-")
            .tempdir()
            .unwrap();
        let source = directory.path().join("driver.c");
        let object_path = directory.path().join("cg.o");
        let binary = directory.path().join("driver");
        std::fs::write(&source, driver).unwrap();
        std::fs::write(&object_path, object).unwrap();
        let link = Command::new(native_host::C_COMPILER)
            .args(["-O2", "-std=gnu11", "-pthread"])
            .arg(&source)
            .arg(&object_path)
            .args(native_host::link_hardening_args())
            .arg("-o")
            .arg(&binary)
            .output()
            .expect("host C compiler");
        assert!(
            link.status.success(),
            "{label}: link failed: {}",
            String::from_utf8_lossy(&link.stderr)
        );
        run(label, &binary)
    }

    fn run(label: &str, binary: &Path) -> String {
        let output = rosetta::command_output_with_timeout(
            &mut Command::new(binary),
            Duration::from_secs(600),
        )
        .unwrap_or_else(|error| panic!("{label}: {error}"));
        assert!(!output.timed_out, "{label}: timed out");
        let stdout = String::from_utf8(output.output.stdout).unwrap();
        assert_eq!(
            output.output.status.code(),
            Some(0),
            "{label}: stdout={stdout} stderr={}",
            String::from_utf8_lossy(&output.output.stderr)
        );
        stdout
    }

    /// `(lane, workload, bits) -> line`, refusing duplicates and malformed
    /// lines.
    fn parse(label: &str, stdout: &str) -> BTreeMap<(String, String, u32), Line> {
        let mut lines = BTreeMap::new();
        let mut done = false;
        for line in stdout.lines() {
            if line == "done" {
                done = true;
                continue;
            }
            let fields: Vec<&str> = line.splitn(6, ' ').collect();
            assert!(fields.len() >= 5, "{label}: malformed line {line:?}");
            let bits = fields[2].strip_prefix("w=").unwrap().parse().unwrap();
            let ok = match fields[3] {
                "ok=1" => true,
                "ok=0" => false,
                other => panic!("{label}: malformed ok field {other:?}"),
            };
            let final_value =
                u64::from_str_radix(fields[4].strip_prefix("final=").unwrap(), 16).unwrap();
            let key = (fields[0].to_string(), fields[1].to_string(), bits);
            let previous = lines.insert(
                key,
                Line {
                    ok,
                    final_value,
                    detail: fields.get(5).unwrap_or(&"").to_string(),
                },
            );
            assert!(previous.is_none(), "{label}: duplicate line {line:?}");
        }
        assert!(done, "{label}: driver did not finish: {stdout}");
        lines
    }

    fn detail_count(line: &Line, key: &str) -> u64 {
        line.detail
            .split_whitespace()
            .find_map(|field| field.strip_prefix(key)?.strip_prefix('='))
            .unwrap_or_else(|| panic!("{key} missing from {:?}", line.detail))
            .parse()
            .unwrap()
    }

    const WORKLOADS: [&str; 11] = [
        "add", "sub", "adjacent", "or_and", "xor", "xchg", "smax", "smin", "umax", "umin",
        "cas_loop",
    ];

    #[test]
    fn contended_rmw_cas_and_litmus_agree_with_c11_and_rust_oracles() {
        let module = atomics_module();
        let oracles: BTreeMap<u32, BTreeMap<&str, u64>> = WIDTHS
            .iter()
            .map(|(bits, _)| (*bits, rust_oracle(*bits)))
            .collect();
        let mut executed = 0;
        let mut store_buffering_observed = 0;
        for opt_level in OPT_LEVELS {
            for (lane, object) in atomics_objects(&module, opt_level) {
                let label = format!("{} {lane} {opt_level:?}", native_host::HOST);
                let lines = parse(&label, &link_and_run(&label, ATOMICS_DRIVER, &object));
                assert_eq!(
                    lines.len(),
                    2 * 4 * WORKLOADS.len() + 12,
                    "{label}: {lines:?}"
                );
                for (bits, _) in WIDTHS {
                    let mask = mask_of(bits);
                    for workload in WORKLOADS {
                        let cg = &lines[&("cg".to_string(), workload.to_string(), bits)];
                        let c11 = &lines[&("c11".to_string(), workload.to_string(), bits)];
                        assert!(cg.ok, "{label}: cg {workload} w={bits}: {cg:?}");
                        assert!(c11.ok, "{label}: c11 {workload} w={bits}: {c11:?}");
                        if workload == "xchg" {
                            // The last token is schedule-dependent; the
                            // driver checked its accounting.
                            assert!((1..=THREADS).contains(&cg.final_value));
                            continue;
                        }
                        assert_eq!(
                            cg.final_value, c11.final_value,
                            "{label}: {workload} w={bits}: CG and C11 finals"
                        );
                        let want = match workload {
                            "adjacent" => ITERS & mask,
                            "or_and" | "xor" => 0,
                            other => oracles[&bits][other],
                        };
                        assert_eq!(
                            cg.final_value, want,
                            "{label}: {workload} w={bits}: CG and Rust std oracle finals"
                        );
                    }
                }
                for litmus in [
                    "mp_release_acquire",
                    "mp_seqcst",
                    "sb_seqcst",
                    "lb_release_acquire",
                    "lb_seqcst",
                ] {
                    let line = &lines[&("cg".to_string(), litmus.to_string(), 64)];
                    assert!(line.ok, "{label}: {litmus}: {line:?}");
                    assert_eq!(detail_count(line, "forbidden"), 0, "{label}: {litmus}");
                }
                for (lane, control) in [
                    ("cg", "mp_relaxed_api"),
                    ("cg", "sb_relaxed_api"),
                    ("c11", "mp_relaxed_control"),
                    ("c11", "sb_relaxed_control"),
                    ("c11", "lb_relaxed_control"),
                ] {
                    let line = &lines[&(lane.to_string(), control.to_string(), 64)];
                    let observed = detail_count(line, "forbidden");
                    eprintln!("{label}: {lane} {control}: weak outcomes observed {observed}");
                    if control == "sb_relaxed_control" {
                        store_buffering_observed += observed;
                    }
                }
                let spinlock = &lines[&("cg".to_string(), "spinlock".to_string(), 64)];
                assert!(
                    spinlock.ok
                        && spinlock.final_value == NM
                        && detail_count(spinlock, "violations") == 0,
                    "{label}: spinlock: {spinlock:?}"
                );
                let mutation = &lines[&("cg".to_string(), "nonatomic_mutation".to_string(), 64)];
                assert!(
                    mutation.ok && detail_count(mutation, "lost") > 0,
                    "{label}: the harness must detect a non-atomic RMW: {mutation:?}"
                );
                executed += 1;
            }
        }
        let lanes = if native_host::DARWIN { 2 } else { 1 };
        assert_eq!(executed, OPT_LEVELS.len() * lanes);
        assert!(
            store_buffering_observed > 0,
            "the store-buffering harness never observed the weak outcome its relaxed control \
             permits, so its seq-cst result would not discriminate"
        );
    }

    #[test]
    fn thread_locals_initialize_per_thread_across_waves_and_match_the_c_view() {
        for opt_level in OPT_LEVELS {
            let label = format!("{} tls {opt_level:?}", native_host::HOST);
            let object = compiler(native_host::TRIPLE, opt_level)
                .compile(&tls_module())
                .unwrap_or_else(|error| panic!("{label}: {error}"))
                .object_code;
            native_host::assert_native_object(&object);
            let stdout = link_and_run(&label, TLS_DRIVER, &object);
            let wave = |n| {
                format!("tls wave={n} ok=1 init=8 zero=8 c_view=8 distinct=1 isolated=8 final=8\n")
            };
            assert_eq!(
                stdout,
                format!(
                    "{}{}{}tls main ok=1 value={}\n",
                    wave(0),
                    wave(1),
                    wave(2),
                    TLS_INIT + 1000
                ),
                "{label}"
            );
        }
    }
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
