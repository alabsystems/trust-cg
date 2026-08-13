//! TRUST-SELF ROUND 23 (thread R23, TRUST BATCH 10): verifying trust-cg's
//! ABI / CALLING-CONVENTION CLASSIFICATION deciders — how the backend decides
//! WHERE a function argument / return value is placed for the target ABI —
//! through the full pipeline Rust -> MIR -> trust-ir (stage1
//! `trust_ir_mir --mir-emit-closure`) -> trust-cg JIT -> machine code,
//! asserting native Rust == JIT over swept real inputs, with the LINKED
//! PRODUCTION functions/types as a SECOND oracle where they are public
//! (the round-7/16/20/22 dual-oracle discipline).
//!
//! WHY THIS IS NEW: prior rounds verified the machine-code ENCODERS (1/7/16),
//! the REGISTER FILES (5/16), the opt/analysis + addressing-mode predicates
//! (20/21), and the scheduler/regalloc deciders (22). The ABI CLASSIFIER — the
//! deciders that assign an argument/return to a register class, a stack slot,
//! or an indirect (sret) pointer — was UNTOUCHED until this round. A wrong
//! classification is not a slowdown: it is a WRONG CALL — the argument lands in
//! the wrong register / stack slot, or an sret pointer is mishandled, silently
//! corrupting the caller<->callee ABI contract.
//!
//! Two ABIs, two slices (both EXTERN-FREE, validate_module = 0, deterministic):
//!   * Slice A — Apple AArch64 (AAPCS64 / DarwinPCS), `trust-cg-lower/abi.rs`:
//!     `Type::bytes`/`Type::align`           (C-layout size/align classifier)
//!     `classify_fp_arg`                      (int-vs-SIMD reg-class selection)
//!     `align_up`                             (stack-slot alignment rounder)
//!     classify_aggregate size threshold      (<=8 -> 1 GPR / 9..=16 -> RegPair
//!     / >16 -> Indirect(sret) decider)
//!   * Slice B — x86-64 System V AMD64 psABI, `trust-cg-lower/x86_64_isel.rs`:
//!     `sysv_scalar_leaf_class`               (INTEGER/SSE leaf class)
//!     `merge_sysv_eightbyte_class`           (the psABI eightbyte-merge rule)
//!     `sysv_eightbyte_lane_type`             (width-correct lane access)
//!     `eightbyte_count`                      (size -> eightbytes)
//!     sret / MEMORY size thresholds          (SysV >16 / WindowsX64 >8)
//!
//! DUAL ORACLE: `Type::{bytes,align}`, `AppleAArch64ABI::{classify_fp_arg,
//! classify_aggregate}`, and `X86CallAbi` are PUBLIC and LINKED into this test
//! binary. The AArch64 aggregate size-threshold decision is cross-checked
//! against the LINKED production `classify_aggregate` run on real
//! `Struct([I8; size])` aggregates — so native==JIT proves the JIT's threshold
//! decision equals the real classifier at the exact 8 / 16 / 17 / 24 byte
//! boundaries. The x86 psABI functions are PRIVATE (not linkable): transcribed
//! VERBATIM, cross-checked against a verbatim native transcription + independent
//! hand-computed boundary values, with `Type::bytes` tying the swept sizes to
//! real aggregate sizes.
//!
//! SCOPE / FINDINGS hit while building this round (see the slice headers):
//!   [F4-VecType] the recursive aggregate-LAYOUT functions (`Type::bytes`/
//!        `align` on Struct/Array, `detect_hfa`, `classify_hfa`, the HFA branch
//!        of `classify_aggregate`, the full SysV eightbyte walk) EMIT cleanly
//!        (validate_module = 0) but their `Vec<Type>::{len,index,iter}` /
//!        `Box<Type>` methods lower to EMPTY-BODIED library leaves the
//!        in-process JIT cannot resolve (`Jit(UnresolvedSymbol("...Vec<t>::
//!        len..."))`) — the F4 / owner-#6 empty-bodied-leaf class, now observed
//!        for the whole `Vec<non-scalar-enum>` recursion family (reported).
//!        The size-based DECISION is therefore transcribed scalar-driven
//!        [B-aggsize]: the threshold COMPARISONS are verbatim; the size + the
//!        aggregate gate are supplied by the caller (verified via the linked
//!        `Type::bytes` / `classify_aggregate`).
//!   [F1] fieldless-enum `==` (`abi == X86CallAbi::SystemV`) does not lower ->
//!        transcribed as `matches!` (result-identical; native oracle runs `==`).
//!   [B5-aa] const-array indexing by a runtime index (`H_ARG_REGS[fpr_idx]`)
//!        does not lower -> `classify_fp_arg` uses equivalent base+index
//!        arithmetic (contiguous FPR views); the LINKED oracle proves identity.
//!   [F6-slicepat] single-element slice patterns (`matches!(v.as_slice(),[f]..)`)
//!        lower to an unsupported `ConstantIndex` projection (RUNG 1) — the
//!        slice-pattern classifiers (`is_sysv_v128_carrier`, single/two-GPR
//!        lane) are out of scope (reported).
//!
//! COVERAGE NOTE: gated to aarch64 (the JIT target). Run tests ONE AT A TIME
//! (`-- --exact <name> --test-threads=1`): the JIT engine is not thread-safe at
//! suite scale (jit-parallel-race-2026-06-29.md). Every JIT execution runs
//! inside a WATCHDOG worker thread.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED PRODUCTION types/functions (the second oracle):
use trust_cg_lower::abi::{AppleAArch64ABI, ArgLocation, ClassifyResult};
use trust_cg_lower::types::Type;
use trust_cg_lower::x86_64_isel::X86CallAbi;

// ── shared harness (round-9/22 pattern) ───────────────────────────────────────

const ABI_AA_IR: &str = include_str!("slices/trust_abi_aarch64_classify.tir");
const ABI_X86_IR: &str = include_str!("slices/trust_abi_x86_sysv_classify.tir");

fn jit_module(text: &str, what: &str) -> trust_cg_codegen::jit::ExecutableBuffer {
    let module = trust_ir::parser::parse_module(text)
        .unwrap_or_else(|e| panic!("MIR-emitted `{what}` trust-ir text must parse: {e:?}"));
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(&module, &HashMap::new())
        .unwrap_or_else(|e| panic!("trust-cg JIT compile of MIR-emitted `{what}` failed: {e:?}"))
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

const WATCHDOG_SECS: u64 = 120;

fn run_watchdogged<T: Send + 'static>(
    what: &'static str,
    expected: usize,
    worker: impl FnOnce(mpsc::Sender<T>) + Send + 'static,
) -> Vec<T> {
    let (tx, rx) = mpsc::channel::<T>();
    std::thread::spawn(move || worker(tx));
    let mut rows = Vec::with_capacity(expected);
    for i in 0..expected {
        match rx.recv_timeout(Duration::from_secs(WATCHDOG_SECS)) {
            Ok(row) => rows.push(row),
            Err(_) => panic!(
                "JIT `{what}` HUNG (watchdog {WATCHDOG_SECS}s): no progress at row {i} of {expected}"
            ),
        }
    }
    rows
}

// ============================================================================
// SLICE A — Apple AArch64 (AAPCS64) argument/return classification.
// ============================================================================

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AbiAaOutC {
    bytes: u32,
    align: u32,
    fp_present: u32,
    fp_reg: u32,
    fp_next: u32,
    agg_kind: u32,
    agg_nregs: u32,
    align_up: i64,
}

impl AbiAaOutC {
    fn poisoned() -> Self {
        AbiAaOutC {
            bytes: 0xDEAD,
            align: 0xDEAD,
            fp_present: 0xDEAD,
            fp_reg: 0xDEAD,
            fp_next: 0xDEAD,
            agg_kind: 0xDEAD,
            agg_nregs: 0xDEAD,
            align_up: 0x0DEA_D0DE_AD0D_EAD0u64 as i64,
        }
    }
}

type AbiAaFn = unsafe extern "C" fn(u32, u32, u32, i64, i64, *mut AbiAaOutC);

/// Scalar production `Type` mirroring the slice's `build_type`.
fn scalar_type(tag: u32) -> Type {
    match tag {
        0 => Type::I8,
        1 => Type::I16,
        2 => Type::I32,
        3 => Type::I64,
        4 => Type::I128,
        5 => Type::F16,
        6 => Type::F32,
        7 => Type::F64,
        8 => Type::B1,
        _ => Type::V128,
    }
}

/// A real NON-HFA aggregate whose `bytes()` is exactly `size` (`Struct([I8;n])`,
/// align 1, no padding) — the second oracle for the aggregate size threshold.
fn agg_of_size(size: u32) -> Type {
    Type::Struct(vec![Type::I8; size as usize])
}

/// VERBATIM native transcription of abi.rs:1006-1008 (`align_up`).
fn nat_align_up(value: i64, align: i64) -> i64 {
    (value + align - 1) & !(align - 1)
}

/// Native oracle row via the LINKED production classifiers.
fn native_aa_row(ty_tag: u32, fpr_idx: u32, size: u32, av: i64, aa: i64) -> AbiAaOutC {
    let ty = scalar_type(ty_tag);
    let bytes = ty.bytes(); // LINKED
    let align = ty.align(); // LINKED

    let (fp_present, fp_reg, fp_next) =
        match AppleAArch64ABI::classify_fp_arg(&ty, fpr_idx as usize) {
            None => (0u32, 9999u32, 9999u32),
            Some((loc, next)) => (
                1,
                match loc {
                    ArgLocation::Reg(r) => r.encoding() as u32,
                    _ => 8888,
                },
                next as u32,
            ),
        };

    // LINKED classify_aggregate on a real Struct([I8;size]) -> (kind, nregs).
    let (agg_kind, agg_nregs) = match AppleAArch64ABI::classify_aggregate(&agg_of_size(size)) {
        ClassifyResult::InRegs { regs } => (0u32, regs.len() as u32),
        ClassifyResult::Indirect { .. } => (1, 0),
        ClassifyResult::OnStack { .. } => (3, 0),
        ClassifyResult::Hfa { count, .. } => (2, count as u32),
    };

    AbiAaOutC {
        bytes,
        align,
        fp_present,
        fp_reg,
        fp_next,
        agg_kind,
        agg_nregs,
        align_up: nat_align_up(av, aa),
    }
}

fn aa_inputs() -> Vec<(u32, u32, u32, i64, i64)> {
    let mut v: Vec<(u32, u32, u32, i64, i64)> = Vec::new();
    // Scalar types 0..=9 (bytes / align / classify_fp_arg on a scalar).
    for tag in 0..=9u32 {
        v.push((tag, 0, 8, 0, 8));
    }
    // classify_fp_arg: FP-view register selection + FPR exhaustion.
    //   5=F16 6=F32 7=F64 9=V128, 3=I64 (non-FP -> None regardless of idx).
    for &fp in &[5u32, 6, 7, 9, 3] {
        for idx in 0..=8u32 {
            v.push((fp, idx, 8, 0, 8));
        }
    }
    // Aggregate size threshold: sizes straddling 8 and 16.
    for &size in &[0u32, 1, 7, 8, 9, 15, 16, 17, 24, 32] {
        v.push((0, 0, size, 0, 8));
    }
    // align_up boundary sweep.
    let avs = [0i64, 1, 7, 8, 9, 15, 16, 17, 31, 63, 64, -1, -8, -9, -16];
    let aas = [1i64, 2, 4, 8, 16];
    for &av in &avs {
        for &aa in &aas {
            v.push((0, 0, 8, av, aa));
        }
    }
    v
}

/// The AArch64 AAPCS64 scalar-shaped classifier layer, native==JIT over a
/// type + FP-exhaustion + aggregate-size + alignment-boundary sweep, JIT vs the
/// LINKED production classifiers.
#[test]
fn trust_abi_aarch64_classify_production_eq_jit() {
    let tuples = aa_inputs();
    let expected = tuples.len();
    let sweep = tuples.clone();
    let rows = run_watchdogged::<AbiAaOutC>("abi_aa", expected, move |tx| {
        let buffer = jit_module(ABI_AA_IR, "abi_aa");
        let f: AbiAaFn = unsafe { std::mem::transmute(bind(&buffer, "abi_aa_root")) };
        for &(ty_tag, fpr_idx, size, av, aa) in &sweep {
            let mut out = AbiAaOutC::poisoned();
            unsafe { f(ty_tag, fpr_idx, size, av, aa, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(ty_tag, fpr_idx, size, av, aa)) in tuples.iter().enumerate() {
        let expect = native_aa_row(ty_tag, fpr_idx, size, av, aa);
        assert_eq!(
            rows[i], expect,
            "abi_aa(ty={ty_tag} fpr={fpr_idx} size={size} av={av} aa={aa}): JIT {:?} != oracle {:?}",
            rows[i], expect
        );
        for val in [
            rows[i].bytes,
            rows[i].align,
            rows[i].fp_present,
            rows[i].fp_reg,
            rows[i].fp_next,
            rows[i].agg_kind,
            rows[i].agg_nregs,
        ] {
            assert_ne!(val, 0xDEAD, "row {i} still poisoned: {:?}", rows[i]);
        }
    }

    let idx = |ty: u32, fp: u32, sz: u32, av: i64, aa: i64| -> usize {
        tuples
            .iter()
            .position(|&t| t == (ty, fp, sz, av, aa))
            .expect("tuple present")
    };
    let r = |i: usize| rows[i];

    // Type::bytes / align on scalars (spot checks).
    assert_eq!(
        (r(idx(2, 0, 8, 0, 8)).bytes, r(idx(2, 0, 8, 0, 8)).align),
        (4, 4),
        "I32 = 4/4"
    );
    assert_eq!(
        r(idx(4, 0, 8, 0, 8)).align,
        16,
        "I128 align is 16 (AAPCS64 quad-word; rustc align_of::<u128>()) — e3b23194"
    );
    assert_eq!(
        (r(idx(9, 0, 8, 0, 8)).bytes, r(idx(9, 0, 8, 0, 8)).align),
        (16, 16),
        "V128 = 16/16"
    );

    // classify_fp_arg: int-vs-SIMD register-class SELECTION + FPR exhaustion.
    assert_eq!(
        (r(idx(6, 0, 8, 0, 8)).fp_reg, r(idx(6, 0, 8, 0, 8)).fp_next),
        (128, 1),
        "F32 idx0 -> S0(128)"
    );
    assert_eq!(r(idx(6, 7, 8, 0, 8)).fp_reg, 135, "F32 idx7 -> S7(135)");
    assert_eq!(
        r(idx(6, 8, 8, 0, 8)).fp_present,
        0,
        "F32 idx8 -> None (FPR exhausted)"
    );
    assert_eq!(r(idx(7, 0, 8, 0, 8)).fp_reg, 96, "F64 idx0 -> D0(96)");
    assert_eq!(r(idx(5, 0, 8, 0, 8)).fp_reg, 165, "F16 idx0 -> H0(165)");
    assert_eq!(r(idx(9, 0, 8, 0, 8)).fp_reg, 64, "V128 idx0 -> V0(64)");
    assert_eq!(
        r(idx(3, 0, 8, 0, 8)).fp_present,
        0,
        "I64 is not an FP arg -> None"
    );

    // Aggregate size threshold — the register-pair-split + Indirect(sret) decider
    // (cross-checked against the LINKED real classify_aggregate on Struct[I8;n]):
    assert_eq!(
        (
            r(idx(0, 0, 8, 0, 8)).agg_kind,
            r(idx(0, 0, 8, 0, 8)).agg_nregs
        ),
        (0, 1),
        "8B agg -> InRegs 1"
    );
    assert_eq!(
        (
            r(idx(0, 0, 9, 0, 8)).agg_kind,
            r(idx(0, 0, 9, 0, 8)).agg_nregs
        ),
        (0, 2),
        "9B agg -> InRegs 2"
    );
    assert_eq!(
        (
            r(idx(0, 0, 16, 0, 8)).agg_kind,
            r(idx(0, 0, 16, 0, 8)).agg_nregs
        ),
        (0, 2),
        "16B agg -> InRegs 2 (RegPair) — the 16-byte boundary"
    );
    assert_eq!(
        r(idx(0, 0, 17, 0, 8)).agg_kind,
        1,
        "17B agg -> Indirect (>16)"
    );
    assert_eq!(r(idx(0, 0, 24, 0, 8)).agg_kind, 1, "24B agg -> Indirect");
    assert_eq!(
        (
            r(idx(0, 0, 0, 0, 8)).agg_kind,
            r(idx(0, 0, 0, 0, 8)).agg_nregs
        ),
        (0, 1),
        "0B agg -> InRegs 1"
    );

    // align_up boundary correctness.
    assert_eq!(r(idx(0, 0, 8, 9, 8)).align_up, 16, "align_up(9,8)=16");
    assert_eq!(r(idx(0, 0, 8, 16, 16)).align_up, 16, "align_up(16,16)=16");
    assert_eq!(r(idx(0, 0, 8, 17, 16)).align_up, 32, "align_up(17,16)=32");
    assert_eq!(r(idx(0, 0, 8, 8, 8)).align_up, 8, "align_up(8,8)=8");
    assert_eq!(r(idx(0, 0, 8, 0, 8)).align_up, 0, "align_up(0,8)=0");
    assert_eq!(r(idx(0, 0, 8, 1, 8)).align_up, 8, "align_up(1,8)=8");
}

/// ARMED negative control (Slice A): patch the classify_aggregate `<= 16`
/// register-pair/Indirect threshold (`%21 = const u32 16` -> 15); a 16-byte
/// aggregate then FAILS `<= 16` and mis-classifies as Indirect instead of
/// InRegs(RegPair). Prove the divergence, then restore + re-pass.
#[test]
fn trust_abi_aarch64_classify_armed_control() {
    const ANCHOR: &str = "%21 = const u32 16";
    assert_eq!(
        ABI_AA_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (classify_aggregate <=16 threshold)"
    );
    let corrupted = ABI_AA_IR.replace(ANCHOR, "%21 = const u32 15");
    assert_ne!(corrupted, ABI_AA_IR);

    let corrupt = run_watchdogged::<(u32, u32)>("abi_aa CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "abi_aa CORRUPTED");
        let f: AbiAaFn = unsafe { std::mem::transmute(bind(&buffer, "abi_aa_root")) };
        let mut out = AbiAaOutC::poisoned();
        unsafe { f(0, 0, 16, 0, 8, &mut out) }; // size = 16
        let _ = tx.send((out.agg_kind, out.agg_nregs));
    })[0];
    let pristine = run_watchdogged::<(u32, u32)>("abi_aa RESTORED", 1, move |tx| {
        let buffer = jit_module(ABI_AA_IR, "abi_aa RESTORED");
        let f: AbiAaFn = unsafe { std::mem::transmute(bind(&buffer, "abi_aa_root")) };
        let mut out = AbiAaOutC::poisoned();
        unsafe { f(0, 0, 16, 0, 8, &mut out) };
        let _ = tx.send((out.agg_kind, out.agg_nregs));
    })[0];

    // Production truth via the LINKED classify_aggregate on a real 16-byte agg.
    let native = native_aa_row(0, 0, 16, 0, 8);
    assert_eq!(
        (native.agg_kind, native.agg_nregs),
        (0, 2),
        "production: 16B agg -> InRegs 2"
    );
    assert_eq!(
        corrupt.0, 1,
        "corrupted module mis-classifies 16B agg as Indirect"
    );
    assert_ne!(
        corrupt.0, native.agg_kind,
        "corrupted JIT DIVERGES from the production oracle"
    );
    assert_eq!(
        (pristine.0, pristine.1),
        (0, 2),
        "pristine module AGREES (restore + re-pass)"
    );
}

// ============================================================================
// SLICE B — x86-64 System V AMD64 psABI aggregate classification.
// ============================================================================

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AbiX86OutC {
    leaf: u32,
    merged: u32,
    lane: u32,
    ebc: u32,
    sret_large: u32,
    mem_byval: u32,
    sret_ret: u32,
}

impl AbiX86OutC {
    fn poisoned() -> Self {
        AbiX86OutC {
            leaf: 0xDEAD,
            merged: 0xDEAD,
            lane: 0xDEAD,
            ebc: 0xDEAD,
            sret_large: 0xDEAD,
            mem_byval: 0xDEAD,
            sret_ret: 0xDEAD,
        }
    }
    fn as_row(&self) -> [u32; 7] {
        [
            self.leaf,
            self.merged,
            self.lane,
            self.ebc,
            self.sret_large,
            self.mem_byval,
            self.sret_ret,
        ]
    }
}

type AbiX86Fn = unsafe extern "C" fn(u32, u32, u32, u32, u32, u32, u32, u32, *mut AbiX86OutC);

#[derive(Clone, Copy, PartialEq, Eq)]
enum Lc {
    Integer,
    Sse,
}

// VERBATIM native transcriptions of the private psABI fns (x86_64_isel.rs).
fn nat_leaf(ty: &Type) -> Option<Lc> {
    match ty {
        Type::B1 | Type::I8 | Type::I16 | Type::I32 | Type::I64 => Some(Lc::Integer),
        Type::F16 | Type::F32 | Type::F64 => Some(Lc::Sse),
        _ => None,
    }
}
fn nat_merge(acc: &mut Option<Lc>, leaf: Lc) {
    *acc = Some(match (*acc, leaf) {
        (None, c) => c,
        (Some(Lc::Integer), _) | (_, Lc::Integer) => Lc::Integer,
        (Some(Lc::Sse), Lc::Sse) => Lc::Sse,
    });
}
fn nat_lane_tag(class: Lc, valid_bytes: u32) -> u32 {
    match (class, valid_bytes) {
        (Lc::Integer, 8) => 3,
        (Lc::Integer, 4) => 2,
        (Lc::Integer, 2) => 1,
        (Lc::Integer, 1) => 0,
        (Lc::Sse, 8) => 7,
        (Lc::Sse, 4) => 6,
        _ => 99,
    }
}
fn nat_ebc(size: u32) -> u32 {
    size.div_ceil(8)
}
// Size deciders — native oracle uses the REAL `==` form (proving the slice's
// [F1] `matches!` rewrite equivalent).
fn nat_is_large(is_agg: bool, size: u32) -> bool {
    is_agg && size > 16
}
fn nat_is_mem_byval(is_agg: bool, abi: X86CallAbi, size: u32) -> bool {
    abi == X86CallAbi::SystemV && is_agg && size > 16
}
fn nat_is_sret_return(is_agg: bool, abi: X86CallAbi, size: u32) -> bool {
    match abi {
        X86CallAbi::SystemV => nat_is_large(is_agg, size),
        X86CallAbi::WindowsX64 => is_agg && size > 8,
    }
}
fn lc_tag(o: Option<Lc>) -> u32 {
    match o {
        None => 9,
        Some(Lc::Integer) => 0,
        Some(Lc::Sse) => 1,
    }
}

fn native_x86_row(t: (u32, u32, u32, u32, u32, u32, u32, u32)) -> [u32; 7] {
    let (leaf_tag, acc_tag, merge_leaf_tag, class_tag, valid, size, is_agg, abi_tag) = t;
    let leaf_ty = scalar_type(leaf_tag);
    let abi = if abi_tag == 0 {
        X86CallAbi::SystemV
    } else {
        X86CallAbi::WindowsX64
    };
    let is_aggregate = is_agg != 0;

    let leaf = lc_tag(nat_leaf(&leaf_ty));
    let mut acc: Option<Lc> = match acc_tag {
        0 => Some(Lc::Integer),
        1 => Some(Lc::Sse),
        _ => None,
    };
    nat_merge(
        &mut acc,
        if merge_leaf_tag == 0 {
            Lc::Integer
        } else {
            Lc::Sse
        },
    );
    let merged = lc_tag(acc);
    let cls = if class_tag == 0 { Lc::Integer } else { Lc::Sse };
    let lane = nat_lane_tag(cls, valid);

    [
        leaf,
        merged,
        lane,
        nat_ebc(size),
        nat_is_large(is_aggregate, size) as u32,
        nat_is_mem_byval(is_aggregate, abi, size) as u32,
        nat_is_sret_return(is_aggregate, abi, size) as u32,
    ]
}

type X86Input = (u32, u32, u32, u32, u32, u32, u32, u32);

fn x86_inputs() -> Vec<X86Input> {
    let mut v: Vec<X86Input> = Vec::new();
    // sysv_scalar_leaf_class over all scalar leaves.
    for leaf in 0..=9u32 {
        v.push((leaf, 2, 0, 0, 8, 8, 1, 0));
    }
    // merge_sysv_eightbyte_class EXHAUSTIVE: acc {Int,Sse,None} x leaf {Int,Sse}.
    for acc in 0..3u32 {
        for ml in 0..2u32 {
            v.push((0, acc, ml, 0, 8, 8, 1, 0));
        }
    }
    // sysv_eightbyte_lane_type EXHAUSTIVE: class {Int,Sse} x valid 0..=9.
    for cls in 0..2u32 {
        for valid in 0..=9u32 {
            v.push((0, 2, 0, cls, valid, 8, 1, 0));
        }
    }
    // size deciders + eightbyte_count: size x is_agg x abi.
    for &size in &[0u32, 1, 8, 9, 15, 16, 17, 24, 32] {
        for is_agg in 0..2u32 {
            for abi in 0..2u32 {
                v.push((0, 2, 0, 0, 8, size, is_agg, abi));
            }
        }
    }
    v
}

/// The x86-64 SysV psABI scalar-shaped classifier layer, native==JIT over
/// exhaustive leaf/merge/lane sub-sweeps + a size x is_agg x abi threshold
/// sweep. Private fns are verbatim-transcribed; boundaries additionally checked
/// against independent hand-computed values; `Type::bytes` ties the sizes to
/// real aggregate sizes.
#[test]
fn trust_abi_x86_sysv_classify_production_eq_jit() {
    let tuples = x86_inputs();
    let expected = tuples.len();
    let sweep = tuples.clone();
    let rows = run_watchdogged::<[u32; 7]>("abi_x86", expected, move |tx| {
        let buffer = jit_module(ABI_X86_IR, "abi_x86");
        let f: AbiX86Fn = unsafe { std::mem::transmute(bind(&buffer, "abi_x86_root")) };
        for &(a, b, c, d, e, g, h, k) in &sweep {
            let mut out = AbiX86OutC::poisoned();
            unsafe { f(a, b, c, d, e, g, h, k, &mut out) };
            if tx.send(out.as_row()).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &t) in tuples.iter().enumerate() {
        let expect = native_x86_row(t);
        assert_eq!(
            rows[i], expect,
            "abi_x86{t:?}: JIT {:?} != oracle {:?}",
            rows[i], expect
        );
        assert!(
            rows[i].iter().all(|&v| v != 0xDEAD),
            "row {i} still poisoned: {:?}",
            rows[i]
        );
    }

    // Tie the swept sizes to REAL aggregate sizes via the LINKED Type::bytes.
    for &size in &[0u32, 1, 8, 9, 15, 16, 17, 24, 32] {
        assert_eq!(
            agg_of_size(size).bytes(),
            size,
            "Struct[I8;{size}] is exactly {size} bytes (linked Type::bytes)"
        );
    }

    // Independent hand-computed boundary oracle for the private fns.
    let pos = |t: (u32, u32, u32, u32, u32, u32, u32, u32)| {
        tuples.iter().position(|&x| x == t).expect("present")
    };
    let row = |t: (u32, u32, u32, u32, u32, u32, u32, u32)| rows[pos(t)];

    // sysv_scalar_leaf_class.
    assert_eq!(row((2, 2, 0, 0, 8, 8, 1, 0))[0], 0, "leaf(I32) = INTEGER");
    assert_eq!(row((3, 2, 0, 0, 8, 8, 1, 0))[0], 0, "leaf(I64) = INTEGER");
    assert_eq!(row((8, 2, 0, 0, 8, 8, 1, 0))[0], 0, "leaf(B1) = INTEGER");
    assert_eq!(row((6, 2, 0, 0, 8, 8, 1, 0))[0], 1, "leaf(F32) = SSE");
    assert_eq!(row((7, 2, 0, 0, 8, 8, 1, 0))[0], 1, "leaf(F64) = SSE");
    assert_eq!(
        row((4, 2, 0, 0, 8, 8, 1, 0))[0],
        9,
        "leaf(I128) = None (two eightbytes)"
    );
    assert_eq!(
        row((9, 2, 0, 0, 8, 8, 1, 0))[0],
        9,
        "leaf(V128) = None (carrier)"
    );

    // merge_sysv_eightbyte_class: INTEGER wins; SSE only if all-SSE.
    assert_eq!(
        row((0, 2, 0, 0, 8, 8, 1, 0))[1],
        0,
        "merge(None, Integer) = Integer"
    );
    assert_eq!(
        row((0, 2, 1, 0, 8, 8, 1, 0))[1],
        1,
        "merge(None, Sse) = Sse"
    );
    assert_eq!(
        row((0, 0, 1, 0, 8, 8, 1, 0))[1],
        0,
        "merge(Integer, Sse) = Integer (INTEGER wins)"
    );
    assert_eq!(
        row((0, 1, 0, 0, 8, 8, 1, 0))[1],
        0,
        "merge(Sse, Integer) = Integer (INTEGER wins)"
    );
    assert_eq!(
        row((0, 1, 1, 0, 8, 8, 1, 0))[1],
        1,
        "merge(Sse, Sse) = Sse (all-SSE)"
    );
    assert_eq!(
        row((0, 0, 0, 0, 8, 8, 1, 0))[1],
        0,
        "merge(Integer, Integer) = Integer"
    );

    // sysv_eightbyte_lane_type: power-of-two widths only; others None.
    assert_eq!(row((0, 2, 0, 0, 8, 8, 1, 0))[2], 3, "lane(Integer,8) = I64");
    assert_eq!(row((0, 2, 0, 0, 4, 8, 1, 0))[2], 2, "lane(Integer,4) = I32");
    assert_eq!(row((0, 2, 0, 0, 2, 8, 1, 0))[2], 1, "lane(Integer,2) = I16");
    assert_eq!(row((0, 2, 0, 0, 1, 8, 1, 0))[2], 0, "lane(Integer,1) = I8");
    assert_eq!(
        row((0, 2, 0, 0, 3, 8, 1, 0))[2],
        99,
        "lane(Integer,3) = None (3-byte tail fails closed)"
    );
    assert_eq!(row((0, 2, 0, 1, 8, 8, 1, 0))[2], 7, "lane(Sse,8) = F64");
    assert_eq!(row((0, 2, 0, 1, 4, 8, 1, 0))[2], 6, "lane(Sse,4) = F32");
    assert_eq!(row((0, 2, 0, 1, 2, 8, 1, 0))[2], 99, "lane(Sse,2) = None");

    // eightbyte_count.
    assert_eq!(
        row((0, 2, 0, 0, 8, 8, 1, 0))[3],
        1,
        "eightbyte_count(8) = 1"
    );
    assert_eq!(
        row((0, 2, 0, 0, 8, 9, 1, 0))[3],
        2,
        "eightbyte_count(9) = 2"
    );
    assert_eq!(
        row((0, 2, 0, 0, 8, 16, 1, 0))[3],
        2,
        "eightbyte_count(16) = 2"
    );
    assert_eq!(
        row((0, 2, 0, 0, 8, 17, 1, 0))[3],
        3,
        "eightbyte_count(17) = 3"
    );

    // THE "exact size at which a struct goes to memory" deciders:
    //   16-byte aggregate: SysV NOT >16 -> in-regs; WindowsX64 return 16>8 -> sret.
    let s16_sysv = row((0, 2, 0, 0, 8, 16, 1, 0));
    assert_eq!(
        (s16_sysv[4], s16_sysv[5], s16_sysv[6]),
        (0, 0, 0),
        "16B agg stays in registers on SysV"
    );
    assert_eq!(
        row((0, 2, 0, 0, 8, 16, 1, 1))[6],
        1,
        "16B agg return goes sret on WindowsX64 (>8)"
    );
    //   17-byte aggregate: SysV >16 -> sret + MEMORY byval.
    let s17 = row((0, 2, 0, 0, 8, 17, 1, 0));
    assert_eq!(
        (s17[4], s17[5], s17[6]),
        (1, 1, 1),
        "17B agg -> sret + MEMORY byval on SysV"
    );
    //   8-byte aggregate: WindowsX64 return 8>8 false -> in-regs.
    assert_eq!(
        row((0, 2, 0, 0, 8, 8, 1, 1))[6],
        0,
        "8B agg return NOT sret on WindowsX64 (8 not >8)"
    );
    //   24-byte aggregate: SysV >16 -> sret + MEMORY byval.
    let a24 = row((0, 2, 0, 0, 8, 24, 1, 0));
    assert_eq!(
        (a24[4], a24[5]),
        (1, 1),
        "24B agg -> sret + MEMORY byval on SysV"
    );
    //   is_agg=false: never sret/MEMORY regardless of size.
    let sc = row((0, 2, 0, 0, 8, 24, 0, 0));
    assert_eq!(
        (sc[4], sc[5], sc[6]),
        (0, 0, 0),
        "non-aggregate is never sret/MEMORY"
    );
    //   mem_byval is SysV-ONLY: a >16 aggregate under WindowsX64 is NOT MEMORY-byval.
    assert_eq!(
        row((0, 2, 0, 0, 8, 24, 1, 1))[5],
        0,
        "mem_byval is SysV-only (false on WindowsX64)"
    );
}

/// ARMED negative control (Slice B): patch `is_large_x86_sret_by_size`'s `> 16`
/// sret threshold (`%19 = const u32 16` -> 15); a 16-byte aggregate then
/// satisfies `> 15` and mis-classifies as sret. Prove divergence, restore,
/// re-pass.
#[test]
fn trust_abi_x86_sysv_classify_armed_control() {
    const ANCHOR: &str = "%4 = const u32 16";
    assert_eq!(
        ABI_X86_IR.matches(ANCHOR).count(),
        1,
        "corruption anchor must be unique (is_large_x86_sret_by_size >16 threshold)"
    );
    let corrupted = ABI_X86_IR.replace(ANCHOR, "%4 = const u32 15");
    assert_ne!(corrupted, ABI_X86_IR);

    // size=16, is_agg=1, abi=SystemV.
    let corrupt = run_watchdogged::<u32>("abi_x86 CORRUPTED", 1, move |tx| {
        let buffer = jit_module(&corrupted, "abi_x86 CORRUPTED");
        let f: AbiX86Fn = unsafe { std::mem::transmute(bind(&buffer, "abi_x86_root")) };
        let mut out = AbiX86OutC::poisoned();
        unsafe { f(0, 2, 0, 0, 8, 16, 1, 0, &mut out) };
        let _ = tx.send(out.sret_large);
    })[0];
    let pristine = run_watchdogged::<u32>("abi_x86 RESTORED", 1, move |tx| {
        let buffer = jit_module(ABI_X86_IR, "abi_x86 RESTORED");
        let f: AbiX86Fn = unsafe { std::mem::transmute(bind(&buffer, "abi_x86_root")) };
        let mut out = AbiX86OutC::poisoned();
        unsafe { f(0, 2, 0, 0, 8, 16, 1, 0, &mut out) };
        let _ = tx.send(out.sret_large);
    })[0];

    let native = nat_is_large(true, 16) as u32;
    assert_eq!(
        native, 0,
        "production: 16B agg is NOT large-sret (16 is not >16)"
    );
    assert_eq!(
        corrupt, 1,
        "corrupted module mis-classifies 16B agg as large-sret"
    );
    assert_ne!(
        corrupt, native,
        "corrupted JIT DIVERGES from the production oracle"
    );
    assert_eq!(
        pristine, 0,
        "pristine module AGREES with the oracle (restore + re-pass)"
    );
}
