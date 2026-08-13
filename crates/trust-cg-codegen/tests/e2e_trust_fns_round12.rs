//! TRUST-SELF ROUND 25 (thread R25, TRUST BATCH 12): verifying trust-cg's
//! FP-VERIFICATION BIT-MODEL — the checker's own IEEE-754 semantics oracle — and
//! one TRANSLATION-VALIDATION arch-legality gate, through the full pipeline
//! Rust -> MIR -> trust-ir (stage1 `trust_ir_mir --mir-emit-closure`) -> trust-cg
//! JIT -> machine code, asserting native Rust == JIT over swept real inputs, with
//! the LINKED PRODUCTION functions as a SECOND oracle (the round-7/16/20/22/23
//! dual-oracle discipline) AND a native transcription (`slice_native`) as a THIRD.
//!
//! WHY THIS IS THE "CHECKER OF THE CHECKER": every prior round verified compiler
//! machinery (encoders, register files, opt/abi/relocation deciders). This round
//! verifies the VERIFIER's own trust base. `trust-cg-verify/src/fp_bitmodel.rs` is
//! the INTEGER-ONLY IEEE-754 model that EVICTED the host FPU from trust-cg's
//! FP-verification TCB: every FP-lowering equivalence proof (smt.rs `try_eval` FP
//! cases) checks a machine instruction's result against THIS model. So a bug HERE
//! is a soundness hole in the self-verification — the FP equivalence proof would be
//! comparing against a WRONG ORACLE and could ACCEPT a bad FP lowering. Hence the
//! REJECT direction is covered as carefully as accept:
//!   * classify: `is_nan` MUST be false for every non-NaN pattern; `is_snan` vs
//!     `is_qnan` is the mantissa-MSB split (a confusion mis-models FP exceptions);
//!     verified EXHAUSTIVELY over ALL 65536 binary16 patterns + structured
//!     binary32/binary64 edges.
//!   * fcmp -> NZCV: the four flags an AArch64 FCMP sets (they feed conditional
//!     branches); a wrong flag is a wrong branch.
//!   * fmin/fmax vs fminnm/fmaxnm: fmin PROPAGATES a lone qNaN (result NaN) but
//!     fminnm returns the NUMBER — a checker that used the wrong one accepts an
//!     FMINNM-as-FMIN miscompile. This subtle difference is asserted explicitly.
//!   * `TargetArch::idiv_traps` (pass_validators.rs) — the crux of #67: the
//!     SDIV-identity integer-divide expansion is TOTAL on AArch64 (idiv_traps=false,
//!     legal) but a TRAPPING (#DE / SIGFPE) miscompile on x86 (idiv_traps=true,
//!     must be REJECTED). A wrong answer here accepts a trapping miscompile.
//!
//! NET-NEW: no prior verification round (e2e_trust_fns_round2..11,
//! e2e_fold_cast_status) linked `trust_cg_verify` at all — the whole crate is
//! net-new to the native==JIT inventory (grep-confirmed). Functions verified:
//! is_nan, is_inf, is_zero, is_subnormal, is_normal, is_qnan, is_snan, fcmp_n,
//! fcmp_z, fcmp_c, fcmp_v, fmin, fmax, fminnm, fmaxnm, fabs, fneg,
//! TargetArch::idiv_traps (18 pure fns).
//!
//! DUAL/TRIPLE ORACLE: every production fn is PUBLIC and LINKED
//! (`trust_cg_verify::fp_bitmodel::{is_nan,..,fmin,fmaxnm}`,
//! `trust_cg_verify::pass_validators::TargetArch::idiv_traps`). `FpFmt` is flattened
//! to its geometry scalars (total, mant, exp_w) in the slice; `bias` is unused by
//! every classify/fcmp/min-max function (source: bias only enters fadd/fmul/fcvt),
//! so it is omitted — a trivially-faithful destructuring. Each JIT row is compared
//! against BOTH the linked production fn (on the production `FpFmt`) AND a native
//! transcription (`slice_native`), so agreement is not mere self-consistency.
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine
//! is not thread-safe at suite scale (jit-parallel-race-2026-06-29.md). Every JIT
//! execution runs inside a WATCHDOG worker thread; the output POD is 0xDEAD-poisoned
//! before each JIT call so a silent no-op fails loudly.

#![cfg(target_arch = "aarch64")]

use std::sync::mpsc;
use std::time::Duration;

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED PRODUCTION functions/types (the second oracle):
use trust_cg_verify::fp_bitmodel::{
    F16, F32, F64, FpFmt, fabs, fcmp_c, fcmp_n, fcmp_v, fcmp_z, fmax, fmaxnm, fmin, fminnm, fneg,
    is_inf, is_nan, is_normal, is_qnan, is_snan, is_subnormal, is_zero,
};
use trust_cg_verify::pass_validators::TargetArch;

// ── shared harness (round-5/9/10/11/22/23 pattern) ────────────────────────────

const CLASSIFY_IR: &str = include_str!("slices/trust_fp_classify.tir");
const FCMP_IR: &str = include_str!("slices/trust_fp_fcmp.tir");
const MINMAX_IR: &str = include_str!("slices/trust_fp_minmax.tir");
const IDIV_IR: &str = include_str!("slices/trust_idiv_traps.tir");

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

// ── out-PODs (mirror the slice's #[repr(C)] structs) ──────────────────────────

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ClassifyOut {
    is_nan: u32,
    is_inf: u32,
    is_zero: u32,
    is_subnormal: u32,
    is_normal: u32,
    is_qnan: u32,
    is_snan: u32,
}
impl ClassifyOut {
    fn poisoned() -> Self {
        ClassifyOut {
            is_nan: 0xDEAD,
            is_inf: 0xDEAD,
            is_zero: 0xDEAD,
            is_subnormal: 0xDEAD,
            is_normal: 0xDEAD,
            is_qnan: 0xDEAD,
            is_snan: 0xDEAD,
        }
    }
}
type ClassifyFn = unsafe extern "C" fn(u32, u32, u64, *mut ClassifyOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FcmpOut {
    n: u32,
    z: u32,
    c: u32,
    v: u32,
}
impl FcmpOut {
    fn poisoned() -> Self {
        FcmpOut {
            n: 0xDEAD,
            z: 0xDEAD,
            c: 0xDEAD,
            v: 0xDEAD,
        }
    }
}
type FcmpFn = unsafe extern "C" fn(u32, u32, u32, u64, u64, *mut FcmpOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MinMaxOut {
    fmin: u64,
    fmax: u64,
    fminnm: u64,
    fmaxnm: u64,
    fabs_a: u64,
    fneg_a: u64,
}
impl MinMaxOut {
    fn poisoned() -> Self {
        MinMaxOut {
            fmin: 0xDEAD,
            fmax: 0xDEAD,
            fminnm: 0xDEAD,
            fmaxnm: 0xDEAD,
            fabs_a: 0xDEAD,
            fneg_a: 0xDEAD,
        }
    }
}
type MinMaxFn = unsafe extern "C" fn(u32, u32, u32, u64, u64, *mut MinMaxOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct IdivOut {
    traps: u32,
}
impl IdivOut {
    fn poisoned() -> Self {
        IdivOut { traps: 0xDEAD }
    }
}
type IdivFn = unsafe extern "C" fn(u32, *mut IdivOut);

// ── geometry helpers ──────────────────────────────────────────────────────────

/// (total, mant, exp_w) for width tag ∈ {16,32,64}.
fn geom(wtag: u8) -> (u32, u32, u32) {
    match wtag {
        16 => (16, 10, 5),
        32 => (32, 23, 8),
        64 => (64, 52, 11),
        _ => unreachable!("bad width tag {wtag}"),
    }
}
fn prod_fmt(wtag: u8) -> FpFmt {
    match wtag {
        16 => F16,
        32 => F32,
        64 => F64,
        _ => unreachable!("bad width tag {wtag}"),
    }
}

/// Representative IEEE bit patterns for a width, hitting every classify category
/// (zero, ±0, min/max subnormal, min/max normal, ±inf, qNaN, sNaN) and every
/// fcmp/min-max branch (sign pairs, +0 vs -0, lone-NaN vs both-NaN). Built purely
/// from the geometry so it is width-generic.
fn reps(total: u32, mant: u32, exp_w: u32) -> Vec<u64> {
    let sign = 1u64 << (total - 1);
    let mant_mask = (1u64 << mant) - 1;
    let exp_ones = (1u64 << exp_w) - 1;
    let inf = exp_ones << mant;
    let bias = (1u64 << (exp_w - 1)) - 1;
    let one = bias << mant; // 1.0
    let two = (bias + 1) << mant; // 2.0
    let min_normal = 1u64 << mant;
    let max_normal = ((exp_ones - 1) << mant) | mant_mask;
    let min_sub = 1u64;
    let max_sub = mant_mask;
    let qnan = inf | (1u64 << (mant - 1)); // mantissa MSB set -> quiet
    let snan = inf | 1; // mantissa low bit, MSB clear -> signaling
    let snan2 = inf | (1u64 << (mant - 2)); // another signaling
    vec![
        0,
        sign,
        min_sub,
        min_sub | sign,
        max_sub,
        min_normal,
        one,
        two,
        max_normal,
        one | sign,
        two | sign,
        max_normal | sign,
        inf,
        inf | sign,
        qnan,
        qnan | sign,
        snan,
        snan | sign,
        snan2,
    ]
}

// ============================================================================
// slice_native — the THIRD oracle: a native transcription of the slice, VERBATIM
// from trust-cg-verify/src/fp_bitmodel.rs with FpFmt flattened to (total,mant,exp_w).
// Kept independent of the production functions so that JIT == slice_native ==
// production is a genuine three-way agreement, not self-consistency.
// ============================================================================
#[allow(clippy::needless_return)]
mod slice_native {
    pub fn sign(total: u32, x: u64) -> bool {
        (x >> (total - 1)) & 1 == 1
    }
    pub fn exp_field(mant: u32, exp_w: u32, x: u64) -> u32 {
        ((x >> mant) & ((1u64 << exp_w) - 1)) as u32
    }
    pub fn exp_max(exp_w: u32) -> u32 {
        (1u32 << exp_w) - 1
    }
    pub fn mant_field(mant: u32, x: u64) -> u64 {
        x & ((1u64 << mant) - 1)
    }
    fn exp_all_ones(mant: u32, exp_w: u32, x: u64) -> bool {
        exp_field(mant, exp_w, x) == exp_max(exp_w)
    }
    fn exp_all_zero(mant: u32, exp_w: u32, x: u64) -> bool {
        exp_field(mant, exp_w, x) == 0
    }
    fn mant_zero(mant: u32, x: u64) -> bool {
        mant_field(mant, x) == 0
    }
    pub fn is_nan(mant: u32, exp_w: u32, x: u64) -> bool {
        exp_all_ones(mant, exp_w, x) && !mant_zero(mant, x)
    }
    pub fn is_inf(mant: u32, exp_w: u32, x: u64) -> bool {
        exp_all_ones(mant, exp_w, x) && mant_zero(mant, x)
    }
    pub fn is_zero(mant: u32, exp_w: u32, x: u64) -> bool {
        exp_all_zero(mant, exp_w, x) && mant_zero(mant, x)
    }
    pub fn is_subnormal(mant: u32, exp_w: u32, x: u64) -> bool {
        exp_all_zero(mant, exp_w, x) && !mant_zero(mant, x)
    }
    pub fn is_normal(mant: u32, exp_w: u32, x: u64) -> bool {
        !exp_all_ones(mant, exp_w, x) && !exp_all_zero(mant, exp_w, x)
    }
    fn mant_msb(mant: u32, x: u64) -> bool {
        (x >> (mant - 1)) & 1 == 1
    }
    pub fn is_qnan(mant: u32, exp_w: u32, x: u64) -> bool {
        is_nan(mant, exp_w, x) && mant_msb(mant, x)
    }
    pub fn is_snan(mant: u32, exp_w: u32, x: u64) -> bool {
        is_nan(mant, exp_w, x) && !mant_msb(mant, x)
    }
    pub fn word_mask(total: u32) -> u64 {
        if total >= 64 {
            u64::MAX
        } else {
            (1u64 << total) - 1
        }
    }
    pub fn fabs(total: u32, x: u64) -> u64 {
        x & !(1u64 << (total - 1)) & word_mask(total)
    }
    pub fn fneg(total: u32, x: u64) -> u64 {
        (x ^ (1u64 << (total - 1))) & word_mask(total)
    }
    fn magnitude(total: u32, x: u64) -> u64 {
        x & !(1u64 << (total - 1)) & word_mask(total)
    }
    fn fp_lt(total: u32, a: u64, b: u64) -> bool {
        let sa = sign(total, a);
        let sb = sign(total, b);
        let ma = magnitude(total, a);
        let mb = magnitude(total, b);
        if sa {
            if sb { mb < ma } else { !(ma == 0 && mb == 0) }
        } else if sb {
            false
        } else {
            ma < mb
        }
    }
    fn fp_eq(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
        let am = a & word_mask(total);
        let bm = b & word_mask(total);
        am == bm || (is_zero(mant, exp_w, a) && is_zero(mant, exp_w, b))
    }
    fn fcmp_unord(mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
        is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b)
    }
    pub fn fcmp_n(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
        !fcmp_unord(mant, exp_w, a, b) && fp_lt(total, a, b)
    }
    pub fn fcmp_z(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
        !fcmp_unord(mant, exp_w, a, b) && fp_eq(total, mant, exp_w, a, b)
    }
    pub fn fcmp_c(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
        !fcmp_n(total, mant, exp_w, a, b)
    }
    pub fn fcmp_v(mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
        fcmp_unord(mant, exp_w, a, b)
    }
    fn quiet(total: u32, mant: u32, x: u64) -> u64 {
        (x | (1u64 << (mant - 1))) & word_mask(total)
    }
    fn select_nan(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
        if is_snan(mant, exp_w, a) {
            quiet(total, mant, a)
        } else if is_snan(mant, exp_w, b) {
            quiet(total, mant, b)
        } else if is_qnan(mant, exp_w, a) {
            a & word_mask(total)
        } else {
            b & word_mask(total)
        }
    }
    fn num_min(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
        if is_zero(mant, exp_w, a) && is_zero(mant, exp_w, b) {
            if sign(total, a) {
                a & word_mask(total)
            } else {
                b & word_mask(total)
            }
        } else if fp_lt(total, a, b) {
            a & word_mask(total)
        } else {
            b & word_mask(total)
        }
    }
    fn num_max(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
        if is_zero(mant, exp_w, a) && is_zero(mant, exp_w, b) {
            if sign(total, a) {
                b & word_mask(total)
            } else {
                a & word_mask(total)
            }
        } else if fp_lt(total, b, a) {
            a & word_mask(total)
        } else {
            b & word_mask(total)
        }
    }
    pub fn fmin(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
        if is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b) {
            select_nan(total, mant, exp_w, a, b)
        } else {
            num_min(total, mant, exp_w, a, b)
        }
    }
    pub fn fmax(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
        if is_nan(mant, exp_w, a) || is_nan(mant, exp_w, b) {
            select_nan(total, mant, exp_w, a, b)
        } else {
            num_max(total, mant, exp_w, a, b)
        }
    }
    fn nm_force_nan(mant: u32, exp_w: u32, a: u64, b: u64) -> bool {
        is_snan(mant, exp_w, a)
            || is_snan(mant, exp_w, b)
            || (is_nan(mant, exp_w, a) && is_nan(mant, exp_w, b))
    }
    pub fn fminnm(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
        if nm_force_nan(mant, exp_w, a, b) {
            select_nan(total, mant, exp_w, a, b)
        } else if is_nan(mant, exp_w, a) {
            b & word_mask(total)
        } else if is_nan(mant, exp_w, b) {
            a & word_mask(total)
        } else {
            num_min(total, mant, exp_w, a, b)
        }
    }
    pub fn fmaxnm(total: u32, mant: u32, exp_w: u32, a: u64, b: u64) -> u64 {
        if nm_force_nan(mant, exp_w, a, b) {
            select_nan(total, mant, exp_w, a, b)
        } else if is_nan(mant, exp_w, a) {
            b & word_mask(total)
        } else if is_nan(mant, exp_w, b) {
            a & word_mask(total)
        } else {
            num_max(total, mant, exp_w, a, b)
        }
    }
    pub fn idiv_traps(arch_tag: u32) -> bool {
        // TargetArch::Aarch64 => false, X86_64 => true
        arch_tag != 0
    }
}

fn b(v: bool) -> u32 {
    if v { 1 } else { 0 }
}

// ============================================================================
// TEST 1 — classify: is_nan / is_inf / is_zero / is_subnormal / is_normal /
//   is_qnan / is_snan.  EXHAUSTIVE over ALL 65536 binary16 patterns + structured
//   binary32/binary64 edges.  JIT == slice_native == production (linked).
// ============================================================================

fn classify_inputs() -> Vec<(u8, u64)> {
    let mut v: Vec<(u8, u64)> = Vec::with_capacity(65536 + 64);
    // binary16: EXHAUSTIVE — every one of the 65536 bit patterns.
    for x in 0..=0xFFFFu64 {
        v.push((16, x));
    }
    // binary32 + binary64: structured edges (all classify categories).
    for &x in &reps(32, 23, 8) {
        v.push((32, x));
    }
    for &x in &reps(64, 52, 11) {
        v.push((64, x));
    }
    v
}

#[test]
fn trust_fp_classify_production_eq_jit() {
    let inputs = classify_inputs();
    let expected = inputs.len();

    // Production oracle (linked) + native transcription oracle, precomputed.
    let prod: Vec<ClassifyOut> = inputs
        .iter()
        .map(|&(w, x)| {
            let f = prod_fmt(w);
            ClassifyOut {
                is_nan: b(is_nan(f, x)),
                is_inf: b(is_inf(f, x)),
                is_zero: b(is_zero(f, x)),
                is_subnormal: b(is_subnormal(f, x)),
                is_normal: b(is_normal(f, x)),
                is_qnan: b(is_qnan(f, x)),
                is_snan: b(is_snan(f, x)),
            }
        })
        .collect();
    let native: Vec<ClassifyOut> = inputs
        .iter()
        .map(|&(w, x)| {
            let (_t, m, e) = geom(w);
            ClassifyOut {
                is_nan: b(slice_native::is_nan(m, e, x)),
                is_inf: b(slice_native::is_inf(m, e, x)),
                is_zero: b(slice_native::is_zero(m, e, x)),
                is_subnormal: b(slice_native::is_subnormal(m, e, x)),
                is_normal: b(slice_native::is_normal(m, e, x)),
                is_qnan: b(slice_native::is_qnan(m, e, x)),
                is_snan: b(slice_native::is_snan(m, e, x)),
            }
        })
        .collect();

    let sweep = inputs.clone();
    let rows = run_watchdogged::<ClassifyOut>("fp_classify", expected, move |tx| {
        let buffer = jit_module(CLASSIFY_IR, "fp_classify");
        let f: ClassifyFn = unsafe { std::mem::transmute(bind(&buffer, "fp_classify_root")) };
        for &(w, x) in &sweep {
            let (_t, m, e) = geom(w);
            let mut out = ClassifyOut::poisoned();
            unsafe { f(m, e, x, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    // Sanity: at least one of each interesting category actually appeared so the
    // exhaustive sweep is not vacuous.
    let (mut saw_nan, mut saw_inf, mut saw_zero, mut saw_sub, mut saw_norm, mut saw_q, mut saw_s) =
        (0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32);
    for (i, &(w, x)) in inputs.iter().enumerate() {
        assert_ne!(
            rows[i].is_nan, 0xDEAD,
            "row {i} still poisoned (w={w} x={x:#x})"
        );
        assert_eq!(
            rows[i], prod[i],
            "classify JIT != PRODUCTION at w={w} x={x:#x}: jit={:?} prod={:?}",
            rows[i], prod[i]
        );
        assert_eq!(
            rows[i], native[i],
            "classify JIT != slice_native at w={w} x={x:#x}",
        );
        saw_nan += rows[i].is_nan;
        saw_inf += rows[i].is_inf;
        saw_zero += rows[i].is_zero;
        saw_sub += rows[i].is_subnormal;
        saw_norm += rows[i].is_normal;
        saw_q += rows[i].is_qnan;
        saw_s += rows[i].is_snan;
    }
    for (n, c) in [
        ("nan", saw_nan),
        ("inf", saw_inf),
        ("zero", saw_zero),
        ("subnormal", saw_sub),
        ("normal", saw_norm),
        ("qnan", saw_q),
        ("snan", saw_s),
    ] {
        assert!(c > 0, "sweep never exercised category {n}");
    }

    // Independent hand-known binary16 oracle (does NOT route through production):
    // exactly-one-hot + the sNaN/qNaN split.
    let pos = |w: u8, x: u64| inputs.iter().position(|&t| t == (w, x)).unwrap();
    let r = |w: u8, x: u64| rows[pos(w, x)];
    // 0x0000 +0
    assert_eq!(
        r(16, 0x0000),
        out7(0, 0, 1, 0, 0, 0, 0),
        "F16 +0 is_zero only"
    );
    // 0x8000 -0
    assert_eq!(
        r(16, 0x8000),
        out7(0, 0, 1, 0, 0, 0, 0),
        "F16 -0 is_zero only"
    );
    // 0x0001 min subnormal
    assert_eq!(
        r(16, 0x0001),
        out7(0, 0, 0, 1, 0, 0, 0),
        "F16 min subnormal"
    );
    // 0x3C00 = 1.0 normal
    assert_eq!(r(16, 0x3C00), out7(0, 0, 0, 0, 1, 0, 0), "F16 1.0 normal");
    // 0x7C00 +inf
    assert_eq!(r(16, 0x7C00), out7(0, 1, 0, 0, 0, 0, 0), "F16 +inf");
    // 0xFC00 -inf
    assert_eq!(r(16, 0xFC00), out7(0, 1, 0, 0, 0, 0, 0), "F16 -inf");
    // 0x7E00 qNaN (mantissa MSB set)
    assert_eq!(
        r(16, 0x7E00),
        out7(1, 0, 0, 0, 0, 1, 0),
        "F16 qNaN -> is_nan+is_qnan"
    );
    // 0x7C01 sNaN (mantissa MSB clear, low bit set)
    assert_eq!(
        r(16, 0x7C01),
        out7(1, 0, 0, 0, 0, 0, 1),
        "F16 sNaN -> is_nan+is_snan"
    );
}

fn out7(nan: u32, inf: u32, zero: u32, sub: u32, norm: u32, q: u32, s: u32) -> ClassifyOut {
    ClassifyOut {
        is_nan: nan,
        is_inf: inf,
        is_zero: zero,
        is_subnormal: sub,
        is_normal: norm,
        is_qnan: q,
        is_snan: s,
    }
}

/// ARMED negative control (classify): invert the mant_msb quiet-bit test
/// (`icmp eq` -> `icmp ne` in the unique mant_msb block), so the checker can no
/// longer tell a signaling NaN from a quiet one. Prove the qNaN/sNaN verdicts flip
/// in JIT machine code, restore, re-pass. A verifier that mis-models sNaN/qNaN would
/// accept an FP lowering that mishandles the FP-exception (invalid-op) semantics.
#[test]
fn trust_fp_classify_armed_control() {
    const ANCHOR: &str =
        "    %7 = and u64 %5, %6\n    %8 = const u64 1\n    %9 = icmp eq u64 %7, %8";
    assert_eq!(
        CLASSIFY_IR.matches(ANCHOR).count(),
        1,
        "mant_msb quiet-bit anchor must be unique"
    );
    let corrupted = CLASSIFY_IR.replace(
        ANCHOR,
        "    %7 = and u64 %5, %6\n    %8 = const u64 1\n    %9 = icmp ne u64 %7, %8",
    );
    assert_ne!(corrupted, CLASSIFY_IR);

    // (mant,exp_w) for F16, a qNaN (0x7E00) and an sNaN (0x7C01).
    let corrupt = run_watchdogged::<(ClassifyOut, ClassifyOut)>("classify CORRUPT", 1, move |tx| {
        let buffer = jit_module(&corrupted, "classify CORRUPT");
        let f: ClassifyFn = unsafe { std::mem::transmute(bind(&buffer, "fp_classify_root")) };
        let mut q = ClassifyOut::poisoned();
        let mut s = ClassifyOut::poisoned();
        unsafe {
            f(10, 5, 0x7E00, &mut q);
            f(10, 5, 0x7C01, &mut s);
        }
        let _ = tx.send((q, s));
    })[0];
    let pristine =
        run_watchdogged::<(ClassifyOut, ClassifyOut)>("classify RESTORED", 1, move |tx| {
            let buffer = jit_module(CLASSIFY_IR, "classify RESTORED");
            let f: ClassifyFn = unsafe { std::mem::transmute(bind(&buffer, "fp_classify_root")) };
            let mut q = ClassifyOut::poisoned();
            let mut s = ClassifyOut::poisoned();
            unsafe {
                f(10, 5, 0x7E00, &mut q);
                f(10, 5, 0x7C01, &mut s);
            }
            let _ = tx.send((q, s));
        })[0];

    // Production truth: 0x7E00 is qNaN, 0x7C01 is sNaN.
    assert_eq!((b(is_qnan(F16, 0x7E00)), b(is_snan(F16, 0x7E00))), (1, 0));
    assert_eq!((b(is_qnan(F16, 0x7C01)), b(is_snan(F16, 0x7C01))), (0, 1));

    // Corrupted: mant_msb inverted -> qNaN classified as sNaN and vice versa.
    assert_eq!(
        corrupt.0.is_qnan, 0,
        "CORRUPT: qNaN 0x7E00 no longer is_qnan"
    );
    assert_eq!(
        corrupt.0.is_snan, 1,
        "CORRUPT: qNaN 0x7E00 mis-flagged is_snan"
    );
    assert_eq!(
        corrupt.1.is_qnan, 1,
        "CORRUPT: sNaN 0x7C01 mis-flagged is_qnan"
    );
    assert_eq!(
        corrupt.1.is_snan, 0,
        "CORRUPT: sNaN 0x7C01 no longer is_snan"
    );
    // is_nan itself is unaffected by the quiet-bit inversion.
    assert_eq!(corrupt.0.is_nan, 1, "CORRUPT: 0x7E00 still is_nan");
    assert_eq!(corrupt.1.is_nan, 1, "CORRUPT: 0x7C01 still is_nan");

    // Restored: agrees with production again.
    assert_eq!(
        (pristine.0.is_qnan, pristine.0.is_snan),
        (1, 0),
        "RESTORED qNaN"
    );
    assert_eq!(
        (pristine.1.is_qnan, pristine.1.is_snan),
        (0, 1),
        "RESTORED sNaN"
    );
}

// ============================================================================
// TEST 2 — fcmp -> NZCV: fcmp_n / fcmp_z / fcmp_c / fcmp_v over ALL pairs of the
//   representative set, all three widths.  JIT == slice_native == production.
// ============================================================================

fn pair_inputs() -> Vec<(u8, u64, u64)> {
    let mut v: Vec<(u8, u64, u64)> = Vec::new();
    for w in [16u8, 32, 64] {
        let (t, m, e) = geom(w);
        let rs = reps(t, m, e);
        for &a in &rs {
            for &b in &rs {
                v.push((w, a, b));
            }
        }
    }
    v
}

#[test]
fn trust_fp_fcmp_production_eq_jit() {
    let inputs = pair_inputs();
    let expected = inputs.len();

    let prod: Vec<FcmpOut> = inputs
        .iter()
        .map(|&(w, a, bb)| {
            let f = prod_fmt(w);
            FcmpOut {
                n: b(fcmp_n(f, a, bb)),
                z: b(fcmp_z(f, a, bb)),
                c: b(fcmp_c(f, a, bb)),
                v: b(fcmp_v(f, a, bb)),
            }
        })
        .collect();
    let native: Vec<FcmpOut> = inputs
        .iter()
        .map(|&(w, a, bb)| {
            let (t, m, e) = geom(w);
            FcmpOut {
                n: b(slice_native::fcmp_n(t, m, e, a, bb)),
                z: b(slice_native::fcmp_z(t, m, e, a, bb)),
                c: b(slice_native::fcmp_c(t, m, e, a, bb)),
                v: b(slice_native::fcmp_v(m, e, a, bb)),
            }
        })
        .collect();

    let sweep = inputs.clone();
    let rows = run_watchdogged::<FcmpOut>("fp_fcmp", expected, move |tx| {
        let buffer = jit_module(FCMP_IR, "fp_fcmp");
        let f: FcmpFn = unsafe { std::mem::transmute(bind(&buffer, "fp_fcmp_root")) };
        for &(w, a, bb) in &sweep {
            let (t, m, e) = geom(w);
            let mut out = FcmpOut::poisoned();
            unsafe { f(t, m, e, a, bb, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(w, a, bb)) in inputs.iter().enumerate() {
        assert_ne!(rows[i].n, 0xDEAD, "row {i} poisoned");
        assert_eq!(
            rows[i], prod[i],
            "fcmp JIT != PRODUCTION at w={w} a={a:#x} b={bb:#x}: jit={:?} prod={:?}",
            rows[i], prod[i]
        );
        assert_eq!(
            rows[i], native[i],
            "fcmp JIT != slice_native at w={w} a={a:#x} b={bb:#x}"
        );
    }

    // Independent hand-known NZCV oracle (ARM DDI 0487): EQ->0110, LT->1000,
    // GT->0010, UNORDERED->0011. Use F32 (native f32::to_bits for inputs only).
    let f = |x: f32| x.to_bits() as u64;
    let idx = |w: u8, a: u64, bb: u64| inputs.iter().position(|&t| t == (w, a, bb)).unwrap();
    let get = |w: u8, a: u64, bb: u64| rows[idx(w, a, bb)];
    // NOTE: the reps set is built from geometry; find F32 patterns for these values.
    let one = f(1.0);
    let two = f(2.0);
    let ninf = f(f32::NEG_INFINITY);
    // 1.0 < 2.0 : ordered LT -> N=1,Z=0,C=0,V=0
    assert_eq!(
        get(32, one, two),
        FcmpOut {
            n: 1,
            z: 0,
            c: 0,
            v: 0
        },
        "F32 1<2 LT"
    );
    // 2.0 > 1.0 : ordered GT -> N=0,Z=0,C=1,V=0
    assert_eq!(
        get(32, two, one),
        FcmpOut {
            n: 0,
            z: 0,
            c: 1,
            v: 0
        },
        "F32 2>1 GT"
    );
    // 1.0 == 1.0 : ordered EQ -> N=0,Z=1,C=1,V=0
    assert_eq!(
        get(32, one, one),
        FcmpOut {
            n: 0,
            z: 1,
            c: 1,
            v: 0
        },
        "F32 1==1 EQ"
    );
    // -inf < 1.0 : ordered LT
    assert_eq!(
        get(32, ninf, one),
        FcmpOut {
            n: 1,
            z: 0,
            c: 0,
            v: 0
        },
        "F32 -inf<1 LT"
    );
    // qNaN vs 1.0 : UNORDERED -> N=0,Z=0,C=1,V=1
    let qn = f32::NAN.to_bits() as u64;
    assert_eq!(
        get(32, qn, one),
        FcmpOut {
            n: 0,
            z: 0,
            c: 1,
            v: 1
        },
        "F32 NaN?1 UNORDERED"
    );
    // +0 == -0 : ordered EQ
    let pz = f(0.0);
    let nz = f(-0.0);
    assert_eq!(
        get(32, pz, nz),
        FcmpOut {
            n: 0,
            z: 1,
            c: 1,
            v: 0
        },
        "F32 +0==-0 EQ"
    );
}

// ============================================================================
// TEST 3 — fmin / fmax / fminnm / fmaxnm / fabs / fneg over ALL pairs, all widths.
//   The soundness centerpiece: fmin PROPAGATES a lone qNaN, fminnm returns the
//   NUMBER — a checker that confuses them accepts an FMINNM-as-FMIN miscompile.
// ============================================================================

#[test]
fn trust_fp_minmax_production_eq_jit() {
    let inputs = pair_inputs();
    let expected = inputs.len();

    let prod: Vec<MinMaxOut> = inputs
        .iter()
        .map(|&(w, a, bb)| {
            let f = prod_fmt(w);
            MinMaxOut {
                fmin: fmin(f, a, bb),
                fmax: fmax(f, a, bb),
                fminnm: fminnm(f, a, bb),
                fmaxnm: fmaxnm(f, a, bb),
                fabs_a: fabs(f, a),
                fneg_a: fneg(f, a),
            }
        })
        .collect();
    let native: Vec<MinMaxOut> = inputs
        .iter()
        .map(|&(w, a, bb)| {
            let (t, m, e) = geom(w);
            MinMaxOut {
                fmin: slice_native::fmin(t, m, e, a, bb),
                fmax: slice_native::fmax(t, m, e, a, bb),
                fminnm: slice_native::fminnm(t, m, e, a, bb),
                fmaxnm: slice_native::fmaxnm(t, m, e, a, bb),
                fabs_a: slice_native::fabs(t, a),
                fneg_a: slice_native::fneg(t, a),
            }
        })
        .collect();

    let sweep = inputs.clone();
    let rows = run_watchdogged::<MinMaxOut>("fp_minmax", expected, move |tx| {
        let buffer = jit_module(MINMAX_IR, "fp_minmax");
        let f: MinMaxFn = unsafe { std::mem::transmute(bind(&buffer, "fp_minmax_root")) };
        for &(w, a, bb) in &sweep {
            let (t, m, e) = geom(w);
            let mut out = MinMaxOut::poisoned();
            unsafe { f(t, m, e, a, bb, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    for (i, &(w, a, bb)) in inputs.iter().enumerate() {
        assert_ne!(rows[i].fmin, 0xDEAD, "row {i} poisoned");
        assert_eq!(
            rows[i], prod[i],
            "minmax JIT != PRODUCTION at w={w} a={a:#x} b={bb:#x}: jit={:?} prod={:?}",
            rows[i], prod[i]
        );
        assert_eq!(
            rows[i], native[i],
            "minmax JIT != slice_native at w={w} a={a:#x} b={bb:#x}"
        );
    }

    // ---- THE REJECT STORY: lone qNaN — fmin PROPAGATES (result is NaN),
    //      fminnm returns the NUMBER. Verified directly in JIT machine code. ----
    let (t, m, e) = geom(32);
    let qn = f32::NAN.to_bits() as u64; // lone qNaN
    let one = 1.0f32.to_bits() as u64;
    let ix = inputs.iter().position(|&x| x == (32, qn, one)).unwrap();
    let jit = rows[ix];
    // fmin(qNaN, 1.0) is a NaN (propagated); fminnm(qNaN, 1.0) == 1.0 (the number).
    assert!(
        is_nan(F32, jit.fmin),
        "F32 fmin(qNaN,1.0) must PROPAGATE NaN"
    );
    assert_eq!(
        jit.fminnm, one,
        "F32 fminnm(qNaN,1.0) must return the NUMBER 1.0"
    );
    assert_ne!(
        jit.fmin, jit.fminnm,
        "fmin != fminnm on a lone qNaN (the soundness distinction)"
    );
    // Symmetric for the other operand order.
    let ix2 = inputs.iter().position(|&x| x == (32, one, qn)).unwrap();
    assert!(is_nan(F32, rows[ix2].fmin), "F32 fmin(1.0,qNaN) NaN");
    assert_eq!(rows[ix2].fminnm, one, "F32 fminnm(1.0,qNaN) == 1.0");

    // fabs/fneg sanity on -1.0 (F32).
    let none = (-1.0f32).to_bits() as u64;
    let ix3 = inputs.iter().position(|&x| x == (32, none, one)).unwrap();
    assert_eq!(rows[ix3].fabs_a, one, "fabs(-1.0)==1.0");
    assert_eq!(rows[ix3].fneg_a, one, "fneg(-1.0)==1.0");
    let _ = (t, m, e);
}

// ============================================================================
// TEST 4 — TranslationValidation arch-legality gate: TargetArch::idiv_traps.
//   AArch64=false (SDIV total; the SDIV-identity div expansion is LEGAL),
//   x86-64=true  (IDIV traps #DE; the same expansion is a TRAPPING miscompile).
//   Exhaustive over both variants; JIT == slice_native == production.
// ============================================================================

#[test]
fn trust_idiv_traps_production_eq_jit() {
    // arch_tag: 0 = Aarch64, 1 = X86_64.
    let expected = 2usize;
    let rows = run_watchdogged::<(u32, u32)>("idiv_traps", expected, move |tx| {
        let buffer = jit_module(IDIV_IR, "idiv_traps");
        let f: IdivFn = unsafe { std::mem::transmute(bind(&buffer, "idiv_traps_root")) };
        for tag in 0u32..2 {
            let mut out = IdivOut::poisoned();
            unsafe { f(tag, &mut out) };
            let _ = tx.send((tag, out.traps));
        }
    });
    assert_eq!(rows.len(), expected);
    for &(tag, traps) in &rows {
        assert_ne!(traps, 0xDEAD, "idiv row tag={tag} poisoned");
        let prod = if tag == 0 {
            TargetArch::Aarch64.idiv_traps()
        } else {
            TargetArch::X86_64.idiv_traps()
        };
        assert_eq!(traps, b(prod), "idiv JIT != PRODUCTION at tag={tag}");
        assert_eq!(
            traps,
            b(slice_native::idiv_traps(tag)),
            "idiv JIT != slice_native tag={tag}"
        );
    }
    // The concrete legality decision.
    let get = |tag: u32| rows.iter().find(|&&(t, _)| t == tag).unwrap().1;
    assert_eq!(
        get(0),
        0,
        "AArch64 idiv does NOT trap (SDIV-identity expansion legal)"
    );
    assert_eq!(
        get(1),
        1,
        "x86-64 IDIV TRAPS (#DE) — SDIV-identity expansion is a miscompile"
    );
}

/// ARMED negative control (idiv): corrupt the switch/return of the AArch64 arm so
/// the gate wrongly reports that AArch64 idiv TRAPS. A verifier consuming this would
/// REJECT the legal SDIV-identity expansion on AArch64 (or, flipped the other way,
/// ACCEPT the trapping x86 expansion). Prove the flip in JIT machine code, restore.
#[test]
fn trust_idiv_traps_armed_control() {
    // bb3 is the Aarch64 (tag 0) arm: `%6 = const bool false`. Flip to true.
    const ANCHOR: &str = "const bool false";
    assert_eq!(
        IDIV_IR.matches(ANCHOR).count(),
        1,
        "idiv AArch64-arm false-constant anchor must be unique"
    );
    let corrupted = IDIV_IR.replace(ANCHOR, "const bool true");
    assert_ne!(corrupted, IDIV_IR);

    let corrupt = run_watchdogged::<(u32, u32)>("idiv CORRUPT", 1, move |tx| {
        let buffer = jit_module(&corrupted, "idiv CORRUPT");
        let f: IdivFn = unsafe { std::mem::transmute(bind(&buffer, "idiv_traps_root")) };
        let mut a = IdivOut::poisoned();
        let mut x = IdivOut::poisoned();
        unsafe {
            f(0, &mut a);
            f(1, &mut x);
        }
        let _ = tx.send((a.traps, x.traps));
    })[0];
    let pristine = run_watchdogged::<(u32, u32)>("idiv RESTORED", 1, move |tx| {
        let buffer = jit_module(IDIV_IR, "idiv RESTORED");
        let f: IdivFn = unsafe { std::mem::transmute(bind(&buffer, "idiv_traps_root")) };
        let mut a = IdivOut::poisoned();
        let mut x = IdivOut::poisoned();
        unsafe {
            f(0, &mut a);
            f(1, &mut x);
        }
        let _ = tx.send((a.traps, x.traps));
    })[0];

    // Production truth.
    assert_eq!(
        b(TargetArch::Aarch64.idiv_traps()),
        0,
        "prod: AArch64 does not trap"
    );
    assert_eq!(b(TargetArch::X86_64.idiv_traps()), 1, "prod: x86-64 traps");
    // Corrupted: AArch64 now wrongly TRAPS (1); x86 unchanged (1).
    assert_eq!(
        corrupt.0, 1,
        "CORRUPT: AArch64 wrongly reported as trapping"
    );
    assert_ne!(
        corrupt.0,
        b(TargetArch::Aarch64.idiv_traps()),
        "CORRUPT JIT diverges from production"
    );
    assert_eq!(corrupt.1, 1, "CORRUPT: x86 arm unchanged");
    // Restored: agrees again.
    assert_eq!(pristine, (0, 1), "RESTORED module agrees with production");
}
