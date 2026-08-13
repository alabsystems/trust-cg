//! TRUST-SELF ROUND 26 (thread R26, TRUST BATCH 13): verifying the SOUNDNESS-
//! CRITICAL CORE of trust-cg's FP-verification TCB — the `fp_bitmodel` integer-only
//! IEEE-754 ARITHMETIC pipeline (fadd / fsub / fmul / fdiv / fsqrt / fcvt +
//! int<->float, RNE) — through the full pipeline Rust -> MIR -> trust-ir
//! (stage1 `trust_ir_mir --mir-emit-closure`) -> trust-cg JIT -> machine code,
//! asserting native Rust == JIT over swept real inputs.
//!
//! R25 (batch 12) verified this module's CLASSIFY / FCMP / MIN-MAX predicates and
//! explicitly DEFERRED the heavier RNE arithmetic. THIS round does the arithmetic:
//! the integer-only IEEE-754 fadd/fmul/fdiv/fsqrt/fcvt against which trust-cg proves
//! its FP-op lowerings (smt.rs `try_eval` FP cases). A ROUNDING bug here means the
//! FP proofs compare against a WRONG oracle -> a soundness hole in self-verification.
//!
//! THE QUAD-ORACLE (the power of this round). fp_bitmodel is DESIGNED to match
//! IEEE-754 exactly (its whole purpose — an FPU-free trustworthy model), so for the
//! same rounding mode (RNE) `fp_bitmodel::fadd(a,b)` MUST equal the host FPU's a+b
//! bit-for-bit. Each row is compared four ways:
//!   (1) slice_native  — a native transcription of the emitted slice (the SAME source
//!       compiled to the .tir), so JIT==slice_native proves the JIT ran THIS code.
//!   (2) JIT            — the trust-cg machine code.
//!   (3) production     — the LINKED `trust_cg_verify::fp_bitmodel::*` functions.
//!   (4) host FPU       — the real f32/f64 op on the input bit patterns (a genuinely
//!       INDEPENDENT ground truth; f32/f64 only — Rust's f16 is unstable, so f16 is
//!       covered by the 3-way native==JIT==production, itself M4-silicon-validated
//!       via the bridge per R25).
//! All four agreeing bit-for-bit across the sweep verifies the model's arithmetic is
//! faithful to IEEE-754. A JIT != {native,production} divergence is a trust-cg codegen
//! bug; a {native==JIT==production} != host-FPU divergence is a REAL bug in the FP
//! model (reported with exact operands + expected vs got bits).
//!
//! SWEEP crosses the rounding + special-value edges where FP bugs hide: normal×normal
//! incl. round-up / round-to-even / round-down (the RNE tie cases); subnormal operands
//! + subnormal results (gradual underflow); overflow->inf; underflow->zero; NaN
//!   propagation (qNaN/sNaN -> quiet NaN); +/-0 sign rules; inf arithmetic
//!   (inf-inf=NaN, inf/inf=NaN, x/0=inf, 0/0=NaN); the exact ULP boundary of each
//!   rounding decision; plus seeded-random bit patterns (deterministic, varying by
//!   index — no rng). f16 all-pairs over a structured representative set (tractable);
//!   f32/f64 structured set × structured set + seeded-random pairs.
//!
//! NET-NEW: R25 (e2e_trust_fns_round12) verified is_nan/…/fmin/fmaxnm/fabs/fneg/
//! idiv_traps (18 predicates) — NOT the arithmetic. The 20 arithmetic entries here
//! (fadd, fsub, fmul, fdiv, fsqrt, fcvt_widen, fcvt_narrow, fcvt_h_to_s, fcvt_h_to_d,
//! fcvt_s_to_h, fcvt_d_to_h, fcvtzs, fcvtzu, fcvtns, fcvtnu, cvtt_to_si, cvt_to_si,
//! scvtf, ucvtf, + the shared RNE core round_word/round_nat) are net-new (grep-
//! confirmed: only round12 links fp_bitmodel; it links no arithmetic symbol).
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine
//! is not thread-safe at suite scale (jit-parallel-race-2026-06-29.md). Every JIT
//! execution runs inside a WATCHDOG worker thread; the output POD is 0xDEAD-poisoned
//! before each JIT call so a silent no-op fails loudly.

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::sync::mpsc;
use std::time::Duration;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

// LINKED PRODUCTION functions (the 3rd oracle):
use trust_cg_verify::fp_bitmodel::{
    F16, F32, F64, FpFmt, cvt_to_si, cvtt_to_si, fadd, fcvt_d_to_h, fcvt_h_to_d, fcvt_h_to_s,
    fcvt_narrow, fcvt_s_to_h, fcvt_widen, fcvtns, fcvtnu, fcvtzs, fcvtzu, fdiv, fmul, fsqrt, fsub,
    scvtf, ucvtf,
};

// The native-transcription oracle (#1) — the EXACT source of the .tir fixtures.
include!("slices/trust_fp_arith_native.rs");

// ── embedded fixtures (emitted by trust_ir_mir from trust_fp_arith_slice.rs) ──
const ADDSUB_IR: &str = include_str!("slices/trust_fp_addsub.tir");
const MUL_IR: &str = include_str!("slices/trust_fp_mul.tir");
const DIV_IR: &str = include_str!("slices/trust_fp_div.tir");
const SQRT_IR: &str = include_str!("slices/trust_fp_sqrt.tir");
const CVT_IR: &str = include_str!("slices/trust_fp_cvt.tir");
const FTI_IR: &str = include_str!("slices/trust_fp_fti.tir");
const ITF_IR: &str = include_str!("slices/trust_fp_itf.tir");

// ── shared harness (R25 pattern) ──────────────────────────────────────────────

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

const WATCHDOG_SECS: u64 = 200;

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

// ── geometry ──────────────────────────────────────────────────────────────────

/// (total, mant, exp_w, bias) for width tag ∈ {16,32,64}.
fn geom(w: u8) -> (u32, u32, u32, u32) {
    match w {
        16 => (16, 10, 5, 15),
        32 => (32, 23, 8, 127),
        64 => (64, 52, 11, 1023),
        _ => unreachable!("bad width tag {w}"),
    }
}
fn prod_fmt(w: u8) -> FpFmt {
    match w {
        16 => F16,
        32 => F32,
        64 => F64,
        _ => unreachable!(),
    }
}

// ── input generation ──────────────────────────────────────────────────────────

/// Representative IEEE bit patterns for a width, crossing every classify category
/// AND a spread of normals/subnormals near rounding boundaries. Width-generic.
fn reps(total: u32, mant: u32, exp_w: u32) -> Vec<u64> {
    let sign = 1u64 << (total - 1);
    let mant_mask = (1u64 << mant) - 1;
    let exp_ones = (1u64 << exp_w) - 1;
    let inf = exp_ones << mant;
    let bias = (1u64 << (exp_w - 1)) - 1;
    let mk = |e: u64, m: u64| (e << mant) | (m & mant_mask);
    let mut v: Vec<u64> = vec![
        // zeros
        0,
        sign,
        // subnormals
        1,         // min subnormal
        mant_mask, // max subnormal
        mant_mask >> 1,
        (mant_mask >> 1) | 1,
        mant_mask ^ (mant_mask >> 2), // a mid subnormal
        // min / near-min normals
        1u64 << mant,               // min normal
        (1u64 << mant) | 1,         // min normal + 1 ulp
        (1u64 << mant) | mant_mask, // just below 2*min normal
        // 1.0, values around 1.0 (dense rounding region)
        mk(bias, 0),                        // 1.0
        mk(bias, 1),                        // 1.0 + 1 ulp
        mk(bias, mant_mask),                // just below 2.0
        mk(bias, mant_mask >> 1),           // 1.5
        mk(bias, (mant_mask >> 1) + 1),     // ~1.5 + ulp
        mk(bias, 1u64 << (mant - 1)),       // 1.5 exactly (mantissa MSB)
        mk(bias, (1u64 << (mant - 1)) | 1), // 1.5 + 1 ulp
        mk(bias, (1u64 << (mant - 1)) - 1), // just below 1.5
        // 2.0, 3.0, 0.5, larger
        mk(bias + 1, 0),                 // 2.0
        mk(bias + 1, mant_mask >> 1),    // 3.0
        mk(bias - 1, 0),                 // 0.5
        mk(bias - 1, mant_mask),         // just below 1.0
        mk(bias + 2, 0),                 // 4.0
        mk(bias + 3, mant_mask),         // ~15.999
        mk(bias + (exp_ones >> 2), 0x5), // a mid-large normal
        mk(exp_ones - 1, mant_mask),     // max normal
        mk(exp_ones - 1, 0),             // large power of two (near overflow)
        mk(exp_ones - 2, mant_mask),     // just below max
        // specials
        inf,
        inf | sign,
        inf | (1u64 << (mant - 1)),       // qNaN
        inf | 1,                          // sNaN
        inf | (1u64 << (mant - 2)),       // another sNaN
        inf | (1u64 << (mant - 1)) | 0x5, // qNaN w/ payload
    ];
    // signed variants of the finite normals (append -x for a subset)
    let base: Vec<u64> = v.clone();
    for &x in &base {
        if x & (!sign) != 0 && x != inf {
            v.push(x | sign);
        }
    }
    v
}

/// Deterministic pseudo-random full-width bit patterns (xorshift64, seeded by index).
fn rand_bits(total: u32, n: usize) -> Vec<u64> {
    let mask = if total >= 64 {
        u64::MAX
    } else {
        (1u64 << total) - 1
    };
    let mut out = Vec::with_capacity(n);
    let mut s: u64 = 0x9E37_79B9_7F4A_7C15 ^ ((total as u64) << 40);
    for _ in 0..n {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        out.push(s & mask);
    }
    out
}

// ── host-FPU oracle (independent ground truth; f32/f64 only) ──────────────────
// #[inline(never)] so the operation is a real hardware instruction on the runtime
// bit patterns (no constant folding, no NaN canonicalization).

#[inline(never)]
fn host_add(w: u8, a: u64, b: u64) -> u64 {
    match w {
        32 => (f32::from_bits(a as u32) + f32::from_bits(b as u32)).to_bits() as u64,
        64 => (f64::from_bits(a) + f64::from_bits(b)).to_bits(),
        _ => unreachable!(),
    }
}
#[inline(never)]
fn host_sub(w: u8, a: u64, b: u64) -> u64 {
    match w {
        32 => (f32::from_bits(a as u32) - f32::from_bits(b as u32)).to_bits() as u64,
        64 => (f64::from_bits(a) - f64::from_bits(b)).to_bits(),
        _ => unreachable!(),
    }
}
#[inline(never)]
fn host_mul(w: u8, a: u64, b: u64) -> u64 {
    match w {
        32 => (f32::from_bits(a as u32) * f32::from_bits(b as u32)).to_bits() as u64,
        64 => (f64::from_bits(a) * f64::from_bits(b)).to_bits(),
        _ => unreachable!(),
    }
}
#[inline(never)]
fn host_div(w: u8, a: u64, b: u64) -> u64 {
    match w {
        32 => (f32::from_bits(a as u32) / f32::from_bits(b as u32)).to_bits() as u64,
        64 => (f64::from_bits(a) / f64::from_bits(b)).to_bits(),
        _ => unreachable!(),
    }
}
#[inline(never)]
fn host_sqrt(w: u8, a: u64) -> u64 {
    match w {
        32 => f32::from_bits(a as u32).sqrt().to_bits() as u64,
        64 => f64::from_bits(a).sqrt().to_bits(),
        _ => unreachable!(),
    }
}

// ── out-PODs (mirror the slice #[repr(C)] structs) ────────────────────────────

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct AddSubOut {
    fadd: u64,
    fsub: u64,
}
type AddSubFn = unsafe extern "C" fn(u32, u32, u32, u64, u64, *mut AddSubOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct MulOut {
    fmul: u64,
}
type MulFn = unsafe extern "C" fn(u32, u32, u32, u32, u64, u64, *mut MulOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct DivOut {
    fdiv: u64,
}
type DivFn = unsafe extern "C" fn(u32, u32, u32, u32, u64, u64, *mut DivOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SqrtOut {
    fsqrt: u64,
}
type SqrtFn = unsafe extern "C" fn(u32, u32, u32, u32, u64, *mut SqrtOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CvtOut {
    out: u64,
}
type CvtFn = unsafe extern "C" fn(u32, u64, *mut CvtOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct FtiOut {
    out: u64,
}
type FtiFn = unsafe extern "C" fn(u32, u32, u32, u32, u32, u32, u64, *mut FtiOut);

#[repr(C)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct ItfOut {
    out: u64,
}
type ItfFn = unsafe extern "C" fn(u32, u32, u32, u32, u32, u32, u64, *mut ItfOut);

const POISON: u64 = 0xDEAD;

// ============================================================================
// TEST 1 — FADD / FSUB.  quad-oracle over f16 all-pairs + f32/f64 structured ×
//   structured + seeded-random pairs.
// ============================================================================

fn binary_pairs() -> Vec<(u8, u64, u64)> {
    let mut v: Vec<(u8, u64, u64)> = Vec::new();
    // explicit named witnesses (exact IEEE f32 bit patterns used by the closing asserts).
    for &(a, bb) in &[
        (0x3F80_0000u64, 0x3F80_0000u64), // 1.0, 1.0
        (0x3F80_0000, 0xBF80_0000),       // 1.0, -1.0
        (0x4000_0000, 0x4040_0000),       // 2.0, 3.0
        (0x3F80_0000, 0x4040_0000),       // 1.0, 3.0
    ] {
        v.push((32, a, bb));
    }
    for w in [16u8, 32, 64] {
        let (t, m, e, _bs) = geom(w);
        let rs = reps(t, m, e);
        // structured × structured (all pairs)
        for &a in &rs {
            for &bb in &rs {
                v.push((w, a, bb));
            }
        }
        // seeded-random × seeded-random
        let ra = rand_bits(t, 90);
        let rb = rand_bits(t, 90);
        for (i, &a) in ra.iter().enumerate() {
            v.push((w, a, rb[i]));
            v.push((w, a, rb[(i + 37) % rb.len()]));
        }
        // random × structured
        for (i, &a) in ra.iter().enumerate() {
            v.push((w, a, rs[i % rs.len()]));
            v.push((w, rs[i % rs.len()], a));
        }
    }
    v
}

#[test]
fn trust_fp_addsub_quad_oracle() {
    let inputs = binary_pairs();
    let expected = inputs.len();
    let sweep = inputs.clone();

    let rows = run_watchdogged::<AddSubOut>("fp_addsub", expected, move |tx| {
        let buffer = jit_module(ADDSUB_IR, "fp_addsub");
        let f: AddSubFn = unsafe { std::mem::transmute(bind(&buffer, "fp_addsub_root")) };
        for &(w, a, bb) in &sweep {
            let (t, m, e, _bs) = geom(w);
            let mut out = AddSubOut {
                fadd: POISON,
                fsub: POISON,
            };
            unsafe { f(t, m, e, a, bb, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut host_checked = 0usize;
    let mut fsub_nan_cases_now_agree = 0usize;
    for (i, &(w, a, bb)) in inputs.iter().enumerate() {
        let (t, m, e, _bs) = geom(w);
        let f = prod_fmt(w);
        let jit = rows[i];
        assert_ne!(jit.fadd, POISON, "row {i} still poisoned (w={w})");
        // (1) native  (3) production
        let nat = AddSubOut {
            fadd: slice_native::fadd(t, m, e, a, bb),
            fsub: slice_native::fsub(t, m, e, a, bb),
        };
        let prod = AddSubOut {
            fadd: fadd(f, a, bb),
            fsub: fsub(f, a, bb),
        };
        assert_eq!(
            jit, prod,
            "FADD/FSUB JIT != PRODUCTION w={w} a={a:#x} b={bb:#x}"
        );
        assert_eq!(
            jit, nat,
            "FADD/FSUB JIT != slice_native w={w} a={a:#x} b={bb:#x}"
        );
        // (4) host FPU (f32/f64)
        if w == 32 || w == 64 {
            let ha = host_add(w, a, bb);
            let hs = host_sub(w, a, bb);
            // FADD is bit-exact vs the host FPU (0 divergences across the whole sweep).
            assert_eq!(
                jit.fadd, ha,
                "FADD model != HOST FPU (REAL model bug) w={w} a={a:#x} b={bb:#x}: model={:#x} host={ha:#x}",
                jit.fadd
            );
            // owner #8 FIXED: FSUB is now bit-exact vs the host FPU EVERYWHERE, including
            // the NaN-sign cases that used to diverge. fp_bitmodel::fsub now dispatches
            // NaN over the ORIGINAL operands (matching ARM FSUB, which propagates b's NaN
            // with its original sign) instead of fadd(a, fneg(b)) which flipped it.
            // See trust_fp_fsub_nan_sign_bug_pinned.
            assert_eq!(
                jit.fsub, hs,
                "FSUB model != HOST FPU (REAL model bug) w={w} a={a:#x} b={bb:#x}: model={:#x} host={hs:#x}",
                jit.fsub
            );
            // Track that the previously-divergent NaN-operand class is still exercised and
            // now AGREES with the host (so the fix's coverage isn't silently lost).
            if slice_native::is_nan(m, e, bb) || slice_native::is_nan(m, e, a) {
                fsub_nan_cases_now_agree += 1;
            }
            host_checked += 1;
        }
    }
    assert!(
        host_checked > 1000,
        "host-FPU cross-check too sparse: {host_checked}"
    );
    // The previously-divergent fsub NaN class must still be exercised by the sweep (so
    // the clean bill is not silently masking a broken host oracle) — now it AGREES.
    assert!(
        fsub_nan_cases_now_agree > 0,
        "the fsub NaN-operand class was never hit — sweep lost coverage"
    );
    eprintln!(
        "addsub host-FPU cross-check: {host_checked} rows; FADD 0 divergences; \
         FSUB 0 divergences (owner #8 FIXED) — {fsub_nan_cases_now_agree} NaN-operand cases now AGREE with host"
    );

    // Named witnesses (from the fp_bitmodel #94 regression tests — the correctly-
    // rounded RNE values as INTEGER bit patterns; a rounding regression flips these).
    let find = |w: u8, a: u64, bb: u64| {
        inputs
            .iter()
            .position(|&t| t == (w, a, bb))
            .map(|ix| rows[ix])
    };
    // 1.0 + 1.0 = 2.0
    assert_eq!(
        find(32, 0x3F80_0000, 0x3F80_0000).unwrap().fadd,
        0x4000_0000
    );
    // 1.0 + (-1.0) = +0
    assert_eq!(
        find(32, 0x3F80_0000, 0xBF80_0000).unwrap().fadd,
        0x0000_0000
    );
}

// ============================================================================
// TEST 1b — owner #8 FIXED (clean bill): fp_bitmodel::fsub now propagates a NaN
//   operand with its ORIGINAL sign, matching the host FPU / ARM FSUB. (Was a
//   fail-loud pin: fsub = fadd(a, fneg(b)) flipped a propagated b-NaN's sign, so an
//   FSUB-lowering equivalence proof compared against a wrong-signed oracle.) A
//   regression re-introducing the fneg-first form fails these `model == host` asserts.
// ============================================================================

#[inline(never)]
fn host_sub32(a: u32, b: u32) -> u32 {
    (f32::from_bits(a) - f32::from_bits(b)).to_bits()
}
#[inline(never)]
fn host_sub64(a: u64, b: u64) -> u64 {
    (f64::from_bits(a) - f64::from_bits(b)).to_bits()
}

#[test]
fn trust_fp_fsub_nan_sign_fixed_clean_bill() {
    // f32: fsub(+0, +qNaN). ARM FSUB propagates the qNaN with its ORIGINAL (+) sign;
    // the fixed model now matches.
    let model = fsub(F32, 0x0000_0000, 0x7FC0_0000) as u32;
    let host = host_sub32(0x0000_0000, 0x7FC0_0000);
    assert_eq!(
        model, 0x7FC0_0000,
        "owner #8 FIXED: model keeps the qNaN's original sign"
    );
    assert_eq!(
        host, 0x7FC0_0000,
        "host ARM FSUB keeps the qNaN's original sign"
    );
    assert_eq!(model, host, "model == host (NaN sign preserved)");
    assert!(slice_native::is_nan(23, 8, model as u64) && slice_native::is_nan(23, 8, host as u64));

    // f32: the mirror, fsub(+0, -qNaN) -> both -qNaN.
    let model2 = fsub(F32, 0x0000_0000, 0xFFC0_0000) as u32;
    let host2 = host_sub32(0x0000_0000, 0xFFC0_0000);
    assert_eq!(model2, 0xFFC0_0000, "owner #8 FIXED: -qNaN preserved");
    assert_eq!(host2, 0xFFC0_0000);
    assert_eq!(model2, host2);

    // f64 analogue.
    let m64 = fsub(F64, 0, 0x7FF8_0000_0000_0000);
    let h64 = host_sub64(0, 0x7FF8_0000_0000_0000);
    assert_eq!(
        m64, 0x7FF8_0000_0000_0000,
        "owner #8 FIXED: f64 fsub keeps original sign"
    );
    assert_eq!(
        h64, 0x7FF8_0000_0000_0000,
        "host f64 FSUB keeps original sign"
    );
    assert_eq!(m64, h64);

    // FADD always matched host (no fneg): fadd(+0, qNaN) both signs.
    assert_eq!(
        fadd(F32, 0, 0x7FC0_0000) as u32,
        host_add_pin(0, 0x7FC0_0000)
    );
    assert_eq!(
        fadd(F32, 0, 0xFFC0_0000) as u32,
        host_add_pin(0, 0xFFC0_0000)
    );
}

#[inline(never)]
fn host_add_pin(a: u32, b: u32) -> u32 {
    (f32::from_bits(a) + f32::from_bits(b)).to_bits()
}

// ============================================================================
// TEST 2 — FMUL.  quad-oracle. (The mantissa product is a plain `mul u128`, which
//   lowers — owner #3 only blocks the *checked* mul.overflow 256-bit form.)
// ============================================================================

#[test]
fn trust_fp_mul_quad_oracle() {
    let inputs = binary_pairs();
    let expected = inputs.len();
    let sweep = inputs.clone();

    let rows = run_watchdogged::<MulOut>("fp_mul", expected, move |tx| {
        let buffer = jit_module(MUL_IR, "fp_mul");
        let f: MulFn = unsafe { std::mem::transmute(bind(&buffer, "fp_mul_root")) };
        for &(w, a, bb) in &sweep {
            let (t, m, e, bs) = geom(w);
            let mut out = MulOut { fmul: POISON };
            unsafe { f(t, m, e, bs, a, bb, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut host_checked = 0usize;
    for (i, &(w, a, bb)) in inputs.iter().enumerate() {
        let (t, m, e, bs) = geom(w);
        let f = prod_fmt(w);
        let jit = rows[i].fmul;
        assert_ne!(jit, POISON, "row {i} poisoned");
        assert_eq!(
            jit,
            fmul(f, a, bb),
            "FMUL JIT != PRODUCTION w={w} a={a:#x} b={bb:#x}"
        );
        assert_eq!(
            jit,
            slice_native::fmul(t, m, e, bs, a, bb),
            "FMUL JIT != slice_native w={w} a={a:#x} b={bb:#x}"
        );
        if w == 32 || w == 64 {
            let h = host_mul(w, a, bb);
            assert_eq!(
                jit, h,
                "FMUL model != HOST FPU (REAL model bug) w={w} a={a:#x} b={bb:#x}: model={jit:#x} host={h:#x}"
            );
            host_checked += 1;
        }
    }
    assert!(host_checked > 1000, "host cross-check too sparse");
    // 2.0 * 3.0 = 6.0
    let find = |a: u64, bb: u64| {
        inputs
            .iter()
            .position(|&t| t == (32, a, bb))
            .map(|ix| rows[ix].fmul)
    };
    assert_eq!(find(0x4000_0000, 0x4040_0000).unwrap(), 0x40C0_0000);
}

// ============================================================================
// TEST 3 — FDIV.  quad-oracle (restoring long division; x/0=inf, 0/0=NaN, inf/inf=NaN).
// ============================================================================

#[test]
fn trust_fp_div_quad_oracle() {
    let inputs = binary_pairs();
    let expected = inputs.len();
    let sweep = inputs.clone();

    let rows = run_watchdogged::<DivOut>("fp_div", expected, move |tx| {
        let buffer = jit_module(DIV_IR, "fp_div");
        let f: DivFn = unsafe { std::mem::transmute(bind(&buffer, "fp_div_root")) };
        for &(w, a, bb) in &sweep {
            let (t, m, e, bs) = geom(w);
            let mut out = DivOut { fdiv: POISON };
            unsafe { f(t, m, e, bs, a, bb, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut host_checked = 0usize;
    for (i, &(w, a, bb)) in inputs.iter().enumerate() {
        let (t, m, e, bs) = geom(w);
        let f = prod_fmt(w);
        let jit = rows[i].fdiv;
        assert_ne!(jit, POISON, "row {i} poisoned");
        assert_eq!(
            jit,
            fdiv(f, a, bb),
            "FDIV JIT != PRODUCTION w={w} a={a:#x} b={bb:#x}"
        );
        assert_eq!(
            jit,
            slice_native::fdiv(t, m, e, bs, a, bb),
            "FDIV JIT != slice_native w={w} a={a:#x} b={bb:#x}"
        );
        if w == 32 || w == 64 {
            let h = host_div(w, a, bb);
            assert_eq!(
                jit, h,
                "FDIV model != HOST FPU (REAL model bug) w={w} a={a:#x} b={bb:#x}: model={jit:#x} host={h:#x}"
            );
            host_checked += 1;
        }
    }
    assert!(host_checked > 1000, "host cross-check too sparse");
    // 1.0 / 3.0 = 0x3eaaaaab ; x/0 -> +Inf ; 0/0 -> qNaN
    let find = |a: u64, bb: u64| {
        inputs
            .iter()
            .position(|&t| t == (32, a, bb))
            .map(|ix| rows[ix].fdiv)
    };
    assert_eq!(find(0x3F80_0000, 0x4040_0000).unwrap(), 0x3EAA_AAAB);
}

// ============================================================================
// TEST 4 — FSQRT.  quad-oracle (digit-by-digit integer sqrt; sqrt(-x)=NaN).
// ============================================================================

fn unary_inputs() -> Vec<(u8, u64)> {
    let mut v: Vec<(u8, u64)> = Vec::new();
    for w in [16u8, 32, 64] {
        let (t, m, e, _bs) = geom(w);
        for &x in &reps(t, m, e) {
            v.push((w, x));
        }
        for &x in &rand_bits(t, 400) {
            v.push((w, x));
        }
    }
    v
}

#[test]
fn trust_fp_sqrt_quad_oracle() {
    let inputs = unary_inputs();
    let expected = inputs.len();
    let sweep = inputs.clone();

    let rows = run_watchdogged::<SqrtOut>("fp_sqrt", expected, move |tx| {
        let buffer = jit_module(SQRT_IR, "fp_sqrt");
        let f: SqrtFn = unsafe { std::mem::transmute(bind(&buffer, "fp_sqrt_root")) };
        for &(w, x) in &sweep {
            let (t, m, e, bs) = geom(w);
            let mut out = SqrtOut { fsqrt: POISON };
            unsafe { f(t, m, e, bs, x, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut host_checked = 0usize;
    for (i, &(w, x)) in inputs.iter().enumerate() {
        let (t, m, e, bs) = geom(w);
        let f = prod_fmt(w);
        let jit = rows[i].fsqrt;
        assert_ne!(jit, POISON, "row {i} poisoned");
        assert_eq!(jit, fsqrt(f, x), "FSQRT JIT != PRODUCTION w={w} x={x:#x}");
        assert_eq!(
            jit,
            slice_native::fsqrt(t, m, e, bs, x),
            "FSQRT JIT != slice_native w={w} x={x:#x}"
        );
        if w == 32 || w == 64 {
            let h = host_sqrt(w, x);
            assert_eq!(
                jit, h,
                "FSQRT model != HOST FPU (REAL model bug) w={w} x={x:#x}: model={jit:#x} host={h:#x}"
            );
            host_checked += 1;
        }
    }
    assert!(host_checked > 500, "host cross-check too sparse");
    // sqrt(2.0)=0x3fb504f3 ; sqrt(4.0)=2.0
    let find = |x: u64| {
        inputs
            .iter()
            .position(|&t| t == (32, x))
            .map(|ix| rows[ix].fsqrt)
    };
    assert_eq!(find(0x4000_0000).unwrap(), 0x3FB5_04F3);
    assert_eq!(find(0x4080_0000).unwrap(), 0x4000_0000);
}

// ============================================================================
// TEST 5 — FCVT float<->float (widen f32->f64, narrow f64->f32, f16<->f32/f64).
//   Host FPU cross-check for the f32<->f64 pair (`as` cast, correctly rounded);
//   f16 covered 3-way (native==JIT==production, M4-validated via bridge).
// ============================================================================

#[test]
fn trust_fp_cvt_quad_oracle() {
    // (op, x) : op 0 widen f32->f64, 1 narrow f64->f32, 2 h_to_s, 3 h_to_d,
    //           4 s_to_h, 5 d_to_h.
    let mut inputs: Vec<(u32, u64)> = Vec::new();
    // widen / s_to_h source = f32 patterns ; h_to_* source = f16 ; narrow/d_to_h = f64.
    for &x in &reps(32, 23, 8) {
        inputs.push((0, x));
        inputs.push((4, x));
    }
    for &x in &rand_bits(32, 300) {
        inputs.push((0, x));
        inputs.push((4, x));
    }
    for &x in &reps(64, 52, 11) {
        inputs.push((1, x));
        inputs.push((5, x));
    }
    for &x in &rand_bits(64, 300) {
        inputs.push((1, x));
        inputs.push((5, x));
    }
    for x in 0u64..=0xFFFF {
        inputs.push((2, x)); // h_to_s exhaustive over all f16
        inputs.push((3, x)); // h_to_d exhaustive over all f16
    }
    let expected = inputs.len();
    let sweep = inputs.clone();

    let rows = run_watchdogged::<CvtOut>("fp_cvt", expected, move |tx| {
        let buffer = jit_module(CVT_IR, "fp_cvt");
        let f: CvtFn = unsafe { std::mem::transmute(bind(&buffer, "fp_cvt_root")) };
        for &(op, x) in &sweep {
            let mut out = CvtOut { out: POISON };
            unsafe { f(op, x, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut host_checked = 0usize;
    for (i, &(op, x)) in inputs.iter().enumerate() {
        let jit = rows[i].out;
        assert_ne!(jit, POISON, "row {i} poisoned");
        let (prod, nat) = match op {
            0 => (fcvt_widen(x), slice_native::fcvt_widen(x)),
            1 => (fcvt_narrow(x), slice_native::fcvt_narrow(x)),
            2 => (fcvt_h_to_s(x), slice_native::fcvt_h_to_s(x)),
            3 => (fcvt_h_to_d(x), slice_native::fcvt_h_to_d(x)),
            4 => (fcvt_s_to_h(x), slice_native::fcvt_s_to_h(x)),
            _ => (fcvt_d_to_h(x), slice_native::fcvt_d_to_h(x)),
        };
        assert_eq!(jit, prod, "FCVT JIT != PRODUCTION op={op} x={x:#x}");
        assert_eq!(jit, nat, "FCVT JIT != slice_native op={op} x={x:#x}");
        // host FPU: widen f32->f64, narrow f64->f32.
        if op == 0 {
            let h = (f32::from_bits(x as u32) as f64).to_bits();
            assert_eq!(
                jit, h,
                "FCVT widen model != HOST x={x:#x}: model={jit:#x} host={h:#x}"
            );
            host_checked += 1;
        } else if op == 1 {
            let h = (f64::from_bits(x) as f32).to_bits() as u64;
            assert_eq!(
                jit, h,
                "FCVT narrow model != HOST x={x:#x}: model={jit:#x} host={h:#x}"
            );
            host_checked += 1;
        }
    }
    assert!(host_checked > 500, "host cross-check too sparse");
    // widen 2.0_f32 -> 2.0_f64 ; narrow 1.0_f64 -> 1.0_f32
    let find = |op: u32, x: u64| {
        inputs
            .iter()
            .position(|&t| t == (op, x))
            .map(|ix| rows[ix].out)
    };
    assert_eq!(find(0, 0x4000_0000).unwrap(), 0x4000_0000_0000_0000);
    assert_eq!(find(1, 0x3FF0_0000_0000_0000).unwrap(), 0x3F80_0000);
    assert_eq!(find(2, 0x3C00).unwrap(), 0x3F80_0000); // 1.0 f16 -> f32
}

// ============================================================================
// TEST 6 — FCVT float->int (FCVTZS/ZU/NS/NU + x86 CVTT/CVT indefinite).
//   Host FPU cross-check via Rust saturating `as` casts (AArch64 modes, int_w 32/64).
// ============================================================================

fn host_fti(mode: u32, int_w: u32, w: u8, x: u64) -> Option<u64> {
    // Only AArch64 modes (0..=3) at int_w 32/64 have a clean Rust `as`-cast oracle.
    if mode > 3 || (int_w != 32 && int_w != 64) {
        return None;
    }
    let fv64 = |xx: u64| {
        if w == 32 {
            f32::from_bits(xx as u32) as f64
        } else {
            f64::from_bits(xx)
        }
    };
    // For fidelity we operate at the source width, then apply the saturating cast.
    match (w, mode, int_w) {
        // round-to-zero (FCVTZS/ZU): Rust `as` is truncate-toward-zero + saturating.
        (32, 0, 32) => Some((f32::from_bits(x as u32) as i32) as u32 as u64),
        (32, 0, 64) => Some((f32::from_bits(x as u32) as i64) as u64),
        (32, 1, 32) => Some((f32::from_bits(x as u32) as u32) as u64),
        (32, 1, 64) => Some(f32::from_bits(x as u32) as u64),
        (64, 0, 32) => Some((f64::from_bits(x) as i32) as u32 as u64),
        (64, 0, 64) => Some((f64::from_bits(x) as i64) as u64),
        (64, 1, 32) => Some((f64::from_bits(x) as u32) as u64),
        (64, 1, 64) => Some(f64::from_bits(x) as u64),
        // round-to-nearest-even (FCVTNS/NU): round_ties_even then saturating cast.
        (_, 2, 32) => Some((fv64(x).round_ties_even() as i32) as u32 as u64),
        (_, 2, 64) => Some((fv64(x).round_ties_even() as i64) as u64),
        (_, 3, 32) => Some((fv64(x).round_ties_even() as u32) as u64),
        (_, 3, 64) => Some(fv64(x).round_ties_even() as u64),
        _ => None,
    }
}

/// A huge-value f->int case: a finite NORMAL whose alignment shift overflows the u128
/// work register (biased exp >= bias + 127). This is the class owner #9's model used to
/// UNDER-saturate to 0; after the fix (guard fires on u128 overflow, `shl2 > lz(sig)`)
/// it saturates correctly (== host). Used only to confirm the sweep still EXERCISES the
/// class (coverage), not to exclude any divergence.
fn fti_huge_value_case(w: u8, x: u64) -> bool {
    let (_t, m, e, bias) = geom(w);
    slice_native::is_normal(m, e, x) && slice_native::exp_field(m, e, x) >= bias + 127
}

fn fti_inputs() -> Vec<(u8, u32, u32, u64)> {
    // (w, int_w, mode, x)
    let mut v: Vec<(u8, u32, u32, u64)> = Vec::new();
    for w in [32u8, 64] {
        let (t, m, e, _bs) = geom(w);
        let mut xs = reps(t, m, e);
        xs.extend(rand_bits(t, 200));
        // Explicit huge power-of-two witnesses that hit the u128-overflow bug window
        // (mantissa 0). f32: eb 254 (2^127). f64: eb in [1150,1201].
        if w == 32 {
            xs.push(254u64 << 23); // 2^127
            xs.push((254u64 << 23) | (1u64 << 31)); // -2^127
            xs.push((254u64 << 23) | 0x40_0000); // 1.5*2^127 (nonzero mant -> self-corrects)
            xs.push(0x4020_0000); // 2.5 (rounding witness)
            xs.push(0x4060_0000); // 3.5 (ties-to-even witness)
        } else {
            for eb in [1150u64, 1173, 1201] {
                xs.push(eb << 52);
                xs.push((eb << 52) | (1u64 << 63));
            }
        }
        for &x in &xs {
            for int_w in [8u32, 16, 32, 64] {
                for mode in 0u32..6 {
                    v.push((w, int_w, mode, x));
                }
            }
        }
    }
    v
}

#[test]
fn trust_fp_fti_quad_oracle() {
    let inputs = fti_inputs();
    let expected = inputs.len();
    let sweep = inputs.clone();

    let rows = run_watchdogged::<FtiOut>("fp_fti", expected, move |tx| {
        let buffer = jit_module(FTI_IR, "fp_fti");
        let f: FtiFn = unsafe { std::mem::transmute(bind(&buffer, "fp_fti_root")) };
        for &(w, int_w, mode, x) in &sweep {
            let (t, m, e, bs) = geom(w);
            let mut out = FtiOut { out: POISON };
            unsafe { f(t, m, e, bs, int_w, mode, x, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut host_checked = 0usize;
    let mut fti_huge_cases_now_agree = 0usize;
    for (i, &(w, int_w, mode, x)) in inputs.iter().enumerate() {
        let (t, m, e, bs) = geom(w);
        let f = prod_fmt(w);
        let jit = rows[i].out;
        assert_ne!(jit, POISON, "row {i} poisoned");
        let (prod, nat) = match mode {
            0 => (
                fcvtzs(f, int_w, x),
                slice_native::fcvtzs(t, m, e, bs, int_w, x),
            ),
            1 => (
                fcvtzu(f, int_w, x),
                slice_native::fcvtzu(t, m, e, bs, int_w, x),
            ),
            2 => (
                fcvtns(f, int_w, x),
                slice_native::fcvtns(t, m, e, bs, int_w, x),
            ),
            3 => (
                fcvtnu(f, int_w, x),
                slice_native::fcvtnu(t, m, e, bs, int_w, x),
            ),
            4 => (
                cvtt_to_si(f, int_w, x),
                slice_native::cvtt_to_si(t, m, e, bs, int_w, x),
            ),
            _ => (
                cvt_to_si(f, int_w, x),
                slice_native::cvt_to_si(t, m, e, bs, int_w, x),
            ),
        };
        assert_eq!(
            jit, prod,
            "FTI JIT != PRODUCTION w={w} int_w={int_w} mode={mode} x={x:#x}"
        );
        assert_eq!(
            jit, nat,
            "FTI JIT != slice_native w={w} int_w={int_w} mode={mode} x={x:#x}"
        );
        if let Some(h) = host_fti(mode, int_w, w, x) {
            // owner #9 FIXED: bit-exact vs the host saturating cast EVERYWHERE, including
            // the huge-value power-of-two window that used to under-saturate to 0.
            assert_eq!(
                jit, h,
                "FTI model != HOST FPU w={w} int_w={int_w} mode={mode} x={x:#x}: model={jit:#x} host={h:#x}"
            );
            // Confirm the previously-buggy huge-value class is still exercised and now agrees.
            if fti_huge_value_case(w, x) {
                fti_huge_cases_now_agree += 1;
            }
            host_checked += 1;
        }
    }
    assert!(host_checked > 1000, "host cross-check too sparse");
    assert!(
        fti_huge_cases_now_agree > 0,
        "the fti huge-value class was never exercised — sweep lost coverage"
    );
    eprintln!(
        "fti host-FPU cross-check: {host_checked} rows; 0 divergences (owner #9 FIXED) — \
         {fti_huge_cases_now_agree} huge-value cases now saturate correctly (== host)"
    );
    // FCVTZS 2.5_f32 -> 2 ; FCVTNS 3.5_f32 -> 4 (ties to even)
    let find = |int_w: u32, mode: u32, x: u64| {
        inputs
            .iter()
            .position(|&t| t == (32u8, int_w, mode, x))
            .map(|ix| rows[ix].out)
    };
    assert_eq!(find(32, 0, 0x4020_0000).unwrap(), 2);
    assert_eq!(find(32, 2, 0x4060_0000).unwrap(), 4);
}

// ============================================================================
// TEST 6b — owner #9 FIXED (clean bill): fp_bitmodel f->int now SATURATES a
//   high-magnitude power-of-two finite input, matching the host / ARM FCVTZS. (Was a
//   fail-loud pin: the significand's single set bit shifted OUT of the u128 work
//   register before the `too_big` guard (shl2 >= 128) fired, so the model returned 0
//   instead of the saturated extreme.) The guard now fires on u128 overflow
//   (`shl2 > lz(sig)`). A regression re-introducing the shl2>=128-only guard fails these.
// ============================================================================

#[test]
fn trust_fp_fti_huge_value_fixed_clean_bill() {
    // f32 2^127 (eb=254, mantissa 0) -> i32::MAX, matching host, across widths/modes/sign.
    assert_eq!(
        fcvtzs(F32, 32, 0x7F00_0000),
        0x7FFF_FFFF,
        "owner #9 FIXED: 2^127 -> i32::MAX"
    );
    assert_eq!(
        fcvtzs(F32, 32, 0x7F00_0000),
        (f32::from_bits(0x7F00_0000) as i32) as u32 as u64,
        "model == host (2^127 -> i32::MAX)"
    );
    assert_eq!(
        fcvtzs(F32, 64, 0x7F00_0000),
        0x7FFF_FFFF_FFFF_FFFF,
        "2^127 -> i64::MAX"
    );
    assert_eq!(
        fcvtzu(F32, 32, 0x7F00_0000),
        0xFFFF_FFFF,
        "2^127 -> u32::MAX"
    );
    assert_eq!(
        fcvtns(F32, 32, 0x7F00_0000),
        0x7FFF_FFFF,
        "2^127 (nearest) -> i32::MAX"
    );
    // -2^127 -> i32::MIN, matching host.
    assert_eq!(
        fcvtzs(F32, 32, 0xFF00_0000),
        0x8000_0000,
        "owner #9 FIXED: -2^127 -> i32::MIN"
    );
    assert_eq!(
        fcvtzs(F32, 32, 0xFF00_0000),
        (f32::from_bits(0xFF00_0000) as i32) as u32 as u64,
        "model == host (-2^127 -> i32::MIN)"
    );

    // f64 2^150 (eb=1173, the [1150,1201] under-saturation window) -> i64::MAX == host.
    let x = 1173u64 << 52;
    assert_eq!(
        fcvtzs(F64, 64, x),
        0x7FFF_FFFF_FFFF_FFFF,
        "owner #9 FIXED: 2^150 -> i64::MAX"
    );
    assert_eq!(
        fcvtzs(F64, 64, x),
        (f64::from_bits(x) as i64) as u64,
        "model == host (2^150)"
    );
    // f64 eb=2046 (>= 1202) was already saturating — still correct.
    assert_eq!(
        fcvtzs(F64, 64, 2046u64 << 52),
        0x7FFF_FFFF_FFFF_FFFF,
        "eb>=1202 still saturates correctly"
    );

    // A NONZERO mantissa huge value also saturates (was self-correcting; still correct).
    assert_eq!(
        fcvtzs(F32, 32, (254u64 << 23) | 0x40_0000),
        0x7FFF_FFFF,
        "1.5*2^127 -> i32::MAX"
    );
}

// ============================================================================
// TEST 7 — int->float (SCVTF / UCVTF).  Host FPU cross-check via Rust int->float
//   `as` (correctly-rounded RNE), for target f32/f64 and int_w 32/64.
// ============================================================================

fn host_itf(signed_tag: u32, int_w: u32, w: u8, x: u64) -> Option<u64> {
    if int_w != 32 && int_w != 64 {
        return None;
    }
    let mask = if int_w >= 64 {
        u64::MAX
    } else {
        (1u64 << int_w) - 1
    };
    let xm = x & mask;
    // Reconstruct the source integer value at int_w, then cast to the target float.
    Some(match (signed_tag, int_w, w) {
        (0, 32, 32) => ((xm as u32) as f32).to_bits() as u64,
        (0, 32, 64) => ((xm as u32) as f64).to_bits(),
        (0, 64, 32) => (xm as f32).to_bits() as u64,
        (0, 64, 64) => (xm as f64).to_bits(),
        (1, 32, 32) => (((xm as u32) as i32) as f32).to_bits() as u64,
        (1, 32, 64) => (((xm as u32) as i32) as f64).to_bits(),
        (1, 64, 32) => ((xm as i64) as f32).to_bits() as u64,
        (1, 64, 64) => ((xm as i64) as f64).to_bits(),
        _ => return None,
    })
}

fn itf_inputs() -> Vec<(u8, u32, u32, u64)> {
    // (target w, int_w, signed_tag, x)
    let mut v: Vec<(u8, u32, u32, u64)> = Vec::new();
    let mut xs: Vec<u64> = vec![
        0,
        1,
        2,
        3,
        5,
        7,
        15,
        16,
        17,
        100,
        0xFF,
        0x100,
        0x1FF,
        0xFFFF,
        0x1_0000,
        0x7FFF_FFFF,
        0x8000_0000,
        0xFFFF_FFFF,
        0x1_0000_0000,
        0x7FFF_FFFF_FFFF_FFFF,
        0x8000_0000_0000_0000,
        0xFFFF_FFFF_FFFF_FFFF,
        0xFFFF_FF80,
        0x0100_0001,
        0x0100_0002,
        0x0100_0003,
    ];
    xs.extend(rand_bits(64, 400));
    for w in [32u8, 64] {
        for int_w in [8u32, 16, 32, 64] {
            for signed_tag in 0u32..2 {
                for &x in &xs {
                    v.push((w, int_w, signed_tag, x));
                }
            }
        }
    }
    v
}

#[test]
fn trust_fp_itf_quad_oracle() {
    let inputs = itf_inputs();
    let expected = inputs.len();
    let sweep = inputs.clone();

    let rows = run_watchdogged::<ItfOut>("fp_itf", expected, move |tx| {
        let buffer = jit_module(ITF_IR, "fp_itf");
        let f: ItfFn = unsafe { std::mem::transmute(bind(&buffer, "fp_itf_root")) };
        for &(w, int_w, signed_tag, x) in &sweep {
            let (t, m, e, bs) = geom(w);
            let mut out = ItfOut { out: POISON };
            unsafe { f(t, m, e, bs, int_w, signed_tag, x, &mut out) };
            if tx.send(out).is_err() {
                return;
            }
        }
    });

    assert_eq!(rows.len(), expected);
    let mut host_checked = 0usize;
    for (i, &(w, int_w, signed_tag, x)) in inputs.iter().enumerate() {
        let (t, m, e, bs) = geom(w);
        let f = prod_fmt(w);
        let jit = rows[i].out;
        assert_ne!(jit, POISON, "row {i} poisoned");
        let (prod, nat) = if signed_tag == 0 {
            (
                ucvtf(f, int_w, x),
                slice_native::ucvtf(t, m, e, bs, int_w, x),
            )
        } else {
            (
                scvtf(f, int_w, x),
                slice_native::scvtf(t, m, e, bs, int_w, x),
            )
        };
        assert_eq!(
            jit, prod,
            "ITF JIT != PRODUCTION w={w} int_w={int_w} s={signed_tag} x={x:#x}"
        );
        assert_eq!(
            jit, nat,
            "ITF JIT != slice_native w={w} int_w={int_w} s={signed_tag} x={x:#x}"
        );
        if let Some(h) = host_itf(signed_tag, int_w, w, x) {
            assert_eq!(
                jit, h,
                "ITF model != HOST FPU (REAL model bug) w={w} int_w={int_w} s={signed_tag} x={x:#x}: model={jit:#x} host={h:#x}"
            );
            host_checked += 1;
        }
    }
    assert!(host_checked > 500, "host cross-check too sparse");
    // SCVTF 1 -> 1.0_f32 ; SCVTF -1 (0xFFFFFFFF@32) -> -1.0_f32
    let find = |int_w: u32, s: u32, x: u64| {
        inputs
            .iter()
            .position(|&t| t == (32u8, int_w, s, x))
            .map(|ix| rows[ix].out)
    };
    assert_eq!(find(32, 1, 1).unwrap(), 0x3F80_0000);
    assert_eq!(find(32, 1, 0xFFFF_FFFF).unwrap(), 0xBF80_0000);
}

// ============================================================================
// ARMED NEGATIVE CONTROLS — corrupt the RNE round-up (the guard-round-sticky
// decision's `+1` increment) in the module text (`add`->`sub`), JIT the corrupted
// module, prove the FP results DIVERGE from production on the round-up cases (the
// rounding logic is load-bearing in the JIT machine code), then re-JIT the pristine
// module and prove it matches production again (restore / re-pass). A rounding bug
// found here would be a soundness hole in the FP-verification TCB, so its absence
// must be demonstrably load-bearing.
//   * round_word (fadd/fmul/fcvt): bb `%52 = add u128 %14, %51`  (mant_place + 1)
//   * round_nat  (fdiv/fsqrt):     bb `%63 = add u128 %28, %62`  (mant_place + 1)
// ============================================================================

/// Run a binary-op module (fadd/fmul/fdiv shape) over `pairs` at f32, returning the
/// primary u64 output per row. `narrow` selects the argument shape (addsub has no
/// bias arg; mul/div do).
fn run_binary_f32(
    ir: String,
    sym: &'static str,
    has_bias: bool,
    pairs: Vec<(u64, u64)>,
) -> Vec<u64> {
    let n = pairs.len();
    run_watchdogged::<u64>(sym, n, move |tx| {
        let buffer = jit_module(&ir, sym);
        let p = bind(&buffer, sym);
        for &(a, bb) in &pairs {
            let mut out: u64 = POISON;
            if has_bias {
                let f: unsafe extern "C" fn(u32, u32, u32, u32, u64, u64, *mut u64) =
                    unsafe { std::mem::transmute(p) };
                unsafe { f(32, 23, 8, 127, a, bb, &mut out) };
            } else {
                let f: unsafe extern "C" fn(u32, u32, u32, u64, u64, *mut u64) =
                    unsafe { std::mem::transmute(p) };
                unsafe { f(32, 23, 8, a, bb, &mut out) };
            }
            if tx.send(out).is_err() {
                return;
            }
        }
    })
}

fn f32_reps_pairs() -> Vec<(u64, u64)> {
    let rs = reps(32, 23, 8);
    let mut v = Vec::new();
    for &a in &rs {
        for &bb in &rs {
            v.push((a, bb));
        }
    }
    // add seeded-random f32 pairs (dense rounding coverage)
    let ra = rand_bits(32, 60);
    let rb = rand_bits(32, 60);
    for i in 0..ra.len() {
        v.push((ra[i], rb[i]));
    }
    v
}

fn armed_binary(
    ir: &str,
    sym: &'static str,
    has_bias: bool,
    anchor: &str,
    prod: impl Fn(u64, u64) -> u64,
) {
    assert_eq!(
        ir.matches(anchor).count(),
        1,
        "round-up anchor `{anchor}` must be unique"
    );
    let corrupted = ir.replace(anchor, &anchor.replace("add u128", "sub u128"));
    assert_ne!(corrupted, ir, "corruption must change the module text");
    let pairs = f32_reps_pairs();
    let corrupt_rows = run_binary_f32(corrupted, sym, has_bias, pairs.clone());
    let pristine_rows = run_binary_f32(ir.to_string(), sym, has_bias, pairs.clone());
    let mut diverged = 0usize;
    for (i, &(a, bb)) in pairs.iter().enumerate() {
        assert_ne!(pristine_rows[i], POISON, "pristine row {i} poisoned");
        let p = prod(a, bb);
        assert_eq!(
            pristine_rows[i], p,
            "RESTORED {sym} != production a={a:#x} b={bb:#x}"
        );
        if corrupt_rows[i] != p {
            diverged += 1;
        }
    }
    assert!(
        diverged > 0,
        "corrupting the RNE round-up (add->sub) changed NO {sym} result — rounding not load-bearing?!"
    );
    eprintln!(
        "{sym} armed control: round-up corruption diverged on {diverged}/{} cases; restored module == production",
        pairs.len()
    );
}

#[test]
fn trust_fp_addsub_armed_round_word() {
    armed_binary(
        ADDSUB_IR,
        "fp_addsub_root",
        false,
        "    %52 = add u128 %14, %51",
        |a, b| fadd(F32, a, b),
    );
}

#[test]
fn trust_fp_mul_armed_round_word() {
    armed_binary(
        MUL_IR,
        "fp_mul_root",
        true,
        "    %52 = add u128 %14, %51",
        |a, b| fmul(F32, a, b),
    );
}

#[test]
fn trust_fp_div_armed_round_nat() {
    armed_binary(
        DIV_IR,
        "fp_div_root",
        true,
        "    %63 = add u128 %28, %62",
        |a, b| fdiv(F32, a, b),
    );
}

#[test]
fn trust_fp_sqrt_armed_round_nat() {
    // fsqrt is unary: corrupt round_nat's round-up, sweep f32 values, prove divergence.
    const ANCHOR: &str = "    %63 = add u128 %28, %62";
    assert_eq!(
        SQRT_IR.matches(ANCHOR).count(),
        1,
        "round_nat round-up anchor must be unique"
    );
    let corrupted = SQRT_IR.replace(ANCHOR, "    %63 = sub u128 %28, %62");
    assert_ne!(corrupted, SQRT_IR);
    let mut xs = reps(32, 23, 8);
    xs.extend(rand_bits(32, 200));
    let run = |ir: String, xs: Vec<u64>| -> Vec<u64> {
        let n = xs.len();
        run_watchdogged::<u64>("fp_sqrt_root", n, move |tx| {
            let buffer = jit_module(&ir, "fp_sqrt_root");
            let f: SqrtFn = unsafe { std::mem::transmute(bind(&buffer, "fp_sqrt_root")) };
            for &x in &xs {
                let mut out = SqrtOut { fsqrt: POISON };
                unsafe { f(32, 23, 8, 127, x, &mut out) };
                if tx.send(out.fsqrt).is_err() {
                    return;
                }
            }
        })
    };
    let corrupt_rows = run(corrupted, xs.clone());
    let pristine_rows = run(SQRT_IR.to_string(), xs.clone());
    let mut diverged = 0usize;
    for (i, &x) in xs.iter().enumerate() {
        let p = fsqrt(F32, x);
        assert_eq!(pristine_rows[i], p, "RESTORED fsqrt != production x={x:#x}");
        if corrupt_rows[i] != p {
            diverged += 1;
        }
    }
    assert!(
        diverged > 0,
        "corrupting fsqrt round-up changed no result — rounding not load-bearing?!"
    );
    eprintln!(
        "fsqrt armed control: round-up corruption diverged on {diverged}/{} cases; restored == production",
        xs.len()
    );
}
