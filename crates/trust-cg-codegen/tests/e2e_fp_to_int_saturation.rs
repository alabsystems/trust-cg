//! TRUST-SELF ROUND 34 (thread R34): AUDIT THE BACKEND f->int CONVERSION
//! SATURATION LOWERING against the Rust `as` (target-width saturating) oracle.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! CONTEXT
//! ═══════════════════════════════════════════════════════════════════════════════
//! Owner #9 (round 26) found the fp_bitmodel MODEL (trust-cg-verify's integer-only
//! IEEE model — the CHECKER of the FP lowering) UNDER-SATURATES high-magnitude
//! power-of-two f->int (returns 0 instead of the int extreme). This round audits a
//! DIFFERENT code path: the ACTUAL backend f->int conversion LOWERING (isel.rs
//! select_fcvt_to_int/select_fcvt_to_uint -> FCVTZS/FCVTZU on aarch64), at the
//! saturation / NaN / overflow boundaries. Does the BACKEND get it right where the
//! MODEL got it wrong?
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! THE ORACLE — Rust `f as iN` / `f as uN` (INDEPENDENT, computed at test time)
//! ═══════════════════════════════════════════════════════════════════════════════
//! Rust's `as` on floats is the TARGET-WIDTH SATURATING conversion (stabilized 1.45,
//! LLVM fptosi.sat/fptoui.sat): huge -> iN::MAX/uN::MAX; very-negative -> iN::MIN
//! (signed) / 0 (unsigned); NaN -> 0; negative -> 0 for unsigned; in-range ->
//! truncate toward zero. This is a clean independent oracle: native Rust, evaluated
//! here at test time. It is NOT the interpreter (interpreter.rs eval_cast does
//! `f as i128` — a 128-bit-width saturation, wrong for target width; confirmed by
//! reading it — so interpret() is deliberately NOT used as the oracle here).
//!
//! trust-ir CastOp semantics (inst.rs docs, rev 5fbd88d):
//!   * FPToSISat / FPToUISat  == Rust `f as iN` / `f as uN` (LLVM fptosi.sat).
//!   * FPToSI    / FPToUI     == raw LLVM fptosi/fptoui: out-of-range / NaN is UB.
//!     So the SATURATING op the backend "must implement" for `as` is the *Sat variant.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! WHAT THE BACKEND ACTUALLY DOES (read from source; verified empirically below)
//! ═══════════════════════════════════════════════════════════════════════════════
//!  (1) FPToSISat / FPToUISat -> i8/i16/i32/u8/u16/u32 first convert into a
//!      64-bit carrier, explicitly clamp at the DESTINATION width, and only then
//!      truncate. The differential below checks every narrow signed/unsigned width
//!      against native Rust `as`, exhaustively over all f16-representable inputs and
//!      over stratified plus pseudorandom f32/f64 bit patterns.
//!  (2) FPToSI -> FcvtToInt -> select_fcvt_to_int -> FcvtzsRR;  FPToUI -> FcvtzuRR.
//!      The MACHINE ENCODER hardcodes `sf_64 = true` for FcvtzsRR/FcvtzuRR
//!      (encode.rs:1989 / :2017) -> ALWAYS the 64-bit (Xd) form, regardless of the
//!      IR destination width; there is NO destination-width clamp (adapter.rs
//!      comment at :6441 acknowledges this). Hardware FCVTZS/FCVTZU saturate at the
//!      REGISTER width and map NaN -> 0.
//!  Consequence, PROVEN below against the Rust `as` oracle bit-exact on real aarch64
//!  hardware:
//!    * FPToSI->i64 and FPToUI->u64 (register width == destination width): the actual
//!      machine result EQUALS Rust `f as i64` / `f as u64` at EVERY boundary (huge /
//!      +-inf / NaN / exact-max-edge / in-range / truncation-direction / sign). The
//!      backend does NOT under-saturate (contrast owner #9's MODEL bug). CLEAN BILL.
//!    * FPToSI/FPToUI -> {i8,i16,i32}/{u8,u16,u32}: because FCVTZS/FCVTZU is always
//!      64-bit and the result is merely truncated to N bits on use, out-of-narrow-
//!      range inputs give sext_N(trunc_N(f as i64)) -- which DIVERGES from Rust
//!      `f as iN`. This is permitted (FPToSI's contract says out-of-range is UB) and
//!      matches the register-width model EXACTLY; it confirms FPToSI must NOT be used
//!      to implement a narrow `as` -- the correct op is FPToSISat/FPToUISat, whose
//!      explicit clamp is independently checked here. The raw-cast behavior is
//!      characterized + witnessed in `narrow_width_register_model`.
//!
//! No emit-from-Rust: the emit-closure frontend has NO float support (R31 Finding A —
//! `scalar_tir_ty` returns None for `ty::Float`). Everything here is hand-built
//! trust-ir driven through the trust-cg JIT; the oracle is native Rust `as`.
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine is
//! not thread-safe at suite scale (jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, CastOp, FuncId, ValueId};

// ── the boundary sweeps (crafted to HIT every saturation / NaN / truncation edge) ──

/// f64 inputs. Named boundary constants are the exact floats at each width edge, plus
/// the huge-magnitude power-of-two class that owner #9's MODEL got wrong.
fn f64_inputs() -> Vec<f64> {
    let mut v = vec![
        // near-zero / truncation-direction / sign
        0.0f64,
        -0.0,
        0.5,
        -0.5,
        1.0,
        -1.0,
        2.9,
        -2.9,
        2.5,
        -2.5,
        127.9,
        -127.9,
        // i8 / u8 edges
        127.0,
        128.0,
        -128.0,
        -129.0,
        200.0,
        -200.0,
        255.0,
        256.0,
        -1.0,
        // i16 / u16 edges
        32767.0,
        32768.0,
        -32768.0,
        -32769.0,
        65535.0,
        65536.0,
        // i32 / u32 edges (all exactly representable in f64)
        2147483647.0,
        2147483648.0,
        -2147483648.0,
        -2147483649.0,
        4294967295.0,
        4294967296.0,
        // i64 / u64 edges
        9223372036854774784.0, // largest f64 strictly < 2^63  (== i64::MAX rounded down)
        9223372036854775808.0, // 2^63  (> i64::MAX -> signed saturates; < u64::MAX)
        18446744073709549568.0, // largest f64 strictly < 2^64
        // huge magnitudes incl. owner-#9's power-of-two class
        1e18,
        1e19,
        -1e18,
        -1e19,
        1e30,
        -1e30,
        1e300,
        -1e300,
        2.0f64.powi(63),
        2.0f64.powi(64),
        2.0f64.powi(127), // owner #9's exact failing class (power of two, huge)
        -(2.0f64.powi(127)),
        f64::MAX,
        f64::MIN,
        f64::MIN_POSITIVE,
        f64::INFINITY,
        f64::NEG_INFINITY,
    ];
    // NaNs (qNaN, -qNaN, sNaN, another payload) — all must map to 0 at every width.
    v.push(f64::NAN);
    v.push(-f64::NAN);
    v.push(f64::from_bits(0x7ff0_0000_0000_0001)); // sNaN
    v.push(f64::from_bits(0xfff8_0000_0000_0002)); // another NaN payload
    v
}

/// f32 inputs — analogous edges within f32's dynamic range.
fn f32_inputs() -> Vec<f32> {
    vec![
        0.0f32,
        -0.0,
        0.5,
        -0.5,
        1.0,
        -1.0,
        2.9,
        -2.9,
        2.5,
        -2.5,
        127.0,
        128.0,
        -128.0,
        -129.0,
        200.0,
        -200.0,
        255.0,
        256.0,
        32767.0,
        32768.0,
        -32768.0,
        65535.0,
        65536.0,
        2147483648.0,           // 2^31
        -2147483648.0,          // -2^31
        4294967296.0,           // 2^32
        9223372036854775808.0,  // 2^63
        18446744073709551616.0, // 2^64
        2.0f32.powi(63),
        2.0f32.powi(64),
        2.0f32.powi(100),
        1e18,
        -1e18,
        1e30,
        -1e30,
        f32::MAX,
        f32::MIN,
        f32::MIN_POSITIVE,
        f32::INFINITY,
        f32::NEG_INFINITY,
        f32::NAN,
        -f32::NAN,
        f32::from_bits(0x7f80_0001), // sNaN
    ]
}

// ── target-width saturating oracle (native Rust `as`) — returns the 64-bit bit
//    pattern the JIT function is expected to leave in x0. Signed widths sign-extend
//    the N-bit result to i64; unsigned widths zero-extend the N-bit result to u64. ──

fn oracle_signed_f64(f: f64, n: u32) -> i64 {
    match n {
        8 => (f as i8) as i64,
        16 => (f as i16) as i64,
        32 => (f as i32) as i64,
        64 => f as i64,
        _ => unreachable!(),
    }
}
fn oracle_unsigned_f64(f: f64, n: u32) -> u64 {
    match n {
        8 => (f as u8) as u64,
        16 => (f as u16) as u64,
        32 => (f as u32) as u64,
        64 => f as u64,
        _ => unreachable!(),
    }
}
fn oracle_signed_f32(f: f32, n: u32) -> i64 {
    match n {
        8 => (f as i8) as i64,
        16 => (f as i16) as i64,
        32 => (f as i32) as i64,
        64 => f as i64,
        _ => unreachable!(),
    }
}
fn oracle_unsigned_f32(f: f32, n: u32) -> u64 {
    match n {
        8 => (f as u8) as u64,
        16 => (f as u16) as u64,
        32 => (f as u32) as u64,
        64 => f as u64,
        _ => unreachable!(),
    }
}

// ── the "register-width model": what the always-64-bit FCVTZS/FCVTZU + N-bit
//    truncate on use is PREDICTED to produce. For width 64 this coincides with the
//    saturating oracle; for narrow widths it is the truncated i64/u64 saturation. ──
fn regwidth_signed_f64(f: f64, n: u32) -> i64 {
    let wide = f as i64; // hardware FCVTZS Xd == Rust `f as i64` (both saturate to i64)
    match n {
        8 => (wide as i8) as i64,
        16 => (wide as i16) as i64,
        32 => (wide as i32) as i64,
        64 => wide,
        _ => unreachable!(),
    }
}
fn regwidth_unsigned_f64(f: f64, n: u32) -> u64 {
    let wide = f as u64; // hardware FCVTZU Xd == Rust `f as u64`
    match n {
        8 => (wide as u8) as u64,
        16 => (wide as u16) as u64,
        32 => (wide as u32) as u64,
        64 => wide,
        _ => unreachable!(),
    }
}

// ── Ty helpers ──────────────────────────────────────────────────────────────────
fn signed_ty(n: u32) -> Ty {
    match n {
        8 => Ty::I8,
        16 => Ty::I16,
        32 => Ty::I32,
        64 => Ty::I64,
        _ => unreachable!(),
    }
}
fn unsigned_ty(n: u32) -> Ty {
    match n {
        8 => Ty::U8,
        16 => Ty::U16,
        32 => Ty::U32,
        64 => Ty::U64,
        _ => unreachable!(),
    }
}

// ── module builder: fn(src) -> {I64|U64} { widen( FPTo{S,U}I(src -> dstN) ) } ──────
//
// signed:   ret I64;  v1 = FPToSI(src->iN);  ret (n==64 ? v1 : SExt iN->I64)
// unsigned: ret U64;  v1 = FPToUI(src->uN);  ret (n==64 ? v1 : ZExt uN->U64)
fn build_conv_fn(
    func_id: u32,
    name: &str,
    module: &mut TrustIrModule,
    src_ty: Ty,
    signed: bool,
    n: u32,
    cast_op: CastOp,
) {
    let dst_small = if signed { signed_ty(n) } else { unsigned_ty(n) };
    let ret_ty = if signed { Ty::I64 } else { Ty::U64 };
    let ft = module.add_func_type(FuncTy {
        params: vec![src_ty.clone()],
        returns: vec![ret_ty.clone()],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));

    let mut body = vec![
        // the conversion under test
        InstrNode::new(Inst::Cast {
            op: cast_op,
            src_ty: src_ty.clone(),
            dst_ty: dst_small.clone(),
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(1)),
    ];
    let ret_val = if n == 64 {
        ValueId::new(1)
    } else {
        body.push(
            InstrNode::new(Inst::Cast {
                op: if signed { CastOp::SExt } else { CastOp::ZExt },
                src_ty: dst_small.clone(),
                dst_ty: ret_ty.clone(),
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
        );
        ValueId::new(2)
    };
    body.push(InstrNode::new(Inst::Return {
        values: vec![ret_val],
    }));

    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), src_ty)],
        body,
    }];
    module.add_function(f);
}

// ── JIT harness ─────────────────────────────────────────────────────────────────
type ConvF64 = unsafe extern "C" fn(f64) -> i64;
type ConvF32 = unsafe extern "C" fn(f32) -> i64;

fn jit_buffer(module: &TrustIrModule) -> trust_cg_codegen::jit::ExecutableBuffer {
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(module, &HashMap::new())
        .expect("hand-built FP->int module must JIT-compile (backend supports FCVTZS/FCVTZU)")
        .buffer
}

fn bind(buffer: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buffer
        .get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

// One module holding all four full-width conversions, keyed by symbol.
fn build_fullwidth_module() -> TrustIrModule {
    let mut m = TrustIrModule::new("fp2int_fullwidth".to_string());
    build_conv_fn(0, "s64_f64", &mut m, Ty::F64, true, 64, CastOp::FPToSI);
    build_conv_fn(1, "u64_f64", &mut m, Ty::F64, false, 64, CastOp::FPToUI);
    build_conv_fn(2, "s64_f32", &mut m, Ty::F32, true, 64, CastOp::FPToSI);
    build_conv_fn(3, "u64_f32", &mut m, Ty::F32, false, 64, CastOp::FPToUI);
    m
}

// ============================================================================
// TEST 1 — FULL-WIDTH CLEAN BILL. FPToSI->i64 / FPToUI->u64 for f64 AND f32,
//   over the whole boundary sweep, must equal Rust `f as i64` / `f as u64`
//   BIT-EXACT. This is the positive result: the backend's full-width f->int
//   path is target-width-saturating and does NOT under-saturate (owner #9 was
//   the MODEL, not this path). Also confirms the huge-value saturation cells
//   are genuinely exercised (>0) and every one is correct.
// ============================================================================
#[test]
fn fullwidth_clean_bill_native_eq_jit() {
    let m = build_fullwidth_module();
    let buf = jit_buffer(&m);

    let s64_f64: ConvF64 = unsafe { std::mem::transmute(bind(&buf, "s64_f64")) };
    let u64_f64: ConvF64 = unsafe { std::mem::transmute(bind(&buf, "u64_f64")) };
    let s64_f32: ConvF32 = unsafe { std::mem::transmute(bind(&buf, "s64_f32")) };
    let u64_f32: ConvF32 = unsafe { std::mem::transmute(bind(&buf, "u64_f32")) };

    let mut huge_sat_cells = 0usize;
    let mut nan_cells = 0usize;
    let mut checked = 0usize;

    for &f in &f64_inputs() {
        // signed i64
        let want = oracle_signed_f64(f, 64);
        let got = unsafe { s64_f64(f) };
        assert_eq!(
            got,
            want,
            "FPToSI f64->i64 MISCOMPILE at f={f:?} ({:#018x}): jit={got} want(f as i64)={want}",
            f.to_bits()
        );
        // unsigned u64
        let want_u = oracle_unsigned_f64(f, 64);
        let got_u = unsafe { u64_f64(f) } as u64;
        assert_eq!(
            got_u,
            want_u,
            "FPToUI f64->u64 MISCOMPILE at f={f:?} ({:#018x}): jit={got_u} want(f as u64)={want_u}",
            f.to_bits()
        );
        checked += 2;
        if f.is_nan() {
            assert_eq!(want, 0, "sanity: NaN oracle must be 0 (signed)");
            assert_eq!(want_u, 0, "sanity: NaN oracle must be 0 (unsigned)");
            nan_cells += 2;
        }
        // a "huge saturation" cell: |f| beyond i64/u64 range or +-inf -> extreme
        if (f.is_infinite() || (f.is_finite() && f.abs() >= 9.3e18))
            && (want == i64::MAX || want == i64::MIN)
        {
            huge_sat_cells += 1;
        }
    }
    for &f in &f32_inputs() {
        let want = oracle_signed_f32(f, 64);
        let got = unsafe { s64_f32(f) };
        assert_eq!(
            got,
            want,
            "FPToSI f32->i64 MISCOMPILE at f={f:?} ({:#010x}): jit={got} want(f as i64)={want}",
            f.to_bits()
        );
        let want_u = oracle_unsigned_f32(f, 64);
        let got_u = unsafe { u64_f32(f) } as u64;
        assert_eq!(
            got_u,
            want_u,
            "FPToUI f32->u64 MISCOMPILE at f={f:?} ({:#010x}): jit={got_u} want(f as u64)={want_u}",
            f.to_bits()
        );
        checked += 2;
        if f.is_nan() {
            nan_cells += 2;
        }
        if (f.is_infinite() || (f.is_finite() && f.abs() >= 9.3e18))
            && (want == i64::MAX || want == i64::MIN)
        {
            huge_sat_cells += 1;
        }
    }

    assert!(
        huge_sat_cells >= 8,
        "huge-value saturation cells under-exercised ({huge_sat_cells}) — the owner-#9 \
         class (2^63/2^64/2^127/+-inf/f64::MAX) must be swept and correct"
    );
    assert!(nan_cells >= 8, "NaN->0 cells under-exercised ({nan_cells})");
    eprintln!(
        "FULL-WIDTH CLEAN BILL: FPToSI->i64 / FPToUI->u64 (f64+f32) == Rust `as` bit-exact on \
         {checked} cells; {huge_sat_cells} huge-saturation cells (2^63/2^64/2^127/+-inf/MAX all \
         -> i64/u64 extreme, NOT 0) and {nan_cells} NaN->0 cells all correct. The backend \
         full-width f->int path does not under-saturate."
    );
}

// ============================================================================
// TEST 2 — NARROW WIDTH register-width characterization. FPToSI->{i8,i16,i32}
//   and FPToUI->{u8,u16,u32}. The backend emits an always-64-bit FCVTZS/FCVTZU
//   with no destination-width clamp, so the result EXACTLY matches the
//   register-width model sext_N(trunc_N(f as i64)) at every input, and DIVERGES
//   from the Rust `f as iN` target-width oracle for out-of-narrow-range inputs.
//   This proves: (a) the exact mechanism (JIT == regwidth model, not arbitrary
//   garbage); (b) narrow FPToSI/FPToUI does NOT implement `as` (the saturating
//   FPToSISat/FPToUISat operations do, and are checked in Test 3). Per trust-ir,
//   FPToSI out-of-range is UB, so this raw-cast behavior is not an unsoundness.
// ============================================================================
#[test]
fn narrow_width_register_model() {
    let mut m = TrustIrModule::new("fp2int_narrow".to_string());
    // signed narrow (f64 source)
    build_conv_fn(0, "s8", &mut m, Ty::F64, true, 8, CastOp::FPToSI);
    build_conv_fn(1, "s16", &mut m, Ty::F64, true, 16, CastOp::FPToSI);
    build_conv_fn(2, "s32", &mut m, Ty::F64, true, 32, CastOp::FPToSI);
    // unsigned narrow (f64 source)
    build_conv_fn(3, "u8", &mut m, Ty::F64, false, 8, CastOp::FPToUI);
    build_conv_fn(4, "u16", &mut m, Ty::F64, false, 16, CastOp::FPToUI);
    build_conv_fn(5, "u32", &mut m, Ty::F64, false, 32, CastOp::FPToUI);
    let buf = jit_buffer(&m);

    let inputs = f64_inputs();
    let mut regmodel_matches = 0usize;
    let mut as_matches = 0usize;
    let mut as_diverges = 0usize;
    let mut huge_narrow_diverge = 0usize;

    for &(sym, signed, n) in &[
        ("s8", true, 8u32),
        ("s16", true, 16),
        ("s32", true, 32),
        ("u8", false, 8),
        ("u16", false, 16),
        ("u32", false, 32),
    ] {
        let f: ConvF64 = unsafe { std::mem::transmute(bind(&buf, sym)) };
        for &x in &inputs {
            let got = unsafe { f(x) };
            let (regmodel, as_oracle) = if signed {
                (regwidth_signed_f64(x, n), oracle_signed_f64(x, n))
            } else {
                (
                    regwidth_unsigned_f64(x, n) as i64,
                    oracle_unsigned_f64(x, n) as i64,
                )
            };
            // (a) the JIT EXACTLY equals the register-width model — the precise
            //     mechanistic characterization (fail-loud if the mechanism differs).
            assert_eq!(
                got,
                regmodel,
                "narrow {sym}: JIT != register-width model at f={x:?} ({:#018x}): jit={got} \
                 model=sext/zext_N(trunc_N(f as {}64))={regmodel} — the FCVTZS-always-64+trunc \
                 characterization is WRONG (new behavior)",
                x.to_bits(),
                if signed { "i" } else { "u" }
            );
            regmodel_matches += 1;
            // (b) relation to the Rust `as` target-width oracle.
            if got == as_oracle {
                as_matches += 1;
            } else {
                as_diverges += 1;
                if x.is_infinite() || (x.is_finite() && x.abs() >= 1e18) {
                    huge_narrow_diverge += 1;
                }
            }
        }
    }

    // The mechanism is exact everywhere.
    assert_eq!(regmodel_matches, 6 * inputs.len());
    // In-range inputs agree with `as`; out-of-range diverge. Both classes present.
    assert!(
        as_diverges > 0,
        "narrow path never diverged from Rust `as` — expected out-of-range divergence \
         (register-width saturation without a destination clamp)"
    );
    assert!(
        as_matches > 0,
        "narrow path never matched Rust `as` — in-range inputs must agree"
    );
    assert!(
        huge_narrow_diverge > 0,
        "no huge-magnitude narrow divergence exercised"
    );

    // PINNED WITNESSES — exact divergences from Rust `as` (register-width, not clamped).
    // 1000.0 as i8: Rust = 127 (saturate);   regmodel = (1000 as i8) = -24.
    let s8: ConvF64 = unsafe { std::mem::transmute(bind(&buf, "s8")) };
    assert_eq!(oracle_signed_f64(1000.0, 8), 127);
    assert_eq!(unsafe { s8(1000.0) }, (1000i64 as i8) as i64);
    assert_ne!(unsafe { s8(1000.0) }, 127, "witness stale: s8(1000.0)");
    // -1000.0 as i8: Rust = -128 (saturate); regmodel = (-1000 as i8) = 24.
    assert_eq!(oracle_signed_f64(-1000.0, 8), -128);
    assert_eq!(unsafe { s8(-1000.0) }, ((-1000i64) as i8) as i64);
    // 1e18 as i32: Rust = i32::MAX; regmodel = ((1e18 as i64) as i32).
    let s32: ConvF64 = unsafe { std::mem::transmute(bind(&buf, "s32")) };
    assert_eq!(oracle_signed_f64(1e18, 32), i32::MAX as i64);
    assert_eq!(unsafe { s32(1e18) }, ((1e18f64 as i64) as i32) as i64);
    assert_ne!(
        unsafe { s32(1e18) },
        i32::MAX as i64,
        "witness stale: s32(1e18)"
    );
    // 300.0 as u8: Rust = 255 (saturate);   regmodel = (300 as u8) = 44.
    let u8f: ConvF64 = unsafe { std::mem::transmute(bind(&buf, "u8")) };
    assert_eq!(oracle_unsigned_f64(300.0, 8), 255);
    assert_eq!(unsafe { u8f(300.0) } as u64, (300u64 as u8) as u64);
    assert_ne!(
        unsafe { u8f(300.0) } as u64,
        255,
        "witness stale: u8(300.0)"
    );

    // In-range sanity: these MUST agree with `as` on both models.
    assert_eq!(unsafe { s8(100.0) }, 100, "s8(100.0) in-range");
    assert_eq!(unsafe { s8(-100.0) }, -100, "s8(-100.0) in-range");
    assert_eq!(unsafe { s8(2.9) }, 2, "s8(2.9) trunc toward zero");
    assert_eq!(unsafe { s8(-2.9) }, -2, "s8(-2.9) trunc toward zero");
    assert_eq!(unsafe { u8f(200.0) } as u64, 200, "u8(200.0) in-range");
    // NaN -> 0 at narrow width too (0 truncates to 0 -> agrees with `as`).
    assert_eq!(unsafe { s8(f64::NAN) }, 0, "s8(NaN)=0");
    assert_eq!(unsafe { u8f(f64::NAN) } as u64, 0, "u8(NaN)=0");

    eprintln!(
        "NARROW WIDTH: JIT == register-width model on all {regmodel_matches} cells (exact \
         mechanism: always-64-bit FCVTZS/FCVTZU + N-bit truncate). vs Rust `as`: {as_matches} \
         agree (in-range), {as_diverges} diverge (out-of-narrow-range, {huge_narrow_diverge} of \
         them huge-magnitude). Narrow FPToSI/FPToUI does NOT implement `as`; the saturating \
         operations are independently checked against Rust `as` in Test 3. Per trust-ir this \
         out-of-range raw-cast case is UB (not unsound)."
    );
}

// ============================================================================
// TEST 3 — NARROW SATURATING CLEAN BILL. Every signed and unsigned narrow
//   destination is checked directly against native Rust `as` semantics:
//     * all 65,536 f16 bit patterns, widened exactly to f32;
//     * every f32/f64 exponent class with adversarial mantissas and both signs;
//     * deterministic full-bit pseudorandom samples; and
//     * the hand-picked boundary/NaN/infinity corpus above.
//   This makes the destination-width clamp, signedness, NaN handling and source
//   precision load-bearing. The old fail-closed pin became stale when this
//   width-audited lowering landed.
// ============================================================================
fn f16_bits_to_f32(bits: u16) -> f32 {
    let sign = u32::from(bits & 0x8000) << 16;
    let exponent = u32::from((bits >> 10) & 0x1f);
    let fraction = u32::from(bits & 0x03ff);
    let f32_bits = match exponent {
        0 if fraction == 0 => sign,
        0 => {
            // Normalize the ten-bit subnormal significand. `shift` puts its
            // leading one in half's implicit-one position (bit 10).
            let shift = fraction.leading_zeros() - 21;
            let normalized_fraction = (fraction << shift) & 0x03ff;
            let unbiased_exponent = -14i32 - shift as i32;
            sign | (((unbiased_exponent + 127) as u32) << 23) | (normalized_fraction << 13)
        }
        0x1f => sign | 0x7f80_0000 | (fraction << 13),
        _ => sign | ((exponent + 112) << 23) | (fraction << 13),
    };
    f32::from_bits(f32_bits)
}

fn narrow_sat_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("fp2int_narrow_saturating".to_string());
    let mut id = 0u32;
    for (suffix, src_ty) in [("f64", Ty::F64), ("f32", Ty::F32)] {
        for n in [8u32, 16, 32] {
            build_conv_fn(
                id,
                &format!("ssat{n}_{suffix}"),
                &mut module,
                src_ty.clone(),
                true,
                n,
                CastOp::FPToSISat,
            );
            id += 1;
            build_conv_fn(
                id,
                &format!("usat{n}_{suffix}"),
                &mut module,
                src_ty.clone(),
                false,
                n,
                CastOp::FPToUISat,
            );
            id += 1;
        }
    }
    module
}

fn stratified_f32_inputs() -> Vec<f32> {
    let mut inputs = f32_inputs();

    // Exhaust every value representable by IEEE binary16. The conversion is
    // an exact bit-level widening above, independent of the backend under test.
    inputs.extend((0u32..=u32::from(u16::MAX)).map(|bits| f16_bits_to_f32(bits as u16)));

    // Hit every binary32 exponent under both signs. Mantissas include exact
    // powers, values adjacent to exponent boundaries, alternating patterns,
    // and the maximum payload (including varied NaNs at exponent 255).
    const MANTISSAS: [u32; 8] = [
        0,
        1,
        0x0000_0002,
        0x001f_ffff,
        0x0020_0000,
        0x0040_0001,
        0x0055_5555,
        0x007f_ffff,
    ];
    for sign in [0u32, 0x8000_0000] {
        for exponent in 0u32..=0xff {
            for mantissa in MANTISSAS {
                inputs.push(f32::from_bits(sign | (exponent << 23) | mantissa));
            }
        }
    }

    // A fixed-seed full-bit sweep catches interactions not aligned with the
    // stratification while remaining exactly reproducible.
    let mut state = 0x6d2b_79f5u32;
    for _ in 0..32_768 {
        state ^= state << 13;
        state ^= state >> 17;
        state ^= state << 5;
        inputs.push(f32::from_bits(state));
    }
    inputs
}

fn stratified_f64_inputs() -> Vec<f64> {
    let mut inputs = f64_inputs();
    const MANTISSAS: [u64; 8] = [
        0,
        1,
        2,
        0x0003_ffff_ffff_ffff,
        0x0004_0000_0000_0000,
        0x0008_0000_0000_0001,
        0x000a_aaaa_aaaa_aaaa,
        0x000f_ffff_ffff_ffff,
    ];
    for sign in [0u64, 0x8000_0000_0000_0000] {
        for exponent in 0u64..=0x7ff {
            for mantissa in MANTISSAS {
                inputs.push(f64::from_bits(sign | (exponent << 52) | mantissa));
            }
        }
    }

    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for _ in 0..32_768 {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        inputs.push(f64::from_bits(state));
    }
    inputs
}

#[test]
fn narrow_saturating_clean_bill_rust_as_differential() {
    let module = narrow_sat_module();
    let buffer = jit_buffer(&module);

    let signed_f64: [(u32, ConvF64); 3] = [
        (8, unsafe {
            std::mem::transmute::<*const u8, ConvF64>(bind(&buffer, "ssat8_f64"))
        }),
        (16, unsafe {
            std::mem::transmute::<*const u8, ConvF64>(bind(&buffer, "ssat16_f64"))
        }),
        (32, unsafe {
            std::mem::transmute::<*const u8, ConvF64>(bind(&buffer, "ssat32_f64"))
        }),
    ];
    let unsigned_f64: [(u32, ConvF64); 3] = [
        (8, unsafe {
            std::mem::transmute::<*const u8, ConvF64>(bind(&buffer, "usat8_f64"))
        }),
        (16, unsafe {
            std::mem::transmute::<*const u8, ConvF64>(bind(&buffer, "usat16_f64"))
        }),
        (32, unsafe {
            std::mem::transmute::<*const u8, ConvF64>(bind(&buffer, "usat32_f64"))
        }),
    ];
    let signed_f32: [(u32, ConvF32); 3] = [
        (8, unsafe {
            std::mem::transmute::<*const u8, ConvF32>(bind(&buffer, "ssat8_f32"))
        }),
        (16, unsafe {
            std::mem::transmute::<*const u8, ConvF32>(bind(&buffer, "ssat16_f32"))
        }),
        (32, unsafe {
            std::mem::transmute::<*const u8, ConvF32>(bind(&buffer, "ssat32_f32"))
        }),
    ];
    let unsigned_f32: [(u32, ConvF32); 3] = [
        (8, unsafe {
            std::mem::transmute::<*const u8, ConvF32>(bind(&buffer, "usat8_f32"))
        }),
        (16, unsafe {
            std::mem::transmute::<*const u8, ConvF32>(bind(&buffer, "usat16_f32"))
        }),
        (32, unsafe {
            std::mem::transmute::<*const u8, ConvF32>(bind(&buffer, "usat32_f32"))
        }),
    ];

    let f32_cases = stratified_f32_inputs();
    let f64_cases = stratified_f64_inputs();
    let mut checked = 0usize;

    for x in f32_cases.iter().copied() {
        for &(n, function) in &signed_f32 {
            let got = unsafe { function(x) };
            let want = oracle_signed_f32(x, n);
            assert_eq!(
                got,
                want,
                "FPToSISat f32->i{n} mismatch at {x:?} (bits {:#010x}): got={got}, \
                 Rust `as`={want}",
                x.to_bits(),
            );
            checked += 1;
        }
        for &(n, function) in &unsigned_f32 {
            let got = unsafe { function(x) } as u64;
            let want = oracle_unsigned_f32(x, n);
            assert_eq!(
                got,
                want,
                "FPToUISat f32->u{n} mismatch at {x:?} (bits {:#010x}): got={got}, \
                 Rust `as`={want}",
                x.to_bits(),
            );
            checked += 1;
        }
    }

    for x in f64_cases.iter().copied() {
        for &(n, function) in &signed_f64 {
            let got = unsafe { function(x) };
            let want = oracle_signed_f64(x, n);
            assert_eq!(
                got,
                want,
                "FPToSISat f64->i{n} mismatch at {x:?} (bits {:#018x}): got={got}, \
                 Rust `as`={want}",
                x.to_bits(),
            );
            checked += 1;
        }
        for &(n, function) in &unsigned_f64 {
            let got = unsafe { function(x) } as u64;
            let want = oracle_unsigned_f64(x, n);
            assert_eq!(
                got,
                want,
                "FPToUISat f64->u{n} mismatch at {x:?} (bits {:#018x}): got={got}, \
                 Rust `as`={want}",
                x.to_bits(),
            );
            checked += 1;
        }
    }

    assert_eq!(
        checked,
        6 * (f32_cases.len() + f64_cases.len()),
        "every input must exercise all six narrow signed/unsigned destinations",
    );
    assert!(
        f32_cases.len() >= 65_536,
        "the exhaustive binary16-representable f32 domain was not covered",
    );
    eprintln!(
        "NARROW SATURATING CLEAN BILL: {checked} native-JIT comparisons across \
         FPToSISat/FPToUISat -> i8/i16/i32/u8/u16/u32; {} f32 inputs (including all 65,536 \
         binary16 bit patterns) and {} f64 inputs all equal Rust `as` bit-exact.",
        f32_cases.len(),
        f64_cases.len(),
    );
}

// ============================================================================
// TEST 4 — ARMED negative controls: the differential is load-bearing.
//   (a) WRONG WIDTH: FPToSI->i32 (widened) vs the i64 oracle must DIVERGE on a
//       huge input (proving destination width is genuinely observed), while the
//       i64 conversion matches the i64 oracle. (b) WRONG CASTOP: FPToUI->u32 vs
//       FPToSI->i32 on -1.0 must differ (unsigned negative -> 0, signed -> -1),
//       proving signedness routing is real. If either control fails to diverge,
//       the harness is a no-op and the clean bill above is worthless.
// ============================================================================
#[test]
fn armed_controls_width_and_signedness() {
    // (a) width control.
    let mut mw = TrustIrModule::new("fp2int_ctrl_width".to_string());
    build_conv_fn(0, "as_i64", &mut mw, Ty::F64, true, 64, CastOp::FPToSI);
    build_conv_fn(1, "as_i32", &mut mw, Ty::F64, true, 32, CastOp::FPToSI);
    let bw = jit_buffer(&mw);
    let as_i64: ConvF64 = unsafe { std::mem::transmute(bind(&bw, "as_i64")) };
    let as_i32: ConvF64 = unsafe { std::mem::transmute(bind(&bw, "as_i32")) };

    let huge = 1e18f64;
    let want_i64 = huge as i64; // exact, in i64 range
    assert_eq!(
        unsafe { as_i64(huge) },
        want_i64,
        "i64 conv must match i64 oracle"
    );
    // i32 conv on the same huge value must NOT equal the i64 oracle: register-width
    // truncation to 32 bits changes the value. (Load-bearing width sensitivity.)
    let i32_got = unsafe { as_i32(huge) };
    assert_ne!(
        i32_got, want_i64,
        "WIDTH CONTROL DEAD: FPToSI->i32 returned the full i64 value on 1e18 — destination \
         width is being ignored end-to-end (differential is a no-op)"
    );
    assert_eq!(
        i32_got,
        ((huge as i64) as i32) as i64,
        "i32 conv should follow the register-width model"
    );

    // (b) signedness control.
    let mut ms = TrustIrModule::new("fp2int_ctrl_sign".to_string());
    build_conv_fn(0, "s32", &mut ms, Ty::F64, true, 32, CastOp::FPToSI);
    build_conv_fn(1, "u32", &mut ms, Ty::F64, false, 32, CastOp::FPToUI);
    let bs = jit_buffer(&ms);
    let s32: ConvF64 = unsafe { std::mem::transmute(bind(&bs, "s32")) };
    let u32f: ConvF64 = unsafe { std::mem::transmute(bind(&bs, "u32")) };

    // -1.0: signed -> -1; unsigned -> 0 (Rust `-1.0 as u32` = 0). Must differ.
    let s = unsafe { s32(-1.0) };
    let u = unsafe { u32f(-1.0) } as u64;
    assert_eq!(s, -1, "FPToSI(-1.0)->i32 must be -1");
    assert_eq!(u, 0, "FPToUI(-1.0)->u32 must be 0 (Rust `-1.0 as u32`)");
    assert_ne!(
        s as u64, u,
        "SIGNEDNESS CONTROL DEAD: FPToSI and FPToUI agreed on -1.0 (signedness ignored)"
    );
    // and a positive in-range value agrees across both (they only differ on sign edges).
    assert_eq!(unsafe { s32(42.0) }, 42);
    assert_eq!(unsafe { u32f(42.0) } as u64, 42);

    eprintln!(
        "ARMED CONTROLS: width-sensitivity load-bearing (FPToSI->i32(1e18) != i64 oracle); \
         signedness load-bearing (FPToSI(-1.0)=-1 vs FPToUI(-1.0)=0). Differential is real."
    );
}
