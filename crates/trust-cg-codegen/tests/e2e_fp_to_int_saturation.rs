//! Native AArch64 FP-to-integer regression and hardware characterization.
//!
//! FPToSISat/FPToUISat are defined everywhere and are compared with native
//! Rust destination-width `as`, including NaNs, infinities and overflow.
//! The unchanged narrow saturation corpus checks 1,008,216 native results.
//!
//! Raw FPToSI/FPToUI have no source-semantic result on out-of-range/NaN inputs.
//! Their existing 200 full-width and 342 narrow sweep rows are all retained:
//! finite inputs in the pinned TrustIR conservative [lo, hi) subset are checked
//! against the Rust destination-width oracle; other rows only characterize
//! current hardware. Those observations do not grant semantics to raw UB.
//!
//! The fixed, independent carrier model is W32 for 8/16/32-bit destinations
//! and X64 for 64-bit destinations, followed by destination-width truncation
//! and extension. It must not be inferred from the observed result.
//!
//! The four historical test names remain, with partitioned evidence labels.
//! A fifth test arms width/signedness controls using defined-everywhere Sat
//! operations. These tests use jit_fast at O1 (uncertified AArch64 JIT), not
//! certified JIT execution or formal proof. Run the complete target with
//! `--test-threads=1`.
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

// Hardware-only model: the integer carrier is W32 for narrow destinations,
// X64 for 64-bit destinations. Rust casts independently model architectural
// saturation at that carrier width; the result is then narrowed and extended.
fn regwidth_signed_f64(f: f64, n: u32) -> i64 {
    let wide = if n <= 32 { (f as i32) as i64 } else { f as i64 };
    match n {
        8 => (wide as i8) as i64,
        16 => (wide as i16) as i64,
        32 => (wide as i32) as i64,
        64 => wide,
        _ => unreachable!(),
    }
}
fn regwidth_unsigned_f64(f: f64, n: u32) -> u64 {
    let wide = if n <= 32 { (f as u32) as u64 } else { f as u64 };
    match n {
        8 => (wide as u8) as u64,
        16 => (wide as u16) as u64,
        32 => (wide as u32) as u64,
        64 => wide,
        _ => unreachable!(),
    }
}

/// Conservative admitted raw-cast subset from pinned TrustIR's numerics
/// policy: finite x in [lo, hi), before truncation. This deliberately excludes
/// the sub-minimum fractional band LLVM may define after truncation.
fn raw_cast_in_conservative_domain(x: f64, signed: bool, n: u32) -> bool {
    let upper = 2.0f64.powi(if signed { n as i32 - 1 } else { n as i32 });
    let lower = if signed { -upper } else { 0.0 };
    x.is_finite() && x >= lower && x < upper
}

/// Returns whether this row supplies source-defined-range evidence. Other
/// rows remain load-bearing observations of hardware, never raw-UB semantics.
fn check_raw_result(
    got: i64,
    x: f64,
    signed: bool,
    n: u32,
    defined_oracle: i64,
    symbol: &str,
) -> bool {
    let admitted = raw_cast_in_conservative_domain(x, signed, n);
    let expected = if admitted {
        defined_oracle
    } else if signed {
        regwidth_signed_f64(x, n)
    } else {
        regwidth_unsigned_f64(x, n) as i64
    };
    let evidence = if admitted {
        "source-defined conservative range"
    } else {
        "hardware characterization only; raw input outside admitted range"
    };
    assert_eq!(
        got,
        expected,
        "{symbol}: {evidence}, f={x:?} ({:#018x}), signed={signed}, width={n}",
        x.to_bits(),
    );
    admitted
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
    let ft = module
        .add_func_type(FuncTy {
            params: vec![src_ty.clone()],
            returns: vec![ret_ty.clone()],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
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
    module
        .try_add_function(f)
        .expect("Module::try_add_function: test fixture");
}

// ── JIT harness ─────────────────────────────────────────────────────────────────
type ConvF64 = unsafe extern "C" fn(f64) -> i64;
type ConvF32 = unsafe extern "C" fn(f32) -> i64;

fn jit_buffer(module: &TrustIrModule) -> trust_cg_codegen::jit::ExecutableBuffer {
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .with_codegen_license(permit_unlicensed())
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
// TEST 1 — Preserve all 200 raw full-width rows, distinguishing source-defined
// inputs from out-of-domain/NaN hardware observations. The historical test
// name is retained; neither its name nor hardware saturation grants raw UB
// a source-level result.
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
    let mut defined_cells = 0usize;
    let mut hardware_cells = 0usize;
    for f in f64_inputs() {
        let want = oracle_signed_f64(f, 64);
        for (symbol, signed, got, expected) in [
            ("s64_f64", true, unsafe { s64_f64(f) }, want),
            (
                "u64_f64",
                false,
                unsafe { u64_f64(f) },
                oracle_unsigned_f64(f, 64) as i64,
            ),
        ] {
            if check_raw_result(got, f, signed, 64, expected, symbol) {
                defined_cells += 1;
            } else {
                hardware_cells += 1;
            }
            checked += 1;
        }
        if f.is_nan() {
            nan_cells += 2;
        }
        if (f.is_infinite() || (f.is_finite() && f.abs() >= 9.3e18))
            && (want == i64::MAX || want == i64::MIN)
        {
            huge_sat_cells += 1;
        }
    }
    for f in f32_inputs() {
        let want = oracle_signed_f32(f, 64);
        for (symbol, signed, got, expected) in [
            ("s64_f32", true, unsafe { s64_f32(f) }, want),
            (
                "u64_f32",
                false,
                unsafe { u64_f32(f) },
                oracle_unsigned_f32(f, 64) as i64,
            ),
        ] {
            // Widening F32 to F64 is exact; keep the independent oracle as the
            // native F32 cast while using that exact value for domain/model.
            if check_raw_result(got, f64::from(f), signed, 64, expected, symbol) {
                defined_cells += 1;
            } else {
                hardware_cells += 1;
            }
            checked += 1;
        }
        if f.is_nan() {
            nan_cells += 2;
        }
        if (f.is_infinite() || (f.is_finite() && f.abs() >= 9.3e18))
            && (want == i64::MAX || want == i64::MIN)
        {
            huge_sat_cells += 1;
        }
    }
    assert_eq!(checked, 200, "retain every original full-width sweep row");
    assert_eq!(defined_cells + hardware_cells, checked);
    // Independently counted from the unchanged literal input corpus and the
    // mathematical conservative intervals, not from generated code results.
    assert_eq!((defined_cells, hardware_cells), (114, 86));
    assert_eq!(huge_sat_cells, 23);
    assert_eq!(nan_cells, 14);
    eprintln!(
        "RAW FULL-WIDTH: {checked} rows = {defined_cells} source-defined conservative-range \
         comparisons + {hardware_cells} hardware-only observations; {huge_sat_cells} huge \
         and {nan_cells} NaN cells retained. No source-semantic credit for raw UB."
    );
}

// ============================================================================
// TEST 2 — Preserve all 342 narrow raw rows and every pinned witness. Defined
//   inputs must match the destination-width Rust oracle. Other rows only
//   characterize W32 hardware saturation followed by narrowing/extension.
//   Comparing those observations with Rust `as` does not give raw UB semantics.
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
    let mut defined_cells = 0usize;
    let mut hardware_cells = 0usize;

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
            if check_raw_result(got, x, signed, n, as_oracle, sym) {
                defined_cells += 1;
            } else {
                hardware_cells += 1;
            }
            // (a) the JIT EXACTLY equals the register-width model — the precise
            //     mechanistic characterization (fail-loud if the mechanism differs).
            assert_eq!(
                got,
                regmodel,
                "narrow {sym}: hardware model mismatch at f={x:?} ({:#018x}): jit={got} \
                 model=sext/zext_N(trunc_N(f as {}32))={regmodel}; \
                 out-of-domain observations are not raw source-semantics evidence",
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
    assert_eq!(
        regmodel_matches, 342,
        "retain every original narrow sweep row"
    );
    assert_eq!(defined_cells + hardware_cells, regmodel_matches);
    assert_eq!((defined_cells, hardware_cells), (118, 224));
    // Both agreement and divergence from `as` occur. This comparison alone
    // does not classify the source domain: some out-of-range rows also agree.
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

    // PINNED HARDWARE WITNESSES — out-of-domain raw inputs, not source semantics.
    // 1000.0 as i8: Rust = 127 (saturate);   regmodel = (1000 as i8) = -24.
    let s8: ConvF64 = unsafe { std::mem::transmute(bind(&buf, "s8")) };
    assert_eq!(oracle_signed_f64(1000.0, 8), 127);
    assert_eq!(unsafe { s8(1000.0) }, (1000i64 as i8) as i64);
    assert_ne!(unsafe { s8(1000.0) }, 127, "witness stale: s8(1000.0)");
    // -1000.0 as i8: Rust = -128 (saturate); regmodel = (-1000 as i8) = 24.
    assert_eq!(oracle_signed_f64(-1000.0, 8), -128);
    assert_eq!(unsafe { s8(-1000.0) }, ((-1000i64) as i8) as i64);
    // W32 hardware saturates 1e18 to I32::MAX, unlike the obsolete X64 model.
    let s32: ConvF64 = unsafe { std::mem::transmute(bind(&buf, "s32")) };
    assert_eq!(oracle_signed_f64(1e18, 32), i32::MAX as i64);
    assert_eq!(unsafe { s32(1e18) }, i32::MAX as i64);
    assert_ne!(
        unsafe { s32(1e18) },
        ((1e18f64 as i64) as i32) as i64,
        "hardware witness must refute the obsolete X64-then-truncate model"
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
    // NaN -> 0 is only a hardware observation for these raw casts.
    assert_eq!(unsafe { s8(f64::NAN) }, 0, "s8(NaN)=0");
    assert_eq!(unsafe { u8f(f64::NAN) } as u64, 0, "u8(NaN)=0");

    eprintln!(
        "RAW NARROW: {regmodel_matches} rows = {defined_cells} source-defined conservative-range \
         comparisons + {hardware_cells} hardware-only observations. W32-then-narrow model \
         matches all rows; {as_matches} observations equal Rust `as`, {as_diverges} differ \
         ({huge_narrow_diverge} huge). Equality outside the admitted range gives no raw-UB \
         correctness credit; defined-everywhere saturation is checked separately."
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
// TEST 4 — Retained raw hardware controls. The I32 width case is out of range,
// and the unsigned -1 case is outside its source domain. They characterize
// instruction behavior only. Test 5 separately arms semantically defined Sat
// controls with the same inputs; no raw-UB observation supports that claim.
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
    // This raw I32 input is out of domain: W32 hardware saturates to I32::MAX.
    let i32_got = unsafe { as_i32(huge) };
    assert_ne!(
        i32_got, want_i64,
        "WIDTH CONTROL DEAD: FPToSI->i32 returned the full i64 value on 1e18 — destination \
         width is being ignored end-to-end (differential is a no-op)"
    );
    assert_eq!(
        i32_got,
        i32::MAX as i64,
        "raw out-of-domain I32 hardware observation should follow the W32 model"
    );

    // (b) signedness control.
    let mut ms = TrustIrModule::new("fp2int_ctrl_sign".to_string());
    build_conv_fn(0, "s32", &mut ms, Ty::F64, true, 32, CastOp::FPToSI);
    build_conv_fn(1, "u32", &mut ms, Ty::F64, false, 32, CastOp::FPToUI);
    let bs = jit_buffer(&ms);
    let s32: ConvF64 = unsafe { std::mem::transmute(bind(&bs, "s32")) };
    let u32f: ConvF64 = unsafe { std::mem::transmute(bind(&bs, "u32")) };

    // Raw -1.0 is admitted for signed I32, but hardware-only for unsigned U32.
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
        "RAW HARDWARE CONTROLS: 6 native calls retained; W32/X64 differ on1e18 and signed/unsigned \
         hardware differs on -1.0. Out-of-domain cases carry no source-semantic credit."
    );
}

// TEST 5 — Additive, source-defined width/signedness controls. Sat operations
// are defined for every input, so the distinguishing cases below are semantic
// regression checks rather than observations of raw out-of-domain behavior.
#[test]
fn saturating_armed_controls_are_source_defined() {
    // Pin the conservative raw classifier independently of generated results.
    assert!(raw_cast_in_conservative_domain(-128.0, true, 8));
    assert!(!raw_cast_in_conservative_domain(-128.5, true, 8));
    assert!(!raw_cast_in_conservative_domain(128.0, true, 8));
    assert!(raw_cast_in_conservative_domain(-0.0, false, 8));
    assert!(!raw_cast_in_conservative_domain(-1.0, false, 8));
    assert!(!raw_cast_in_conservative_domain(f64::NAN, true, 64));
    assert!(!raw_cast_in_conservative_domain(f64::INFINITY, false, 64));

    let mut module = TrustIrModule::new("fp2int_defined_sat_controls".to_owned());
    build_conv_fn(
        0,
        "ssat64",
        &mut module,
        Ty::F64,
        true,
        64,
        CastOp::FPToSISat,
    );
    build_conv_fn(
        1,
        "ssat32",
        &mut module,
        Ty::F64,
        true,
        32,
        CastOp::FPToSISat,
    );
    build_conv_fn(
        2,
        "usat32",
        &mut module,
        Ty::F64,
        false,
        32,
        CastOp::FPToUISat,
    );
    let buffer = jit_buffer(&module);
    let signed64: ConvF64 = unsafe { std::mem::transmute(bind(&buffer, "ssat64")) };
    let signed32: ConvF64 = unsafe { std::mem::transmute(bind(&buffer, "ssat32")) };
    let unsigned32: ConvF64 = unsafe { std::mem::transmute(bind(&buffer, "usat32")) };
    let huge = 1e18f64;
    let actual = unsafe {
        [
            signed64(huge),
            signed32(huge),
            signed32(-1.0),
            unsigned32(-1.0),
            signed32(42.0),
            unsigned32(42.0),
        ]
    };
    let expected = [
        huge as i64,
        (huge as i32) as i64,
        (-1.0f64 as i32) as i64,
        (-1.0f64 as u32) as i64,
        (42.0f64 as i32) as i64,
        (42.0f64 as u32) as i64,
    ];
    assert_eq!(actual.len(), 6);
    assert_eq!(
        actual, expected,
        "all Sat control inputs are source-defined"
    );
    assert_ne!(
        actual[0], actual[1],
        "Sat width control must distinguish I64/I32"
    );
    assert_ne!(
        actual[2], actual[3],
        "Sat signedness control must distinguish I32/U32"
    );
    assert_eq!(
        actual[4], actual[5],
        "positive in-range conversions must agree"
    );
    eprintln!(
        "SOURCE-DEFINED SAT CONTROLS: 6 native comparisons; width and signedness mutations refuted."
    );
}

/// This file's fixtures are hand-built and carry no codegen license
/// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
/// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
/// them passes because it was silently refused.
fn permit_unlicensed() -> trust_cg_lower::CodegenLicensePolicy {
    trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit)
}
