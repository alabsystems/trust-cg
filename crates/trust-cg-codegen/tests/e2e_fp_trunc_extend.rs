//! TRUST-SELF ROUND 36 (thread R36): AUDIT THE BACKEND f32<->f64 TRUNCATE / EXTEND
//! LOWERING (FCVT) against the Rust `x as f32` / `x as f64` oracle.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! CONTEXT — the conversion trilogy completes
//! ═══════════════════════════════════════════════════════════════════════════════
//! R34 audited f->int SATURATION (FCVTZS/FCVTZU) — full-width CLEAN.
//! R35 audited int->f ROUNDING/SIGNEDNESS (SCVTF/UCVTF) — i64/u64 CLEAN, but found
//!     TWO real backend miscompiles: narrow-signed SIToFP (owner #12) and i128->f
//!     low-64 truncation (owner #13), both rooted in the `sf`-hardcode / half-split
//!     register class on the INTEGER side of the fp<->int encoders.
//! THIS round (R36) audits the THIRD leg: float<->float precision conversion,
//!     f32<->f64. Two things can go wrong:
//!   (1) FPTrunc (f64->f32) ROUNDS (round-to-nearest-even). A wrong tie-break, a
//!       failure to overflow to +-inf, a wrong gradual-underflow (subnormal) result,
//!       or a mishandled NaN payload is a real miscompile.
//!   (2) FPExt (f32->f64) is EXACT (every f32 widens with no rounding). Any bit that
//!       is not a faithful widen (incl. subnormal f32 -> f64 normal, NaN payload
//!       left-justification, sNaN quieting) is a bug.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! THE ORACLE — Rust `x as f32` / `x as f64` (INDEPENDENT, computed at test time)
//! ═══════════════════════════════════════════════════════════════════════════════
//! Rust float<->float `as` is the standard IEEE-754 conversion: FPExt (widen) is
//! EXACT; FPTrunc (narrow) is round-to-nearest-ties-to-even, with too-large ->
//! +-inf and too-small -> subnormal/0 (gradual underflow). NaN -> NaN.
//! The oracle is evaluated at RUNTIME here (`std::hint::black_box(v) as f{32,64}`)
//! so native Rust emits the SAME hardware FCVT the JIT does — the input is never a
//! compile-time constant the rustc frontend could const-fold via apfloat (which
//! could disagree on unspecified NaN payloads). Both sides are therefore "the
//! aarch64 FCVT on exactly these bits"; native==JIT is the codegen claim.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! WHAT THE BACKEND ACTUALLY DOES (read from source; verified empirically below)
//! ═══════════════════════════════════════════════════════════════════════════════
//!  * CastOp::FPExt  -> Opcode::FPExt  -> isel select_fp_ext  (isel.rs:9588):
//!    (F32,F64) => AArch64Opcode::FcvtSD, dst RegClass::Fpr64.
//!    CastOp::FPTrunc-> Opcode::FPTrunc-> isel select_fp_trunc (isel.rs:9622):
//!    (F64,F32) => AArch64Opcode::FcvtDS, dst RegClass::Fpr32.
//!    Both opcodes are selected from the REAL (src_ty,dst_ty), not a hardcode.
//!  * ENCODER (encode.rs:2044/2054 -> encoding_fp::encode_fp_precision_cvt): BOTH the
//!    source ftype[23:22] AND the destination opc[16:15] are passed EXPLICITLY as the
//!    FpSize pair the opcode variant carries (Single=00 / Double=01). There is NO
//!    `sf`/width hardcode analogous to the R34/R35 fp<->int encoders (which forced
//!    sf=64 on the integer register). `FCVT Dd,Sn` (widen) = 0x1E22C000|regs;
//!    `FCVT Sd,Dn` (narrow) = 0x1E624000|regs. Rounding is the hardware FCVT under
//!    the default FPCR (round-to-nearest-even, no Default-NaN) — matching Rust `as`.
//!    => STRUCTURALLY there is no place for a width/precision bug here; this file
//!    machine-checks that empirically at every rounding/overflow/underflow/NaN edge.
//!
//! ═══════════════════════════════════════════════════════════════════════════════
//! HOW INPUT BITS ARE CONTROLLED (exactness discipline)
//! ═══════════════════════════════════════════════════════════════════════════════
//! Each module takes the source float's BITS as an integer param and Bitcasts them
//! into the FP register INSIDE the module (Bitcast i64->f64 = FMOV Dd,Xn; Bitcast
//! i32->f32 = FMOV Sd,Wn — bitwise, no quieting), so the exact bit pattern (incl.
//! sNaN payloads) reaches the FCVT unmodified. The result float is returned in d0/s0
//! and read via to_bits() (a bitwise register read). This removes any ABI
//! float-argument-passing question from the audit.
//!
//! No emit-from-Rust: the emit-closure frontend has NO float support (R31 Finding A —
//! `scalar_tir_ty` returns None for `ty::Float`). Everything here is hand-built
//! trust-ir driven through the trust-cg JIT; the oracle is native Rust `as`.
//!
//! Run tests ONE AT A TIME (`-- --exact <name> --test-threads=1`): the JIT engine is
//! not thread-safe at suite scale (jit-parallel-race-2026-06-29.md).

#![cfg(target_arch = "aarch64")]

use std::collections::HashMap;
use std::hint::black_box;

use trust_cg_codegen::Target;
use trust_cg_codegen::compiler::{Compiler, CompilerConfig};

use trust_ir::{
    Block as TrustIrBlock, FuncTy, Function as TrustIrFunction, Inst, InstrNode,
    Module as TrustIrModule, Ty,
};
use trust_ir::{BlockId, CastOp, FuncId, ValueId};

// ── module builders ────────────────────────────────────────────────────────────────
//
// FPTrunc  fn(i64) -> f32:  v1 = Bitcast(i64->f64, v0); v2 = FPTrunc(f64->f32, v1); return v2
// FPExt    fn(i32) -> f64:  v1 = Bitcast(i32->f32, v0); v2 = FPExt(f32->f64, v1);   return v2
//
// The float RESULT bits are read on the Rust side via f32::to_bits()/f64::to_bits().

/// FPTrunc f64->f32: param carries the f64 source BITS (as i64), Bitcast into a
/// double register, FCVT-narrow to f32, return f32.
fn build_fptrunc(func_id: u32, name: &str, m: &mut TrustIrModule) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I64],
        returns: vec![Ty::F32],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I64)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I64,
                dst_ty: Ty::F64,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Cast {
                op: CastOp::FPTrunc,
                src_ty: Ty::F64,
                dst_ty: Ty::F32,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
}

/// FPExt f32->f64: param carries the f32 source BITS (as i32), Bitcast into a single
/// register, FCVT-widen to f64, return f64.
fn build_fpext(func_id: u32, name: &str, m: &mut TrustIrModule) {
    let ft = m.add_func_type(FuncTy {
        params: vec![Ty::I32],
        returns: vec![Ty::F64],
        is_vararg: false,
    });
    let mut f = TrustIrFunction::new(FuncId::new(func_id), name, ft, BlockId::new(0));
    f.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::I32)],
        body: vec![
            InstrNode::new(Inst::Cast {
                op: CastOp::Bitcast,
                src_ty: Ty::I32,
                dst_ty: Ty::F32,
                operand: ValueId::new(0),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Cast {
                op: CastOp::FPExt,
                src_ty: Ty::F32,
                dst_ty: Ty::F64,
                operand: ValueId::new(1),
            })
            .with_result(ValueId::new(2)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(2)],
            }),
        ],
    }];
    m.add_function(f);
}

// ── JIT harness ─────────────────────────────────────────────────────────────────
fn jit_buffer(m: &TrustIrModule) -> trust_cg_codegen::jit::ExecutableBuffer {
    let config = CompilerConfig::jit_fast(Target::Aarch64);
    Compiler::new(config)
        .compile_module_to_jit(m, &HashMap::new())
        .expect(
            "hand-built f32<->f64 FCVT module must JIT-compile (backend supports FcvtSD/FcvtDS)",
        )
        .buffer
}
fn bind(buf: &trust_cg_codegen::jit::ExecutableBuffer, sym: &str) -> *const u8 {
    buf.get_fn_ptr_bound(sym)
        .unwrap_or_else(|| panic!("JIT symbol `{sym}` not found"))
        .as_ptr()
}

type F32FromBits = unsafe extern "C" fn(u64) -> f32; // FPTrunc: f64-bits -> f32
type F64FromBits = unsafe extern "C" fn(u32) -> f64; // FPExt:   f32-bits -> f64

// The RUNTIME oracles: black_box forces native Rust to emit a hardware FCVT on the
// exact bits (never const-folded), so it is bit-for-bit the same operation the JIT
// performs. This is the counterpart to the JIT's machine-code FCVT.
#[inline(never)]
fn oracle_fptrunc_bits(f64_bits: u64) -> u32 {
    (black_box(f64::from_bits(f64_bits)) as f32).to_bits()
}
#[inline(never)]
fn oracle_fpext_bits(f32_bits: u32) -> u64 {
    (black_box(f32::from_bits(f32_bits)) as f64).to_bits()
}

// ============================================================================
// TEST 1 — FPExt f32->f64 EXACT CLEAN BILL.
//   Widening is exact: every f32 (normal, subnormal, +-0, +-inf, MIN/MAX/
//   MIN_POSITIVE) widens to the SAME numeric value as an f64, with the low 29
//   mantissa bits zero (f32's 23-bit mantissa left-justified into f64's 52).
//   JIT bits must equal Rust `x as f64` bit-exact; and the exactness structural
//   property (widened == original value; low-29 mantissa bits zero for finite)
//   is independently asserted.
// ============================================================================
#[test]
fn fpext_f32_to_f64_exact_clean_bill() {
    let mut m = TrustIrModule::new("fpext_clean".to_string());
    build_fpext(0, "ext", &mut m);
    let buf = jit_buffer(&m);
    let ext: F64FromBits = unsafe { std::mem::transmute(bind(&buf, "ext")) };

    // f32 inputs, by bit pattern, spanning the whole classification space.
    let mut inputs: Vec<u32> = vec![
        0.0f32.to_bits(),
        (-0.0f32).to_bits(),
        1.0f32.to_bits(),
        (-1.0f32).to_bits(),
        2.0f32.to_bits(),
        0.5f32.to_bits(),
        std::f32::consts::PI.to_bits(),
        (-std::f32::consts::PI).to_bits(),
        1.0e30f32.to_bits(),
        1.0e-30f32.to_bits(),
        f32::MAX.to_bits(),
        f32::MIN.to_bits(),
        f32::MIN_POSITIVE.to_bits(), // smallest NORMAL f32 = 2^-126
        f32::INFINITY.to_bits(),
        f32::NEG_INFINITY.to_bits(),
        // subnormal f32 (exponent 0, nonzero mantissa) — MUST become a normal f64
        0x0000_0001, // smallest positive subnormal = 2^-149
        0x0000_0002,
        0x007F_FFFF, // largest subnormal
        0x0040_0000, // mid subnormal
        0x8000_0001, // negative smallest subnormal
        // arbitrary normals
        0x4048_F5C3,
        0xC2F6_E979,
        0x3F80_0001, // 1.0 + 1 ulp
        0x7F7F_FFFF, // == f32::MAX
    ];
    // a dense band of consecutive f32 encodings around 1.0 (all exact-widen)
    for k in 0..64u32 {
        inputs.push(0x3F80_0000 + k);
    }

    let mut checked = 0usize;
    let mut subnormals = 0usize;
    for &b in &inputs {
        let jit = unsafe { ext(b) }.to_bits();
        let want = oracle_fpext_bits(b);
        assert_eq!(
            jit, want,
            "FPExt f32->f64 MISCOMPILE at f32 bits {b:#010x}: jit={jit:#018x} want(x as f64)={want:#018x}"
        );
        // Independent exactness property (skip NaN/inf: value comparison is for finite).
        let fv = f32::from_bits(b);
        if fv.is_finite() {
            // widened value equals original numeric value EXACTLY
            assert_eq!(
                f64::from_bits(jit),
                fv as f64,
                "FPExt not value-exact at {b:#010x}"
            );
            // low 29 mantissa bits of the f64 must be zero (f32's 23-bit mantissa
            // maps to the top 23 of f64's 52; 52-23 = 29 trailing zero bits), for
            // NORMAL results. (subnormal f32 -> normal f64 also has this property
            // because the subnormal mantissa is renormalized with trailing zeros.)
            if fv != 0.0 {
                assert_eq!(
                    jit & 0x1FFF_FFFF,
                    0,
                    "FPExt low-29 mantissa bits not zero at {b:#010x}"
                );
            }
            if (b & 0x7F80_0000) == 0 && (b & 0x007F_FFFF) != 0 {
                subnormals += 1;
                // a subnormal f32 becomes a NORMAL f64 (exponent field nonzero)
                assert_ne!(
                    jit & 0x7FF0_0000_0000_0000,
                    0,
                    "subnormal f32 must widen to NORMAL f64"
                );
            }
        }
        checked += 1;
    }
    assert!(
        subnormals >= 4,
        "subnormal f32 cells under-exercised ({subnormals})"
    );
    eprintln!(
        "FPExt CLEAN BILL: f32->f64 widen == Rust `x as f64` bit-exact on {checked} cells \
         (normals, {subnormals} subnormals->normal-f64, +-0, +-inf, MIN/MAX/MIN_POSITIVE, \
         dense 1.0 band). Widening is EXACT: value preserved, low-29 mantissa bits zero. \
         FcvtSD is faithful."
    );
}

// ============================================================================
// TEST 2 — FPExt NaN payload. f32 qNaN/sNaN widen to f64 NaN; the payload is
//   left-justified and sNaN is quieted (hardware FCVT). JIT bits must equal the
//   runtime Rust `as f64` oracle bit-exact, and the result must be NaN.
// ============================================================================
#[test]
fn fpext_nan_payload() {
    let mut m = TrustIrModule::new("fpext_nan".to_string());
    build_fpext(0, "ext", &mut m);
    let buf = jit_buffer(&m);
    let ext: F64FromBits = unsafe { std::mem::transmute(bind(&buf, "ext")) };

    // qNaN (MSB of mantissa set) and sNaN (MSB clear, low payload set) f32 patterns.
    let nans: &[u32] = &[
        0x7FC0_0000, // canonical qNaN
        0xFFC0_0000, // negative qNaN
        0x7FC0_1234, // qNaN with payload
        0x7FFF_FFFF, // qNaN all-payload
        0x7F80_0001, // sNaN (min payload)
        0xFF80_0001, // negative sNaN
        0x7FBF_FFFF, // sNaN max payload (MSB of mantissa clear)
        0x7F80_4321, // sNaN with payload
    ];
    let mut bit_matches = 0usize;
    for &b in nans {
        let jit = unsafe { ext(b) };
        let jit_bits = jit.to_bits();
        assert!(
            jit.is_nan(),
            "FPExt of NaN f32 {b:#010x} must be NaN, got {jit_bits:#018x}"
        );
        let want = oracle_fpext_bits(b);
        assert_eq!(
            jit_bits, want,
            "FPExt NaN payload DIVERGES from runtime `as f64` at f32 {b:#010x}: \
             jit={jit_bits:#018x} want={want:#018x}"
        );
        // sNaN must be quieted (top mantissa bit of the f64 result set).
        assert_ne!(
            jit_bits & 0x0008_0000_0000_0000,
            0,
            "widened NaN must be quiet"
        );
        bit_matches += 1;
    }
    assert_eq!(bit_matches, nans.len());
    eprintln!(
        "FPExt NaN: all {bit_matches} qNaN/sNaN f32 widen to f64 NaN, payload left-justified \
         and sNaN quieted, bit-exact vs runtime `x as f64`. FcvtSD NaN handling faithful."
    );
}

// ============================================================================
// TEST 3 — FPTrunc f64->f32 RNE ROUNDING CLEAN BILL (the primary bug site).
//   Narrowing rounds to nearest, ties to even. Sweep exact values, ties-to-even,
//   round-up, round-down, dense ULP bands, and hard-pinned witnesses. Every cell
//   must be bit-exact to Rust `x as f32`.
// ============================================================================
#[test]
fn fptrunc_f64_to_f32_rounding_clean_bill() {
    let mut m = TrustIrModule::new("fptrunc_round".to_string());
    build_fptrunc(0, "tr", &mut m);
    let buf = jit_buffer(&m);
    let tr: F32FromBits = unsafe { std::mem::transmute(bind(&buf, "tr")) };

    let call = |x: f64| -> u32 { unsafe { tr(x.to_bits()) }.to_bits() };

    // Exactly-representable-in-f32 values (round-trip, no rounding).
    let exact: &[f64] = &[
        0.0,
        -0.0,
        1.0,
        -1.0,
        2.0,
        0.5,
        -0.5,
        3.0,
        100.0,
        0.25,
        16777216.0, /*2^24*/
        -16777216.0,
        1.0 + 2f64.powi(-23), /*1 + 1 f32-ulp*/
    ];
    // Values that MUST round (more than 24 significant mantissa bits).
    // At magnitude 2^24 the f32 ULP is 2, so 2^24+1 is an exact halfway (ties to even).
    let m24 = 16777216.0f64; // 2^24
    let rounders: &[f64] = &[
        m24 + 1.0,                  // halfway -> ties to even -> 2^24        (0x4b80_0000)
        m24 + 3.0,                  // halfway -> ties to even -> 2^24+4      (0x4b80_0002)
        m24 + 2.0,                  // exact (even) -> 2^24+2
        m24 + 5.0,                  // halfway -> ties to even -> 2^24+4
        1.0 + 2f64.powi(-24),       // halfway at magnitude 1 -> ties to even -> 1.0
        1.0 + 3.0 * 2f64.powi(-24), // halfway -> ties to even -> 1+2^-22
        0.1,
        0.2,
        0.3,
        1.0 / 3.0,
        std::f64::consts::PI,
        std::f64::consts::E,
        std::f64::consts::LN_2,
        1.7976931348623157e30,
        -1.7976931348623157e30,
        1234567.891011,
        -9876543.21,
    ];

    let mut checked = 0usize;
    let mut round_cells = 0usize;
    for &x in exact.iter().chain(rounders) {
        let jit = call(x);
        let want = oracle_fptrunc_bits(x.to_bits());
        assert_eq!(
            jit,
            want,
            "FPTrunc f64->f32 MISCOMPILE at x={x:e} ({:#018x}): jit={jit:#010x} want(x as f32)={want:#010x}",
            x.to_bits()
        );
        checked += 1;
    }

    // Dense ULP band straddling 2^24 (where consecutive integers stop being
    // representable in f32) — every value's rounding direction is checked vs oracle.
    for d in -4i64..=64 {
        let x = m24 + d as f64;
        let jit = call(x);
        let want = oracle_fptrunc_bits(x.to_bits());
        assert_eq!(
            jit, want,
            "FPTrunc dense-2^24 at 2^24{d:+}: jit={jit:#010x} want={want:#010x}"
        );
        checked += 1;
        if d > 0 && (d % 2 == 1) {
            round_cells += 1; // odd offset above 2^24 must round (low bit lost)
        }
    }
    // Dense band walking consecutive f64 ULPs just above 1.0 (each rounds into the
    // f32 grid, exercising ties and round-up/round-down finely).
    let one = 1.0f64.to_bits();
    for k in 0..200u64 {
        let x = f64::from_bits(one + k * 4096); // step several f64 ulps at a time
        let jit = call(x);
        let want = oracle_fptrunc_bits(x.to_bits());
        assert_eq!(
            jit, want,
            "FPTrunc dense-1.0 k={k}: jit={jit:#010x} want={want:#010x}"
        );
        checked += 1;
        round_cells += 1;
    }
    // Powers of two +- small across the exponent range (exact powers + rounding).
    for e in -60i32..=100 {
        for &off in &[0.0f64, 1.0, -1.0, 3.0] {
            let base = 2f64.powi(e);
            let x = base + off * base * 2f64.powi(-26); // perturb by sub-ULP-ish amount
            let jit = call(x);
            let want = oracle_fptrunc_bits(x.to_bits());
            assert_eq!(
                jit, want,
                "FPTrunc pow2 e={e} off={off}: jit={jit:#010x} want={want:#010x}"
            );
            checked += 1;
            if off != 0.0 {
                round_cells += 1;
            }
        }
    }

    // Hard-pinned RNE witnesses (documented in the report).
    assert_eq!(call(m24 + 1.0), 0x4b80_0000, "2^24+1 ties to even -> 2^24");
    assert_eq!(
        call(m24 + 3.0),
        0x4b80_0002,
        "2^24+3 rounds up (ties to even) -> 2^24+4"
    );
    assert_eq!(
        call(1.0 + 2f64.powi(-24)),
        0x3f80_0000,
        "1+2^-24 ties to even -> 1.0"
    );
    assert_eq!(call(0.1), (0.1f32).to_bits(), "0.1_f64 -> nearest f32");

    assert!(
        round_cells >= 100,
        "RNE-rounding cells under-exercised ({round_cells})"
    );
    eprintln!(
        "FPTrunc RNE CLEAN BILL: {checked} f64->f32 cells bit-exact vs Rust `x as f32` \
         ({round_cells} genuine rounding cells: dense 2^24 band, dense 1.0 ULP walk, \
         powers-of-two 2^-60..2^100). Ties-to-even correct: 2^24+1->2^24, 2^24+3->2^24+4, \
         1+2^-24->1.0. FcvtDS rounding faithful."
    );
}

// ============================================================================
// TEST 4 — FPTrunc OVERFLOW -> +-inf (NOT saturated to f32::MAX).
//   |f64| above the round-to-nearest overflow threshold must become +-inf, per
//   IEEE (a saturating clamp to f32::MAX would be WRONG). The exact f32::MAX
//   boundary round-trips; just above the midpoint overflows. JIT == Rust `as f32`.
// ============================================================================
#[test]
fn fptrunc_overflow_to_inf() {
    let mut m = TrustIrModule::new("fptrunc_ovf".to_string());
    build_fptrunc(0, "tr", &mut m);
    let buf = jit_buffer(&m);
    let tr: F32FromBits = unsafe { std::mem::transmute(bind(&buf, "tr")) };
    let call = |x: f64| -> u32 { unsafe { tr(x.to_bits()) }.to_bits() };

    let f32max = f32::MAX as f64; // exact
    // The overflow round-nearest threshold is the midpoint between f32::MAX and 2^128.
    let two128 = 2f64.powi(128);
    let midpoint = (f32max + two128) / 2.0; // = 2^128 - 2^103

    let cases: &[(f64, &str)] = &[
        (f32max, "f32::MAX exact -> round-trips"),
        (f32max * (1.0 - 2f64.powi(-30)), "just below MAX -> MAX"),
        (1e300, "1e300 -> +inf"),
        (-1e300, "-1e300 -> -inf"),
        (two128, "2^128 -> +inf"),
        (-two128, "-2^128 -> -inf"),
        (f64::MAX, "f64::MAX -> +inf"),
        (f64::MIN, "f64::MIN -> -inf"),
        (f64::INFINITY, "+inf -> +inf"),
        (f64::NEG_INFINITY, "-inf -> -inf"),
    ];
    let mut overflowed = 0usize;
    for &(x, desc) in cases {
        let jit = call(x);
        let want = oracle_fptrunc_bits(x.to_bits());
        assert_eq!(
            jit, want,
            "FPTrunc overflow [{desc}] x={x:e}: jit={jit:#010x} want={want:#010x}"
        );
        if x.abs() >= two128 || x.is_infinite() {
            assert!(
                f32::from_bits(jit).is_infinite(),
                "[{desc}] must be inf, got {jit:#010x}"
            );
            // CRITICAL: must be +-inf, NOT saturated to +-f32::MAX.
            assert_ne!(
                jit & 0x7FFF_FFFF,
                f32::MAX.to_bits(),
                "[{desc}] must NOT clamp to f32::MAX"
            );
            overflowed += 1;
        }
    }
    // The exact overflow boundary: just below midpoint -> f32::MAX; at/above -> inf.
    let just_below = f64::from_bits(midpoint.to_bits() - 1);
    let at_or_above = midpoint;
    assert_eq!(
        call(just_below),
        oracle_fptrunc_bits(just_below.to_bits()),
        "boundary just_below"
    );
    assert_eq!(
        call(at_or_above),
        oracle_fptrunc_bits(at_or_above.to_bits()),
        "boundary midpoint"
    );
    assert_eq!(
        call(f32max),
        f32::MAX.to_bits(),
        "f32::MAX round-trips to f32::MAX (not inf)"
    );

    assert!(overflowed >= 6);
    eprintln!(
        "FPTrunc OVERFLOW: {overflowed} too-large f64 -> +-inf (NOT clamped to f32::MAX), \
         bit-exact vs Rust `x as f32`; f32::MAX round-trips; the round-nearest overflow \
         midpoint (2^128-2^103) agrees with the oracle. IEEE overflow, not saturation."
    );
}

// ============================================================================
// TEST 5 — FPTrunc UNDERFLOW -> subnormal / 0 (gradual underflow, round-to-nearest).
//   f64 magnitudes below f32::MIN_POSITIVE (2^-126) become f32 subnormals down to
//   2^-149, then round to 0. RNE applies in the subnormal grid too. JIT == Rust `as`.
// ============================================================================
#[test]
fn fptrunc_underflow_subnormal() {
    let mut m = TrustIrModule::new("fptrunc_unf".to_string());
    build_fptrunc(0, "tr", &mut m);
    let buf = jit_buffer(&m);
    let tr: F32FromBits = unsafe { std::mem::transmute(bind(&buf, "tr")) };
    let call = |x: f64| -> u32 { unsafe { tr(x.to_bits()) }.to_bits() };

    let cases: &[(f64, &str)] = &[
        (
            2f64.powi(-126),
            "2^-126 = f32::MIN_POSITIVE (smallest normal)",
        ),
        (2f64.powi(-127), "2^-127 -> f32 subnormal"),
        (2f64.powi(-140), "2^-140 -> f32 subnormal"),
        (2f64.powi(-149), "2^-149 -> smallest f32 subnormal"),
        (2f64.powi(-150), "2^-150 -> halfway -> ties to even -> 0"),
        (2f64.powi(-149) * 1.5, "1.5*2^-149 -> rounds to 2^-148"),
        (2f64.powi(-149) * 0.75, "0.75*2^-149 -> rounds to 2^-149"),
        (
            2f64.powi(-149) * 0.5,
            "0.5*2^-149 = halfway 0..min -> ties to even -> 0",
        ),
        (2f64.powi(-149) * 0.49, "just under half min -> 0"),
        (1e-300, "1e-300 -> 0"),
        (-2f64.powi(-140), "negative subnormal"),
        (-1e-300, "negative underflow -> -0"),
        (2f64.powi(-130), "2^-130 -> subnormal"),
        (2f64.powi(-145) + 2f64.powi(-149), "subnormal grid sum"),
    ];
    let mut subnormal_results = 0usize;
    let mut underflow_to_zero = 0usize;
    for &(x, desc) in cases {
        let jit = call(x);
        let want = oracle_fptrunc_bits(x.to_bits());
        assert_eq!(
            jit, want,
            "FPTrunc underflow [{desc}] x={x:e}: jit={jit:#010x} want={want:#010x}"
        );
        let cls = (jit & 0x7F80_0000, jit & 0x007F_FFFF);
        if cls.0 == 0 && cls.1 != 0 {
            subnormal_results += 1; // exponent 0, nonzero mantissa = subnormal
        }
        if jit & 0x7FFF_FFFF == 0 {
            underflow_to_zero += 1;
        }
    }
    // Dense subnormal sweep: multiples of the smallest subnormal (2^-149), each RNE.
    let min_sub = 2f64.powi(-149);
    for k in 0..80u64 {
        let x = min_sub * (k as f64 + 0.5); // half-integer multiples exercise ties
        let jit = call(x);
        let want = oracle_fptrunc_bits(x.to_bits());
        assert_eq!(
            jit, want,
            "FPTrunc subnormal grid k={k}.5: jit={jit:#010x} want={want:#010x}"
        );
    }
    assert!(
        subnormal_results >= 5,
        "subnormal-result cells under-exercised ({subnormal_results})"
    );
    assert!(
        underflow_to_zero >= 2,
        "underflow-to-zero cells under-exercised ({underflow_to_zero})"
    );
    eprintln!(
        "FPTrunc UNDERFLOW: gradual underflow correct — {subnormal_results} f64 -> f32 subnormal, \
         {underflow_to_zero} -> +-0 (ties to even at the 2^-150 boundary), plus an 80-cell \
         half-integer subnormal-grid RNE sweep, all bit-exact vs Rust `x as f32`. FcvtDS \
         subnormal/underflow faithful."
    );
}

// ============================================================================
// TEST 6 — FPTrunc NaN / +-inf / +-0 special values.
//   qNaN/sNaN f64 -> f32 NaN (payload truncated MSBs, sNaN quieted); +-inf -> +-inf;
//   +-0 -> +-0. JIT bits == runtime Rust `as f32` bit-exact.
// ============================================================================
#[test]
fn fptrunc_nan_inf_zero() {
    let mut m = TrustIrModule::new("fptrunc_special".to_string());
    build_fptrunc(0, "tr", &mut m);
    let buf = jit_buffer(&m);
    let tr: F32FromBits = unsafe { std::mem::transmute(bind(&buf, "tr")) };
    let callb = |bits: u64| -> u32 { unsafe { tr(bits) }.to_bits() };

    // +-0 and +-inf.
    for (bits, is_inf, desc) in [
        (0.0f64.to_bits(), false, "+0"),
        ((-0.0f64).to_bits(), false, "-0"),
        (f64::INFINITY.to_bits(), true, "+inf"),
        (f64::NEG_INFINITY.to_bits(), true, "-inf"),
    ] {
        let jit = callb(bits);
        let want = oracle_fptrunc_bits(bits);
        assert_eq!(
            jit, want,
            "FPTrunc special [{desc}]: jit={jit:#010x} want={want:#010x}"
        );
        let v = f32::from_bits(jit);
        if is_inf {
            assert!(v.is_infinite(), "[{desc}] must be inf");
        } else {
            assert_eq!(v, 0.0, "[{desc}] must be zero");
        }
    }
    // Sign of zero preserved.
    assert_eq!(callb(0.0f64.to_bits()), 0x0000_0000, "+0 -> +0");
    assert_eq!(callb((-0.0f64).to_bits()), 0x8000_0000, "-0 -> -0");

    // qNaN / sNaN f64.
    let nans: &[u64] = &[
        0x7FF8_0000_0000_0000, // canonical qNaN
        0xFFF8_0000_0000_0000, // negative qNaN
        0x7FF8_0000_1234_5678, // qNaN with payload
        0x7FFF_FFFF_FFFF_FFFF, // qNaN all-payload
        0x7FF0_0000_0000_0001, // sNaN (min payload)
        0xFFF0_0000_0000_0001, // negative sNaN
        0x7FF7_FFFF_FFFF_FFFF, // sNaN max payload
        0x7FF0_0000_ABCD_0000, // sNaN with payload
    ];
    let mut nan_ok = 0usize;
    for &b in nans {
        let jit = callb(b);
        let jv = f32::from_bits(jit);
        assert!(
            jv.is_nan(),
            "FPTrunc of NaN f64 {b:#018x} must be NaN, got {jit:#010x}"
        );
        let want = oracle_fptrunc_bits(b);
        assert_eq!(
            jit, want,
            "FPTrunc NaN payload DIVERGES from runtime `as f32` at f64 {b:#018x}: \
             jit={jit:#010x} want={want:#010x}"
        );
        // narrowed NaN must be quiet (top mantissa bit of the f32 result set).
        assert_ne!(jit & 0x0040_0000, 0, "narrowed NaN must be quiet");
        nan_ok += 1;
    }
    assert_eq!(nan_ok, nans.len());
    eprintln!(
        "FPTrunc SPECIALS: +-0 -> +-0 (sign preserved), +-inf -> +-inf, and all {nan_ok} \
         qNaN/sNaN f64 -> quiet f32 NaN, payload MSBs truncated, bit-exact vs runtime \
         `x as f32`. FcvtDS special-value handling faithful."
    );
}

// ============================================================================
// TEST 7 — ARMED CONTROLS: the differential is load-bearing.
//   (a) FPTrunc actually ROUNDS (loses information): an f64 needing >24 mantissa
//       bits, narrowed then widened back, must DIFFER from the original f64 — so a
//       no-op / wrong-precision lowering would fail this. FPExt of the SAME rounded
//       f32 is EXACT, proving the two ops are genuinely distinct precisions.
//   (b) OVERFLOW is real inf, not a clamp (a saturating narrow would diverge).
//   (c) round-trip identity: an EXACTLY-representable f32 survives f32->f64->f32.
// ============================================================================
#[test]
fn armed_controls_round_trip_and_precision() {
    let mut mt = TrustIrModule::new("ctrl_tr".to_string());
    build_fptrunc(0, "tr", &mut mt);
    let buft = jit_buffer(&mt);
    let tr: F32FromBits = unsafe { std::mem::transmute(bind(&buft, "tr")) };

    let mut me = TrustIrModule::new("ctrl_ext".to_string());
    build_fpext(0, "ext", &mut me);
    let bufe = jit_buffer(&me);
    let ext: F64FromBits = unsafe { std::mem::transmute(bind(&bufe, "ext")) };

    let trunc = |x: f64| -> f32 { f32::from_bits(unsafe { tr(x.to_bits()) }.to_bits()) };
    let widen = |x: f32| -> f64 { f64::from_bits(unsafe { ext(x.to_bits()) }.to_bits()) };

    // (a) FPTrunc LOSES INFORMATION on a value needing >24 mantissa bits.
    let x = 16777217.0f64; // 2^24 + 1, exact in f64, NOT representable in f32
    let narrowed = trunc(x); // must round to 16777216.0
    assert_eq!(narrowed.to_bits(), 0x4b80_0000, "2^24+1 narrows to 2^24");
    let back = widen(narrowed); // FPExt is EXACT: 16777216.0
    assert_eq!(back, 16777216.0, "FPExt of the narrowed f32 is exact");
    assert_ne!(
        back, x,
        "ROUNDING CONTROL DEAD: f64->f32->f64 preserved 2^24+1 — FPTrunc did not round \
         (a no-op or wrong-precision lowering would leak the low bit)"
    );
    // FPExt of that f32 is exact (its own round-trip is lossless), unlike FPTrunc's.
    assert_eq!(
        widen(narrowed) as f32,
        narrowed,
        "FPExt/FPTrunc round-trip of an f32-exact value"
    );

    // (b) OVERFLOW is inf, NOT a saturating clamp to f32::MAX.
    let big = 1e300f64;
    let nb = trunc(big);
    assert!(nb.is_infinite(), "1e300 narrows to +inf");
    assert_ne!(
        nb.to_bits() & 0x7FFF_FFFF,
        f32::MAX.to_bits(),
        "OVERFLOW CONTROL DEAD: 1e300 clamped to f32::MAX instead of +inf"
    );

    // (c) round-trip identity for EXACTLY-representable f32 values (widen then narrow).
    for &fb in &[
        1.0f32.to_bits(),
        0.5f32.to_bits(),
        0x4048_f5c3u32, // exact f32 encoding of 3.14
        f32::MAX.to_bits(),
        0x0000_0001u32,
    ] {
        let f = f32::from_bits(fb);
        let round_trip = trunc(widen(f)); // f32 -> f64 (exact) -> f32 (must be identity)
        assert_eq!(
            round_trip.to_bits(),
            fb,
            "f32->f64->f32 identity failed at {fb:#010x}"
        );
    }

    // (d) FPTrunc vs FPExt are DISTINCT ops on the same input value: FPExt(2^24) is
    //     exact (2^24), while FPTrunc(2^24+1) rounds to 2^24 — i.e. narrowing moved
    //     the value off 2^24+1 (information lost) whereas widening never does.
    assert_eq!(
        widen(16777216.0f32),
        16777216.0,
        "FPExt exact (no rounding ever)"
    );
    assert_eq!(
        trunc(16777217.0).to_bits(),
        0x4b80_0000,
        "FPTrunc rounded 2^24+1 down to 2^24"
    );
    assert_ne!(
        trunc(16777217.0).to_bits(),
        0x4b80_0001,
        "PRECISION CONTROL: FPTrunc must ROUND 2^24+1 to 2^24 (0x4b80_0000), not leak a \
         low bit into a bogus 0x4b80_0001 — proving narrowing is not a bit-copy"
    );

    eprintln!(
        "ARMED CONTROLS: FPTrunc genuinely ROUNDS (2^24+1 -> 2^24, round-trip diverges from \
         the original f64); FPExt is EXACT (its round-trip is lossless); overflow is +inf \
         NOT an f32::MAX clamp; f32->f64->f32 is the identity on exact values. The two \
         precisions are distinct and load-bearing."
    );
}

// ============================================================================
// TEST 8 — FALSIFICATION: the JIT==oracle differential would CATCH a wrong
//   narrowing. A plausible-but-BROKEN f64->f32 lowering that merely CHOPS the low
//   mantissa bits (truncation, no round-to-nearest) is modeled here; on rounding
//   inputs it produces DIFFERENT bits from BOTH the correct JIT result and the Rust
//   `as` oracle. This proves the clean bill above is load-bearing: if FcvtDS rounded
//   wrongly (or lowered to a mantissa chop), Tests 3-6 would fire. It also confirms
//   the JIT genuinely ROUNDS (matches oracle, not the chop) on those same inputs.
// ============================================================================
#[test]
fn falsification_chop_model_would_be_caught() {
    let mut m = TrustIrModule::new("fptrunc_falsify".to_string());
    build_fptrunc(0, "tr", &mut m);
    let buf = jit_buffer(&m);
    let tr: F32FromBits = unsafe { std::mem::transmute(bind(&buf, "tr")) };
    let call = |x: f64| -> u32 { unsafe { tr(x.to_bits()) }.to_bits() };

    // The BROKEN model: reinterpret the f64, keep sign+exponent (re-biased) and the
    // TOP 23 mantissa bits, DROP the low 29 — i.e. round-toward-zero-ish chop with no
    // RNE. Only defined for finite in-range normals (enough to exhibit divergence).
    fn chop_narrow(x: f64) -> u32 {
        let b = x.to_bits();
        let sign = ((b >> 63) & 1) as u32;
        let exp = ((b >> 52) & 0x7FF) as i64;
        let mant = b & 0x000F_FFFF_FFFF_FFFF;
        let e = exp - 1023 + 127; // rebias f64->f32
        assert!(e > 0 && e < 255, "chop model only for in-range normals");
        let mant23 = (mant >> 29) as u32; // CHOP: drop low 29, no rounding
        (sign << 31) | ((e as u32) << 23) | mant23
    }

    // Inputs whose correct RNE result ROUNDS UP (so the chop, which rounds down,
    // differs from both the JIT and the oracle).
    let round_up_inputs: &[f64] = &[
        16777216.0 + 3.0,               // 2^24+3 -> RNE 2^24+4; chop -> 2^24+2
        1.0 + 3.0 * 2f64.powi(-24),     // -> RNE 1+2^-22; chop -> 1+2^-23
        1.0 + 7.0 * 2f64.powi(-25),     // rounds up
        100.0 + 100.0 * 2f64.powi(-24), // rounds up near 100
    ];
    let mut caught = 0usize;
    for &x in round_up_inputs {
        let jit = call(x);
        let want = oracle_fptrunc_bits(x.to_bits());
        let chop = chop_narrow(x);
        // JIT is CORRECT (rounds like the oracle)...
        assert_eq!(
            jit, want,
            "JIT must equal oracle at x={x:e}: jit={jit:#010x} want={want:#010x}"
        );
        // ...and the BROKEN chop model DIFFERS from both -> the audit would catch it.
        assert_ne!(
            jit, chop,
            "FALSIFICATION FAILED: the round-to-nearest JIT result equals the chop model at \
             x={x:e} — the differential could not distinguish a no-round lowering"
        );
        assert_ne!(
            want, chop,
            "oracle must also differ from the chop model at x={x:e}"
        );
        // and specifically: correct rounds UP, chop rounds DOWN (differ by 1 ulp).
        assert_eq!(
            jit.wrapping_sub(chop),
            1,
            "correct = chop + 1 ulp (rounded up) at x={x:e}"
        );
        caught += 1;
    }
    assert!(caught >= 4);
    eprintln!(
        "FALSIFICATION: on {caught} round-up inputs the JIT matches the Rust `as` oracle \
         (genuine RNE) and DIVERGES by exactly 1 ulp from a mantissa-chop (no-round) model — \
         so a broken/round-toward-zero FcvtDS lowering WOULD be caught by Tests 3-6. The clean \
         bill is load-bearing, not a vacuous pass."
    );
}
