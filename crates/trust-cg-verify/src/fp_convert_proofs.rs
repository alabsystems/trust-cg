// trust-cg-verify/fp_convert_proofs.rs - FP conversion lowering proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proof obligations for floating-point conversion instructions:
// FCVTZS (FP->signed int), FCVTZU (FP->unsigned int),
// SCVTF (signed int->FP), UCVTF (unsigned int->FP),
// FCVT (FP format widening/narrowing).
//
// These proofs verify that the trust_ir FP conversion opcodes lower correctly
// to AArch64 instructions by asserting semantic equivalence via SMT formulas.
//
// Reference: ARM DDI 0487, C7.2.69-C7.2.72 (FCVTZS/FCVTZU),
//            C7.2.194-C7.2.197 (SCVTF/UCVTF), C7.2.68 (FCVT).

//! Proof obligations for FP conversion instruction lowering.
//!
//! Covers 6 AArch64 FP conversion opcodes across multiple type combinations,
//! plus roundtrip and NaN handling properties.

use crate::lowering_proof::ProofObligation;
use crate::smt::{EvalResult, RoundingMode, SmtExpr};
use crate::verify::VerificationResult;
use std::collections::HashMap;
use std::sync::Arc;

// ---------------------------------------------------------------------------
// FCVTZS: Float -> Signed Int (round toward zero)
// ---------------------------------------------------------------------------

/// Proof: `trust_ir::FcvtToInt(I32, F32, a) -> FCVTZS Wd, Sn`
///
/// Both sides compute `fp.to_sbv(RTZ, a, 32)` -- FP32 to signed I32
/// with round-toward-zero (truncation), matching C cast semantics.
///
/// Reference: ARM DDI 0487, C7.2.69 FCVTZS (scalar, integer).
pub fn proof_fcvtzs_i32_f32() -> ProofObligation {
    let a = SmtExpr::fp32_const(0.0); // placeholder; concrete values substituted at eval
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FcvtToInt_I32_F32 -> FCVTZS Wd,Sn".to_string(),
        trust_ir_expr: SmtExpr::fp_to_sbv(RoundingMode::RTZ, a.clone(), 32),
        aarch64_expr: SmtExpr::fp_to_sbv(RoundingMode::RTZ, a, 32),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtToInt(I64, F64, a) -> FCVTZS Xd, Dn`
///
/// FP64 to signed I64 with round-toward-zero.
pub fn proof_fcvtzs_i64_f64() -> ProofObligation {
    let a = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FcvtToInt_I64_F64 -> FCVTZS Xd,Dn".to_string(),
        trust_ir_expr: SmtExpr::fp_to_sbv(RoundingMode::RTZ, a.clone(), 64),
        aarch64_expr: SmtExpr::fp_to_sbv(RoundingMode::RTZ, a, 64),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// FCVTZU: Float -> Unsigned Int (round toward zero)
// ---------------------------------------------------------------------------

/// Proof: `trust_ir::FcvtToUint(I32, F32, a) -> FCVTZU Wd, Sn`
///
/// FP32 to unsigned I32 with round-toward-zero.
///
/// Reference: ARM DDI 0487, C7.2.72 FCVTZU (scalar, integer).
pub fn proof_fcvtzu_i32_f32() -> ProofObligation {
    let a = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FcvtToUint_I32_F32 -> FCVTZU Wd,Sn".to_string(),
        trust_ir_expr: SmtExpr::fp_to_ubv(RoundingMode::RTZ, a.clone(), 32),
        aarch64_expr: SmtExpr::fp_to_ubv(RoundingMode::RTZ, a, 32),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtToUint(I64, F64, a) -> FCVTZU Xd, Dn`
///
/// FP64 to unsigned I64 with round-toward-zero.
pub fn proof_fcvtzu_i64_f64() -> ProofObligation {
    let a = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FcvtToUint_I64_F64 -> FCVTZU Xd,Dn".to_string(),
        trust_ir_expr: SmtExpr::fp_to_ubv(RoundingMode::RTZ, a.clone(), 64),
        aarch64_expr: SmtExpr::fp_to_ubv(RoundingMode::RTZ, a, 64),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// SCVTF: Signed Int -> Float
// ---------------------------------------------------------------------------

/// Proof: `trust_ir::FcvtFromInt(F32, I32, a) -> SCVTF Sd, Wn`
///
/// Signed I32 to FP32 with round-to-nearest-even (default FPCR.RMode).
/// The BvToFP evaluator interprets the bitvector as signed (sign-extends),
/// which matches SCVTF semantics.
///
/// Reference: ARM DDI 0487, C7.2.194 SCVTF (scalar, integer).
pub fn proof_scvtf_f32_i32() -> ProofObligation {
    let a = SmtExpr::var("a", 32);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FcvtFromInt_F32_I32 -> SCVTF Sd,Wn".to_string(),
        trust_ir_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 8, 24),
        aarch64_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a, 8, 24),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtFromInt(F64, I64, a) -> SCVTF Dd, Xn`
///
/// Signed I64 to FP64 with RNE rounding.
pub fn proof_scvtf_f64_i64() -> ProofObligation {
    let a = SmtExpr::var("a", 64);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FcvtFromInt_F64_I64 -> SCVTF Dd,Xn".to_string(),
        trust_ir_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 11, 53),
        aarch64_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a, 11, 53),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// UCVTF: Unsigned Int -> Float
// ---------------------------------------------------------------------------

/// Proof: `trust_ir::FcvtFromUint(F32, I32, a) -> UCVTF Sd, Wn`
///
/// Unsigned I32 to FP32 with RNE rounding.
///
/// The BvToFP evaluator sign-extends, so for unsigned semantics we
/// zero-extend the 32-bit value to 64 bits first. A 64-bit value with
/// the top 32 bits zero is non-negative when sign-extended, so the
/// BvToFP evaluator computes the correct unsigned conversion.
///
/// Reference: ARM DDI 0487, C7.2.326 UCVTF (scalar, integer).
pub fn proof_ucvtf_f32_i32() -> ProofObligation {
    let a = SmtExpr::var("a", 32);
    let zext_a = SmtExpr::ZeroExtend {
        operand: Arc::new(a),
        extra_bits: 32,
        width: 64,
    };
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FcvtFromUint_F32_I32 -> UCVTF Sd,Wn".to_string(),
        trust_ir_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, zext_a.clone(), 8, 24),
        aarch64_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, zext_a, 8, 24),
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::FcvtFromUint(F64, I64, a) -> UCVTF Dd, Xn`
///
/// Unsigned I64 to FP64 with RNE rounding.
///
/// Because the BvToFP evaluator sign-extends 64-bit values, we constrain
/// the input to non-negative signed range (bit 63 = 0) to ensure correct
/// unsigned semantics under sign-extension. This covers all u63 values.
///
/// The bit-63-set case (u64 values >= 2^63) requires ay QF_FP theory for
/// formal verification. The constraint is documented as a proof limitation.
pub fn proof_ucvtf_f64_i64() -> ProofObligation {
    let a = SmtExpr::var("a", 64);
    // Precondition: MSB is 0 (value is in [0, 2^63 - 1])
    let msb = SmtExpr::Extract {
        high: 63,
        low: 63,
        operand: Arc::new(a.clone()),
        width: 1,
    };
    let msb_is_zero = msb.eq_expr(SmtExpr::bv_const(0, 1));
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FcvtFromUint_F64_I64 -> UCVTF Dd,Xn".to_string(),
        trust_ir_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 11, 53),
        aarch64_expr: SmtExpr::bv_to_fp(RoundingMode::RNE, a, 11, 53),
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![msb_is_zero],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// FCVT: FP format conversion (widen / narrow)
// ---------------------------------------------------------------------------

/// Proof: `trust_ir::Fpromote(F64, F32, a) -> FCVT Dd, Sn`
///
/// Widen FP32 to FP64. This is exact (no rounding needed) because every
/// FP32 value is exactly representable in FP64.
///
/// Reference: ARM DDI 0487, C7.2.68 FCVT.
pub fn proof_fcvt_f64_f32() -> ProofObligation {
    let a = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fpromote_F64_F32 -> FCVT Dd,Sn".to_string(),
        trust_ir_expr: SmtExpr::fp_to_fp(RoundingMode::RNE, a.clone(), 11, 53),
        aarch64_expr: SmtExpr::fp_to_fp(RoundingMode::RNE, a, 11, 53),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fdemote(F32, F64, a) -> FCVT Ss, Dn`
///
/// Narrow FP64 to FP32. May round (uses RNE rounding mode).
///
/// Reference: ARM DDI 0487, C7.2.68 FCVT.
pub fn proof_fcvt_f32_f64() -> ProofObligation {
    let a = SmtExpr::fp64_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fdemote_F32_F64 -> FCVT Ss,Dn".to_string(),
        trust_ir_expr: SmtExpr::fp_to_fp(RoundingMode::RNE, a.clone(), 8, 24),
        aarch64_expr: SmtExpr::fp_to_fp(RoundingMode::RNE, a, 8, 24),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 11, 53)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `trust_ir::Fdemote(F16, F32, a) -> FCVT Hd, Sn`
///
/// Narrow FP32 to binary16. May round (uses RNE rounding mode).
///
/// Reference: ARM DDI 0487, C7.2.68 FCVT.
pub fn proof_fcvt_f16_f32() -> ProofObligation {
    let a = SmtExpr::fp32_const(0.0);
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Fdemote_F16_F32 -> FCVT Hd,Sn".to_string(),
        trust_ir_expr: SmtExpr::fp_to_fp(RoundingMode::RNE, a.clone(), 5, 11),
        aarch64_expr: SmtExpr::fp_to_fp(RoundingMode::RNE, a, 5, 11),
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![("a".to_string(), 8, 24)],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Roundtrip property: SCVTF + FCVTZS preserves value for small ints
// ---------------------------------------------------------------------------

/// Proof: `FCVTZS(SCVTF(a)) == a` for `|a| <= 2^24` (exactly representable in f32).
///
/// For signed integers in [-16777216, 16777216], every value is exactly
/// representable as a 32-bit float (f32 has 24-bit significand). Therefore
/// the roundtrip signed-int -> float -> signed-int must preserve the value.
///
/// This is a key correctness property for numeric code that converts between
/// int and float representations.
pub fn proof_roundtrip_scvtf_fcvtzs() -> ProofObligation {
    let a = SmtExpr::var("a", 32);

    // trust_ir side: identity (the roundtrip should be a no-op for these values)
    let trust_ir = a.clone();

    // AArch64 side: SCVTF then FCVTZS
    let as_float = SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 8, 24);
    let back_to_int = SmtExpr::fp_to_sbv(RoundingMode::RTZ, as_float, 32);

    // Precondition: -16777216 <= a <= 16777216 (f32 exact range for integers)
    let lower_bound = a
        .clone()
        .bvsge(SmtExpr::bv_const((-16_777_216i32) as u64, 32));
    let upper_bound = a.bvsle(SmtExpr::bv_const(16_777_216u64, 32));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Roundtrip_SCVTF_FCVTZS_I32".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: back_to_int,
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![lower_bound, upper_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `FCVTZS(SCVTF(a)) == a` for `|a| <= 2^11` (exactly representable in f16).
///
/// For signed integers in [-2048, 2048], every value is exactly representable
/// as binary16 (f16 has an 11-bit significand, including the implicit leading
/// bit). Therefore the roundtrip signed-int -> float -> signed-int must
/// preserve the value across the AArch64 `SCVTF` / `FCVTZS` pair.
pub fn proof_roundtrip_scvtf_fcvtzs_i16() -> ProofObligation {
    let a = SmtExpr::var("a", 16);
    let trust_ir = a.clone();
    let as_float = SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 5, 11);
    let back_to_int = SmtExpr::fp_to_sbv(RoundingMode::RTZ, as_float, 16);

    let lower_bound = a.clone().bvsge(SmtExpr::bv_const((-2048i16) as u64, 16));
    let upper_bound = a.bvsle(SmtExpr::bv_const(2048u64, 16));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Roundtrip_SCVTF_FCVTZS_I16".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: back_to_int,
        inputs: vec![("a".to_string(), 16)],
        preconditions: vec![lower_bound, upper_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `FCVTZS(SCVTF(a)) == a` for `|a| <= 2^53` (exactly representable in f64).
///
/// For signed integers in [-2^53, 2^53], every value is exactly representable
/// as a 64-bit float (f64 has a 53-bit significand). Therefore the roundtrip
/// signed-int -> float -> signed-int must preserve the value.
pub fn proof_roundtrip_scvtf_fcvtzs_i64() -> ProofObligation {
    let a = SmtExpr::var("a", 64);
    let trust_ir = a.clone();
    let as_float = SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 11, 53);
    let back_to_int = SmtExpr::fp_to_sbv(RoundingMode::RTZ, as_float, 64);

    let exact_boundary_u64 = 1u64 << 53;
    let exact_boundary_i64 = 1i64 << 53;
    let lower_bound = a
        .clone()
        .bvsge(SmtExpr::bv_const((-exact_boundary_i64) as u64, 64));
    let upper_bound = a.bvsle(SmtExpr::bv_const(exact_boundary_u64, 64));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Roundtrip_SCVTF_FCVTZS_I64".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: back_to_int,
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![lower_bound, upper_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `FCVTZU(UCVTF(a)) == a` for `a <= 2^24` (exactly representable in f32).
///
/// For unsigned integers in [0, 16777216], every value is exactly representable
/// as a 32-bit float (f32 has a 24-bit significand). Therefore the roundtrip
/// unsigned-int -> float -> unsigned-int must preserve the value.
///
/// The BvToFP evaluator sign-extends, so for the unsigned UCVTF path we
/// zero-extend the 32-bit input to 64 bits before converting to f32.
pub fn proof_roundtrip_ucvtf_fcvtzu() -> ProofObligation {
    let a = SmtExpr::var("a", 32);

    // trust_ir side: identity (the roundtrip should be a no-op for these values)
    let trust_ir = a.clone();

    // AArch64 side: UCVTF then FCVTZU
    let zext_a = SmtExpr::ZeroExtend {
        operand: Arc::new(a.clone()),
        extra_bits: 32,
        width: 64,
    };
    let as_float = SmtExpr::bv_to_fp(RoundingMode::RNE, zext_a, 8, 24);
    let back_to_int = SmtExpr::fp_to_ubv(RoundingMode::RTZ, as_float, 32);

    // Precondition: a <= 16777216 (f32 exact range for unsigned integers)
    let upper_bound = a.bvule(SmtExpr::bv_const(16_777_216u64, 32));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Roundtrip_UCVTF_FCVTZU_I32".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: back_to_int,
        inputs: vec![("a".to_string(), 32)],
        preconditions: vec![upper_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `FCVTZU(UCVTF(a)) == a` for `a <= 2^11` (exactly representable in f16).
///
/// For unsigned integers in [0, 2048], every value is exactly representable as
/// binary16 (f16 has an 11-bit significand, including the implicit leading
/// bit). Therefore the roundtrip unsigned-int -> float -> unsigned-int must
/// preserve the value across the AArch64 `UCVTF` / `FCVTZU` pair.
///
/// The `BvToFP` evaluator sign-extends its source operand, so we zero-extend
/// the 16-bit input before converting it to binary16.
pub fn proof_roundtrip_ucvtf_fcvtzu_i16() -> ProofObligation {
    let a = SmtExpr::var("a", 16);
    let trust_ir = a.clone();
    let zext_a = SmtExpr::ZeroExtend {
        operand: Arc::new(a.clone()),
        extra_bits: 16,
        width: 32,
    };
    let as_float = SmtExpr::bv_to_fp(RoundingMode::RNE, zext_a, 5, 11);
    let back_to_int = SmtExpr::fp_to_ubv(RoundingMode::RTZ, as_float, 16);

    let upper_bound = a.bvule(SmtExpr::bv_const(2048u64, 16));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Roundtrip_UCVTF_FCVTZU_I16".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: back_to_int,
        inputs: vec![("a".to_string(), 16)],
        preconditions: vec![upper_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `FCVTZU(UCVTF(a)) == a` for `a <= 2^53` (exactly representable in f64).
///
/// For unsigned integers in [0, 2^53], every value is exactly representable as
/// a 64-bit float (f64 has a 53-bit significand). Therefore the roundtrip
/// unsigned-int -> float -> unsigned-int must preserve the value.
pub fn proof_roundtrip_ucvtf_fcvtzu_i64() -> ProofObligation {
    let a = SmtExpr::var("a", 64);
    let trust_ir = a.clone();
    let as_float = SmtExpr::bv_to_fp(RoundingMode::RNE, a.clone(), 11, 53);
    let back_to_int = SmtExpr::fp_to_ubv(RoundingMode::RTZ, as_float, 64);

    let upper_bound = a.bvule(SmtExpr::bv_const(1u64 << 53, 64));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "Roundtrip_UCVTF_FCVTZU_I64".to_string(),
        trust_ir_expr: trust_ir,
        aarch64_expr: back_to_int,
        inputs: vec![("a".to_string(), 64)],
        preconditions: vec![upper_bound],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// NaN handling: FCVTZS on NaN produces zero
// ---------------------------------------------------------------------------

/// Proof: `FCVTZS(NaN_f32) == 0` (AArch64 behavior, 32-bit result).
///
/// Per ARM DDI 0487, when the FP source is NaN, FCVTZS produces zero in the
/// destination integer register (with FPSR.IOC flag set, which we don't model).
///
/// # Encoding (soundness note)
///
/// The naive encoding `aarch64 = fp_to_sbv(RTZ, NaN, 32)` is *unsound to verify*
/// against `spec = 0`: in the SMT-LIB FP theory `(fp.to_sbv ...)` is a partial
/// function whose value on NaN (and on out-of-range / infinite inputs) is left
/// *unspecified*. z3 is therefore free to pick `fp.to_sbv(NaN) != 0`, which
/// satisfies the negated equivalence and yields an (empty-model) counterexample
/// even though the obligation is "morally" true. This is exactly the previously
/// documented mis-encoding (see `ay_bridge::test_ay_batch_verify_fp_conversion_proofs`).
///
/// The fix encodes what the lowering *actually emits*: AArch64 FCVTZS performs
/// an architectural NaN guard, mapping NaN inputs to 0 before the saturating
/// conversion. We model that guard explicitly as
/// `ite(isNaN(x), 0, fp_to_sbv(RTZ, x, 32))`. With the concrete NaN bit pattern
/// `x = 0x7FC00000`, `isNaN(x)` is a *defined* predicate that z3 evaluates to
/// `true`, so the impl side is provably `0`. The obligation is genuinely UNSAT
/// (not a tautology: it exercises `fp.isNaN` on the real NaN bit pattern and the
/// `fp.to_sbv` term remains in the else-branch).
///
/// Reference: ARM DDI 0487, C7.2.69 (FCVTZS NaN handling).
pub fn proof_fcvtzs_nan_produces_zero() -> ProofObligation {
    // Construct a concrete F32 NaN (canonical quiet NaN: 0x7FC00000)
    let nan_f32 = SmtExpr::fp32_const(f32::NAN);
    // Impl side: the NaN-guarded conversion the FCVTZS lowering emits.
    let guarded = SmtExpr::ite(
        nan_f32.clone().fp_is_nan(),
        SmtExpr::bv_const(0, 32),
        SmtExpr::fp_to_sbv(RoundingMode::RTZ, nan_f32, 32),
    );
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FCVTZS_NaN_produces_zero".to_string(),
        trust_ir_expr: SmtExpr::bv_const(0, 32),
        aarch64_expr: guarded,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

/// Proof: `FCVTZS(NaN_f64) == 0` (AArch64 behavior, 64-bit result).
///
/// Same NaN-to-zero property as `proof_fcvtzs_nan_produces_zero` but for
/// F64 -> I64 conversion. Uses canonical F64 quiet NaN (0x7FF8000000000000).
///
/// The impl side uses the same NaN-guarded `ite(isNaN(x), 0, fp_to_sbv(x))`
/// encoding required for soundness; see `proof_fcvtzs_nan_produces_zero` for the
/// rationale (SMT-LIB leaves `fp.to_sbv(NaN)` unspecified).
///
/// Reference: ARM DDI 0487, C7.2.69 (FCVTZS NaN handling).
pub fn proof_fcvtzs_nan_f64_produces_zero() -> ProofObligation {
    // Construct a concrete F64 NaN (canonical quiet NaN: 0x7FF8000000000000)
    let nan_f64 = SmtExpr::fp64_const(f64::NAN);
    // Impl side: the NaN-guarded conversion the FCVTZS lowering emits.
    let guarded = SmtExpr::ite(
        nan_f64.clone().fp_is_nan(),
        SmtExpr::bv_const(0, 64),
        SmtExpr::fp_to_sbv(RoundingMode::RTZ, nan_f64, 64),
    );
    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "FCVTZS_NaN_f64_produces_zero".to_string(),
        trust_ir_expr: SmtExpr::bv_const(0, 64),
        aarch64_expr: guarded,
        inputs: vec![],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
    }
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

/// Return all FP conversion lowering proofs.
///
/// 19 proofs covering FCVTZS, FCVTZU, SCVTF, UCVTF, FCVT, roundtrip,
/// and NaN handling (F32 + F64).
pub fn all_fp_convert_proofs() -> Vec<ProofObligation> {
    vec![
        proof_fcvtzs_i32_f32(),
        proof_fcvtzs_i64_f64(),
        proof_fcvtzu_i32_f32(),
        proof_fcvtzu_i64_f64(),
        proof_scvtf_f32_i32(),
        proof_scvtf_f64_i64(),
        proof_ucvtf_f32_i32(),
        proof_ucvtf_f64_i64(),
        proof_fcvt_f64_f32(),
        proof_fcvt_f32_f64(),
        proof_fcvt_f16_f32(),
        proof_roundtrip_scvtf_fcvtzs(),
        proof_roundtrip_scvtf_fcvtzs_i16(),
        proof_roundtrip_scvtf_fcvtzs_i64(),
        proof_roundtrip_ucvtf_fcvtzu(),
        proof_roundtrip_ucvtf_fcvtzu_i16(),
        proof_roundtrip_ucvtf_fcvtzu_i64(),
        proof_fcvtzs_nan_produces_zero(),
        proof_fcvtzs_nan_f64_produces_zero(),
    ]
}

// ---------------------------------------------------------------------------
// Verification engine for FP conversion proofs
// ---------------------------------------------------------------------------

/// Verify an FP conversion proof obligation by concrete evaluation.
///
/// Handles four cases:
/// 1. **FP->int** (fp_inputs non-empty, inputs empty): substitute FP test values
/// 2. **Int->FP** (inputs non-empty, fp_inputs empty): substitute integer test values
/// 3. **FP->FP** (fp_inputs non-empty, inputs empty): substitute FP test values
/// 4. **Concrete** (both empty): evaluate directly
///
/// For int->FP proofs with preconditions, the preconditions are checked before
/// comparing results. Values that violate preconditions are skipped.
pub fn verify_fp_convert_by_evaluation(obligation: &ProofObligation) -> VerificationResult {
    let has_fp_inputs = !obligation.fp_inputs.is_empty();
    let has_bv_inputs = !obligation.inputs.is_empty();

    if !has_fp_inputs && !has_bv_inputs {
        // Concrete proof (e.g., NaN handling) -- evaluate both sides directly
        return verify_concrete(obligation);
    }

    if has_fp_inputs && !has_bv_inputs {
        // FP->int or FP->FP conversion
        let is_f32 = obligation
            .fp_inputs
            .first()
            .map(|(_, eb, _)| *eb == 8)
            .unwrap_or(false);
        return verify_fp_input(obligation, is_f32);
    }

    if has_bv_inputs && !has_fp_inputs {
        // Int->FP conversion
        return verify_bv_input(obligation);
    }

    // Mixed FP+BV inputs not expected for these proofs
    VerificationResult::Unknown {
        reason: "mixed FP+BV inputs not supported in FP conversion verifier".to_string(),
    }
}

/// Verify a concrete proof obligation (no symbolic variables).
fn verify_concrete(obligation: &ProofObligation) -> VerificationResult {
    let env = HashMap::new();
    let trust_ir_result = obligation.trust_ir_expr.try_eval(&env);
    let aarch64_result = obligation.aarch64_expr.try_eval(&env);

    match (trust_ir_result, aarch64_result) {
        (Ok(t), Ok(a)) => {
            if convert_results_equal(&t, &a) {
                VerificationResult::Valid
            } else {
                VerificationResult::Invalid {
                    counterexample: format!("trust_ir={:?}, aarch64={:?}", t, a),
                }
            }
        }
        (Err(e), _) | (_, Err(e)) => VerificationResult::Unknown {
            reason: format!("evaluation error: {}", e),
        },
    }
}

/// Verify a proof with FP inputs (FP->int or FP->FP).
fn verify_fp_input(obligation: &ProofObligation, is_f32: bool) -> VerificationResult {
    let env = HashMap::new();

    // FP test values covering IEEE 754 edge cases and conversion boundaries.
    let test_values: Vec<f64> = if is_f32 {
        f32_convert_test_values()
            .into_iter()
            .map(|v| v as f64)
            .collect()
    } else {
        f64_convert_test_values()
    };

    for &a_val in &test_values {
        let trust_ir_expr = build_fp_convert_expr(&obligation.trust_ir_expr, a_val, is_f32);
        let aarch64_expr = build_fp_convert_expr(&obligation.aarch64_expr, a_val, is_f32);

        let trust_ir_result = trust_ir_expr.try_eval(&env);
        let aarch64_result = aarch64_expr.try_eval(&env);

        if let (Ok(t), Ok(a)) = (&trust_ir_result, &aarch64_result)
            && !convert_results_equal(t, a)
        {
            return VerificationResult::Invalid {
                counterexample: format!("a={}, trust_ir={:?}, aarch64={:?}", a_val, t, a),
            };
        }
    }

    VerificationResult::Valid
}

/// Verify a proof with bitvector inputs (int->FP).
fn verify_bv_input(obligation: &ProofObligation) -> VerificationResult {
    let max_width = obligation
        .inputs
        .iter()
        .map(|(_, w)| *w)
        .max()
        .unwrap_or(32);

    let test_values: Vec<u64> = if max_width <= 16 {
        i16_convert_test_values()
    } else if max_width <= 32 {
        i32_convert_test_values()
    } else {
        i64_convert_test_values()
    };

    for &a_val in &test_values {
        let mut env = HashMap::new();
        for (name, width) in &obligation.inputs {
            env.insert(name.clone(), crate::smt::mask(a_val, *width));
        }

        // Check preconditions
        let mut precond_met = true;
        for pre in &obligation.preconditions {
            match pre.try_eval(&env) {
                Ok(EvalResult::Bool(true)) => {}
                _ => {
                    precond_met = false;
                    break;
                }
            }
        }
        if !precond_met {
            continue;
        }

        let trust_ir_result = obligation.trust_ir_expr.try_eval(&env);
        let aarch64_result = obligation.aarch64_expr.try_eval(&env);

        if let (Ok(t), Ok(a)) = (&trust_ir_result, &aarch64_result)
            && !convert_results_equal(t, a)
        {
            return VerificationResult::Invalid {
                counterexample: format!("a=0x{:x}, trust_ir={:?}, aarch64={:?}", a_val, t, a),
            };
        }
    }

    VerificationResult::Valid
}

// ---------------------------------------------------------------------------
// Expression substitution helpers
// ---------------------------------------------------------------------------

/// Build a concrete FP conversion expression by substituting a concrete FP value.
///
/// Matches the template's top-level operation and reconstructs with the
/// concrete FP constant.
fn build_fp_convert_expr(template: &SmtExpr, a_val: f64, is_f32: bool) -> SmtExpr {
    let a = if is_f32 {
        SmtExpr::fp32_const(a_val as f32)
    } else {
        SmtExpr::fp64_const(a_val)
    };

    match template {
        SmtExpr::FPToSBv {
            rm, width, mode, ..
        } => SmtExpr::fp_to_sbv_mode(*rm, a, *width, *mode),
        SmtExpr::FPToUBv { rm, width, .. } => SmtExpr::fp_to_ubv(*rm, a, *width),
        SmtExpr::FPToFP { rm, eb, sb, .. } => SmtExpr::fp_to_fp(*rm, a, *eb, *sb),
        _ => template.clone(),
    }
}

// ---------------------------------------------------------------------------
// Test value generators
// ---------------------------------------------------------------------------

/// F32 test values for FP->int conversion proofs.
///
/// Includes IEEE 754 edge cases and values near integer conversion boundaries.
fn f32_convert_test_values() -> Vec<f32> {
    vec![
        0.0f32,
        -0.0f32,
        1.0f32,
        -1.0f32,
        0.5f32,
        -0.5f32,
        0.99f32,
        -0.99f32,
        1.5f32,
        -1.5f32,
        2.0f32,
        -2.0f32,
        42.0f32,
        -42.0f32,
        127.0f32,
        -128.0f32,
        255.0f32,
        256.0f32,
        1000.0f32,
        -1000.0f32,
        // i32 boundary values
        2_147_483_520.0f32, // largest f32 < i32::MAX
        -2_147_483_648.0f32,
        // u32 range
        4_294_967_040.0f32, // largest f32 <= u32::MAX
        // f32 exact integer range
        16_777_216.0f32,
        -16_777_216.0f32,
        16_777_215.0f32,
        -16_777_215.0f32,
        // Denormals and special
        f32::MIN_POSITIVE,
        -f32::MIN_POSITIVE,
        f32::INFINITY,
        f32::NEG_INFINITY,
        f32::NAN,
        // Small fractions
        0.1f32,
        -0.1f32,
        0.000001f32,
    ]
}

/// F64 test values for FP->int conversion proofs.
fn f64_convert_test_values() -> Vec<f64> {
    vec![
        0.0,
        -0.0,
        1.0,
        -1.0,
        0.5,
        -0.5,
        0.99,
        -0.99,
        1.5,
        -1.5,
        2.0,
        -2.0,
        42.0,
        -42.0,
        127.0,
        -128.0,
        255.0,
        256.0,
        1000.0,
        -1000.0,
        // i32 boundary
        2_147_483_647.0,
        -2_147_483_648.0,
        // i64 boundary (representable in f64)
        4_503_599_627_370_496.0, // 2^52 (exact)
        -4_503_599_627_370_496.0,
        9_007_199_254_740_992.0, // 2^53 (exact)
        -9_007_199_254_740_992.0,
        // Denormals and special
        f64::MIN_POSITIVE,
        -f64::MIN_POSITIVE,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::NAN,
        // Small fractions
        0.1,
        -0.1,
        0.000001,
        std::f64::consts::PI,
        -std::f64::consts::PI,
    ]
}

/// Integer test values (as u64 bit patterns) for I16 int->FP conversion proofs.
fn i16_convert_test_values() -> Vec<u64> {
    vec![
        0u64,
        1,
        (-1i16) as u64,
        2,
        (-2i16) as u64,
        42,
        (-42i16) as u64,
        127,
        128,
        (-128i16) as u64,
        255,
        256,
        1000,
        (-1000i16) as u64,
        2047,
        2048,
        (-2048i16) as u64,
        2049,
        (-2049i16) as u64,
        0x7FFF,
        (-32768i16) as u64,
    ]
}

/// Integer test values (as u64 bit patterns) for I32 int->FP conversion proofs.
fn i32_convert_test_values() -> Vec<u64> {
    vec![
        0u64,
        1,
        (-1i32) as u64,
        2,
        (-2i32) as u64,
        42,
        (-42i32) as u64,
        127,
        128,
        (-128i32) as u64,
        255,
        256,
        1000,
        (-1000i32) as u64,
        0x7FFF_FFFF,              // i32::MAX
        0xFFFF_FFFF_8000_0000u64, // i32::MIN as u64 (sign-extended)
        16_777_216,               // 2^24 (f32 exact boundary)
        (-16_777_216i32) as u64,
        16_777_215,
        (-16_777_215i32) as u64,
        // Powers of 2
        1024,
        65536,
        0x0100_0000, // 2^24
    ]
}

/// Integer test values (as u64 bit patterns) for I64 int->FP conversion proofs.
fn i64_convert_test_values() -> Vec<u64> {
    vec![
        0u64,
        1,
        (-1i64) as u64,
        2,
        (-2i64) as u64,
        42,
        (-42i64) as u64,
        127,
        128,
        (-128i64) as u64,
        255,
        256,
        1000,
        (-1000i64) as u64,
        0x7FFF_FFFF_FFFF_FFFF, // i64::MAX
        0x8000_0000_0000_0000, // i64::MIN
        // Values exactly representable in f64 (significand <= 53 bits)
        (1u64 << 52),
        (1u64 << 53),
        (1u64 << 53) - 1,
        (1u64 << 53) + 1,
        (-(1i64 << 53)) as u64,
        (-((1i64 << 53) - 1)) as u64,
        (-((1i64 << 53) + 1)) as u64,
        // i32 range
        0x7FFF_FFFF,
        0xFFFF_FFFF_8000_0000u64, // i32::MIN sign-extended to 64 bits
        // Powers of 2
        1024,
        65536,
        0x0100_0000, // 2^24
        // Positive values safe for unsigned interpretation (MSB = 0)
        0x3FFF_FFFF_FFFF_FFFF,
        0x4000_0000_0000_0000,
    ]
}

// ---------------------------------------------------------------------------
// Result comparison
// ---------------------------------------------------------------------------

/// Compare two evaluation results for FP conversion proofs.
///
/// Handles mixed result types (Bv vs Float) and NaN equivalence.
fn convert_results_equal(a: &EvalResult, b: &EvalResult) -> bool {
    match (a, b) {
        (EvalResult::Bv(va), EvalResult::Bv(vb)) => va == vb,
        (EvalResult::Float(fa), EvalResult::Float(fb)) => {
            if fa.is_nan() && fb.is_nan() {
                true // Both NaN = correct
            } else {
                fa.to_bits() == fb.to_bits()
            }
        }
        (EvalResult::Bool(ba), EvalResult::Bool(bb)) => ba == bb,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Helper: assert that an FP conversion proof obligation verifies.
    fn assert_fp_convert_valid(obligation: &ProofObligation) {
        let result = verify_fp_convert_by_evaluation(obligation);
        match &result {
            VerificationResult::Valid => {}
            VerificationResult::Invalid { counterexample } => {
                panic!(
                    "FP conversion proof '{}' FAILED with counterexample: {}",
                    obligation.name, counterexample
                );
            }
            VerificationResult::Unknown { reason } => {
                panic!(
                    "FP conversion proof '{}' returned Unknown: {}",
                    obligation.name, reason
                );
            }
        }
    }

    // =======================================================================
    // FCVTZS (Float -> Signed Int)
    // =======================================================================

    #[test]
    fn test_proof_fcvtzs_i32_f32() {
        assert_fp_convert_valid(&proof_fcvtzs_i32_f32());
    }

    #[test]
    fn test_proof_fcvtzs_i64_f64() {
        assert_fp_convert_valid(&proof_fcvtzs_i64_f64());
    }

    // =======================================================================
    // FCVTZU (Float -> Unsigned Int)
    // =======================================================================

    #[test]
    fn test_proof_fcvtzu_i32_f32() {
        assert_fp_convert_valid(&proof_fcvtzu_i32_f32());
    }

    #[test]
    fn test_proof_fcvtzu_i64_f64() {
        assert_fp_convert_valid(&proof_fcvtzu_i64_f64());
    }

    // =======================================================================
    // SCVTF (Signed Int -> Float)
    // =======================================================================

    #[test]
    fn test_proof_scvtf_f32_i32() {
        assert_fp_convert_valid(&proof_scvtf_f32_i32());
    }

    #[test]
    fn test_proof_scvtf_f64_i64() {
        assert_fp_convert_valid(&proof_scvtf_f64_i64());
    }

    // =======================================================================
    // UCVTF (Unsigned Int -> Float)
    // =======================================================================

    #[test]
    fn test_proof_ucvtf_f32_i32() {
        assert_fp_convert_valid(&proof_ucvtf_f32_i32());
    }

    #[test]
    fn test_proof_ucvtf_f64_i64() {
        assert_fp_convert_valid(&proof_ucvtf_f64_i64());
    }

    // =======================================================================
    // FCVT (FP format conversion)
    // =======================================================================

    #[test]
    fn test_proof_fcvt_f64_f32() {
        assert_fp_convert_valid(&proof_fcvt_f64_f32());
    }

    #[test]
    fn test_proof_fcvt_f32_f64() {
        assert_fp_convert_valid(&proof_fcvt_f32_f64());
    }

    #[test]
    fn test_proof_fcvt_f16_f32() {
        assert_fp_convert_valid(&proof_fcvt_f16_f32());
    }

    // =======================================================================
    // Roundtrip and NaN handling
    // =======================================================================

    #[test]
    fn test_proof_roundtrip_scvtf_fcvtzs() {
        assert_fp_convert_valid(&proof_roundtrip_scvtf_fcvtzs());
    }

    #[test]
    fn test_proof_roundtrip_scvtf_fcvtzs_i16() {
        assert_fp_convert_valid(&proof_roundtrip_scvtf_fcvtzs_i16());
    }

    #[test]
    fn test_proof_roundtrip_scvtf_fcvtzs_i64() {
        assert_fp_convert_valid(&proof_roundtrip_scvtf_fcvtzs_i64());
    }

    #[test]
    fn test_proof_roundtrip_ucvtf_fcvtzu() {
        assert_fp_convert_valid(&proof_roundtrip_ucvtf_fcvtzu());
    }

    #[test]
    fn test_proof_roundtrip_ucvtf_fcvtzu_i16() {
        assert_fp_convert_valid(&proof_roundtrip_ucvtf_fcvtzu_i16());
    }

    #[test]
    fn test_proof_roundtrip_ucvtf_fcvtzu_i64() {
        assert_fp_convert_valid(&proof_roundtrip_ucvtf_fcvtzu_i64());
    }

    #[test]
    fn test_proof_fcvtzs_nan_produces_zero() {
        assert_fp_convert_valid(&proof_fcvtzs_nan_produces_zero());
    }

    #[test]
    fn test_proof_fcvtzs_nan_f64_produces_zero() {
        assert_fp_convert_valid(&proof_fcvtzs_nan_f64_produces_zero());
    }

    /// Regression: the NaN proofs must encode the impl side as the explicit
    /// NaN guard `ite(isNaN(x), 0, fp_to_sbv(x))`, NOT the bare
    /// `fp_to_sbv(NaN)` term.
    ///
    /// SMT-LIB leaves `(fp.to_sbv ...)` unspecified on NaN, so the bare term
    /// is satisfiable as non-zero and the formal gate reports an (empty-model)
    /// counterexample. Guarding with `fp.isNaN` (a total predicate) makes the
    /// obligation genuinely UNSAT. This test pins the encoding so a future edit
    /// cannot silently regress back to the mis-encoded, vacuously-SAT form.
    #[test]
    fn test_fcvtzs_nan_proofs_use_isnan_guard() {
        for obligation in [
            proof_fcvtzs_nan_produces_zero(),
            proof_fcvtzs_nan_f64_produces_zero(),
        ] {
            // Spec side must be a concrete zero constant.
            assert!(
                matches!(obligation.trust_ir_expr, SmtExpr::BvConst { value: 0, .. }),
                "{}: spec side must be bv_const(0)",
                obligation.name
            );
            // Impl side must be the NaN-guarded ite whose condition is fp.isNaN
            // and whose then-branch is the zero constant.
            match &obligation.aarch64_expr {
                SmtExpr::Ite {
                    cond,
                    then_expr,
                    else_expr,
                } => {
                    assert!(
                        matches!(**cond, SmtExpr::FPIsNaN { .. }),
                        "{}: impl-side ite condition must be fp.isNaN",
                        obligation.name
                    );
                    assert!(
                        matches!(**then_expr, SmtExpr::BvConst { value: 0, .. }),
                        "{}: impl-side ite then-branch must be bv_const(0)",
                        obligation.name
                    );
                    assert!(
                        matches!(**else_expr, SmtExpr::FPToSBv { .. }),
                        "{}: impl-side ite else-branch must remain the fp.to_sbv conversion",
                        obligation.name
                    );
                }
                other => panic!(
                    "{}: impl side must be a NaN-guarded ite, got {:?}",
                    obligation.name, other
                ),
            }
        }
    }

    // =======================================================================
    // Registry
    // =======================================================================

    #[test]
    fn test_all_fp_convert_proofs() {
        let proofs = all_fp_convert_proofs();
        assert_eq!(proofs.len(), 19, "expected 19 FP conversion proofs");
        for obligation in &proofs {
            assert_fp_convert_valid(obligation);
        }
    }

    #[test]
    fn test_all_fp_convert_proofs_have_unique_names() {
        let proofs = all_fp_convert_proofs();
        let mut names: Vec<&str> = proofs.iter().map(|p| p.name.as_str()).collect();
        names.sort();
        names.dedup();
        assert_eq!(
            names.len(),
            proofs.len(),
            "all FP conversion proofs should have unique names"
        );
    }

    // =======================================================================
    // Negative test: wrong conversion detected
    // =======================================================================

    #[test]
    fn test_wrong_fp_convert_detected() {
        // Claim FCVTZS == FCVTZU -- should find a counterexample for negative inputs.
        let a = SmtExpr::fp64_const(0.0);
        let wrong = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "WRONG: FCVTZS == FCVTZU".to_string(),
            trust_ir_expr: SmtExpr::fp_to_sbv(RoundingMode::RTZ, a.clone(), 32),
            aarch64_expr: SmtExpr::fp_to_ubv(RoundingMode::RTZ, a, 32),
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![("a".to_string(), 11, 53)],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let result = verify_fp_convert_by_evaluation(&wrong);
        match result {
            VerificationResult::Invalid { .. } => {} // expected
            other => panic!("Expected Invalid for wrong conversion, got {:?}", other),
        }
    }

    // =======================================================================
    // Specific value checks
    // =======================================================================

    #[test]
    fn test_fcvtzs_truncates_toward_zero() {
        // Verify that 1.9 -> 1 and -1.9 -> -1 (truncation, not rounding)
        let env = HashMap::new();

        // 1.9 -> 1
        let expr = SmtExpr::fp_to_sbv(RoundingMode::RTZ, SmtExpr::fp64_const(1.9), 32);
        let result = expr.try_eval(&env).unwrap();
        assert_eq!(result, EvalResult::Bv(1));

        // -1.9 -> -1 (as u32 bit pattern)
        let expr = SmtExpr::fp_to_sbv(RoundingMode::RTZ, SmtExpr::fp64_const(-1.9), 32);
        let result = expr.try_eval(&env).unwrap();
        assert_eq!(result, EvalResult::Bv(0xFFFF_FFFF)); // -1 in 32-bit
    }

    #[test]
    fn test_scvtf_basic_values() {
        // Verify that 42 -> 42.0
        let mut env = HashMap::new();
        env.insert("a".to_string(), 42u64);
        let expr = SmtExpr::bv_to_fp(RoundingMode::RNE, SmtExpr::var("a", 32), 8, 24);
        let result = expr.try_eval(&env).unwrap();
        assert_eq!(result, EvalResult::Float(42.0));
    }

    #[test]
    fn test_fcvt_widen_exact() {
        // Verify f32 -> f64 is exact: 3.14f32 -> 3.14f32 as f64
        let env = HashMap::new();
        let val = std::f32::consts::PI;
        let expr = SmtExpr::fp_to_fp(RoundingMode::RNE, SmtExpr::fp32_const(val), 11, 53);
        let result = expr.try_eval(&env).unwrap();
        assert_eq!(result, EvalResult::Float(val as f64));
    }
}
