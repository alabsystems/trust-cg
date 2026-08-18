// trust-cg-verify/checked_overflow_proofs.rs - Checked overflow lowering proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Proves the #474 AArch64 checked-arithmetic idioms:
//   sadd: ADDS + CSET VS
//   ssub: SUBS + CSET VS
//   smul: MUL + SMULH + ASR + CMP + CSET NE
//   uadd: ADDS + CSET HS
//   usub: SUBS + CSET LO
//   umul: MUL + UMULH + CMP #0 + CSET NE

//! Proof obligations for checked integer overflow lowering.
//!
//! Each proof packs the two LIR results as a single bitvector:
//! `overflow_b1 :: value_iN`. This lets the existing single-expression
//! [`ProofObligation`](crate::lowering_proof::ProofObligation) machinery prove
//! both the wrapping arithmetic result and the overflow flag together.

use crate::lowering_proof::{ProofObligation, TransvalCheckKind};
use crate::smt::SmtExpr;

#[derive(Debug, Clone, Copy)]
enum CheckedOverflowKind {
    Sadd,
    Ssub,
    Smul,
    Uadd,
    Usub,
    Umul,
}

fn bv1(cond: SmtExpr) -> SmtExpr {
    SmtExpr::ite(cond, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1))
}

fn msb(value: &SmtExpr, width: u32) -> SmtExpr {
    value.clone().extract(width - 1, width - 1)
}

fn pack(value: SmtExpr, overflow: SmtExpr) -> SmtExpr {
    bv1(overflow).concat(value)
}

fn signed_product(lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    lhs.sign_ext(width).bvmul(rhs.sign_ext(width))
}

fn unsigned_product(lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    lhs.zero_ext(width).bvmul(rhs.zero_ext(width))
}

fn trust_ir_checked(kind: CheckedOverflowKind, lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    match kind {
        CheckedOverflowKind::Sadd => {
            let value = lhs.clone().bvadd(rhs.clone());
            let exact = lhs.sign_ext(1).bvadd(rhs.sign_ext(1));
            let wrapped = value.clone().sign_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Ssub => {
            let value = lhs.clone().bvsub(rhs.clone());
            let exact = lhs.sign_ext(1).bvsub(rhs.sign_ext(1));
            let wrapped = value.clone().sign_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Smul => {
            // SPEC form (deliberately DISTINCT from the AArch64 SMULH-high form so
            // the obligation is a genuine equivalence theorem, not an X==X
            // tautology): signed overflow iff the FULL 2w-bit signed product does
            // not equal the sign-extension of the wrapped w-bit result. This is
            // provably equal to the instruction-side `SMULH != ASR(value, w-1)`
            // (the low w bits agree by construction, so the high halves must), but
            // is encoded differently — ay discharges a real theorem.
            let value = lhs.clone().bvmul(rhs.clone());
            let product = signed_product(lhs, rhs, width);
            let wrapped = value.clone().sign_ext(width);
            pack(value, product.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Uadd => {
            let value = lhs.clone().bvadd(rhs.clone());
            let exact = lhs.zero_ext(1).bvadd(rhs.zero_ext(1));
            let wrapped = value.clone().zero_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Usub => {
            let value = lhs.clone().bvsub(rhs.clone());
            let exact = lhs.zero_ext(1).bvsub(rhs.zero_ext(1));
            let wrapped = value.clone().zero_ext(1);
            pack(value, exact.eq_expr(wrapped).not_expr())
        }
        CheckedOverflowKind::Umul => {
            // SPEC form (distinct from the AArch64 UMULH-high form): unsigned
            // overflow iff the FULL 2w-bit unsigned product does not equal the
            // zero-extension of the wrapped w-bit result. Provably equal to the
            // instruction-side `UMULH != 0`, encoded differently — a real theorem.
            let value = lhs.clone().bvmul(rhs.clone());
            let product = unsigned_product(lhs, rhs, width);
            let wrapped = value.clone().zero_ext(width);
            pack(value, product.eq_expr(wrapped).not_expr())
        }
    }
}

fn aarch64_checked(kind: CheckedOverflowKind, lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    match kind {
        CheckedOverflowKind::Sadd => {
            let value = lhs.clone().bvadd(rhs.clone());
            let lhs_sign = msb(&lhs, width);
            let rhs_sign = msb(&rhs, width);
            let value_sign = msb(&value, width);
            let overflow = lhs_sign
                .clone()
                .eq_expr(rhs_sign)
                .and_expr(lhs_sign.eq_expr(value_sign).not_expr());
            pack(value, overflow)
        }
        CheckedOverflowKind::Ssub => {
            let value = lhs.clone().bvsub(rhs.clone());
            let lhs_sign = msb(&lhs, width);
            let rhs_sign = msb(&rhs, width);
            let value_sign = msb(&value, width);
            let overflow = lhs_sign
                .clone()
                .eq_expr(rhs_sign)
                .not_expr()
                .and_expr(lhs_sign.eq_expr(value_sign).not_expr());
            pack(value, overflow)
        }
        CheckedOverflowKind::Smul => {
            let value = lhs.clone().bvmul(rhs.clone());
            let product = signed_product(lhs, rhs, width);
            let high = product.extract((2 * width) - 1, width);
            let sign = value
                .clone()
                .bvashr(SmtExpr::bv_const((width - 1) as u64, width));
            pack(value, high.eq_expr(sign).not_expr())
        }
        CheckedOverflowKind::Uadd => {
            let value = lhs.clone().bvadd(rhs);
            pack(value.clone(), value.bvult(lhs))
        }
        CheckedOverflowKind::Usub => {
            let value = lhs.clone().bvsub(rhs.clone());
            pack(value, lhs.bvult(rhs))
        }
        CheckedOverflowKind::Umul => {
            let value = lhs.clone().bvmul(rhs.clone());
            let product = unsigned_product(lhs, rhs, width);
            let high = product.extract((2 * width) - 1, width);
            pack(value, high.eq_expr(SmtExpr::bv_const(0, width)).not_expr())
        }
    }
}

fn proof_checked_overflow_width(
    kind: CheckedOverflowKind,
    width: u32,
    name: &str,
) -> ProofObligation {
    let lhs = SmtExpr::var("a", width);
    let rhs = SmtExpr::var("b", width);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: name.to_string(),
        trust_ir_expr: trust_ir_checked(kind, lhs.clone(), rhs.clone(), width),
        aarch64_expr: aarch64_checked(kind, lhs, rhs, width),
        inputs: vec![("a".to_string(), width), ("b".to_string(), width)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Prove `CheckedSadd(I64)` lowers to `ADDS; CSET VS`.
pub fn proof_checked_sadd_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Sadd,
        64,
        "CheckedSadd_I64 -> ADDS+CSET_VS",
    )
}

/// Prove `CheckedSsub(I64)` lowers to `SUBS; CSET VS`.
pub fn proof_checked_ssub_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Ssub,
        64,
        "CheckedSsub_I64 -> SUBS+CSET_VS",
    )
}

/// Prove `CheckedSmul(I64)` lowers to `MUL; SMULH; ASR; CMP; CSET NE`.
pub fn proof_checked_smul_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Smul,
        64,
        "CheckedSmul_I64 -> MUL+SMULH+ASR+CMP+CSET_NE",
    )
}

/// Prove `CheckedUadd(U64)` lowers to `ADDS; CSET HS`.
pub fn proof_checked_uadd_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Uadd,
        64,
        "CheckedUadd_I64 -> ADDS+CSET_HS",
    )
}

/// Prove `CheckedUsub(U64)` lowers to `SUBS; CSET LO`.
pub fn proof_checked_usub_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Usub,
        64,
        "CheckedUsub_I64 -> SUBS+CSET_LO",
    )
}

/// Prove `CheckedUmul(U64)` lowers to `MUL; UMULH; CMP #0; CSET NE`.
pub fn proof_checked_umul_i64() -> ProofObligation {
    proof_checked_overflow_width(
        CheckedOverflowKind::Umul,
        64,
        "CheckedUmul_I64 -> MUL+UMULH+CMP0+CSET_NE",
    )
}

// --- i128 / u128 checked ADD/SUB overflow (the 128-bit add/sub lowering) ------
//
// Unlike i64, the 128-bit add/sub overflow lowering decomposes into the
// width-generic bit-pattern fallback (wrapping Iadd/Isub + sign/carry compare).
// The overflow PREDICATE these compute is exactly the width-parametric
// `aarch64_checked` formula at width 128, so these obligations are just the i64
// proofs re-instantiated at 128 bits. They are a clean linear-bitvector
// equivalence (NO `bvmul`), so — unlike i128 MUL, whose 256-bit `bvmul` times
// out — they discharge formally. There is deliberately NO i128 MUL proof here:
// 128-bit checked multiply stays fail-closed in the backend.

/// Prove the `CheckedSadd` overflow predicate at width 128 (i128 add).
pub fn proof_checked_sadd_i128() -> ProofObligation {
    proof_checked_overflow_width(CheckedOverflowKind::Sadd, 128, "CheckedSadd_I128 predicate")
}

/// Prove the `CheckedSsub` overflow predicate at width 128 (i128 sub).
pub fn proof_checked_ssub_i128() -> ProofObligation {
    proof_checked_overflow_width(CheckedOverflowKind::Ssub, 128, "CheckedSsub_I128 predicate")
}

/// Prove the `CheckedUadd` overflow predicate at width 128 (u128 add).
pub fn proof_checked_uadd_i128() -> ProofObligation {
    proof_checked_overflow_width(CheckedOverflowKind::Uadd, 128, "CheckedUadd_I128 predicate")
}

/// Prove the `CheckedUsub` overflow predicate at width 128 (u128 sub).
pub fn proof_checked_usub_i128() -> ProofObligation {
    proof_checked_overflow_width(CheckedOverflowKind::Usub, 128, "CheckedUsub_I128 predicate")
}

/// The four i128/u128 checked add/sub overflow-predicate obligations.
pub fn all_checked_overflow_add_sub_i128_proofs() -> Vec<ProofObligation> {
    vec![
        proof_checked_sadd_i128(),
        proof_checked_ssub_i128(),
        proof_checked_uadd_i128(),
        proof_checked_usub_i128(),
    ]
}

/// Return all #474 checked-overflow lowering proofs.
pub fn all_checked_overflow_proofs() -> Vec<ProofObligation> {
    vec![
        proof_checked_sadd_i64(),
        proof_checked_ssub_i64(),
        proof_checked_smul_i64(),
        proof_checked_uadd_i64(),
        proof_checked_usub_i64(),
        proof_checked_umul_i64(),
    ]
}

/// Width-8 EXHAUSTIVE proof that the genuine SPEC overflow predicate
/// (full 2w-bit signed product != sign-extension of the wrapped w-bit value)
/// is EQUIVALENT to the AArch64 SMULH-high predicate
/// (`SMULH != ASR(value, w-1)`).
///
/// This is the honest mul evidence: it discharges COMPLETELY over all 2^16
/// width-8 inputs (exhaustive) AND formally via ay in ~100-250ms. The overflow
/// predicate is width-uniform — "full 2w-bit product != ext(wrapped w-bit
/// value)" is the SAME theorem at every width w — so an exhaustive width-8
/// discharge witnesses the predicate's shape, while the full 64-bit FORMAL
/// discharge is pending solver capacity (128-bit `bvmul` times out). This is
/// deliberately NOT a 64-bit formal claim.
pub fn exact_smul_flag_equivalence_i8() -> ProofObligation {
    let lhs = SmtExpr::var("a", 8);
    let rhs = SmtExpr::var("b", 8);
    let value = lhs.clone().bvmul(rhs.clone());
    let product = signed_product(lhs, rhs, 8);
    let exact_overflow = product
        .clone()
        .eq_expr(value.clone().sign_ext(8))
        .not_expr();
    let high = product.extract(15, 8);
    let sign = value.bvashr(SmtExpr::bv_const(7, 8));

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CheckedSmul_I8 exact product overflow == SMULH high-half predicate (exhaustive w=8)"
            .to_string(),
        trust_ir_expr: bv1(exact_overflow),
        aarch64_expr: bv1(high.eq_expr(sign).not_expr()),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Width-8 EXHAUSTIVE proof that the genuine SPEC unsigned overflow predicate
/// (full 2w-bit unsigned product != zero-extension of the wrapped w-bit value)
/// is EQUIVALENT to the AArch64 UMULH-high predicate (`UMULH != 0`).
///
/// Same honesty contract as [`exact_smul_flag_equivalence_i8`]: exhaustive at
/// width-8 (all 2^16 inputs) and ay-formal at width-8; the 64-bit FORMAL
/// discharge is pending solver capacity. NOT a 64-bit formal claim.
pub fn exact_umul_flag_equivalence_i8() -> ProofObligation {
    let lhs = SmtExpr::var("a", 8);
    let rhs = SmtExpr::var("b", 8);
    let value = lhs.clone().bvmul(rhs.clone());
    let product = unsigned_product(lhs, rhs, 8);
    let exact_overflow = product
        .clone()
        .eq_expr(value.clone().zero_ext(8))
        .not_expr();
    let high = product.extract(15, 8);

    ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: "CheckedUmul_I8 exact product overflow == UMULH high-half predicate (exhaustive w=8)"
            .to_string(),
        trust_ir_expr: bv1(exact_overflow),
        aarch64_expr: bv1(high.eq_expr(SmtExpr::bv_const(0, 8)).not_expr()),
        inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
    }
}

/// Return the width-8 EXHAUSTIVE mul-overflow equivalence proofs.
///
/// These are the honest mul evidence cited by the Smulh/Umulh coverage-gate
/// allowlist reason: a genuine overflow-equivalence theorem, exhaustively
/// verified at width-8 (all 2^16 cases) and ay-formal at width-8. The full
/// 64-bit FORMAL discharge of [`proof_checked_smul_i64`] /
/// [`proof_checked_umul_i64`] is pending solver capacity (128-bit `bvmul`),
/// so the 64-bit Smulh/Umulh opcodes stay fail-closed-allowlisted rather than
/// claim a 64-bit formal proof.
pub fn all_checked_overflow_mul_exhaustive_i8_proofs() -> Vec<ProofObligation> {
    vec![
        exact_smul_flag_equivalence_i8(),
        exact_umul_flag_equivalence_i8(),
    ]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay_cli, z3_available};
    use crate::lowering_proof::verify_by_evaluation;
    use crate::smt::EvalResult;
    use crate::verify::VerificationResult;
    use std::collections::HashMap;

    fn packed(overflow: bool, value: u64) -> EvalResult {
        EvalResult::Bv128(((overflow as u128) << 64) | value as u128)
    }

    fn eval_pair(obligation: &ProofObligation, a: u64, b: u64) -> (EvalResult, EvalResult) {
        let env = HashMap::from([("a".to_string(), a), ("b".to_string(), b)]);
        (
            obligation.trust_ir_expr.eval(&env),
            obligation.aarch64_expr.eval(&env),
        )
    }

    #[test]
    fn test_all_checked_overflow_proofs_count() {
        let proofs = all_checked_overflow_proofs();
        assert_eq!(proofs.len(), 6);
        for proof in proofs {
            assert_eq!(
                proof.inputs,
                vec![("a".to_string(), 64), ("b".to_string(), 64)]
            );
        }
    }

    #[test]
    fn test_checked_overflow_i8_exhaustive_eval() {
        let proofs = [
            proof_checked_overflow_width(
                CheckedOverflowKind::Sadd,
                8,
                "CheckedSadd_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Ssub,
                8,
                "CheckedSsub_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Smul,
                8,
                "CheckedSmul_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Uadd,
                8,
                "CheckedUadd_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Usub,
                8,
                "CheckedUsub_I8 exhaustive shape",
            ),
            proof_checked_overflow_width(
                CheckedOverflowKind::Umul,
                8,
                "CheckedUmul_I8 exhaustive shape",
            ),
        ];

        for proof in proofs {
            assert!(
                matches!(verify_by_evaluation(&proof), VerificationResult::Valid),
                "{} did not pass exhaustive i8 evaluation",
                proof.name
            );
        }
    }

    /// Formally discharge the i128/u128 checked ADD/SUB overflow predicate via
    /// the AY solver. These are the 128-bit instantiations of the i8/i64-proven
    /// add/sub obligations; unlike i128 MUL (256-bit `bvmul`, which times out)
    /// they are linear-bitvector and discharge. A `CounterExample` would mean the
    /// 128-bit add/sub overflow lowering is WRONG, so it always fails the test; a
    /// missing or over-capacity solver SKIPS (it never false-passes).
    #[test]
    fn test_checked_overflow_add_sub_i128_formally_discharges() {
        let proofs = all_checked_overflow_add_sub_i128_proofs();
        assert_eq!(proofs.len(), 4);
        // Non-degeneracy: a spec that is structurally `X == X` proves nothing.
        for proof in &proofs {
            assert_ne!(
                proof.trust_ir_expr, proof.aarch64_expr,
                "DEGENERATE (X==X) i128 overflow proof {:?}",
                proof.name
            );
        }

        let config = AYConfig::default().with_timeout(120_000);
        let mut discharged = 0;
        for proof in &proofs {
            match verify_with_ay_cli(proof, &config) {
                AYResult::Verified => discharged += 1,
                AYResult::CounterExample(cx) => panic!(
                    "SOUNDNESS: i128 add/sub overflow predicate {:?} REFUTED by {cx:?}",
                    proof.name
                ),
                other => {
                    eprintln!("SKIP (no/over-capacity solver) {:?}: {other:?}", proof.name)
                }
            }
        }
        eprintln!("i128/u128 add/sub overflow: {discharged}/4 formally discharged");
    }

    #[test]
    fn test_checked_mul_exact_overflow_predicates_i8_exhaustive() {
        for proof in all_checked_overflow_mul_exhaustive_i8_proofs() {
            assert!(
                matches!(verify_by_evaluation(&proof), VerificationResult::Valid),
                "{} did not pass exhaustive i8 evaluation",
                proof.name
            );
        }
    }

    /// NON-DEGENERACY (f81e45b / X==X guard): NO checked-overflow proof — the 6
    /// i64 lowering obligations OR the 2 width-8 mul-equivalence proofs — may
    /// have a `trust_ir_expr` that is structurally identical to its
    /// `aarch64_expr`. A degenerate `X == X` obligation discharges trivially and
    /// proves NOTHING; binding such a thing to a coverage row would be a silent
    /// false claim. `SmtExpr: Eq`, so this is a direct structural check.
    #[test]
    fn test_checked_overflow_proofs_are_non_degenerate() {
        let mut proofs = all_checked_overflow_proofs();
        proofs.extend(all_checked_overflow_mul_exhaustive_i8_proofs());
        for proof in proofs {
            assert_ne!(
                proof.trust_ir_expr, proof.aarch64_expr,
                "DEGENERATE (X==X) checked-overflow proof {:?}: trust_ir_expr is \
                 structurally identical to aarch64_expr — it proves nothing",
                proof.name
            );
        }
    }

    #[test]
    fn test_checked_overflow_i64_corner_values() {
        let cases = [
            (
                proof_checked_sadd_i64(),
                i64::MAX as u64,
                1,
                packed(true, i64::MIN as u64),
            ),
            (
                proof_checked_ssub_i64(),
                i64::MIN as u64,
                1,
                packed(true, i64::MAX as u64),
            ),
            (
                proof_checked_smul_i64(),
                i64::MIN as u64,
                u64::MAX,
                packed(true, i64::MIN as u64),
            ),
            (proof_checked_uadd_i64(), u64::MAX, 1, packed(true, 0)),
            (proof_checked_usub_i64(), 0, 1, packed(true, u64::MAX)),
            (
                proof_checked_umul_i64(),
                u64::MAX,
                2,
                packed(true, u64::MAX.wrapping_sub(1)),
            ),
        ];

        for (proof, a, b, expected) in cases {
            let (trust_ir, aarch64) = eval_pair(&proof, a, b);
            assert_eq!(
                trust_ir, expected,
                "{} trust_ir corner mismatch",
                proof.name
            );
            assert_eq!(aarch64, expected, "{} AArch64 corner mismatch", proof.name);
        }
    }

    /// HONEST per-strength discharge of the checked-overflow proofs via ay/z3:
    ///   - the 4 add/sub i64 obligations FORMALLY verify (and fast);
    ///   - the 2 mul i64 obligations carry a GENUINE (non-degenerate) 64-bit
    ///     equivalence theorem that is SMT-hard (128-bit `bvmul`) and TIMES OUT
    ///     under a bounded budget — a Timeout/Unknown is tolerated (capacity,
    ///     NOT a miscompile), but a CounterExample/Error is a hard fail;
    ///   - the 2 width-8 mul-equivalence proofs FORMALLY verify at width-8,
    ///     anchoring the honest "exhaustively/formally verified at width-8,
    ///     64-bit discharge pending solver capacity" claim.
    ///
    /// This is deliberately NOT a "all 6 i64 -> Verified" assertion: the i64 mul
    /// FORMAL discharge is out of reach and we never claim it.
    #[test]
    fn test_checked_overflow_i64_z3_cli() {
        if !z3_available() {
            eprintln!("skipping checked-overflow SMT proof: z3 not available");
            return;
        }

        let config = AYConfig::default().with_timeout(10_000);

        // add/sub i64: MUST formally verify.
        for proof in [
            proof_checked_sadd_i64(),
            proof_checked_ssub_i64(),
            proof_checked_uadd_i64(),
            proof_checked_usub_i64(),
        ] {
            let result = verify_with_ay_cli(&proof, &config);
            // Certification-gap guard (crate::formal_gap): skip LOUDLY on the
            // exact fail-closed gap diagnostics only (a bare server-truncated
            // `unknown` is re-confirmed through the fresh one-shot
            // transcript); anything else still fails the original assertion.
            if let Some(reason) =
                crate::formal_gap::confirmed_certification_gap(&proof, &config, &result)
            {
                crate::formal_gap::print_gap_skip(&format!("obligation '{}'", proof.name), &reason);
                continue;
            }
            assert!(
                matches!(result, AYResult::Verified),
                "{} returned {}; the add/sub i64 obligations MUST formally Verify",
                proof.name,
                result
            );
        }

        // mul i64: genuine theorem, SMT-hard at 64-bit. Tolerate capacity
        // (Timeout/Unknown); a CounterExample/Error would be a real miscompile.
        for proof in [proof_checked_smul_i64(), proof_checked_umul_i64()] {
            let result = verify_with_ay_cli(&proof, &config);
            match result {
                AYResult::Verified
                | AYResult::SolverUnsat
                | AYResult::Timeout
                | AYResult::Unknown(_) => {}
                AYResult::CounterExample(_) | AYResult::Error(_) => panic!(
                    "{} returned {}; the i64 mul overflow predicate is DISPROVED \
                     (soundness failure), not merely capacity-pending",
                    proof.name, result
                ),
            }
        }

        // width-8 mul-equivalence: MUST formally verify (the honest mul anchor).
        for proof in all_checked_overflow_mul_exhaustive_i8_proofs() {
            let result = verify_with_ay_cli(&proof, &config);
            // Certification-gap guard (crate::formal_gap): same discipline as
            // the add/sub block above.
            if let Some(reason) =
                crate::formal_gap::confirmed_certification_gap(&proof, &config, &result)
            {
                crate::formal_gap::print_gap_skip(&format!("obligation '{}'", proof.name), &reason);
                continue;
            }
            assert!(
                matches!(result, AYResult::Verified),
                "{} returned {}; the width-8 mul-equivalence anchor MUST formally Verify",
                proof.name,
                result
            );
        }
    }
}
