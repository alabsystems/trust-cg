//! Classification in the operand's IEEE format, not the evaluator's f64 carrier.
//! Integer exponent fields are the independent oracle. These are finite tests;
//! only the binary16 bit-pattern domain is exhaustively enumerated.
use std::collections::HashMap;

use trust_cg_verify::lowering_proof::{
    VerificationConfig, proof_fcmp_lt_f32, verify_by_evaluation_with_config,
};
use trust_cg_verify::smt::{EvalResult, SmtExpr};
use trust_cg_verify::verify::VerificationResult;

fn audit(eb: u32, sb: u32, values: impl Iterator<Item = u64>, expected_count: usize) {
    let exponent_mask = (1_u64 << eb) - 1;
    let raw = SmtExpr::bv_bits_to_fp(SmtExpr::var("raw", eb + sb), eb, sb).fp_is_normal();
    let mut env = HashMap::from([("raw".into(), 0)]);
    let (mut cases, mut mismatches, mut normals) = (0, 0, 0);
    let mut examples = Vec::new();
    for bits in values {
        let exponent = (bits >> (sb - 1)) & exponent_mask;
        let expected = exponent != 0 && exponent != exponent_mask;
        normals += usize::from(expected);
        env.insert("raw".into(), bits);
        let constant = SmtExpr::fp_const(bits, eb, sb).fp_is_normal();
        for (kind, tree) in [("raw", &raw), ("constant", &constant)] {
            let actual = tree.try_eval(&env);
            if !matches!(&actual, Ok(EvalResult::Bool(value)) if *value == expected) {
                mismatches += 1;
                if examples.len() < 8 {
                    examples.push(format!(
                        "{kind} bits={bits:x} expected={expected} actual={actual:?}"
                    ));
                }
            }
        }
        cases += 1;
    }
    assert_eq!(cases, expected_count);
    assert!(normals > 0 && normals < cases);
    eprintln!(
        "IEEE({eb},{sb}) cases={cases} checks={} normal_cases={normals} mismatches={mismatches}",
        cases * 2
    );
    assert_eq!(mismatches, 0, "{examples:?}");
}

#[test]
fn binary16_is_normal_exhausts_all_raw_and_constant_patterns() {
    audit(5, 11, 0..=u16::MAX as u64, 65_536);
}

#[test]
fn binary32_is_normal_checks_every_exponent_and_sign_with_boundary_fractions() {
    let values = (0..256_u64).flat_map(|exponent| {
        [0, 1_u64 << 31].into_iter().flat_map(move |sign| {
            [0, 1, 0x0040_0000, 0x007f_ffff]
                .into_iter()
                .map(move |fraction| sign | (exponent << 23) | fraction)
        })
    });
    audit(8, 24, values, 2_048);
}

#[test]
fn binary64_is_normal_checks_every_exponent_and_sign_with_boundary_fractions() {
    let values = (0..2048_u64).flat_map(|exponent| {
        [0, 1_u64 << 63].into_iter().flat_map(move |sign| {
            [0, 1, 0x0008_0000_0000_0000, 0x000f_ffff_ffff_ffff]
                .into_iter()
                .map(move |fraction| sign | (exponent << 52) | fraction)
        })
    });
    audit(11, 53, values, 16_384);
}

#[test]
fn normal_is_not_finite_nonzero_and_normal_preconditions_use_source_width() {
    let mut proof = proof_fcmp_lt_f32();
    proof.inputs = vec![("a_bits".into(), 32)];
    proof.fp_inputs.clear();
    let a = SmtExpr::bv_bits_to_fp(SmtExpr::var("a_bits", 32), 8, 24);
    let materialize =
        |predicate| SmtExpr::ite(predicate, SmtExpr::bv_const(1, 1), SmtExpr::bv_const(0, 1));
    proof.trust_ir_expr = materialize(a.clone().fp_is_normal());
    proof.aarch64_expr = materialize(
        a.clone()
            .fp_is_zero()
            .not_expr()
            .and_expr(a.clone().fp_is_inf().not_expr())
            .and_expr(a.clone().fp_is_nan().not_expr()),
    );
    let config = VerificationConfig::with_sample_count(0);
    let result = verify_by_evaluation_with_config(&proof, &config);
    assert!(
        matches!(result, VerificationResult::Invalid { .. }),
        "nonzero F32 subnormals refute normal == finite_nonzero: {result:?}"
    );
    // Under a genuinely normal-input precondition, both predicates are true.
    // The old widened-carrier classifier wrongly admitted subnormals.
    proof.preconditions = vec![a.fp_is_normal()];
    assert!(matches!(
        verify_by_evaluation_with_config(&proof, &config),
        VerificationResult::Valid
    ));
    let env = HashMap::from([("a_bits".into(), 1)]);
    assert_eq!(
        proof.preconditions[0].try_eval(&env).unwrap(),
        EvalResult::Bool(false)
    );
}

#[test]
fn normal_rejects_non_fp_and_unsupported_fp_operand_sorts() {
    for operand in [SmtExpr::bv_const(1, 32), SmtExpr::fp_const(1, 6, 10)] {
        assert!(operand.fp_is_normal().try_eval(&HashMap::new()).is_err());
    }
}
