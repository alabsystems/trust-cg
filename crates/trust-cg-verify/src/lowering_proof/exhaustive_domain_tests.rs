// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::verify::VerificationStrength;

fn obligation(widths: &[u32]) -> ProofObligation {
    ProofObligation {
        name: format!("complete_input_domain_{widths:?}"),
        trust_ir_expr: SmtExpr::bv_const(0, 64),
        aarch64_expr: SmtExpr::bv_const(0, 64),
        inputs: widths
            .iter()
            .enumerate()
            .map(|(index, width)| (format!("x{index}"), *width))
            .collect(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(TransvalCheckKind::InstructionLowering),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

#[test]
fn input_domain_budget_counts_all_widths_without_more_default_work() {
    let config = VerificationConfig::default();
    for widths in [vec![16], vec![8, 8], vec![3, 5, 8], vec![1; 16]] {
        let proof = obligation(&widths);
        assert_eq!(exhaustive_input_count(&proof, &config), Some(65_536));
        assert!(matches!(
            VerificationStrength::for_obligation_with_config(&proof, &config),
            VerificationStrength::Exhaustive
        ));
    }
    for widths in [vec![17], vec![8, 16], vec![16, 8], vec![1; 17]] {
        let proof = obligation(&widths);
        assert_eq!(exhaustive_input_count(&proof, &config), None);
        assert!(matches!(
            VerificationStrength::for_obligation_with_config(&proof, &config),
            VerificationStrength::Statistical { .. }
        ));
    }
}

#[test]
fn input_domain_budget_preserves_explicit_configuration_and_checks_overflow() {
    let mut config = VerificationConfig {
        exhaustive_threshold: 1,
        ..VerificationConfig::default()
    };
    assert_eq!(exhaustive_input_count(&obligation(&[2]), &config), Some(4));
    assert_eq!(
        exhaustive_input_count(&obligation(&[1, 1]), &config),
        Some(4)
    );
    assert_eq!(exhaustive_input_count(&obligation(&[1, 2]), &config), None);
    config.exhaustive_threshold = 16;
    assert_eq!(
        exhaustive_input_count(&obligation(&[16, 16]), &config),
        Some(1u64 << 32)
    );
    config.exhaustive_threshold = u32::MAX;
    assert_eq!(
        exhaustive_input_count(&obligation(&[32, 32]), &config),
        None
    );
    assert_eq!(exhaustive_input_count(&obligation(&[64]), &config), None);
}

#[test]
fn incomplete_or_ambiguous_domains_never_claim_exhaustive_strength() {
    let mut proofs = vec![obligation(&[]), obligation(&[0]), obligation(&[128])];
    let mut duplicate = obligation(&[1, 1]);
    duplicate.inputs[1].0 = duplicate.inputs[0].0.clone();
    proofs.push(duplicate);
    let mut fp = obligation(&[1]);
    fp.fp_inputs.push(("f".into(), 8, 24));
    proofs.push(fp);
    for proof in proofs {
        assert_eq!(
            exhaustive_input_count(&proof, &VerificationConfig::default()),
            None
        );
        assert!(!VerificationStrength::for_obligation(&proof).is_complete());
    }
}

#[test]
fn mixed_width_exhaustion_reaches_values_above_the_first_input_width() {
    let mut proof = obligation(&[1, 9]);
    let small = SmtExpr::var("x0", 1).zero_ext(8);
    let wide = SmtExpr::var("x1", 9);
    proof.trust_ir_expr = small.clone().bvxor(wide.clone());
    proof.aarch64_expr = small.bvxor(wide.bvand(SmtExpr::bv_const(255, 9)));
    let config = VerificationConfig::with_sample_count(0);
    assert_eq!(exhaustive_input_count(&proof, &config), Some(1024));
    assert!(matches!(
        verify_by_evaluation_with_config(&proof, &config),
        VerificationResult::Invalid { .. }
    ));
    let compiled = CompiledObligation::try_new(&proof).expect("integer tapes compile");
    for tapes in [None, Some(&compiled)] {
        assert!(matches!(
            verify_by_evaluation_with_compiled(&proof, &config, tapes),
            VerificationResult::Invalid { .. }
        ));
    }
}

#[test]
fn three_input_exhaustion_refutes_a_fault_at_every_independent_tuple() {
    let config = VerificationConfig::with_sample_count(0);
    for fault in 0..64 {
        let mut proof = obligation(&[1, 2, 3]);
        let packed = SmtExpr::var("x0", 1)
            .zero_ext(63)
            .bvor(
                SmtExpr::var("x1", 2)
                    .zero_ext(62)
                    .bvshl(SmtExpr::bv_const(1, 64)),
            )
            .bvor(
                SmtExpr::var("x2", 3)
                    .zero_ext(61)
                    .bvshl(SmtExpr::bv_const(3, 64)),
            );
        proof.aarch64_expr = SmtExpr::ite(
            packed.eq_expr(SmtExpr::bv_const(fault, 64)),
            SmtExpr::bv_const(1, 64),
            SmtExpr::bv_const(0, 64),
        );
        assert_eq!(exhaustive_input_count(&proof, &config), Some(64));
        let compiled = CompiledObligation::try_new(&proof).expect("tuple tapes compile");
        for tapes in [None, Some(&compiled)] {
            assert!(
                matches!(
                    verify_by_evaluation_with_compiled(&proof, &config, tapes),
                    VerificationResult::Invalid { .. }
                ),
                "missed tuple {fault}"
            );
        }
    }
}

#[test]
fn bounded_exhaustion_keeps_vacuous_identity_out_of_the_memo_shortcut() {
    for widths in [vec![16], vec![1, 2, 3]] {
        let mut proof = obligation(&widths);
        proof
            .preconditions
            .push(SmtExpr::bv_const(0, 1).eq_expr(SmtExpr::bv_const(1, 1)));
        let config = VerificationConfig::with_sample_count(0);
        assert!(matches!(
            verify_by_evaluation_with_config(&proof, &config),
            VerificationResult::Unknown { .. }
        ));
        assert!(matches!(
            memoized_verify_by_evaluation(&proof, &config),
            VerificationResult::Unknown { .. }
        ));
    }
}

#[test]
fn mixed_width_sampling_uses_each_declared_domain_when_budget_is_exceeded() {
    let mut proof = obligation(&[1, 17]);
    let wide = SmtExpr::var("x1", 17);
    proof.trust_ir_expr = wide.clone();
    proof.aarch64_expr = wide.bvand(SmtExpr::bv_const(1, 17));
    let config = VerificationConfig::with_sample_count(0);
    assert!(exhaustive_input_count(&proof, &config).is_none());
    assert!(matches!(
        verify_by_evaluation_with_config(&proof, &config),
        VerificationResult::Invalid { .. }
    ));
    assert!(!VerificationStrength::for_obligation(&proof).is_complete());
}

#[test]
fn movn_forms_receive_complete_input_enumeration_not_statistical_credit() {
    let config = VerificationConfig::for_proof_promotion();
    for &(width, shift) in crate::const_materialize_proofs::MOVN_FORMS {
        let proof = crate::const_materialize_proofs::proof_movn_halfword(width, shift);
        assert_eq!(exhaustive_input_count(&proof, &config), Some(65_536));
        let (result, strength) = discharge_registry_obligation(&proof, &config);
        assert!(
            matches!(result, VerificationResult::Valid),
            "{}",
            proof.name
        );
        assert!(matches!(strength, VerificationStrength::Exhaustive));
        let mut wrong = proof.clone();
        wrong.aarch64_expr = wrong.aarch64_expr.bvxor(SmtExpr::bv_const(1, 64));
        assert!(matches!(
            verify_by_evaluation_with_config(&wrong, &config),
            VerificationResult::Invalid { .. }
        ));
    }
}
