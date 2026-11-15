use super::*;
use crate::smt::SmtSort;

fn arithmetic(width: u32) -> ProofObligation {
    let a = SmtExpr::var("a", width);
    let b = SmtExpr::var("b", width);
    ProofObligation {
        name: format!("fallible evaluator control {width}"),
        trust_ir_expr: a.clone().bvadd(b.clone()),
        aarch64_expr: b.bvadd(a),
        inputs: vec![("a".into(), width), ("b".into(), width)],
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: Some(TransvalCheckKind::DataFlow),
        machine_side_provenance: MachineSideProvenance::StaticDb,
    }
}

fn unknown(result: VerificationResult, name: &str) {
    assert!(
        matches!(result, VerificationResult::Unknown { ref reason } if reason.contains(name)),
        "expected explicit unknown identifying {name}, got {result:?}"
    );
}

#[test]
fn unsupported_source_and_machine_results_are_unknown() {
    for width in [4, 64] {
        for source in [false, true] {
            let mut obligation = arithmetic(width);
            let expression = SmtExpr::uf("unsupported_result", vec![], SmtSort::BitVec(width));
            if source {
                obligation.trust_ir_expr = expression;
            } else {
                obligation.aarch64_expr = expression;
            }
            unknown(
                verify_by_evaluation_with_config(
                    &obligation,
                    &VerificationConfig::with_sample_count(8),
                ),
                "unsupported_result",
            );
        }
    }
}

#[test]
fn unsupported_precondition_cannot_credit_identical_results() {
    for width in [4, 64] {
        let mut obligation = arithmetic(width);
        obligation.aarch64_expr = obligation.trust_ir_expr.clone();
        obligation
            .preconditions
            .push(SmtExpr::uf("unsupported_guard", vec![], SmtSort::Bool));
        unknown(
            verify_by_evaluation_with_config(
                &obligation,
                &VerificationConfig::with_sample_count(8),
            ),
            "unsupported_guard",
        );
    }
}

#[test]
fn missing_precondition_binding_is_unknown() {
    for width in [4, 64] {
        let mut obligation = arithmetic(width);
        obligation
            .preconditions
            .push(SmtExpr::var("absent", width).eq_expr(SmtExpr::bv_const(0, width)));
        unknown(
            verify_by_evaluation_with_config(
                &obligation,
                &VerificationConfig::with_sample_count(8),
            ),
            "absent",
        );
    }
}

#[test]
fn identical_unsupported_results_do_not_shortcut_to_valid() {
    let mut obligation = arithmetic(64);
    obligation.trust_ir_expr = SmtExpr::uf("identical_unsupported", vec![], SmtSort::BitVec(64));
    obligation.aarch64_expr = obligation.trust_ir_expr.clone();
    let config = VerificationConfig::with_sample_count(8);
    unknown(
        verify_by_evaluation_with_config(&obligation, &config),
        "identical_unsupported",
    );
    unknown(
        memoized_verify_by_evaluation(&obligation, &config),
        "identical_unsupported",
    );
}

#[test]
fn interpreted_chunk_paths_propagate_unsupported_evaluation() {
    for in_precondition in [false, true] {
        let mut obligation = arithmetic(64);
        if in_precondition {
            obligation
                .preconditions
                .push(SmtExpr::uf("chunk_guard", vec![], SmtSort::Bool));
        } else {
            obligation.aarch64_expr = SmtExpr::uf("chunk_result", vec![], SmtSort::BitVec(64));
        }
        let mut env = EvalEnv::default();
        env.insert("a".into(), 0);
        env.insert("b".into(), 0);
        let expected = if in_precondition {
            "chunk_guard"
        } else {
            "chunk_result"
        };
        unknown(
            random_chunk_2(&obligation, None, 64, 17, 5, 1, &env).expect_err("terminal unknown"),
            expected,
        );
        unknown(
            random_chunk_multi(&obligation, None, 17, 5, 1, &env).expect_err("terminal unknown"),
            expected,
        );
    }
}

#[test]
fn arbitrary_memory_frame_remains_unknown_to_concrete_evaluation() {
    let obligation = crate::source_bound_frame::frame_obligation();
    unknown(
        verify_by_evaluation_with_config(&obligation, &VerificationConfig::with_sample_count(8)),
        "entry_memory",
    );
}

#[test]
fn supported_arithmetic_keeps_compiled_and_interpreted_positive_verdicts() {
    for width in [4, 64] {
        let obligation = arithmetic(width);
        let config = VerificationConfig::with_sample_count(8);
        assert!(CompiledObligation::try_new(&obligation).is_some());
        assert!(matches!(
            verify_by_evaluation_with_config(&obligation, &config),
            VerificationResult::Valid
        ));
        assert!(matches!(
            verify_by_evaluation_with_compiled(&obligation, &config, None),
            VerificationResult::Valid
        ));
    }
}

#[test]
fn genuine_arithmetic_counterexamples_remain_refuted() {
    for width in [4, 64] {
        let mut obligation = arithmetic(width);
        obligation.aarch64_expr = SmtExpr::var("a", width).bvsub(SmtExpr::var("b", width));
        let config = VerificationConfig::with_sample_count(8);
        assert!(matches!(
            verify_by_evaluation_with_config(&obligation, &config),
            VerificationResult::Invalid { .. }
        ));
        assert!(matches!(
            verify_by_evaluation_with_compiled(&obligation, &config, None),
            VerificationResult::Invalid { .. }
        ));
    }
}

#[test]
fn false_preconditions_remain_unmet_on_exhaustive_path() {
    let mut obligation = arithmetic(4);
    obligation.preconditions.push(SmtExpr::bool_const(false));
    assert!(matches!(
        verify_by_evaluation_with_config(&obligation, &VerificationConfig::default()),
        VerificationResult::Unknown { .. }
    ));
}
