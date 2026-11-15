use super::*;
use crate::ay_bridge::{AYConfig, generate_smt2_query_raw};
use crate::lowering_proof::{
    all_fp_lowering_proofs, proof_fdiv_f32, proof_fdiv_f64, proof_fsqrt_f64,
    verify_by_evaluation_with_config, verify_fp_by_evaluation,
};

#[test]
fn symbolic_fp_values_bind_all_eighteen_rows_and_run_default_samples() {
    let rows: Vec<_> = all_fp_lowering_proofs()
        .into_iter()
        .filter(applies)
        .collect();
    assert_eq!(rows.len(), 18);
    for obligation in rows {
        assert!(obligation.fp_inputs.is_empty());
        let query = generate_smt2_query_raw(&obligation, &AYConfig::default());
        let assertion = query
            .lines()
            .find(|line| line.starts_with("(assert "))
            .unwrap();
        for (name, _) in &obligation.inputs {
            assert!(
                assertion.contains(name),
                "{} has unbound {name}: {query}",
                obligation.name
            );
        }
        assert!(
            !assertion.contains("(fp #b"),
            "{} retained a zero placeholder",
            obligation.name
        );
        assert!(
            !obligation.is_genuinely_proven(),
            "symbolic model identities gain no lowering authority"
        );
        assert!(
            matches!(
                verify_by_evaluation_with_config(&obligation, &VerificationConfig::default()),
                VerificationResult::Valid
            ),
            "{}",
            obligation.name
        );
    }
}

#[test]
fn symbolic_fp_values_refute_swapped_division_and_zero_replacement() {
    for original in [proof_fdiv_f32(), proof_fdiv_f64()] {
        let mut swapped = original.clone();
        let SmtExpr::FPDiv { lhs, rhs, .. } = &mut swapped.aarch64_expr else {
            panic!("division")
        };
        std::mem::swap(lhs, rhs);
        assert!(matches!(
            verify_fp_by_evaluation(&swapped),
            VerificationResult::Invalid { .. }
        ));
        let mut zero = original;
        zero.aarch64_expr = if zero.inputs[0].1 == 32 {
            SmtExpr::fp32_const(0.0)
        } else {
            SmtExpr::fp64_const(0.0)
        };
        assert!(matches!(
            verify_fp_by_evaluation(&zero),
            VerificationResult::Invalid { .. }
        ));
    }
}

#[test]
fn symbolic_fp_values_refuse_malformed_bindings_modes_and_vacuous_conditions() {
    let original = proof_fsqrt_f64();
    for mutation in 0..9 {
        let mut obligation = original.clone();
        match mutation {
            0 => obligation.inputs.clear(),
            1 => obligation.inputs.push(obligation.inputs[0].clone()),
            2 => obligation.inputs[0].1 = 32,
            3 => obligation.fp_inputs.push(("unbound".into(), 11, 53)),
            4 => {
                obligation.trust_ir_expr = SmtExpr::fp64_const(0.0);
                obligation.aarch64_expr = obligation.trust_ir_expr.clone();
            }
            5 => {
                obligation.trust_ir_expr = SmtExpr::var("missing", 64);
                obligation.aarch64_expr = obligation.trust_ir_expr.clone();
            }
            6 => {
                let SmtExpr::FPSqrt { rm, .. } = &mut obligation.aarch64_expr else {
                    panic!("sqrt")
                };
                *rm = RoundingMode::RTZ;
            }
            7 => obligation.preconditions.push(SmtExpr::bool_const(false)),
            8 => obligation.preconditions.push(SmtExpr::var("missing", 1)),
            _ => unreachable!(),
        }
        assert!(
            matches!(
                verify_fp_by_evaluation(&obligation),
                VerificationResult::Unknown { .. }
            ),
            "mutation {mutation}"
        );
        assert!(
            matches!(
                verify_by_evaluation_with_config(
                    &obligation,
                    &VerificationConfig::with_sample_count(7)
                ),
                VerificationResult::Unknown { .. }
            ),
            "primary dispatch mutation {mutation}"
        );
    }
}

#[test]
fn symbolic_fp_values_final_random_sample_can_refute() {
    let mut obligation = proof_fsqrt_f64();
    obligation.name = "renamed operand-preserving value check".into();
    let config = VerificationConfig::with_sample_count(100_000);
    let mut state = sample_seed(&obligation.name);
    for _ in 0..config.sample_count {
        state = sample_lcg_step(state);
    }
    assert!(!checked_fcmp::edge_bits(64).contains(&state));
    let last = SmtExpr::var("fp_a_bits", 64).eq_expr(SmtExpr::bv_const(state, 64));
    // Infinity is distinct from the square root of every finite input, and
    // from NaN if this raw input is negative. Check the actual witness too.
    obligation.aarch64_expr = SmtExpr::ite(
        last,
        SmtExpr::fp64_const(f64::INFINITY),
        obligation.aarch64_expr,
    );
    let mut env = EvalEnv::default();
    env.insert("fp_a_bits".into(), state);
    assert!(matches!(
        check_point(&obligation, &env),
        Err(VerificationResult::Invalid { .. })
    ));
    assert!(matches!(
        verify(&obligation, &VerificationConfig::with_sample_count(99_999)),
        VerificationResult::Valid
    ));
    assert!(matches!(
        verify(&obligation, &config),
        VerificationResult::Invalid { .. }
    ));
}

#[test]
fn symbolic_fp_values_share_the_work_bound_with_conditions() {
    let mut obligation = proof_fsqrt_f64();
    let mut condition = SmtExpr::bool_const(true);
    for _ in 0..13 {
        condition = SmtExpr::And {
            lhs: std::sync::Arc::new(condition.clone()),
            rhs: std::sync::Arc::new(condition),
        };
    }
    obligation.preconditions.push(condition);
    assert!(matches!(
        verify_fp_by_evaluation(&obligation),
        VerificationResult::Unknown { .. }
    ));
    obligation.preconditions.clear();
    let mut value = obligation.aarch64_expr.clone();
    for _ in 0..130 {
        value = SmtExpr::FPNeg {
            operand: std::sync::Arc::new(value),
        };
    }
    obligation.aarch64_expr = value;
    assert!(matches!(
        verify_fp_by_evaluation(&obligation),
        VerificationResult::Unknown { .. }
    ));
}
