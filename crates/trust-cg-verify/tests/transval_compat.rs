#![cfg(feature = "trust-types-bridge")]

use trust_cg_verify::smt::trust_formula_adapter::FormulaAdapterContext;
use trust_cg_verify::transval_compat::{
    TransvalCheckResult, TransvalCompatError, TransvalValidationStrength,
    TransvalValidationVerdict, refinement_vc_to_proof_obligation,
    verification_report_to_validation_json, verification_report_to_validation_result,
};
use trust_cg_verify::{
    MachineSideProvenance, ProofResult, SmtExpr, TransvalCheckKind, VerificationReport,
    VerificationResult, VerificationStrength,
};
use trust_types::{BlockId, CheckKind, Formula, RefinementVc, Sort, TranslationCheck};

fn var(name: &str, sort: Sort) -> Formula {
    Formula::Var(name.to_string(), sort)
}

fn bv_var(name: &str, width: u32) -> Formula {
    var(name, Sort::BitVec(width))
}

fn vc(kind: CheckKind, formula: Formula, description: &str) -> RefinementVc {
    RefinementVc {
        check: TranslationCheck {
            source_point: BlockId(0),
            target_point: BlockId(1),
            kind,
            formula,
            description: description.to_string(),
        },
        source_function: "source_fn".to_string(),
        target_function: "target_fn".to_string(),
    }
}

#[test]
fn data_flow_refinement_vc_converts_to_proof_obligation() {
    let ctx = FormulaAdapterContext::new()
        .with_bv_var("src_a", 32)
        .with_bv_var("src_b", 32)
        .with_bv_var("dst_a", 32)
        .with_bv_var("dst_b", 32);
    let formula = Formula::Eq(
        Box::new(Formula::BvAdd(
            Box::new(bv_var("src_a", 32)),
            Box::new(bv_var("src_b", 32)),
            32,
        )),
        Box::new(Formula::BvAdd(
            Box::new(bv_var("dst_a", 32)),
            Box::new(bv_var("dst_b", 32)),
            32,
        )),
    );

    let obligation = refinement_vc_to_proof_obligation(
        &vc(CheckKind::DataFlow, formula, "i32 add dataflow"),
        &ctx,
    )
    .unwrap();

    assert_eq!(obligation.name, "i32 add dataflow");
    assert_eq!(obligation.category, Some(TransvalCheckKind::DataFlow));
    assert_eq!(
        obligation.machine_side_provenance,
        MachineSideProvenance::StaticDb
    );
    assert_eq!(
        obligation.inputs,
        vec![
            ("dst_a".to_string(), 32),
            ("dst_b".to_string(), 32),
            ("src_a".to_string(), 32),
            ("src_b".to_string(), 32),
        ]
    );
    assert!(obligation.preconditions.is_empty());
    assert!(matches!(obligation.trust_ir_expr, SmtExpr::BvAdd { .. }));
    assert!(matches!(obligation.aarch64_expr, SmtExpr::BvAdd { .. }));
}

#[test]
fn control_flow_refinement_vc_converts_bool_equivalence() {
    let ctx = FormulaAdapterContext::new()
        .with_bool_var("src_taken")
        .with_bool_var("dst_taken");
    let formula = Formula::Eq(
        Box::new(var("src_taken", Sort::Bool)),
        Box::new(var("dst_taken", Sort::Bool)),
    );

    let obligation = refinement_vc_to_proof_obligation(
        &vc(CheckKind::ControlFlow, formula, "branch condition"),
        &ctx,
    )
    .unwrap();

    assert_eq!(obligation.category, Some(TransvalCheckKind::ControlFlow));
    assert_eq!(
        obligation.inputs,
        vec![("dst_taken".to_string(), 1), ("src_taken".to_string(), 1),]
    );
    assert_eq!(
        obligation.trust_ir_expr.sort(),
        trust_cg_verify::SmtSort::Bool
    );
    assert_eq!(
        obligation.aarch64_expr.sort(),
        trust_cg_verify::SmtSort::Bool
    );
}

#[test]
fn return_value_refinement_vc_converts_with_precondition() {
    let ctx = FormulaAdapterContext::new()
        .with_bv_var("src_ret", 32)
        .with_bv_var("dst_ret", 32)
        .with_bv_var("limit", 32);
    let precondition = Formula::BvULt(
        Box::new(bv_var("limit", 32)),
        Box::new(Formula::BitVec {
            value: 10,
            width: 32,
        }),
        32,
    );
    let equality = Formula::Eq(
        Box::new(bv_var("src_ret", 32)),
        Box::new(bv_var("dst_ret", 32)),
    );
    let formula = Formula::Implies(Box::new(precondition), Box::new(equality));

    let obligation = refinement_vc_to_proof_obligation(
        &vc(CheckKind::ReturnValue, formula, "return value"),
        &ctx,
    )
    .unwrap();

    assert_eq!(obligation.category, Some(TransvalCheckKind::ReturnValue));
    assert_eq!(obligation.preconditions.len(), 1);
    assert_eq!(
        obligation.inputs,
        vec![
            ("dst_ret".to_string(), 32),
            ("limit".to_string(), 32),
            ("src_ret".to_string(), 32),
        ]
    );
}

#[test]
fn unsupported_formula_fails_closed_with_diagnostic() {
    let ctx = FormulaAdapterContext::new()
        .with_bv_var("src", 32)
        .with_bv_var("dst", 32);
    let formula = Formula::Eq(
        Box::new(Formula::BvURem(
            Box::new(bv_var("src", 32)),
            Box::new(Formula::BitVec {
                value: 3,
                width: 32,
            }),
            32,
        )),
        Box::new(bv_var("dst", 32)),
    );

    let err = refinement_vc_to_proof_obligation(
        &vc(CheckKind::DataFlow, formula, "unsupported rem"),
        &ctx,
    )
    .unwrap_err();

    assert!(matches!(err, TransvalCompatError::FormulaAdapter(_)));
    assert!(err.to_string().contains("BvURem"));
}

#[test]
fn verification_report_exports_validation_transport() {
    let report = VerificationReport {
        results: vec![
            ProofResult {
                name: "df".to_string(),
                category: "data_flow".to_string(),
                result: VerificationResult::Valid,
                strength: VerificationStrength::Exhaustive,
            },
            ProofResult {
                name: "rv".to_string(),
                category: "return_value".to_string(),
                result: VerificationResult::Valid,
                strength: VerificationStrength::Formal,
            },
        ],
    };

    let result = verification_report_to_validation_result(&report, "source_fn", "target_fn");

    assert_eq!(result.verdict, TransvalValidationVerdict::Validated);
    assert_eq!(result.checks_total, 2);
    assert_eq!(result.checks_passed, 2);
    assert_eq!(result.classification.data_flow, 1);
    assert_eq!(result.classification.return_value, 1);
    assert_eq!(result.checks[0].result, TransvalCheckResult::Valid);
    assert_eq!(
        result.checks[1].strength,
        TransvalValidationStrength::SmtUnsat
    );

    let json = verification_report_to_validation_json(&report, "source_fn", "target_fn").unwrap();
    assert!(json.contains("trust-cg.transval_validation_result.v1"));
}

#[test]
fn unsupported_transport_check_is_unknown_not_validated() {
    let report = VerificationReport {
        results: vec![ProofResult {
            name: "unsupported".to_string(),
            category: "unsupported".to_string(),
            result: VerificationResult::Unknown {
                reason: "unsupported formula shape".to_string(),
            },
            strength: VerificationStrength::Statistical { sample_count: 1 },
        }],
    };

    let result = verification_report_to_validation_result(&report, "source_fn", "target_fn");

    assert_eq!(result.classification.unsupported, 1);
    assert_eq!(
        result.verdict,
        TransvalValidationVerdict::Unknown {
            reason: "one or more checks are unsupported by the transval compatibility layer"
                .to_string()
        }
    );
    assert_eq!(
        result.checks[0].strength,
        TransvalValidationStrength::Sampled { sample_count: 1 }
    );
}
