// trust-cg-verify/transval_compat.rs - tRust translation-validation bridge
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Compatibility layer between Trust Codegen verification and tRust trust-transval.
//!
//! This module is enabled by the `trust-types-bridge` feature and builds on
//! [`crate::smt::trust_formula_adapter`]. The first supported VC slice is
//! intentionally narrow and fail-closed: only equality-shaped refinement
//! formulas, optionally guarded by one implication precondition, are converted
//! into [`ProofObligation`] values. Unsupported formulas remain adapter errors
//! with diagnostics rather than being treated as validated.

use crate::lowering_proof::{MachineSideProvenance, ProofObligation, TransvalCheckKind};
use crate::smt::trust_formula_adapter::{
    FormulaAdapterContext, FormulaAdapterError, formula_to_smt,
};
use crate::smt::{SmtExpr, SmtSort};
use crate::verify::{ProofResult, VerificationReport, VerificationResult, VerificationStrength};
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use thiserror::Error;
use trust_types::{CheckKind, Formula, RefinementVc, TranslationCheck};

/// Stable schema tag for Trust Codegen's trust-transval-compatible result transport.
pub const TRANSVAL_VALIDATION_RESULT_SCHEMA: &str = "trust-cg.transval_validation_result.v1";

/// Errors returned by the fail-closed tRust/Trust Codegen adapter.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum TransvalCompatError {
    #[error("unsupported RefinementVc formula shape: {0}")]
    UnsupportedFormulaShape(&'static str),

    #[error("formula conversion failed: {0}")]
    FormulaAdapter(#[from] FormulaAdapterError),

    #[error("precondition must be Bool, got {sort:?}")]
    NonBooleanPrecondition { sort: SmtSort },

    #[error("input '{name}' has inconsistent widths: {first} and {second}")]
    InconsistentInputWidth {
        name: String,
        first: u32,
        second: u32,
    },
}

/// Convert one tRust `RefinementVc` into an Trust Codegen [`ProofObligation`].
///
/// Supported formulas are:
/// - `Eq(source_expr, target_expr)`;
/// - `Implies(precondition, Eq(source_expr, target_expr))`.
///
/// The adapter rejects all other shapes because a `ProofObligation` represents
/// equivalence between two expressions, not an arbitrary boolean VC.
pub fn refinement_vc_to_proof_obligation(
    vc: &RefinementVc,
    ctx: &FormulaAdapterContext,
) -> Result<ProofObligation, TransvalCompatError> {
    translation_check_to_proof_obligation(&vc.check, &vc.source_function, &vc.target_function, ctx)
}

/// Convert a batch of tRust `RefinementVc`s into Trust Codegen proof obligations.
pub fn refinement_vcs_to_proof_obligations(
    vcs: &[RefinementVc],
    ctx: &FormulaAdapterContext,
) -> Result<Vec<ProofObligation>, TransvalCompatError> {
    vcs.iter()
        .map(|vc| refinement_vc_to_proof_obligation(vc, ctx))
        .collect()
}

/// Convert one tRust `TranslationCheck` into an Trust Codegen [`ProofObligation`].
pub fn translation_check_to_proof_obligation(
    check: &TranslationCheck,
    source_function: &str,
    target_function: &str,
    ctx: &FormulaAdapterContext,
) -> Result<ProofObligation, TransvalCompatError> {
    let category = check_kind_to_transval_kind(&check.kind);
    let (trust_ir_expr, aarch64_expr, preconditions) =
        formula_to_equivalence_parts(&check.formula, ctx)?;
    let inputs = collect_obligation_inputs(&trust_ir_expr, &aarch64_expr, &preconditions, ctx)?;

    Ok(ProofObligation {
        // This bridge imports a target-side formula; it does not reconstruct
        // semantics from Trust Codegen's emitted machine instruction. Keep the
        // conservative legacy provenance so it cannot receive reconstructed
        // proof credit.
        machine_side_provenance: MachineSideProvenance::StaticDb,
        name: obligation_name(check, source_function, target_function),
        trust_ir_expr,
        aarch64_expr,
        inputs,
        preconditions,
        fp_inputs: Vec::new(),
        category: Some(category),
    })
}

/// Map tRust's standard check taxonomy to Trust Codegen's transval-compatible kinds.
pub fn check_kind_to_transval_kind(kind: &CheckKind) -> TransvalCheckKind {
    match kind {
        CheckKind::DataFlow => TransvalCheckKind::DataFlow,
        CheckKind::ControlFlow => TransvalCheckKind::ControlFlow,
        CheckKind::ReturnValue => TransvalCheckKind::ReturnValue,
        CheckKind::Termination => TransvalCheckKind::Termination,
    }
}

fn formula_to_equivalence_parts(
    formula: &Formula,
    ctx: &FormulaAdapterContext,
) -> Result<(SmtExpr, SmtExpr, Vec<SmtExpr>), TransvalCompatError> {
    match formula {
        Formula::Eq(..) => {
            let (lhs, rhs) = formula_eq_to_smt_parts(formula, ctx)?;
            Ok((lhs, rhs, Vec::new()))
        }
        Formula::Implies(precondition, consequent) => {
            let Formula::Eq(..) = &**consequent else {
                return Err(TransvalCompatError::UnsupportedFormulaShape(
                    "expected Implies(precondition, Eq(lhs, rhs))",
                ));
            };

            let precondition = formula_to_smt(precondition, ctx)?;
            if precondition.sort() != SmtSort::Bool {
                return Err(TransvalCompatError::NonBooleanPrecondition {
                    sort: precondition.sort(),
                });
            }

            let (lhs, rhs) = formula_eq_to_smt_parts(consequent, ctx)?;
            Ok((lhs, rhs, vec![precondition]))
        }
        _ => Err(TransvalCompatError::UnsupportedFormulaShape(
            "expected Eq(lhs, rhs) or Implies(precondition, Eq(lhs, rhs))",
        )),
    }
}

fn formula_eq_to_smt_parts(
    formula: &Formula,
    ctx: &FormulaAdapterContext,
) -> Result<(SmtExpr, SmtExpr), TransvalCompatError> {
    match formula_to_smt(formula, ctx)? {
        SmtExpr::Eq { lhs, rhs } => Ok((lhs.as_ref().clone(), rhs.as_ref().clone())),
        _ => Err(TransvalCompatError::UnsupportedFormulaShape(
            "formula adapter did not produce an equality",
        )),
    }
}

fn collect_obligation_inputs(
    trust_ir_expr: &SmtExpr,
    aarch64_expr: &SmtExpr,
    preconditions: &[SmtExpr],
    ctx: &FormulaAdapterContext,
) -> Result<Vec<(String, u32)>, TransvalCompatError> {
    let mut inputs = BTreeMap::new();
    collect_expr_inputs(trust_ir_expr, ctx, &mut inputs)?;
    collect_expr_inputs(aarch64_expr, ctx, &mut inputs)?;
    for precondition in preconditions {
        collect_expr_inputs(precondition, ctx, &mut inputs)?;
    }
    Ok(inputs.into_iter().collect())
}

fn collect_expr_inputs(
    expr: &SmtExpr,
    ctx: &FormulaAdapterContext,
    inputs: &mut BTreeMap<String, u32>,
) -> Result<(), TransvalCompatError> {
    for name in expr.free_vars() {
        let sort = ctx.var_sort(&name)?;
        let width = sort.width().unwrap_or(1);
        if let Some(first) = inputs.insert(name.clone(), width)
            && first != width
        {
            return Err(TransvalCompatError::InconsistentInputWidth {
                name,
                first,
                second: width,
            });
        }
    }
    Ok(())
}

fn obligation_name(
    check: &TranslationCheck,
    source_function: &str,
    target_function: &str,
) -> String {
    let description = check.description.trim();
    if description.is_empty() {
        format!(
            "{:?} refinement {}:{:?} -> {}:{:?}",
            check.kind, source_function, check.source_point, target_function, check.target_point
        )
    } else {
        description.to_string()
    }
}

/// Trust-transval-compatible verification-result transport.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransvalValidationResult {
    pub schema: String,
    pub source_system: String,
    pub source_function: String,
    pub target_function: String,
    pub verdict: TransvalValidationVerdict,
    pub checks_total: usize,
    pub checks_passed: usize,
    pub classification: TransvalValidationClassification,
    pub checks: Vec<TransvalValidationCheck>,
}

/// Trust-transval vocabulary for the aggregate result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TransvalValidationVerdict {
    Validated,
    Refuted { reason: String },
    Unknown { reason: String },
}

/// Coarse trust-transval classification counts.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransvalValidationClassification {
    pub data_flow: usize,
    pub control_flow: usize,
    pub return_value: usize,
    pub termination: usize,
    pub trust_cg_specific: usize,
    pub unsupported: usize,
}

/// Per-check transport entry.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransvalValidationCheck {
    pub name: String,
    pub kind: String,
    pub result: TransvalCheckResult,
    pub strength: TransvalValidationStrength,
    pub diagnostics: Vec<String>,
}

/// Per-check result in trust-transval-compatible vocabulary.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum TransvalCheckResult {
    Valid,
    Invalid,
    Unknown,
}

/// Verification strength vocabulary for the transport result.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum TransvalValidationStrength {
    Exhaustive,
    Sampled { sample_count: u64 },
    SmtUnsat,
}

/// Summarize an Trust Codegen [`VerificationReport`] using trust-transval vocabulary.
pub fn verification_report_to_validation_result(
    report: &VerificationReport,
    source_function: impl Into<String>,
    target_function: impl Into<String>,
) -> TransvalValidationResult {
    let checks: Vec<_> = report.results.iter().map(proof_result_to_check).collect();
    let mut classification = TransvalValidationClassification::default();
    for check in &checks {
        classify_transport_check(&check.kind, &mut classification);
    }

    TransvalValidationResult {
        schema: TRANSVAL_VALIDATION_RESULT_SCHEMA.to_string(),
        source_system: "trust-cg".to_string(),
        source_function: source_function.into(),
        target_function: target_function.into(),
        verdict: validation_verdict(report, &classification),
        checks_total: report.total(),
        checks_passed: report.passed(),
        classification,
        checks,
    }
}

/// Serialize a trust-transval-compatible validation result as pretty JSON.
pub fn validation_result_to_json(
    result: &TransvalValidationResult,
) -> Result<String, serde_json::Error> {
    serde_json::to_string_pretty(result)
}

/// Convert an Trust Codegen [`VerificationReport`] directly to pretty transport JSON.
pub fn verification_report_to_validation_json(
    report: &VerificationReport,
    source_function: impl Into<String>,
    target_function: impl Into<String>,
) -> Result<String, serde_json::Error> {
    let result = verification_report_to_validation_result(report, source_function, target_function);
    validation_result_to_json(&result)
}

fn proof_result_to_check(result: &ProofResult) -> TransvalValidationCheck {
    let (check_result, diagnostics) = match &result.result {
        VerificationResult::Valid => (TransvalCheckResult::Valid, Vec::new()),
        VerificationResult::Invalid { counterexample } => {
            (TransvalCheckResult::Invalid, vec![counterexample.clone()])
        }
        VerificationResult::Unknown { reason } => {
            (TransvalCheckResult::Unknown, vec![reason.clone()])
        }
    };

    TransvalValidationCheck {
        name: result.name.clone(),
        kind: result.category.clone(),
        result: check_result,
        strength: verification_strength_to_transport(&result.strength),
        diagnostics,
    }
}

fn verification_strength_to_transport(
    strength: &VerificationStrength,
) -> TransvalValidationStrength {
    match strength {
        VerificationStrength::Exhaustive => TransvalValidationStrength::Exhaustive,
        VerificationStrength::Statistical { sample_count } => TransvalValidationStrength::Sampled {
            sample_count: *sample_count,
        },
        VerificationStrength::Formal => TransvalValidationStrength::SmtUnsat,
    }
}

fn classify_transport_check(kind: &str, classification: &mut TransvalValidationClassification) {
    match kind {
        "data_flow" => classification.data_flow += 1,
        "control_flow" => classification.control_flow += 1,
        "return_value" => classification.return_value += 1,
        "termination" => classification.termination += 1,
        "unsupported" => classification.unsupported += 1,
        _ => classification.trust_cg_specific += 1,
    }
}

fn validation_verdict(
    report: &VerificationReport,
    classification: &TransvalValidationClassification,
) -> TransvalValidationVerdict {
    if report.total() == 0 {
        return TransvalValidationVerdict::Unknown {
            reason: "no verification checks".to_string(),
        };
    }

    if let Some(reason) = report
        .results
        .iter()
        .find_map(|result| match &result.result {
            VerificationResult::Invalid { counterexample } => Some(counterexample.clone()),
            _ => None,
        })
    {
        return TransvalValidationVerdict::Refuted { reason };
    }

    if classification.unsupported > 0 {
        return TransvalValidationVerdict::Unknown {
            reason: "one or more checks are unsupported by the transval compatibility layer"
                .to_string(),
        };
    }

    if let Some(reason) = report
        .results
        .iter()
        .find_map(|result| match &result.result {
            VerificationResult::Unknown { reason } => Some(reason.clone()),
            _ => None,
        })
    {
        return TransvalValidationVerdict::Unknown { reason };
    }

    TransvalValidationVerdict::Validated
}
