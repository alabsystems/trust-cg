// trust-cg-verify/verify.rs - Verification interface
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! High-level verification interface.
//!
//! The [`Verifier`] provides a unified entry point for running all proof
//! obligations in the Trust Codegen verification pipeline. Individual proof categories
//! (arithmetic lowering, NZCV flags, comparisons, branches, peephole
//! optimizations, memory model) can be run independently or together via
//! [`Verifier::verify_comprehensive`].
//!
//! Results are collected into a [`VerificationReport`] that tracks per-proof
//! pass/fail status and provides summary statistics.
//!
//! # Verification strength levels
//!
//! The verification system supports three strength levels, described by
//! [`VerificationStrength`]:
//!
//! | Level | Implementation | Guarantee | When used |
//! |-------|---------------|-----------|-----------|
//! | [`VerificationStrength::Exhaustive`] | Concrete evaluation of all inputs | **Complete** for that bit-width | Widths <= 8, inputs <= 2 |
//! | [`VerificationStrength::Statistical`] | Edge cases + N random samples | **Probabilistic** (configurable N, default 100K) | Widths > 8 (32-bit, 64-bit) |
//! | [`VerificationStrength::Formal`] | External SMT solver (ay/Z3) | Complete for the represented obligation | Via [`crate::ay_bridge`] when a solver is on `PATH` |
//!
//! ## Current status
//!
//! The core evaluator APIs run proofs at **Exhaustive** or **Statistical**
//! strength depending on bit-width. The 32/64-bit proofs use statistical
//! verification with 100,000 random samples (configurable via
//! [`crate::lowering_proof::VerificationConfig`]). This provides high
//! confidence but is not a formal proof. Solver-backed tests call the external
//! solver path in v0.1.0.
//!
//! ## Formal verification backends
//!
//! 1. **Evaluation testing**: Fast, catches regressions and
//!    most bugs. Exhaustive for 8-bit, statistical for 32/64-bit.
//!    No external solver required.
//! 2. **ay CLI**: Proof obligations serialized to SMT-LIB2 via
//!    [`crate::lowering_proof::ProofObligation::to_smt2`] and verified with
//!    an external z3/ay solver. See [`crate::ay_bridge::verify_with_ay`].
//!    Always available when a solver binary is on PATH.
//!    Use [`crate::verification_runner::VerificationRunner::run_auto`] to select
//!    the strongest available v0.1.0 backend.

use std::collections::HashMap;

use thiserror::Error;
use trust_cg_lower::Function;
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::types::Type;

use crate::lowering_proof::{
    ProofObligation, TransvalCheckKind, VerificationConfig, verify_by_evaluation,
    verify_by_evaluation_with_config,
};
use crate::smt::SmtExpr;

/// Describes the strength of verification applied to a proof obligation.
///
/// This enum classifies the guarantee level of a verification result.
/// It is informational -- it tells the caller what kind of verification
/// was actually performed, so they can assess confidence appropriately.
///
/// # Strength levels
///
/// - **Exhaustive**: Every possible input was tested. This is equivalent to
///   a formal proof for the tested bit-width, but does not extend to wider
///   types. For example, exhaustive 8-bit verification proves correctness
///   for all 256 (or 65,536 for two inputs) values, but says nothing about
///   32-bit behavior.
///
/// - **Statistical**: A combination of edge cases and random samples was tested.
///   The default configuration tests 36 edge-case combinations plus 100,000
///   random samples. This provides high confidence but is not a formal proof.
///   Structured or adversarial bugs could theoretically hide in the untested
///   input space.
///
/// - **Formal**: An SMT solver (ay/z3) proved the property for ALL inputs
///   of the represented bit-width. This is available via
///   [`crate::ay_bridge::verify_with_ay`] when a supported external solver is
///   present.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationStrength {
    /// Complete enumeration of all inputs. Proof is exhaustive for the
    /// tested bit-width (<= 8-bit with <= 2 inputs by default).
    Exhaustive,

    /// Edge cases plus N random samples. High confidence but not a formal
    /// proof. Used for 32/64-bit proofs. The sample count is configurable
    /// via [`VerificationConfig`].
    ///
    /// The `sample_count` field records how many random trials were used.
    Statistical {
        /// Number of random samples that were tested (excludes edge cases).
        sample_count: u64,
    },

    /// SMT solver provided a complete formal proof for all inputs.
    /// Available via an external ay/Z3-compatible solver in v0.1.0.
    Formal,
}

impl VerificationStrength {
    /// Determine the verification strength that would be used for a proof
    /// obligation with the given parameters and default configuration.
    pub fn for_obligation(obligation: &ProofObligation) -> Self {
        Self::for_obligation_with_config(obligation, &VerificationConfig::default())
    }

    /// Determine the verification strength for a proof obligation with
    /// a custom configuration.
    pub fn for_obligation_with_config(
        obligation: &ProofObligation,
        config: &VerificationConfig,
    ) -> Self {
        let width = obligation.inputs.first().map(|(_, w)| *w).unwrap_or(32);
        let num_inputs = obligation.inputs.len();

        if num_inputs <= 2 && width <= config.exhaustive_threshold {
            VerificationStrength::Exhaustive
        } else {
            VerificationStrength::Statistical {
                sample_count: config.sample_count,
            }
        }
    }

    /// Returns true if this is a complete (exhaustive or formal) verification.
    pub fn is_complete(&self) -> bool {
        matches!(
            self,
            VerificationStrength::Exhaustive | VerificationStrength::Formal
        )
    }

    /// Returns a human-readable description of the verification strength.
    pub fn description(&self) -> String {
        match self {
            VerificationStrength::Exhaustive => {
                "Exhaustive: all input combinations tested".to_string()
            }
            VerificationStrength::Statistical { sample_count } => {
                format!(
                    "Statistical: edge cases + {} random samples (not a formal proof)",
                    sample_count
                )
            }
            VerificationStrength::Formal => {
                "Formal: SMT solver proved correctness for all inputs".to_string()
            }
        }
    }
}

impl std::fmt::Display for VerificationStrength {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            VerificationStrength::Exhaustive => write!(f, "Exhaustive"),
            VerificationStrength::Statistical { sample_count } => {
                write!(f, "Statistical({})", sample_count)
            }
            VerificationStrength::Formal => write!(f, "Formal"),
        }
    }
}

/// Verification result for a single proof obligation.
#[derive(Debug, Clone)]
pub enum VerificationResult {
    /// Verification succeeded - property holds for all inputs.
    Valid,
    /// Verification failed - counterexample found.
    Invalid { counterexample: String },
    /// Verification inconclusive (timeout, unknown, ay not available).
    Unknown { reason: String },
}

/// Result for a single named proof obligation.
#[derive(Debug, Clone)]
pub struct ProofResult {
    /// Name of the proof obligation.
    pub name: String,
    /// Category this proof belongs to (e.g., "memory", "arithmetic", "peephole").
    pub category: String,
    /// The verification outcome.
    pub result: VerificationResult,
    /// The strength of verification that was applied.
    /// See [`VerificationStrength`] for what each level guarantees.
    pub strength: VerificationStrength,
}

impl ProofResult {
    /// Returns true if the proof was verified as valid.
    pub fn is_valid(&self) -> bool {
        matches!(self.result, VerificationResult::Valid)
    }

    /// Returns true if the proof found a counterexample.
    pub fn is_invalid(&self) -> bool {
        matches!(self.result, VerificationResult::Invalid { .. })
    }
}

/// Aggregated verification report across multiple proof categories.
#[derive(Debug, Clone)]
pub struct VerificationReport {
    /// All individual proof results.
    pub results: Vec<ProofResult>,
}

impl VerificationReport {
    /// Create an empty report.
    pub fn new() -> Self {
        Self {
            results: Vec::new(),
        }
    }

    /// Total number of proofs checked.
    pub fn total(&self) -> usize {
        self.results.len()
    }

    /// Number of proofs that passed (Valid).
    pub fn passed(&self) -> usize {
        self.results.iter().filter(|r| r.is_valid()).count()
    }

    /// Number of proofs that failed (Invalid).
    pub fn failed(&self) -> usize {
        self.results.iter().filter(|r| r.is_invalid()).count()
    }

    /// Number of proofs that were inconclusive (Unknown).
    pub fn unknown(&self) -> usize {
        self.results
            .iter()
            .filter(|r| matches!(r.result, VerificationResult::Unknown { .. }))
            .count()
    }

    /// Returns true if all proofs passed.
    pub fn all_valid(&self) -> bool {
        self.results.iter().all(|r| r.is_valid())
    }

    /// Returns only the failed proof results.
    pub fn failures(&self) -> Vec<&ProofResult> {
        self.results.iter().filter(|r| r.is_invalid()).collect()
    }

    /// Returns results for a specific category.
    pub fn by_category(&self, category: &str) -> Vec<&ProofResult> {
        self.results
            .iter()
            .filter(|r| r.category == category)
            .collect()
    }

    /// Merge another report into this one.
    pub fn merge(&mut self, other: VerificationReport) {
        self.results.extend(other.results);
    }

    /// Number of proofs verified with exhaustive (complete) strength.
    pub fn exhaustive_count(&self) -> usize {
        self.results
            .iter()
            .filter(|r| matches!(r.strength, VerificationStrength::Exhaustive))
            .count()
    }

    /// Number of proofs verified with statistical (sampling) strength.
    pub fn statistical_count(&self) -> usize {
        self.results
            .iter()
            .filter(|r| matches!(r.strength, VerificationStrength::Statistical { .. }))
            .count()
    }

    /// Number of proofs verified with formal (SMT solver) strength.
    pub fn formal_count(&self) -> usize {
        self.results
            .iter()
            .filter(|r| matches!(r.strength, VerificationStrength::Formal))
            .count()
    }

    /// Format a human-readable summary.
    ///
    /// The summary includes per-category pass/fail counts and a breakdown
    /// of verification strength levels so the reader understands the
    /// confidence level of each proof.
    pub fn summary(&self) -> String {
        let mut lines = Vec::new();
        lines.push(format!(
            "Verification Report: {}/{} passed, {} failed, {} unknown",
            self.passed(),
            self.total(),
            self.failed(),
            self.unknown()
        ));
        lines.push(format!(
            "  Strength: {} exhaustive, {} statistical, {} formal",
            self.exhaustive_count(),
            self.statistical_count(),
            self.formal_count()
        ));

        // Group by category
        let mut categories: Vec<String> = self.results.iter().map(|r| r.category.clone()).collect();
        categories.sort();
        categories.dedup();

        for cat in &categories {
            let cat_results = self.by_category(cat);
            let cat_passed = cat_results.iter().filter(|r| r.is_valid()).count();
            let cat_total = cat_results.len();
            let cat_exhaustive = cat_results
                .iter()
                .filter(|r| matches!(r.strength, VerificationStrength::Exhaustive))
                .count();
            let cat_statistical = cat_results
                .iter()
                .filter(|r| matches!(r.strength, VerificationStrength::Statistical { .. }))
                .count();
            lines.push(format!(
                "  {}: {}/{} passed ({} exhaustive, {} statistical)",
                cat, cat_passed, cat_total, cat_exhaustive, cat_statistical
            ));

            // List failures
            for r in &cat_results {
                if r.is_invalid()
                    && let VerificationResult::Invalid { ref counterexample } = r.result
                {
                    lines.push(format!("    FAIL: {} — {}", r.name, counterexample));
                }
            }
        }

        lines.join("\n")
    }
}

impl Default for VerificationReport {
    fn default() -> Self {
        Self::new()
    }
}

/// Whole-function translation-validation report for a single source/target pair.
///
/// The first supported slice is intentionally narrow: one mapped entry block,
/// pure integer scalar SSA data flow, and a terminal `Return`. Unsupported
/// memory, calls, hidden-state address forms, FP/aggregate/vector types, loops,
/// and branches fail closed with [`VerificationResult::Unknown`].
#[derive(Debug, Clone)]
pub struct WholeFunctionVerificationReport {
    /// Function being verified.
    pub function_name: String,
    /// Source block to target block mapping used by this verification run.
    pub block_mapping: Vec<(Block, Block)>,
    /// Checked whole-function obligations.
    pub obligations: Vec<ProofResult>,
}

impl WholeFunctionVerificationReport {
    /// Total number of whole-function obligations checked.
    pub fn total(&self) -> usize {
        self.obligations.len()
    }

    /// Number of obligations that verified as valid.
    pub fn passed(&self) -> usize {
        self.obligations.iter().filter(|r| r.is_valid()).count()
    }

    /// Number of obligations that found a counterexample.
    pub fn failed(&self) -> usize {
        self.obligations.iter().filter(|r| r.is_invalid()).count()
    }

    /// Number of obligations that were inconclusive or unsupported.
    pub fn unknown(&self) -> usize {
        self.obligations
            .iter()
            .filter(|r| matches!(r.result, VerificationResult::Unknown { .. }))
            .count()
    }

    /// Returns true if every emitted whole-function obligation was valid.
    pub fn all_valid(&self) -> bool {
        self.obligations.iter().all(|r| r.is_valid())
    }

    /// Collapse the report to the legacy single-result API shape.
    pub fn result(&self) -> VerificationResult {
        let failures: Vec<String> = self
            .obligations
            .iter()
            .filter_map(|r| match &r.result {
                VerificationResult::Invalid { counterexample } => {
                    Some(format!("{}: {}", r.name, counterexample))
                }
                _ => None,
            })
            .collect();
        if !failures.is_empty() {
            return VerificationResult::Invalid {
                counterexample: failures.join("; "),
            };
        }

        let unknowns: Vec<String> = self
            .obligations
            .iter()
            .filter_map(|r| match &r.result {
                VerificationResult::Unknown { reason } => Some(format!("{}: {}", r.name, reason)),
                _ => None,
            })
            .collect();
        if !unknowns.is_empty() {
            return VerificationResult::Unknown {
                reason: unknowns.join("; "),
            };
        }

        VerificationResult::Valid
    }
}

/// Verification error.
#[derive(Debug, Error)]
pub enum VerifyError {
    #[error("encoding error: {0}")]
    Encoding(String),
    #[error("solver error: {0}")]
    Solver(String),
}

/// Run a set of proof obligations and collect results into a report.
///
/// Each proof is verified using mock evaluation ([`verify_by_evaluation`])
/// with default configuration. The verification strength (exhaustive vs
/// statistical) is determined by the proof obligation's bit-width and
/// input count. See [`VerificationStrength`] for details.
fn run_proofs(obligations: &[ProofObligation], category: &str) -> VerificationReport {
    let config = VerificationConfig::default();
    let results = obligations
        .iter()
        .map(|obligation| {
            let strength = VerificationStrength::for_obligation_with_config(obligation, &config);
            let result = verify_by_evaluation(obligation);
            ProofResult {
                name: obligation.name.clone(),
                category: category.to_string(),
                result,
                strength,
            }
        })
        .collect();

    VerificationReport { results }
}

#[derive(Debug, Clone)]
struct TypedExpr {
    expr: SmtExpr,
    ty: Type,
}

#[derive(Debug, Clone)]
struct EncodedBlock {
    return_values: Vec<TypedExpr>,
}

#[derive(Debug, Clone)]
enum WholeFunctionDiagnostic {
    Invalid {
        kind: TransvalCheckKind,
        name: String,
        detail: String,
    },
    Unknown {
        kind: TransvalCheckKind,
        name: String,
        reason: String,
    },
}

impl WholeFunctionDiagnostic {
    fn into_report(
        self,
        function_name: String,
        block_mapping: Vec<(Block, Block)>,
    ) -> WholeFunctionVerificationReport {
        let (kind, name, result) = match self {
            WholeFunctionDiagnostic::Invalid { kind, name, detail } => (
                kind,
                name,
                VerificationResult::Invalid {
                    counterexample: detail,
                },
            ),
            WholeFunctionDiagnostic::Unknown { kind, name, reason } => {
                (kind, name, VerificationResult::Unknown { reason })
            }
        };

        WholeFunctionVerificationReport {
            function_name,
            block_mapping,
            obligations: vec![ProofResult {
                name,
                category: kind.as_category_str().to_string(),
                result,
                strength: VerificationStrength::Exhaustive,
            }],
        }
    }
}

fn invalid_diag(
    kind: TransvalCheckKind,
    name: impl Into<String>,
    detail: impl Into<String>,
) -> WholeFunctionDiagnostic {
    WholeFunctionDiagnostic::Invalid {
        kind,
        name: name.into(),
        detail: detail.into(),
    }
}

fn unknown_diag(
    kind: TransvalCheckKind,
    name: impl Into<String>,
    reason: impl Into<String>,
) -> WholeFunctionDiagnostic {
    WholeFunctionDiagnostic::Unknown {
        kind,
        name: name.into(),
        reason: reason.into(),
    }
}

fn verify_whole_function_obligation(
    name: String,
    kind: TransvalCheckKind,
    source_expr: SmtExpr,
    target_expr: SmtExpr,
    inputs: &[(String, u32)],
) -> ProofResult {
    let obligation = ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name,
        trust_ir_expr: source_expr,
        aarch64_expr: target_expr,
        inputs: inputs.to_vec(),
        preconditions: vec![],
        fp_inputs: vec![],
        category: Some(kind),
    };
    let config = if obligation.inputs.is_empty() {
        VerificationConfig::with_sample_count(0)
    } else {
        VerificationConfig::default()
    };
    let strength = VerificationStrength::for_obligation_with_config(&obligation, &config);
    let result = verify_by_evaluation_with_config(&obligation, &config);
    ProofResult {
        name: obligation.name,
        category: kind.as_category_str().to_string(),
        result,
        strength,
    }
}

fn build_straight_line_block_mapping(
    original: &Function,
    transformed: &Function,
) -> Result<Vec<(Block, Block)>, WholeFunctionDiagnostic> {
    if !original.blocks.contains_key(&original.entry_block) {
        return Err(unknown_diag(
            TransvalCheckKind::ControlFlow,
            "whole_function.control_flow.block_mapping",
            format!(
                "source entry block {:?} is missing from function {}",
                original.entry_block, original.name
            ),
        ));
    }
    if !transformed.blocks.contains_key(&transformed.entry_block) {
        return Err(unknown_diag(
            TransvalCheckKind::ControlFlow,
            "whole_function.control_flow.block_mapping",
            format!(
                "target entry block {:?} is missing from function {}",
                transformed.entry_block, transformed.name
            ),
        ));
    }

    let source_order = original.layout_order();
    let target_order = transformed.layout_order();
    if source_order.len() != 1 || target_order.len() != 1 {
        return Err(unknown_diag(
            TransvalCheckKind::ControlFlow,
            "whole_function.control_flow.block_mapping",
            format!(
                "unsupported control flow: scalar straight-line subset requires exactly one reachable block (source={}, target={}); loops, branches, and multi-block functions are not verified",
                source_order.len(),
                target_order.len()
            ),
        ));
    }

    Ok(vec![(source_order[0], target_order[0])])
}

fn is_supported_scalar_type(ty: &Type) -> bool {
    matches!(ty, Type::B1 | Type::I8 | Type::I16 | Type::I32 | Type::I64)
}

fn validate_supported_signature(
    original: &Function,
    transformed: &Function,
    source_block: Block,
    target_block: Block,
) -> Result<Vec<(String, u32)>, WholeFunctionDiagnostic> {
    if original.signature.params != transformed.signature.params
        || original.signature.returns != transformed.signature.returns
    {
        return Err(invalid_diag(
            TransvalCheckKind::ReturnValue,
            "whole_function.return_value.signature",
            format!(
                "signature mismatch: source params {:?} returns {:?}; target params {:?} returns {:?}",
                original.signature.params,
                original.signature.returns,
                transformed.signature.params,
                transformed.signature.returns
            ),
        ));
    }

    for ty in original
        .signature
        .params
        .iter()
        .chain(original.signature.returns.iter())
    {
        if !is_supported_scalar_type(ty) {
            return Err(unknown_diag(
                TransvalCheckKind::DataFlow,
                "whole_function.data_flow.signature",
                format!(
                    "unsupported signature type {:?}; supported scalar subset is B1/I8/I16/I32/I64",
                    ty
                ),
            ));
        }
    }

    let source = original.blocks.get(&source_block).ok_or_else(|| {
        unknown_diag(
            TransvalCheckKind::ControlFlow,
            "whole_function.control_flow.block_mapping",
            format!("source block {:?} is missing", source_block),
        )
    })?;
    let target = transformed.blocks.get(&target_block).ok_or_else(|| {
        unknown_diag(
            TransvalCheckKind::ControlFlow,
            "whole_function.control_flow.block_mapping",
            format!("target block {:?} is missing", target_block),
        )
    })?;

    for (role, block) in [("source", source), ("target", target)] {
        if block.params.len() != original.signature.params.len() {
            return Err(unknown_diag(
                TransvalCheckKind::DataFlow,
                "whole_function.data_flow.params",
                format!(
                    "{} entry parameter count {} does not match signature parameter count {}",
                    role,
                    block.params.len(),
                    original.signature.params.len()
                ),
            ));
        }

        for (idx, ((_, block_ty), sig_ty)) in block
            .params
            .iter()
            .zip(original.signature.params.iter())
            .enumerate()
        {
            if block_ty != sig_ty {
                return Err(unknown_diag(
                    TransvalCheckKind::DataFlow,
                    "whole_function.data_flow.params",
                    format!(
                        "{} entry parameter {} has type {:?}, expected {:?}",
                        role, idx, block_ty, sig_ty
                    ),
                ));
            }
        }
    }

    Ok(original
        .signature
        .params
        .iter()
        .enumerate()
        .map(|(idx, ty)| (format!("arg{}", idx), ty.bits()))
        .collect())
}

fn encode_straight_line_block(
    func: &Function,
    block_id: Block,
    role: &str,
) -> Result<EncodedBlock, WholeFunctionDiagnostic> {
    if !func.stack_slots.is_empty() {
        return Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.hidden_state",
            format!(
                "{} function has {} stack slots; hidden stack state is outside the scalar subset",
                role,
                func.stack_slots.len()
            ),
        ));
    }

    let block = func.blocks.get(&block_id).ok_or_else(|| {
        unknown_diag(
            TransvalCheckKind::ControlFlow,
            "whole_function.control_flow.block_mapping",
            format!("{} block {:?} is missing", role, block_id),
        )
    })?;

    let mut values: HashMap<Value, TypedExpr> = HashMap::new();
    for (idx, (value, ty)) in block.params.iter().enumerate() {
        if !is_supported_scalar_type(ty) {
            return Err(unknown_diag(
                TransvalCheckKind::DataFlow,
                "whole_function.data_flow.params",
                format!("{} parameter {} has unsupported type {:?}", role, idx, ty),
            ));
        }
        if values
            .insert(
                *value,
                TypedExpr {
                    expr: SmtExpr::var(format!("arg{}", idx), ty.bits()),
                    ty: ty.clone(),
                },
            )
            .is_some()
        {
            return Err(unknown_diag(
                TransvalCheckKind::DataFlow,
                "whole_function.data_flow.params",
                format!("{} duplicate block parameter value {:?}", role, value),
            ));
        }
    }

    let mut return_values = None;
    for (idx, inst) in block.instructions.iter().enumerate() {
        if return_values.is_some() {
            return Err(unknown_diag(
                TransvalCheckKind::ControlFlow,
                "whole_function.control_flow.terminator",
                format!(
                    "{} has instruction after terminal Return at block {:?} instruction {}",
                    role, block_id, idx
                ),
            ));
        }

        match &inst.opcode {
            Opcode::Return => {
                if !inst.results.is_empty() {
                    return Err(unknown_diag(
                        TransvalCheckKind::ReturnValue,
                        "whole_function.return_value.terminator",
                        format!("{} Return unexpectedly defines results", role),
                    ));
                }
                if inst.args.len() != func.signature.returns.len() {
                    return Err(unknown_diag(
                        TransvalCheckKind::ReturnValue,
                        "whole_function.return_value.arity",
                        format!(
                            "{} Return has {} values, expected {} from signature",
                            role,
                            inst.args.len(),
                            func.signature.returns.len()
                        ),
                    ));
                }
                let mut ret = Vec::with_capacity(inst.args.len());
                for (ret_idx, (arg, expected_ty)) in inst
                    .args
                    .iter()
                    .zip(func.signature.returns.iter())
                    .enumerate()
                {
                    let value = values.get(arg).ok_or_else(|| {
                        unknown_diag(
                            TransvalCheckKind::DataFlow,
                            "whole_function.data_flow.undefined_value",
                            format!(
                                "{} Return value {} uses undefined value {:?}",
                                role, ret_idx, arg
                            ),
                        )
                    })?;
                    if &value.ty != expected_ty {
                        return Err(unknown_diag(
                            TransvalCheckKind::ReturnValue,
                            "whole_function.return_value.type",
                            format!(
                                "{} Return value {} has type {:?}, expected {:?}",
                                role, ret_idx, value.ty, expected_ty
                            ),
                        ));
                    }
                    ret.push(value.clone());
                }
                return_values = Some(ret);
            }
            _ => {
                let result = encode_scalar_instruction(func, inst, &values, role, idx)?;
                bind_results(func, inst, result, &mut values, role, idx)?;
            }
        }
    }

    let return_values = return_values.ok_or_else(|| {
        invalid_diag(
            TransvalCheckKind::ControlFlow,
            "whole_function.control_flow.terminator",
            format!(
                "{} block {:?} has no terminal Return; scalar subset requires both mapped blocks to return",
                role, block_id
            ),
        )
    })?;

    Ok(EncodedBlock { return_values })
}

fn encode_scalar_instruction(
    func: &Function,
    inst: &Instruction,
    values: &HashMap<Value, TypedExpr>,
    role: &str,
    index: usize,
) -> Result<TypedExpr, WholeFunctionDiagnostic> {
    match &inst.opcode {
        Opcode::Iconst { ty, imm } => {
            expect_arity(inst, role, index, 0, 1)?;
            if !is_supported_scalar_type(ty) {
                return Err(unknown_diag(
                    TransvalCheckKind::DataFlow,
                    "whole_function.data_flow.unsupported_type",
                    format!("{} Iconst at instruction {} has unsupported type {:?}", role, index, ty),
                ));
            }
            Ok(TypedExpr {
                expr: SmtExpr::bv_const(*imm as u64, ty.bits()),
                ty: ty.clone(),
            })
        }
        Opcode::Iconst128 { .. } => {
            // This whole-function transvalidator does not model 128-bit scalar
            // data flow (see `is_supported_scalar_type`, which excludes I128).
            // Fail closed exactly like the I128 `Iconst` arm above rather than
            // introduce a partially-modeled i128 value that a downstream op
            // could silently truncate. The wide-i128 constant is instead
            // certified on the x86 critical path by the per-instruction
            // `MovRI` proofs that `Opcode::Iconst128` lowers to.
            expect_arity(inst, role, index, 0, 1)?;
            Err(unknown_diag(
                TransvalCheckKind::DataFlow,
                "whole_function.data_flow.unsupported_type",
                format!(
                    "{} Iconst128 at instruction {} has unsupported type {:?}",
                    role,
                    index,
                    Type::I128
                ),
            ))
        }
        Opcode::Copy => {
            expect_arity(inst, role, index, 1, 1)?;
            get_arg(values, inst, role, index, 0)
        }
        Opcode::Iadd
        | Opcode::Isub
        | Opcode::Imul
        | Opcode::Band
        | Opcode::Bor
        | Opcode::Bxor
        | Opcode::BandNot
        | Opcode::BorNot => {
            expect_arity(inst, role, index, 2, 1)?;
            let lhs = get_arg(values, inst, role, index, 0)?;
            let rhs = get_arg(values, inst, role, index, 1)?;
            let ty = require_same_type(&lhs, &rhs, role, index, &inst.opcode)?;
            let expr = match &inst.opcode {
                Opcode::Iadd => lhs.expr.bvadd(rhs.expr),
                Opcode::Isub => lhs.expr.bvsub(rhs.expr),
                Opcode::Imul => lhs.expr.bvmul(rhs.expr),
                Opcode::Band => lhs.expr.bvand(rhs.expr),
                Opcode::Bor => lhs.expr.bvor(rhs.expr),
                Opcode::Bxor => lhs.expr.bvxor(rhs.expr),
                Opcode::BandNot => {
                    let width = ty.bits();
                    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
                    lhs.expr.bvand(rhs.expr.bvxor(all_ones))
                }
                Opcode::BorNot => {
                    let width = ty.bits();
                    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
                    lhs.expr.bvor(rhs.expr.bvxor(all_ones))
                }
                _ => unreachable!(),
            };
            Ok(TypedExpr { expr, ty })
        }
        Opcode::Ineg | Opcode::Bnot => {
            expect_arity(inst, role, index, 1, 1)?;
            let arg = get_arg(values, inst, role, index, 0)?;
            let expr = match &inst.opcode {
                Opcode::Ineg => arg.expr.bvneg(),
                Opcode::Bnot => {
                    let width = arg.ty.bits();
                    let all_ones = SmtExpr::bv_const(crate::smt::mask(u64::MAX, width), width);
                    arg.expr.bvxor(all_ones)
                }
                _ => unreachable!(),
            };
            Ok(TypedExpr { expr, ty: arg.ty })
        }
        Opcode::Icmp { cond } => {
            expect_arity(inst, role, index, 2, 1)?;
            let lhs = get_arg(values, inst, role, index, 0)?;
            let rhs = get_arg(values, inst, role, index, 1)?;
            let ty = require_same_type(&lhs, &rhs, role, index, &inst.opcode)?;
            let expr = crate::trust_ir_semantics::encode_trust_ir_icmp(cond, ty, lhs.expr, rhs.expr);
            Ok(TypedExpr { expr, ty: Type::B1 })
        }
        _ => Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.unsupported_opcode",
            unsupported_opcode_reason(role, index, &inst.opcode),
        )),
    }
    .and_then(|typed| {
        let result = inst.results.first().copied();
        if let Some(value) = result
            && let Some(hint) = func.value_types.get(&value)
            && hint != &typed.ty
        {
            return Err(unknown_diag(
                TransvalCheckKind::DataFlow,
                "whole_function.data_flow.type_hint",
                format!(
                    "{} instruction {} result {:?} inferred type {:?} conflicts with value_types hint {:?}",
                    role, index, value, typed.ty, hint
                ),
            ));
        }
        Ok(typed)
    })
}

fn bind_results(
    func: &Function,
    inst: &Instruction,
    result: TypedExpr,
    values: &mut HashMap<Value, TypedExpr>,
    role: &str,
    index: usize,
) -> Result<(), WholeFunctionDiagnostic> {
    let Some(result_value) = inst.results.first().copied() else {
        return Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.arity",
            format!("{} instruction {} produced no result to bind", role, index),
        ));
    };
    if inst.results.len() != 1 {
        return Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.arity",
            format!(
                "{} instruction {} has {} results; scalar subset supports one-result instructions",
                role,
                index,
                inst.results.len()
            ),
        ));
    }
    if let Some(hint) = func.value_types.get(&result_value)
        && hint != &result.ty
    {
        return Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.type_hint",
            format!(
                "{} instruction {} result {:?} inferred type {:?} conflicts with value_types hint {:?}",
                role, index, result_value, result.ty, hint
            ),
        ));
    }
    if values.insert(result_value, result).is_some() {
        return Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.duplicate_value",
            format!(
                "{} instruction {} redefines value {:?}",
                role, index, result_value
            ),
        ));
    }
    Ok(())
}

fn expect_arity(
    inst: &Instruction,
    role: &str,
    index: usize,
    args: usize,
    results: usize,
) -> Result<(), WholeFunctionDiagnostic> {
    if inst.args.len() != args || inst.results.len() != results {
        return Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.arity",
            format!(
                "{} instruction {} {:?} expected {} args/{} results, got {} args/{} results",
                role,
                index,
                inst.opcode,
                args,
                results,
                inst.args.len(),
                inst.results.len()
            ),
        ));
    }
    Ok(())
}

fn get_arg(
    values: &HashMap<Value, TypedExpr>,
    inst: &Instruction,
    role: &str,
    index: usize,
    arg_index: usize,
) -> Result<TypedExpr, WholeFunctionDiagnostic> {
    let value = inst.args[arg_index];
    values.get(&value).cloned().ok_or_else(|| {
        unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.undefined_value",
            format!(
                "{} instruction {} {:?} uses undefined arg {} value {:?}",
                role, index, inst.opcode, arg_index, value
            ),
        )
    })
}

fn require_same_type(
    lhs: &TypedExpr,
    rhs: &TypedExpr,
    role: &str,
    index: usize,
    opcode: &Opcode,
) -> Result<Type, WholeFunctionDiagnostic> {
    if lhs.ty != rhs.ty {
        return Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.type",
            format!(
                "{} instruction {} {:?} operand type mismatch: {:?} vs {:?}",
                role, index, opcode, lhs.ty, rhs.ty
            ),
        ));
    }
    if !is_supported_scalar_type(&lhs.ty) {
        return Err(unknown_diag(
            TransvalCheckKind::DataFlow,
            "whole_function.data_flow.unsupported_type",
            format!(
                "{} instruction {} {:?} has unsupported operand type {:?}",
                role, index, opcode, lhs.ty
            ),
        ));
    }
    Ok(lhs.ty.clone())
}

fn unsupported_opcode_reason(role: &str, index: usize, opcode: &Opcode) -> String {
    let prefix = format!("{} instruction {} {:?} is unsupported", role, index, opcode);
    match opcode {
        Opcode::Load { .. }
        | Opcode::Store { .. }
        | Opcode::AtomicLoad { .. }
        | Opcode::AtomicStore { .. }
        | Opcode::AtomicRmw { .. }
        | Opcode::CmpXchg { .. }
        | Opcode::Fence { .. }
        | Opcode::Memcpy
        | Opcode::Memmove
        | Opcode::Memset => format!(
            "{}: memory forms and hidden memory state are outside the scalar straight-line subset",
            prefix
        ),
        Opcode::Call { .. }
        | Opcode::CallIndirect
        | Opcode::CallVariadic { .. }
        | Opcode::Invoke { .. } => format!(
            "{}: calls are outside the scalar straight-line subset",
            prefix
        ),
        Opcode::Jump { .. }
        | Opcode::Brif { .. }
        | Opcode::Switch { .. }
        | Opcode::LandingPad { .. }
        | Opcode::Resume => format!(
            "{}: branches, EH control flow, and loops are outside the scalar straight-line subset",
            prefix
        ),
        Opcode::GlobalRef { .. }
        | Opcode::ExternRef { .. }
        | Opcode::TlsRef { .. }
        | Opcode::StackAddr { .. }
        | Opcode::StructGep { .. }
        | Opcode::ArrayGep { .. } => format!(
            "{}: address-producing hidden-state dependencies are outside the scalar subset",
            prefix
        ),
        Opcode::Fconst { .. }
        | Opcode::Fneg
        | Opcode::Fabs
        | Opcode::Fsqrt
        | Opcode::Ffloor
        | Opcode::Fceil
        | Opcode::Ftrunc
        | Opcode::Fadd
        | Opcode::Fsub
        | Opcode::Fmul
        | Opcode::Fdiv
        | Opcode::Fcmp { .. }
        | Opcode::FcvtToInt { .. }
        | Opcode::FcvtToUint { .. }
        | Opcode::FcvtFromInt { .. }
        | Opcode::FcvtFromUint { .. }
        | Opcode::FPExt
        | Opcode::FPTrunc => format!("{}: floating-point lowering is not in this slice", prefix),
        Opcode::Sdiv
        | Opcode::Udiv
        | Opcode::Srem
        | Opcode::Urem
        | Opcode::Ishl
        | Opcode::Ushr
        | Opcode::Sshr
        | Opcode::Select { .. }
        | Opcode::CheckedSadd
        | Opcode::CheckedSsub
        | Opcode::CheckedSmul => format!(
            "{}: this opcode has side preconditions or multi-result semantics not modeled by the first slice",
            prefix
        ),
        Opcode::Sextend { .. }
        | Opcode::Uextend { .. }
        | Opcode::Trunc { .. }
        | Opcode::Bitcast { .. }
        | Opcode::ExtractBits { .. }
        | Opcode::SextractBits { .. }
        | Opcode::InsertBits { .. } => format!(
            "{}: casts and bitfield operations are not yet wired into whole-function composition",
            prefix
        ),
        Opcode::Return => format!(
            "{}: Return is only supported as the terminal instruction",
            prefix
        ),
        _ => format!(
            "{}: supported opcodes are Iconst, Copy, Iadd, Isub, Imul, Ineg, Icmp, Band, Bor, Bxor, BandNot, BorNot, and Bnot",
            prefix
        ),
    }
}

/// Function verifier -- unified entry point for the verification pipeline.
///
/// Runs proof obligations from all verification categories:
/// - Arithmetic lowering (add, sub, mul, neg)
/// - NZCV flags (N, Z, C, V correctness)
/// - Comparison lowering (10 conditions, 32-bit + 64-bit)
/// - Branch lowering (conditional branch semantics)
/// - Peephole optimizations (identity rules)
/// - Memory model (load/store equivalence, roundtrip, non-interference, endianness)
/// - Optimization proofs (constant folding, CSE/LICM, DCE, CFG, copy propagation)
///
/// # Verification strength
///
/// All proofs are currently run using **mock evaluation** via
/// [`crate::lowering_proof::verify_by_evaluation`]. This means:
///
/// - **8-bit proofs** (with <= 2 inputs): Exhaustive -- every input combination
///   is tested. Equivalent to a formal proof for 8-bit semantics.
/// - **32/64-bit proofs**: Statistical -- edge cases (0, 1, MAX, etc.) plus
///   100,000 random samples. High confidence but **not a formal proof**.
///
/// To get formal guarantees for 32/64-bit proofs, use
/// [`crate::ay_bridge::verify_with_ay`] on individual proof obligations.
///
/// The sample count for statistical verification is configurable via
/// [`VerificationConfig`] and [`crate::lowering_proof::verify_by_evaluation_with_config`].
pub struct Verifier {
    timeout_ms: u64,
}

impl Verifier {
    /// Create a new verifier with default settings.
    pub fn new() -> Self {
        Self { timeout_ms: 30000 }
    }

    /// Set solver timeout in milliseconds.
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Get the configured timeout.
    pub fn timeout_ms(&self) -> u64 {
        self.timeout_ms
    }

    /// Verify that a transformation is semantics-preserving.
    ///
    /// Delegates to [`Self::verify_whole_function_transformation`] and collapses
    /// the whole-function report to the legacy single-result shape.
    pub fn verify_transformation(
        &self,
        original: &Function,
        transformed: &Function,
    ) -> Result<VerificationResult, VerifyError> {
        Ok(self
            .verify_whole_function_transformation(original, transformed)?
            .result())
    }

    /// Verify a whole-function source/target transformation for the documented
    /// scalar straight-line subset.
    ///
    /// Supported today:
    /// - same signature on both functions,
    /// - exactly one mapped entry block on each side,
    /// - scalar integer types `B1`, `I8`, `I16`, `I32`, `I64`,
    /// - pure SSA instructions `Iconst`, `Copy`, `Iadd`, `Isub`, `Imul`, `Ineg`,
    ///   `Icmp`, `Band`, `Bor`, `Bxor`, `BandNot`, `BorNot`, `Bnot`,
    /// - a terminal `Return`.
    ///
    /// The verifier builds source/target block mapping, composes SMT expressions
    /// through the mapped blocks, and checks `ControlFlow`, `DataFlow`, and
    /// `ReturnValue` obligations with the existing [`ProofObligation`] evaluator.
    /// Anything outside this subset returns `Unknown` with an explicit reason.
    pub fn verify_whole_function_transformation(
        &self,
        original: &Function,
        transformed: &Function,
    ) -> Result<WholeFunctionVerificationReport, VerifyError> {
        let function_name = original.name.clone();
        let block_mapping = match build_straight_line_block_mapping(original, transformed) {
            Ok(mapping) => mapping,
            Err(diag) => return Ok(diag.into_report(function_name, Vec::new())),
        };
        let (source_block, target_block) = block_mapping[0];

        let inputs =
            match validate_supported_signature(original, transformed, source_block, target_block) {
                Ok(inputs) => inputs,
                Err(diag) => return Ok(diag.into_report(function_name, block_mapping)),
            };

        let source = match encode_straight_line_block(original, source_block, "source") {
            Ok(encoded) => encoded,
            Err(diag) => return Ok(diag.into_report(function_name, block_mapping)),
        };
        let target = match encode_straight_line_block(transformed, target_block, "target") {
            Ok(encoded) => encoded,
            Err(diag) => return Ok(diag.into_report(function_name, block_mapping)),
        };

        if source.return_values.len() != target.return_values.len() {
            return Ok(invalid_diag(
                TransvalCheckKind::ReturnValue,
                "whole_function.return_value.arity",
                format!(
                    "return value count mismatch: source={}, target={}",
                    source.return_values.len(),
                    target.return_values.len()
                ),
            )
            .into_report(function_name, block_mapping));
        }

        let mut obligations = Vec::new();
        obligations.push(verify_whole_function_obligation(
            "whole_function.control_flow.entry_returns".to_string(),
            TransvalCheckKind::ControlFlow,
            SmtExpr::bv_const(1, 1),
            SmtExpr::bv_const(1, 1),
            &[],
        ));

        if source.return_values.is_empty() {
            obligations.push(verify_whole_function_obligation(
                "whole_function.return_value.void".to_string(),
                TransvalCheckKind::ReturnValue,
                SmtExpr::bv_const(1, 1),
                SmtExpr::bv_const(1, 1),
                &[],
            ));
        }

        for (idx, (source_value, target_value)) in source
            .return_values
            .iter()
            .zip(target.return_values.iter())
            .enumerate()
        {
            if source_value.ty != target_value.ty {
                return Ok(invalid_diag(
                    TransvalCheckKind::ReturnValue,
                    format!("whole_function.return_value.{}", idx),
                    format!(
                        "return value {} type mismatch: source {:?}, target {:?}",
                        idx, source_value.ty, target_value.ty
                    ),
                )
                .into_report(function_name, block_mapping));
            }

            obligations.push(verify_whole_function_obligation(
                format!("whole_function.data_flow.return{}", idx),
                TransvalCheckKind::DataFlow,
                source_value.expr.clone(),
                target_value.expr.clone(),
                &inputs,
            ));
            obligations.push(verify_whole_function_obligation(
                format!("whole_function.return_value.{}", idx),
                TransvalCheckKind::ReturnValue,
                source_value.expr.clone(),
                target_value.expr.clone(),
                &inputs,
            ));
        }

        Ok(WholeFunctionVerificationReport {
            function_name,
            block_mapping,
            obligations,
        })
    }

    // -------------------------------------------------------------------
    // Per-category verification methods
    // -------------------------------------------------------------------

    /// Verify all arithmetic lowering proofs (add, sub, mul, neg).
    ///
    /// Returns a report with 5 proof results.
    pub fn verify_arithmetic(&self) -> VerificationReport {
        use crate::lowering_proof::all_arithmetic_proofs;
        run_proofs(&all_arithmetic_proofs(), "arithmetic")
    }

    /// Verify all NZCV flag correctness proofs and comparison/branch lowering.
    ///
    /// Includes: 4 flag proofs, 10 comparison proofs (32-bit), 3 comparison
    /// proofs (64-bit), 4 branch proofs = 21 total.
    pub fn verify_nzcv(&self) -> VerificationReport {
        use crate::lowering_proof::all_nzcv_proofs;
        run_proofs(&all_nzcv_proofs(), "nzcv")
    }

    /// Verify all peephole optimization identity proofs.
    ///
    /// Returns a report with 11+ proof results (identity rules for
    /// add-zero, sub-zero, mul-one, shifts, OR/AND/XOR, etc.).
    pub fn verify_peephole(&self) -> VerificationReport {
        use crate::peephole_proofs::all_peephole_proofs;
        run_proofs(&all_peephole_proofs(), "peephole")
    }

    /// Verify all array-based memory model proofs (27 obligations).
    ///
    /// Includes:
    /// - 6 load equivalence proofs (trust_ir Load == AArch64 LDR)
    /// - 6 store equivalence proofs (trust_ir Store == AArch64 STR)
    /// - 4 store-load roundtrip proofs (store then load returns original)
    /// - 8 non-interference proofs (store at A doesn't affect B, with overlap guards)
    /// - 3 endianness proofs (little-endian byte ordering)
    pub fn verify_memory_model(&self) -> VerificationReport {
        use crate::memory_proofs::all_memory_proofs;
        run_proofs(&all_memory_proofs(), "memory")
    }

    /// Verify all optimization proofs (constant folding, CSE/LICM, DCE, etc.).
    pub fn verify_optimizations(&self) -> VerificationReport {
        let mut report = VerificationReport::new();

        // Constant folding proofs
        {
            use crate::const_fold_proofs::all_const_fold_proofs;
            report.merge(run_proofs(&all_const_fold_proofs(), "const_fold"));
        }

        // CSE/LICM proofs
        {
            use crate::cse_licm_proofs::all_cse_licm_proofs;
            report.merge(run_proofs(&all_cse_licm_proofs(), "cse_licm"));
        }

        // CFG proofs
        {
            use crate::cfg_proofs::all_cfg_proofs;
            report.merge(run_proofs(&all_cfg_proofs(), "cfg"));
        }

        // General opt proofs
        {
            use crate::opt_proofs::all_opt_proofs;
            report.merge(run_proofs(&all_opt_proofs(), "opt"));
        }

        report
    }

    /// Run all proof obligations across the entire verification pipeline.
    ///
    /// This is the comprehensive verification entry point. It runs:
    /// 1. Arithmetic lowering proofs
    /// 2. NZCV flag + comparison + branch proofs
    /// 3. Peephole optimization proofs
    /// 4. Memory model proofs (load/store equivalence, roundtrip, endianness)
    /// 5. Optimization proofs (const fold, copy prop, CSE/LICM, DCE, CFG)
    ///
    /// Returns a [`VerificationReport`] with per-proof pass/fail results
    /// and summary statistics.
    pub fn verify_comprehensive(&self) -> VerificationReport {
        let mut report = VerificationReport::new();
        report.merge(self.verify_arithmetic());
        report.merge(self.verify_nzcv());
        report.merge(self.verify_peephole());
        report.merge(self.verify_memory_model());
        report.merge(self.verify_optimizations());
        report
    }
}

impl Default for Verifier {
    fn default() -> Self {
        Self::new()
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_verification_report_empty() {
        let report = VerificationReport::new();
        assert_eq!(report.total(), 0);
        assert_eq!(report.passed(), 0);
        assert_eq!(report.failed(), 0);
        assert!(report.all_valid());
    }

    #[test]
    fn test_verification_report_mixed() {
        let report = VerificationReport {
            results: vec![
                ProofResult {
                    name: "proof_a".to_string(),
                    category: "test".to_string(),
                    result: VerificationResult::Valid,
                    strength: VerificationStrength::Exhaustive,
                },
                ProofResult {
                    name: "proof_b".to_string(),
                    category: "test".to_string(),
                    result: VerificationResult::Invalid {
                        counterexample: "a=1, b=2".to_string(),
                    },
                    strength: VerificationStrength::Statistical {
                        sample_count: 100_000,
                    },
                },
                ProofResult {
                    name: "proof_c".to_string(),
                    category: "other".to_string(),
                    result: VerificationResult::Unknown {
                        reason: "timeout".to_string(),
                    },
                    strength: VerificationStrength::Formal,
                },
            ],
        };
        assert_eq!(report.total(), 3);
        assert_eq!(report.passed(), 1);
        assert_eq!(report.failed(), 1);
        assert_eq!(report.unknown(), 1);
        assert!(!report.all_valid());
        assert_eq!(report.failures().len(), 1);
        assert_eq!(report.by_category("test").len(), 2);
        assert_eq!(report.by_category("other").len(), 1);
        assert_eq!(report.exhaustive_count(), 1);
        assert_eq!(report.statistical_count(), 1);
        assert_eq!(report.formal_count(), 1);
    }

    #[test]
    fn test_verification_report_merge() {
        let mut r1 = VerificationReport {
            results: vec![ProofResult {
                name: "a".to_string(),
                category: "cat1".to_string(),
                result: VerificationResult::Valid,
                strength: VerificationStrength::Exhaustive,
            }],
        };
        let r2 = VerificationReport {
            results: vec![ProofResult {
                name: "b".to_string(),
                category: "cat2".to_string(),
                result: VerificationResult::Valid,
                strength: VerificationStrength::Statistical {
                    sample_count: 100_000,
                },
            }],
        };
        r1.merge(r2);
        assert_eq!(r1.total(), 2);
        assert!(r1.all_valid());
    }

    #[test]
    fn test_verification_report_summary_format() {
        let report = VerificationReport {
            results: vec![
                ProofResult {
                    name: "proof_a".to_string(),
                    category: "arithmetic".to_string(),
                    result: VerificationResult::Valid,
                    strength: VerificationStrength::Exhaustive,
                },
                ProofResult {
                    name: "proof_b".to_string(),
                    category: "memory".to_string(),
                    result: VerificationResult::Valid,
                    strength: VerificationStrength::Statistical {
                        sample_count: 100_000,
                    },
                },
            ],
        };
        let summary = report.summary();
        assert!(summary.contains("2/2 passed"));
        assert!(summary.contains("1 exhaustive, 1 statistical"));
        assert!(summary.contains("arithmetic: 1/1 passed"));
        assert!(summary.contains("memory: 1/1 passed"));
    }

    #[test]
    fn test_verifier_arithmetic() {
        let verifier = Verifier::new();
        let report = verifier.verify_arithmetic();
        // Coverage floor: historic baseline 20. Grows monotonically as new
        // arithmetic proofs land (#418). Same pattern as `test_verifier_memory_model`
        // below. Regression is still caught: any decrease fails.
        assert!(
            report.total() >= 20,
            "expected >= 20 arithmetic proofs, got {}",
            report.total()
        );
        assert!(
            report.all_valid(),
            "Arithmetic proofs failed:\n{}",
            report.summary()
        );
    }

    #[test]
    fn test_verifier_memory_model() {
        let verifier = Verifier::new();
        let report = verifier.verify_memory_model();
        // #62: 14 degenerate Load_I*/Store_I*/WriteCombine/Aligned X==X retracted.
        assert!(
            report.total() >= 48,
            "expected >= 48 memory proofs, got {}",
            report.total()
        );
        assert!(
            report.all_valid(),
            "Memory proofs failed:\n{}",
            report.summary()
        );
    }

    #[test]
    fn test_verifier_nzcv() {
        let verifier = Verifier::new();
        let report = verifier.verify_nzcv();
        // #62: 4 degenerate NZCV flag X==X retracted, and the degenerate UGE/HS
        // pair removed from comparison+branch (reconstruction-credited). Now:
        // 9 cmp (32) + 9 cmp (64) + 9 branch (32) + 9 branch (64) = 36.
        assert_eq!(report.total(), 36);
        assert!(
            report.all_valid(),
            "NZCV proofs failed:\n{}",
            report.summary()
        );
    }

    #[test]
    fn test_verifier_peephole() {
        let verifier = Verifier::new();
        let report = verifier.verify_peephole();
        assert!(report.total() > 0);
        assert!(
            report.all_valid(),
            "Peephole proofs failed:\n{}",
            report.summary()
        );
    }

    // -----------------------------------------------------------------------
    // VerificationStrength tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_verification_strength_for_8bit_obligation() {
        use crate::lowering_proof::ProofObligation;
        use crate::smt::SmtExpr;

        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_8bit".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let strength = VerificationStrength::for_obligation(&obligation);
        assert_eq!(strength, VerificationStrength::Exhaustive);
        assert!(strength.is_complete());
        assert!(strength.description().contains("Exhaustive"));
        assert_eq!(format!("{}", strength), "Exhaustive");
    }

    #[test]
    fn test_verification_strength_for_32bit_obligation() {
        use crate::lowering_proof::ProofObligation;
        use crate::smt::SmtExpr;

        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_32bit".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let strength = VerificationStrength::for_obligation(&obligation);
        assert_eq!(
            strength,
            VerificationStrength::Statistical {
                sample_count: 100_000
            }
        );
        assert!(!strength.is_complete());
        assert!(strength.description().contains("Statistical"));
        assert!(strength.description().contains("100000"));
        assert_eq!(format!("{}", strength), "Statistical(100000)");
    }

    #[test]
    fn test_verification_strength_for_64bit_obligation() {
        use crate::lowering_proof::ProofObligation;
        use crate::smt::SmtExpr;

        let a = SmtExpr::var("a", 64);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_64bit".to_string(),
            trust_ir_expr: a.clone(),
            aarch64_expr: a,
            inputs: vec![("a".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let strength = VerificationStrength::for_obligation(&obligation);
        assert_eq!(
            strength,
            VerificationStrength::Statistical {
                sample_count: 100_000
            }
        );
        assert!(!strength.is_complete());
    }

    #[test]
    fn test_verification_strength_with_custom_config() {
        use crate::lowering_proof::ProofObligation;
        use crate::smt::SmtExpr;

        let a = SmtExpr::var("a", 32);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_custom".to_string(),
            trust_ir_expr: a.clone(),
            aarch64_expr: a,
            inputs: vec![("a".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = VerificationConfig::with_sample_count(500_000);
        let strength = VerificationStrength::for_obligation_with_config(&obligation, &config);
        assert_eq!(
            strength,
            VerificationStrength::Statistical {
                sample_count: 500_000
            }
        );
    }

    #[test]
    fn test_verification_strength_formal() {
        let strength = VerificationStrength::Formal;
        assert!(strength.is_complete());
        assert!(strength.description().contains("Formal"));
        assert!(strength.description().contains("SMT"));
        assert_eq!(format!("{}", strength), "Formal");
    }

    #[test]
    fn test_verification_strength_in_report() {
        // Verify that the Verifier populates strength fields correctly
        let verifier = Verifier::new();
        let report = verifier.verify_arithmetic();

        // Arithmetic proofs include both 32-bit and 64-bit obligations,
        // so we should see statistical strength for those.
        assert!(
            report.statistical_count() > 0,
            "Arithmetic proofs should include statistical (32/64-bit) verifications"
        );

        // The report summary should mention strength breakdown
        let summary = report.summary();
        assert!(
            summary.contains("exhaustive") || summary.contains("statistical"),
            "Summary should mention verification strength"
        );
    }

    // -----------------------------------------------------------------------
    // Whole-function transformation tests
    // -----------------------------------------------------------------------

    use trust_cg_lower::function::{BasicBlock as LowerBasicBlock, Signature as LowerSignature};
    use trust_cg_lower::instructions::{
        Block as LowerBlock, Instruction as LowerInstruction, Opcode as LowerOpcode,
        Value as LowerValue,
    };
    use trust_cg_lower::types::Type as LowerType;

    fn lir_inst(
        opcode: LowerOpcode,
        args: Vec<LowerValue>,
        results: Vec<LowerValue>,
    ) -> LowerInstruction {
        LowerInstruction {
            opcode,
            args,
            results,
        }
    }

    fn scalar_function(
        name: &str,
        params: Vec<LowerType>,
        returns: Vec<LowerType>,
        block_params: Vec<(LowerValue, LowerType)>,
        instructions: Vec<LowerInstruction>,
    ) -> Function {
        let mut func = Function::new(name, LowerSignature { params, returns });
        func.entry_block = LowerBlock(0);
        func.block_order = vec![LowerBlock(0)];
        func.blocks.insert(
            LowerBlock(0),
            LowerBasicBlock {
                params: block_params,
                instructions,
                source_locs: Vec::new(),
            },
        );
        func
    }

    fn add_function(name: &str, opcode: LowerOpcode, reversed: bool) -> Function {
        let a = LowerValue(0);
        let b = LowerValue(1);
        let out = LowerValue(2);
        let args = if reversed { vec![b, a] } else { vec![a, b] };
        scalar_function(
            name,
            vec![LowerType::I8, LowerType::I8],
            vec![LowerType::I8],
            vec![(a, LowerType::I8), (b, LowerType::I8)],
            vec![
                lir_inst(opcode, args, vec![out]),
                lir_inst(LowerOpcode::Return, vec![out], vec![]),
            ],
        )
    }

    #[test]
    fn test_verify_transformation_passes_straight_line_scalar_function() {
        let source = add_function("add_commuted", LowerOpcode::Iadd, false);
        let target = add_function("add_commuted", LowerOpcode::Iadd, true);
        let verifier = Verifier::new();

        let report = verifier
            .verify_whole_function_transformation(&source, &target)
            .expect("whole-function verification should run");
        assert!(report.all_valid(), "{:?}", report.result());
        assert_eq!(report.block_mapping, vec![(LowerBlock(0), LowerBlock(0))]);
        assert!(
            report
                .obligations
                .iter()
                .any(|r| r.category == "control_flow")
        );
        assert!(report.obligations.iter().any(|r| r.category == "data_flow"));
        assert!(
            report
                .obligations
                .iter()
                .any(|r| r.category == "return_value")
        );

        let legacy_result = verifier
            .verify_transformation(&source, &target)
            .expect("legacy API should delegate to whole-function verifier");
        assert!(matches!(legacy_result, VerificationResult::Valid));
    }

    #[test]
    fn test_verify_transformation_detects_return_value_mismatch() {
        let source = add_function("bad_return", LowerOpcode::Iadd, false);
        let target = add_function("bad_return", LowerOpcode::Isub, false);

        let result = Verifier::new()
            .verify_transformation(&source, &target)
            .expect("verification should run");

        let VerificationResult::Invalid { counterexample } = result else {
            panic!(
                "expected return-value mismatch to be Invalid, got {:?}",
                result
            );
        };
        assert!(counterexample.contains("whole_function.return_value"));
        assert!(counterexample.contains("inputs:"));
    }

    #[test]
    fn test_verify_transformation_detects_control_flow_mismatch() {
        let source = add_function("missing_return", LowerOpcode::Iadd, false);
        let a = LowerValue(0);
        let b = LowerValue(1);
        let out = LowerValue(2);
        let target = scalar_function(
            "missing_return",
            vec![LowerType::I8, LowerType::I8],
            vec![LowerType::I8],
            vec![(a, LowerType::I8), (b, LowerType::I8)],
            vec![lir_inst(LowerOpcode::Iadd, vec![a, b], vec![out])],
        );

        let result = Verifier::new()
            .verify_transformation(&source, &target)
            .expect("verification should run");

        let VerificationResult::Invalid { counterexample } = result else {
            panic!(
                "expected control-flow mismatch to be Invalid, got {:?}",
                result
            );
        };
        assert!(counterexample.contains("whole_function.control_flow"));
        assert!(counterexample.contains("no terminal Return"));
    }

    #[test]
    fn test_verify_transformation_rejects_unsupported_memory_construct() {
        let ptr = LowerValue(0);
        let zero = LowerValue(1);
        let source = scalar_function(
            "unsupported_load",
            vec![LowerType::I64],
            vec![LowerType::I8],
            vec![(ptr, LowerType::I64)],
            vec![
                lir_inst(
                    LowerOpcode::Iconst {
                        ty: LowerType::I8,
                        imm: 0,
                    },
                    vec![],
                    vec![zero],
                ),
                lir_inst(LowerOpcode::Return, vec![zero], vec![]),
            ],
        );

        let loaded = LowerValue(1);
        let target = scalar_function(
            "unsupported_load",
            vec![LowerType::I64],
            vec![LowerType::I8],
            vec![(ptr, LowerType::I64)],
            vec![
                lir_inst(
                    LowerOpcode::Load {
                        ty: LowerType::I8,
                        align: None,
                    },
                    vec![ptr],
                    vec![loaded],
                ),
                lir_inst(LowerOpcode::Return, vec![loaded], vec![]),
            ],
        );

        let result = Verifier::new()
            .verify_transformation(&source, &target)
            .expect("verification should run");

        let VerificationResult::Unknown { reason } = result else {
            panic!(
                "expected unsupported memory construct to be Unknown, got {:?}",
                result
            );
        };
        assert!(reason.contains("unsupported"));
        assert!(reason.contains("memory forms"));
    }

    /// ENC-11 verdict-tier TAXONOMY LOCK: a Statistical (sampled) verdict is a
    /// strictly-weaker, NON-PROOF tier. `is_complete()` — the "counts as a
    /// complete proof for its width" predicate — must EXCLUDE Statistical; only
    /// Exhaustive and Formal are complete. The human-readable description must
    /// disclose it is not a formal proof, and the label must read "Statistical",
    /// never "Formal". Crediting a sampled verdict as proven is the exact
    /// soundness-reporting lie PROOF-4/5 + P3c closed.
    #[test]
    fn enc11_statistical_is_a_strictly_weaker_non_proof_tier() {
        let stat = VerificationStrength::Statistical {
            sample_count: 100_000,
        };
        assert!(
            !stat.is_complete(),
            "Statistical must never count as a complete proof"
        );
        assert!(VerificationStrength::Exhaustive.is_complete());
        assert!(VerificationStrength::Formal.is_complete());
        assert!(
            stat.description().contains("not a formal proof"),
            "the Statistical description must disclose it is not a proof, got {:?}",
            stat.description()
        );
        assert!(format!("{stat}").starts_with("Statistical"));
        assert_ne!(
            format!("{stat}"),
            format!("{}", VerificationStrength::Formal)
        );
    }
}
