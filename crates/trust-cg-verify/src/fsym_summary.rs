// Symbolic execution: bounded function-summary scaffold
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Per-function summaries for bounded fsym preflight output.
//!
//! Solver escalation is default-off. The built-in local adapter exhaustively
//! checks tiny typed arithmetic/null obligations, while the opt-in ay adapter
//! routes typed arithmetic/null obligations through the real ay bridge.

use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay};
use crate::fsym_arith::ArithUbKind;
use crate::fsym_trust_ir::{
    FsymTrustIrDiagnostic, FsymTrustIrDiagnosticKind, FsymTrustIrReport, FsymTrustIrSkip,
    FsymTrustIrSolverCandidate, FsymTrustIrSolverObligation, FsymTrustIrUnknown, scan_module,
};
use crate::lowering_proof::ProofObligation;
use crate::smt::{EvalResult, SmtExpr, mask};
use std::collections::{BTreeMap, HashMap};
use trust_ir::Module;

/// Default state budget for the deterministic bounded local solver.
pub const DEFAULT_FSYM_SOLVER_MAX_STATES: u64 = 65_536;

/// Default variable count budget for the deterministic bounded local solver.
pub const DEFAULT_FSYM_SOLVER_MAX_VARIABLES: usize = 4;

/// Stable label for the bounded preflight outcome of one function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FsymFunctionOutcome {
    /// The bounded evaluator scanned the function and found no concrete UB or
    /// unknown obligations.
    NoConcreteUb,
    /// The bounded evaluator found at least one concrete UB witness.
    ConcreteUb,
    /// The function was outside the bounded evaluator scope.
    Skipped,
    /// The bounded evaluator could not prove or refute at least one obligation.
    UnknownObligations,
}

/// Solver-escalation placeholder for an unknown fsym obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymSolverEscalation {
    pub label: String,
    pub kind: FsymTrustIrDiagnosticKind,
    pub module: String,
    pub function: String,
    pub block: u32,
    pub inst_index: usize,
    pub reason: String,
    pub path_guards: Vec<String>,
    pub candidate_expression: Option<String>,
    pub solver_candidate: Option<FsymTrustIrSolverCandidate>,
}

impl FsymSolverEscalation {
    fn from_unknown(unknown: FsymTrustIrUnknown) -> Self {
        Self {
            label: unknown.label,
            kind: unknown.kind,
            module: unknown.module,
            function: unknown.function,
            block: unknown.block,
            inst_index: unknown.inst_index,
            reason: unknown.reason,
            path_guards: unknown.path_guards,
            candidate_expression: unknown.candidate_expression,
            solver_candidate: unknown.solver_candidate,
        }
    }
}

/// Default-off solver escalation settings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FsymSolverEscalationConfig {
    pub enabled: bool,
    pub max_variables: usize,
    pub max_states: u64,
}

impl Default for FsymSolverEscalationConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            max_variables: DEFAULT_FSYM_SOLVER_MAX_VARIABLES,
            max_states: DEFAULT_FSYM_SOLVER_MAX_STATES,
        }
    }
}

impl FsymSolverEscalationConfig {
    pub fn enabled() -> Self {
        Self {
            enabled: true,
            ..Self::default()
        }
    }
}

/// Stable status classes for bounded fsym solver escalation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FsymSolverStatus {
    ProvenSafe,
    ConcreteUb,
    Unsupported,
    Timeout,
    SolverError,
}

impl FsymSolverStatus {
    pub fn as_str(self) -> &'static str {
        match self {
            FsymSolverStatus::ProvenSafe => "proven_safe",
            FsymSolverStatus::ConcreteUb => "concrete_ub",
            FsymSolverStatus::Unsupported => "unsupported",
            FsymSolverStatus::Timeout => "timeout",
            FsymSolverStatus::SolverError => "solver_error",
        }
    }

    fn remains_unknown(self) -> bool {
        matches!(
            self,
            FsymSolverStatus::Unsupported
                | FsymSolverStatus::Timeout
                | FsymSolverStatus::SolverError
        )
    }
}

/// Adapter result before summary provenance is attached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymSolverResponse {
    pub status: FsymSolverStatus,
    pub detail: String,
    pub witness: Vec<(String, u64)>,
}

impl FsymSolverResponse {
    fn proven_safe(detail: impl Into<String>) -> Self {
        Self {
            status: FsymSolverStatus::ProvenSafe,
            detail: detail.into(),
            witness: Vec::new(),
        }
    }

    fn concrete_ub(detail: impl Into<String>, witness: Vec<(String, u64)>) -> Self {
        Self {
            status: FsymSolverStatus::ConcreteUb,
            detail: detail.into(),
            witness,
        }
    }

    fn unsupported(detail: impl Into<String>) -> Self {
        Self {
            status: FsymSolverStatus::Unsupported,
            detail: detail.into(),
            witness: Vec::new(),
        }
    }

    fn timeout(detail: impl Into<String>) -> Self {
        Self {
            status: FsymSolverStatus::Timeout,
            detail: detail.into(),
            witness: Vec::new(),
        }
    }

    fn solver_error(detail: impl Into<String>) -> Self {
        Self {
            status: FsymSolverStatus::SolverError,
            detail: detail.into(),
            witness: Vec::new(),
        }
    }
}

/// Solver escalation result with fsym provenance attached.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymSolverEscalationResult {
    pub label: String,
    pub kind: FsymTrustIrDiagnosticKind,
    pub module: String,
    pub function: String,
    pub block: u32,
    pub inst_index: usize,
    pub status: FsymSolverStatus,
    pub detail: String,
    pub witness: Vec<(String, u64)>,
}

/// Solver escalation output. Disabled configs return an enabled=false report
/// with no results.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FsymSolverEscalationReport {
    pub enabled: bool,
    pub results: Vec<FsymSolverEscalationResult>,
}

impl FsymSolverEscalationReport {
    pub fn proven_safe_count(&self) -> usize {
        self.results
            .iter()
            .filter(|result| result.status == FsymSolverStatus::ProvenSafe)
            .count()
    }

    pub fn concrete_ub_count(&self) -> usize {
        self.results
            .iter()
            .filter(|result| result.status == FsymSolverStatus::ConcreteUb)
            .count()
    }

    pub fn remaining_unknown_count(&self) -> usize {
        self.results
            .iter()
            .filter(|result| result.status.remains_unknown())
            .count()
    }
}

/// Boundary for future ay-backed escalation.
pub trait FsymSolverAdapter {
    fn solve(
        &self,
        obligation: &FsymSolverEscalation,
        config: &FsymSolverEscalationConfig,
    ) -> FsymSolverResponse;
}

/// Deterministic bounded local adapter used for conservative tests and wiring.
pub struct FsymLocalSolverAdapter;

type FsymAYCheckFn = fn(&ProofObligation, &AYConfig) -> AYResult;

/// Real ay-backed adapter for typed fsym escalation.
pub struct FsymAYSolverAdapter {
    ay_config: AYConfig,
    check: FsymAYCheckFn,
}

impl FsymAYSolverAdapter {
    pub fn new() -> Self {
        Self::with_config(AYConfig::default())
    }

    pub fn with_config(ay_config: AYConfig) -> Self {
        Self {
            ay_config,
            check: verify_with_ay,
        }
    }

    #[cfg(test)]
    fn with_checker(ay_config: AYConfig, check: FsymAYCheckFn) -> Self {
        Self { ay_config, check }
    }
}

impl Default for FsymAYSolverAdapter {
    fn default() -> Self {
        Self::new()
    }
}

/// Bounded fsym summary for one function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FsymFunctionSummary {
    pub module: Option<String>,
    pub function: String,
    pub outcome: FsymFunctionOutcome,
    pub diagnostics: Vec<FsymTrustIrDiagnostic>,
    pub unknown_obligations: Vec<FsymSolverEscalation>,
    pub skip: Option<FsymTrustIrSkip>,
}

impl FsymFunctionSummary {
    fn new_scanned(function: String) -> Self {
        Self {
            module: None,
            function,
            outcome: FsymFunctionOutcome::NoConcreteUb,
            diagnostics: Vec::new(),
            unknown_obligations: Vec::new(),
            skip: None,
        }
    }

    fn recompute_outcome(&mut self) {
        self.outcome = if self.skip.is_some() {
            FsymFunctionOutcome::Skipped
        } else if !self.diagnostics.is_empty() {
            FsymFunctionOutcome::ConcreteUb
        } else if !self.unknown_obligations.is_empty() {
            FsymFunctionOutcome::UnknownObligations
        } else {
            FsymFunctionOutcome::NoConcreteUb
        };
    }
}

/// Module-level function-summary collection.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct FsymSummary {
    pub functions: Vec<FsymFunctionSummary>,
}

/// Aggregate bounded fsym counters for corpus gates and CLI-style summaries.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct FsymSummaryCounters {
    pub scanned: usize,
    pub skipped: usize,
    pub unknown: usize,
    pub concrete_ub: usize,
}

impl FsymSummary {
    /// Scan a trust_ir module through the public bounded fsym scanner and summarize
    /// the per-function outcomes.
    pub fn scan_trust_ir_module(module: &Module) -> Self {
        Self::from_trust_ir_report(scan_module(module))
    }

    pub fn from_trust_ir_report(report: FsymTrustIrReport) -> Self {
        let mut functions = BTreeMap::<String, FsymFunctionSummary>::new();

        for function in report.scanned_function_names {
            functions
                .entry(function.clone())
                .or_insert_with(|| FsymFunctionSummary::new_scanned(function));
        }

        for diagnostic in report.diagnostics {
            let function = diagnostic.function.clone();
            let summary = functions
                .entry(function.clone())
                .or_insert_with(|| FsymFunctionSummary::new_scanned(function));
            summary.module = Some(diagnostic.module.clone());
            summary.diagnostics.push(diagnostic);
        }

        for unknown in report.unknown_obligations {
            let function = unknown.function.clone();
            let module = unknown.module.clone();
            let summary = functions
                .entry(function.clone())
                .or_insert_with(|| FsymFunctionSummary::new_scanned(function));
            summary.module.get_or_insert(module);
            summary
                .unknown_obligations
                .push(FsymSolverEscalation::from_unknown(unknown));
        }

        for skip in report.skipped_functions {
            let function = skip.function.clone();
            let summary = functions
                .entry(function.clone())
                .or_insert_with(|| FsymFunctionSummary::new_scanned(function));
            summary.skip = Some(skip);
        }

        let mut functions = functions.into_values().collect::<Vec<_>>();
        for summary in &mut functions {
            summary.recompute_outcome();
        }

        Self { functions }
    }

    pub fn count_by_outcome(&self, outcome: FsymFunctionOutcome) -> usize {
        self.functions
            .iter()
            .filter(|summary| summary.outcome == outcome)
            .count()
    }

    pub fn counters(&self) -> FsymSummaryCounters {
        let skipped = self
            .functions
            .iter()
            .filter(|summary| summary.skip.is_some())
            .count();
        let unknown = self
            .functions
            .iter()
            .map(|summary| summary.unknown_obligations.len())
            .sum();
        let concrete_ub = self
            .functions
            .iter()
            .map(|summary| summary.diagnostics.len())
            .sum();

        FsymSummaryCounters {
            scanned: self.functions.len().saturating_sub(skipped),
            skipped,
            unknown,
            concrete_ub,
        }
    }

    pub fn counters_after_solver_escalation(
        &self,
        solver_report: &FsymSolverEscalationReport,
    ) -> FsymSummaryCounters {
        let mut counters = self.counters();
        if !solver_report.enabled {
            return counters;
        }

        let resolved_unknowns =
            solver_report.proven_safe_count() + solver_report.concrete_ub_count();
        counters.unknown = counters.unknown.saturating_sub(resolved_unknowns);
        counters.concrete_ub += solver_report.concrete_ub_count();
        counters
    }

    pub fn escalate_unknown_obligations_with(
        &self,
        config: &FsymSolverEscalationConfig,
        adapter: &impl FsymSolverAdapter,
    ) -> FsymSolverEscalationReport {
        if !config.enabled {
            return FsymSolverEscalationReport {
                enabled: false,
                results: Vec::new(),
            };
        }

        let mut results = Vec::new();
        for summary in &self.functions {
            for obligation in &summary.unknown_obligations {
                let response = adapter.solve(obligation, config);
                results.push(FsymSolverEscalationResult {
                    label: obligation.label.clone(),
                    kind: obligation.kind,
                    module: obligation.module.clone(),
                    function: obligation.function.clone(),
                    block: obligation.block,
                    inst_index: obligation.inst_index,
                    status: response.status,
                    detail: response.detail,
                    witness: response.witness,
                });
            }
        }

        FsymSolverEscalationReport {
            enabled: true,
            results,
        }
    }

    pub fn escalate_unknown_obligations_locally(
        &self,
        config: &FsymSolverEscalationConfig,
    ) -> FsymSolverEscalationReport {
        self.escalate_unknown_obligations_with(config, &FsymLocalSolverAdapter)
    }

    pub fn escalate_unknown_obligations_with_ay(
        &self,
        config: &FsymSolverEscalationConfig,
        ay_config: AYConfig,
    ) -> FsymSolverEscalationReport {
        let adapter = FsymAYSolverAdapter::with_config(ay_config);
        self.escalate_unknown_obligations_with(config, &adapter)
    }
}

impl FsymSolverAdapter for FsymLocalSolverAdapter {
    fn solve(
        &self,
        obligation: &FsymSolverEscalation,
        config: &FsymSolverEscalationConfig,
    ) -> FsymSolverResponse {
        if obligation.candidate_expression.is_none() {
            return FsymSolverResponse::unsupported("missing explicit candidate expression");
        }

        let Some(candidate) = &obligation.solver_candidate else {
            return FsymSolverResponse::unsupported("missing typed solver candidate");
        };

        match (obligation.kind, &candidate.obligation) {
            (
                FsymTrustIrDiagnosticKind::NullDeref,
                FsymTrustIrSolverObligation::NullDeref { .. },
            ) => solve_null_candidate(candidate, config),
            (
                FsymTrustIrDiagnosticKind::Arithmetic,
                FsymTrustIrSolverObligation::Arithmetic { .. },
            ) => solve_arithmetic_candidate(candidate, config),
            (
                FsymTrustIrDiagnosticKind::OutOfBounds,
                FsymTrustIrSolverObligation::OutOfBounds { .. },
            ) => solve_oob_candidate(candidate, config),
            (FsymTrustIrDiagnosticKind::UseAfterFree, _) => FsymSolverResponse::unsupported(
                "bounded local escalation only supports null, arithmetic, and bounds obligations",
            ),
            _ => FsymSolverResponse::solver_error(
                "diagnostic kind does not match typed solver candidate",
            ),
        }
    }
}

impl FsymSolverAdapter for FsymAYSolverAdapter {
    fn solve(
        &self,
        obligation: &FsymSolverEscalation,
        _config: &FsymSolverEscalationConfig,
    ) -> FsymSolverResponse {
        if obligation.candidate_expression.is_none() {
            return FsymSolverResponse::unsupported("missing explicit candidate expression");
        }

        let Some(candidate) = &obligation.solver_candidate else {
            return FsymSolverResponse::unsupported("missing typed solver candidate");
        };

        match (obligation.kind, &candidate.obligation) {
            (
                FsymTrustIrDiagnosticKind::NullDeref,
                FsymTrustIrSolverObligation::NullDeref { .. },
            )
            | (
                FsymTrustIrDiagnosticKind::Arithmetic,
                FsymTrustIrSolverObligation::Arithmetic { .. },
            )
            | (
                FsymTrustIrDiagnosticKind::OutOfBounds,
                FsymTrustIrSolverObligation::OutOfBounds { .. },
            ) => match build_ay_fsym_obligation(obligation, candidate) {
                Ok(proof) => fsym_response_from_ay_result((self.check)(&proof, &self.ay_config)),
                Err(error) => error.into_response(),
            },
            (FsymTrustIrDiagnosticKind::UseAfterFree, _) => FsymSolverResponse::unsupported(
                "ay fsym escalation only supports null, arithmetic, and bounds obligations",
            ),
            _ => FsymSolverResponse::solver_error(
                "diagnostic kind does not match typed solver candidate",
            ),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum LocalSolverError {
    Unsupported(String),
    SolverError(String),
}

impl LocalSolverError {
    fn unsupported(detail: impl Into<String>) -> Self {
        Self::Unsupported(detail.into())
    }

    fn solver_error(detail: impl Into<String>) -> Self {
        Self::SolverError(detail.into())
    }

    fn into_response(self) -> FsymSolverResponse {
        match self {
            LocalSolverError::Unsupported(detail) => FsymSolverResponse::unsupported(detail),
            LocalSolverError::SolverError(detail) => FsymSolverResponse::solver_error(detail),
        }
    }
}

fn build_ay_fsym_obligation(
    escalation: &FsymSolverEscalation,
    candidate: &FsymTrustIrSolverCandidate,
) -> Result<ProofObligation, LocalSolverError> {
    let ub_condition = ay_ub_condition(candidate)?;
    let mut vars = BTreeMap::new();
    for guard in &candidate.path_guards {
        collect_supported_var_widths(guard, &mut vars)?;
    }
    collect_supported_var_widths(&ub_condition, &mut vars)?;

    let preconditions = candidate
        .path_guards
        .iter()
        .map(ay_bool_guard)
        .collect::<Result<Vec<_>, _>>()?;

    Ok(ProofObligation {
        machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
        name: format!(
            "fsym {:?} {} bb{} inst{}",
            escalation.kind, escalation.function, escalation.block, escalation.inst_index
        ),
        trust_ir_expr: SmtExpr::bool_const(false),
        aarch64_expr: ub_condition,
        inputs: vars.into_iter().collect(),
        preconditions,
        fp_inputs: Vec::new(),
        category: None,
    })
}

fn ay_ub_condition(candidate: &FsymTrustIrSolverCandidate) -> Result<SmtExpr, LocalSolverError> {
    match &candidate.obligation {
        FsymTrustIrSolverObligation::NullDeref { ptr, ptr_width } => {
            if !(1..=64).contains(ptr_width) {
                return Err(LocalSolverError::unsupported(
                    "pointer width is outside the ay fsym solver bounds",
                ));
            }
            if ptr.try_bv_width().ok() != Some(*ptr_width) {
                return Err(LocalSolverError::solver_error(
                    "pointer expression width does not match metadata",
                ));
            }
            Ok(ptr.clone().eq_expr(SmtExpr::bv_const(0, *ptr_width)))
        }
        FsymTrustIrSolverObligation::Arithmetic {
            kind,
            lhs,
            rhs,
            width,
        } => {
            if !(1..=64).contains(width) {
                return Err(LocalSolverError::unsupported(
                    "arithmetic width is outside the ay fsym solver bounds",
                ));
            }
            if lhs.try_bv_width().ok() != Some(*width) {
                return Err(LocalSolverError::solver_error(
                    "lhs expression width does not match metadata",
                ));
            }
            if !matches!(kind, ArithUbKind::Sneg) && rhs.is_none() {
                return Err(LocalSolverError::solver_error(
                    "binary arithmetic candidate is missing rhs",
                ));
            }
            if let Some(rhs) = rhs
                && rhs.try_bv_width().ok() != Some(*width)
            {
                return Err(LocalSolverError::solver_error(
                    "rhs expression width does not match metadata",
                ));
            }

            arithmetic_ub_condition(*kind, lhs, rhs.as_ref(), *width)
        }
        FsymTrustIrSolverObligation::OutOfBounds {
            byte_offset,
            object_size_bytes,
            access_size_bytes,
            width,
        } => oob_ub_condition(byte_offset, object_size_bytes, *access_size_bytes, *width),
    }
}

fn oob_ub_condition(
    byte_offset: &SmtExpr,
    object_size_bytes: &SmtExpr,
    access_size_bytes: u64,
    width: u32,
) -> Result<SmtExpr, LocalSolverError> {
    if !(1..=64).contains(&width) {
        return Err(LocalSolverError::unsupported(
            "bounds width is outside the ay fsym solver bounds",
        ));
    }
    if byte_offset.try_bv_width().ok() != Some(width) {
        return Err(LocalSolverError::solver_error(
            "byte offset expression width does not match metadata",
        ));
    }
    if object_size_bytes.try_bv_width().ok() != Some(width) {
        return Err(LocalSolverError::solver_error(
            "object-size expression width does not match metadata",
        ));
    }

    let negative_offset = byte_offset.clone().bvslt(SmtExpr::bv_const(0, width));
    let extended_width = width + 1;
    let end = byte_offset
        .clone()
        .zero_ext(1)
        .bvadd(SmtExpr::bv_const(access_size_bytes, extended_width));
    let past_object = end.bvugt(object_size_bytes.clone().zero_ext(1));
    Ok(negative_offset.or_expr(past_object))
}

fn arithmetic_ub_condition(
    kind: ArithUbKind,
    lhs: &SmtExpr,
    rhs: Option<&SmtExpr>,
    width: u32,
) -> Result<SmtExpr, LocalSolverError> {
    match kind {
        ArithUbKind::Udiv | ArithUbKind::Urem => {
            let rhs = rhs.ok_or_else(|| {
                LocalSolverError::solver_error("division/remainder candidate is missing rhs")
            })?;
            Ok(rhs.clone().eq_expr(SmtExpr::bv_const(0, width)))
        }
        ArithUbKind::Sdiv | ArithUbKind::Srem => {
            let rhs = rhs.ok_or_else(|| {
                LocalSolverError::solver_error("division/remainder candidate is missing rhs")
            })?;
            let div_zero = rhs.clone().eq_expr(SmtExpr::bv_const(0, width));
            let min_div_minus_one = lhs
                .clone()
                .eq_expr(SmtExpr::bv_const(int_min(width), width))
                .and_expr(
                    rhs.clone()
                        .eq_expr(SmtExpr::bv_const(mask(u64::MAX, width), width)),
                );
            Ok(div_zero.or_expr(min_div_minus_one))
        }
        ArithUbKind::Sadd => {
            let rhs = rhs.ok_or_else(|| {
                LocalSolverError::solver_error("signed overflow candidate is missing rhs")
            })?;
            let full = lhs.clone().sign_ext(1).bvadd(rhs.clone().sign_ext(1));
            let wrapped = lhs.clone().bvadd(rhs.clone()).sign_ext(1);
            Ok(bv_ne(full, wrapped))
        }
        ArithUbKind::Ssub => {
            let rhs = rhs.ok_or_else(|| {
                LocalSolverError::solver_error("signed overflow candidate is missing rhs")
            })?;
            let full = lhs.clone().sign_ext(1).bvsub(rhs.clone().sign_ext(1));
            let wrapped = lhs.clone().bvsub(rhs.clone()).sign_ext(1);
            Ok(bv_ne(full, wrapped))
        }
        ArithUbKind::Smul => {
            let rhs = rhs.ok_or_else(|| {
                LocalSolverError::solver_error("signed overflow candidate is missing rhs")
            })?;
            let full = lhs
                .clone()
                .sign_ext(width)
                .bvmul(rhs.clone().sign_ext(width));
            let wrapped = lhs.clone().bvmul(rhs.clone()).sign_ext(width);
            Ok(bv_ne(full, wrapped))
        }
        ArithUbKind::Sneg => {
            let full = lhs.clone().sign_ext(1).bvneg();
            let wrapped = lhs.clone().bvneg().sign_ext(1);
            Ok(bv_ne(full, wrapped))
        }
    }
}

fn ay_bool_guard(guard: &SmtExpr) -> Result<SmtExpr, LocalSolverError> {
    if is_bool_expr(guard) {
        Ok(guard.clone())
    } else if guard.try_bv_width().ok() == Some(1) {
        Ok(guard.clone().eq_expr(SmtExpr::bv_const(1, 1)))
    } else {
        Err(LocalSolverError::unsupported(
            "path guard is not a boolean or 1-bit bitvector expression",
        ))
    }
}

fn is_bool_expr(expr: &SmtExpr) -> bool {
    match expr {
        SmtExpr::BoolConst(_)
        | SmtExpr::Eq { .. }
        | SmtExpr::Not { .. }
        | SmtExpr::BvSlt { .. }
        | SmtExpr::BvSge { .. }
        | SmtExpr::BvSgt { .. }
        | SmtExpr::BvSle { .. }
        | SmtExpr::BvUlt { .. }
        | SmtExpr::BvUge { .. }
        | SmtExpr::BvUgt { .. }
        | SmtExpr::BvUle { .. }
        | SmtExpr::And { .. }
        | SmtExpr::Or { .. }
        | SmtExpr::FPEq { .. }
        | SmtExpr::FPLt { .. }
        | SmtExpr::FPGt { .. }
        | SmtExpr::FPGe { .. }
        | SmtExpr::FPLe { .. }
        | SmtExpr::FPIsNaN { .. }
        | SmtExpr::FPIsInf { .. }
        | SmtExpr::FPIsZero { .. }
        | SmtExpr::FPIsNormal { .. }
        | SmtExpr::ForAll { .. }
        | SmtExpr::Exists { .. } => true,
        SmtExpr::Ite {
            then_expr,
            else_expr,
            ..
        } => is_bool_expr(then_expr) && is_bool_expr(else_expr),
        _ => false,
    }
}

fn bv_ne(lhs: SmtExpr, rhs: SmtExpr) -> SmtExpr {
    lhs.eq_expr(rhs).not_expr()
}

fn fsym_response_from_ay_result(result: AYResult) -> FsymSolverResponse {
    match result {
        AYResult::Verified => {
            FsymSolverResponse::proven_safe("ay proved path guards exclude the UB condition")
        }
        AYResult::SolverUnsat => FsymSolverResponse::unsupported(
            "ay returned UNSAT without an independently accepted exact proof",
        ),
        AYResult::CounterExample(witness) => {
            FsymSolverResponse::concrete_ub("ay found a concrete UB witness", witness)
        }
        AYResult::Timeout => {
            FsymSolverResponse::timeout("ay timed out while solving fsym obligation")
        }
        AYResult::Unknown(detail) => {
            FsymSolverResponse::unsupported(format!("ay returned unknown: {detail}"))
        }
        AYResult::Error(detail) => {
            FsymSolverResponse::solver_error(format!("ay solver error: {detail}"))
        }
    }
}

fn solve_null_candidate(
    candidate: &FsymTrustIrSolverCandidate,
    config: &FsymSolverEscalationConfig,
) -> FsymSolverResponse {
    let FsymTrustIrSolverObligation::NullDeref { ptr, ptr_width } = &candidate.obligation else {
        return FsymSolverResponse::solver_error("expected null-deref candidate");
    };

    if !(1..=64).contains(ptr_width) {
        return FsymSolverResponse::unsupported("pointer width is outside the local solver bounds");
    }
    if ptr.try_bv_width().ok() != Some(*ptr_width) {
        return FsymSolverResponse::solver_error(
            "pointer expression width does not match metadata",
        );
    }

    solve_by_enumeration(candidate, config, &[ptr], |env| {
        Ok(eval_bv_masked(ptr, *ptr_width, env)? == 0)
    })
}

fn solve_arithmetic_candidate(
    candidate: &FsymTrustIrSolverCandidate,
    config: &FsymSolverEscalationConfig,
) -> FsymSolverResponse {
    let FsymTrustIrSolverObligation::Arithmetic {
        kind,
        lhs,
        rhs,
        width,
    } = &candidate.obligation
    else {
        return FsymSolverResponse::solver_error("expected arithmetic candidate");
    };

    if !(1..=64).contains(width) {
        return FsymSolverResponse::unsupported(
            "arithmetic width is outside the local solver bounds",
        );
    }
    if lhs.try_bv_width().ok() != Some(*width) {
        return FsymSolverResponse::solver_error("lhs expression width does not match metadata");
    }
    if !matches!(kind, ArithUbKind::Sneg) && rhs.is_none() {
        return FsymSolverResponse::solver_error("binary arithmetic candidate is missing rhs");
    }
    if let Some(rhs) = rhs
        && rhs.try_bv_width().ok() != Some(*width)
    {
        return FsymSolverResponse::solver_error("rhs expression width does not match metadata");
    }

    let mut expressions = vec![lhs];
    if let Some(rhs) = rhs {
        expressions.push(rhs);
    }

    solve_by_enumeration(candidate, config, &expressions, |env| {
        arithmetic_has_ub(*kind, lhs, rhs.as_ref(), *width, env)
    })
}

fn solve_oob_candidate(
    candidate: &FsymTrustIrSolverCandidate,
    config: &FsymSolverEscalationConfig,
) -> FsymSolverResponse {
    let FsymTrustIrSolverObligation::OutOfBounds {
        byte_offset,
        object_size_bytes,
        access_size_bytes,
        width,
    } = &candidate.obligation
    else {
        return FsymSolverResponse::solver_error("expected out-of-bounds candidate");
    };

    if !(1..=64).contains(width) {
        return FsymSolverResponse::unsupported("bounds width is outside the local solver bounds");
    }
    if byte_offset.try_bv_width().ok() != Some(*width) {
        return FsymSolverResponse::solver_error(
            "byte offset expression width does not match metadata",
        );
    }
    if object_size_bytes.try_bv_width().ok() != Some(*width) {
        return FsymSolverResponse::solver_error(
            "object-size expression width does not match metadata",
        );
    }

    solve_by_enumeration(
        candidate,
        config,
        &[byte_offset, object_size_bytes],
        |env| {
            bounds_has_ub(
                byte_offset,
                object_size_bytes,
                *access_size_bytes,
                *width,
                env,
            )
        },
    )
}

fn solve_by_enumeration<F>(
    candidate: &FsymTrustIrSolverCandidate,
    config: &FsymSolverEscalationConfig,
    expressions: &[&SmtExpr],
    has_ub: F,
) -> FsymSolverResponse
where
    F: Fn(&HashMap<String, u64>) -> Result<bool, String>,
{
    let mut vars = BTreeMap::new();
    for guard in &candidate.path_guards {
        if let Err(error) = collect_supported_var_widths(guard, &mut vars) {
            return error.into_response();
        }
    }
    for expr in expressions {
        if let Err(error) = collect_supported_var_widths(expr, &mut vars) {
            return error.into_response();
        }
    }

    if vars.len() > config.max_variables {
        return FsymSolverResponse::timeout(format!(
            "bounded local solver variable count {} exceeds limit {}",
            vars.len(),
            config.max_variables
        ));
    }

    let state_count = match bounded_state_count(&vars) {
        Ok(count) => count,
        Err(error) => return error.into_response(),
    };
    if state_count > u128::from(config.max_states) {
        return FsymSolverResponse::timeout(format!(
            "bounded local solver state count {state_count} exceeds limit {}",
            config.max_states
        ));
    }

    for state in 0..state_count {
        let env = state_env(&vars, state);
        let guards_hold = match guards_hold_for_env(&candidate.path_guards, &env) {
            Ok(guards_hold) => guards_hold,
            Err(detail) => return FsymSolverResponse::solver_error(detail),
        };
        if !guards_hold {
            continue;
        }

        match has_ub(&env) {
            Ok(true) => {
                return FsymSolverResponse::concrete_ub(
                    "bounded local solver found a concrete UB witness",
                    sorted_witness(&env),
                );
            }
            Ok(false) => {}
            Err(detail) => return FsymSolverResponse::solver_error(detail),
        }
    }

    FsymSolverResponse::proven_safe(format!(
        "bounded local solver exhausted {state_count} state(s) without a UB witness"
    ))
}

fn collect_supported_var_widths(
    expr: &SmtExpr,
    vars: &mut BTreeMap<String, u32>,
) -> Result<(), LocalSolverError> {
    match expr {
        SmtExpr::Var { name, width } => insert_var_width(vars, name, *width),
        SmtExpr::BvConst { .. } | SmtExpr::BoolConst(_) => Ok(()),
        SmtExpr::BvAdd { lhs, rhs, .. }
        | SmtExpr::BvSub { lhs, rhs, .. }
        | SmtExpr::BvMul { lhs, rhs, .. }
        | SmtExpr::BvSDiv { lhs, rhs, .. }
        | SmtExpr::BvUDiv { lhs, rhs, .. }
        | SmtExpr::BvURem { lhs, rhs, .. }
        | SmtExpr::BvAnd { lhs, rhs, .. }
        | SmtExpr::BvOr { lhs, rhs, .. }
        | SmtExpr::BvXor { lhs, rhs, .. }
        | SmtExpr::BvShl { lhs, rhs, .. }
        | SmtExpr::BvLshr { lhs, rhs, .. }
        | SmtExpr::BvAshr { lhs, rhs, .. }
        | SmtExpr::Eq { lhs, rhs }
        | SmtExpr::BvSlt { lhs, rhs, .. }
        | SmtExpr::BvSge { lhs, rhs, .. }
        | SmtExpr::BvSgt { lhs, rhs, .. }
        | SmtExpr::BvSle { lhs, rhs, .. }
        | SmtExpr::BvUlt { lhs, rhs, .. }
        | SmtExpr::BvUge { lhs, rhs, .. }
        | SmtExpr::BvUgt { lhs, rhs, .. }
        | SmtExpr::BvUle { lhs, rhs, .. }
        | SmtExpr::And { lhs, rhs }
        | SmtExpr::Or { lhs, rhs } => {
            collect_supported_var_widths(lhs, vars)?;
            collect_supported_var_widths(rhs, vars)
        }
        SmtExpr::BvNeg { operand, .. }
        | SmtExpr::Not { operand }
        | SmtExpr::Extract { operand, .. }
        | SmtExpr::ZeroExtend { operand, .. }
        | SmtExpr::SignExtend { operand, .. } => collect_supported_var_widths(operand, vars),
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_supported_var_widths(cond, vars)?;
            collect_supported_var_widths(then_expr, vars)?;
            collect_supported_var_widths(else_expr, vars)
        }
        SmtExpr::Concat { hi, lo, .. } => {
            collect_supported_var_widths(hi, vars)?;
            collect_supported_var_widths(lo, vars)
        }
        _ => Err(LocalSolverError::unsupported(
            "candidate uses unsupported SMT expression shape",
        )),
    }
}

fn insert_var_width(
    vars: &mut BTreeMap<String, u32>,
    name: &str,
    width: u32,
) -> Result<(), LocalSolverError> {
    if !(1..=64).contains(&width) {
        return Err(LocalSolverError::unsupported(format!(
            "variable `{name}` has unsupported bit width {width}"
        )));
    }

    match vars.get(name).copied() {
        Some(existing) if existing != width => Err(LocalSolverError::solver_error(format!(
            "variable `{name}` has conflicting widths {existing} and {width}"
        ))),
        Some(_) => Ok(()),
        None => {
            vars.insert(name.to_string(), width);
            Ok(())
        }
    }
}

fn bounded_state_count(vars: &BTreeMap<String, u32>) -> Result<u128, LocalSolverError> {
    let mut count = 1_u128;
    for width in vars.values().copied() {
        let domain = 1_u128
            .checked_shl(width)
            .ok_or_else(|| LocalSolverError::solver_error("state-space shift overflow"))?;
        count = count
            .checked_mul(domain)
            .ok_or_else(|| LocalSolverError::solver_error("state-space product overflow"))?;
    }
    Ok(count)
}

fn state_env(vars: &BTreeMap<String, u32>, mut state: u128) -> HashMap<String, u64> {
    let mut env = HashMap::new();
    for (name, width) in vars {
        let domain = 1_u128 << *width;
        let value = (state % domain) as u64;
        state /= domain;
        env.insert(name.clone(), value);
    }
    env
}

fn guards_hold_for_env(guards: &[SmtExpr], env: &HashMap<String, u64>) -> Result<bool, String> {
    for guard in guards {
        let holds = match guard
            .try_eval(env)
            .map_err(|error| format!("failed to evaluate path guard: {error}"))?
        {
            EvalResult::Bool(value) => value,
            EvalResult::Bv(value) if guard.try_bv_width().ok() == Some(1) => value == 1,
            EvalResult::Bv128(value) if guard.try_bv_width().ok() == Some(1) => value == 1,
            other => return Err(format!("path guard evaluated to non-bool value: {other:?}")),
        };
        if !holds {
            return Ok(false);
        }
    }
    Ok(true)
}

fn eval_bv_masked(expr: &SmtExpr, width: u32, env: &HashMap<String, u64>) -> Result<u64, String> {
    let value = match expr
        .try_eval(env)
        .map_err(|error| format!("failed to evaluate bitvector expression: {error}"))?
    {
        EvalResult::Bv(value) => value,
        EvalResult::Bv128(value) => u64::try_from(value)
            .map_err(|_| "bitvector expression produced a value wider than u64".to_string())?,
        other => return Err(format!("bitvector expression evaluated to {other:?}")),
    };
    Ok(mask(value, width))
}

fn arithmetic_has_ub(
    kind: ArithUbKind,
    lhs: &SmtExpr,
    rhs: Option<&SmtExpr>,
    width: u32,
    env: &HashMap<String, u64>,
) -> Result<bool, String> {
    let lhs = eval_bv_masked(lhs, width, env)?;
    match kind {
        ArithUbKind::Udiv | ArithUbKind::Urem => {
            let rhs = eval_bv_masked(
                rhs.ok_or_else(|| "division/remainder candidate is missing rhs".to_string())?,
                width,
                env,
            )?;
            Ok(rhs == 0)
        }
        ArithUbKind::Sdiv | ArithUbKind::Srem => {
            let rhs = eval_bv_masked(
                rhs.ok_or_else(|| "division/remainder candidate is missing rhs".to_string())?,
                width,
                env,
            )?;
            Ok(rhs == 0 || signed_min_div_minus_one(lhs, rhs, width))
        }
        ArithUbKind::Sadd | ArithUbKind::Ssub | ArithUbKind::Smul => {
            let rhs = eval_bv_masked(
                rhs.ok_or_else(|| "signed overflow candidate is missing rhs".to_string())?,
                width,
                env,
            )?;
            Ok(signed_overflow(kind, lhs, Some(rhs), width))
        }
        ArithUbKind::Sneg => Ok(signed_overflow(kind, lhs, None, width)),
    }
}

fn bounds_has_ub(
    byte_offset: &SmtExpr,
    object_size_bytes: &SmtExpr,
    access_size_bytes: u64,
    width: u32,
    env: &HashMap<String, u64>,
) -> Result<bool, String> {
    let offset = eval_bv_masked(byte_offset, width, env)?;
    if offset & int_min(width) != 0 {
        return Ok(true);
    }

    let object_size = eval_bv_masked(object_size_bytes, width, env)?;
    let end = u128::from(offset) + u128::from(access_size_bytes);
    Ok(end > u128::from(object_size))
}

fn signed_min_div_minus_one(lhs: u64, rhs: u64, width: u32) -> bool {
    lhs == int_min(width) && rhs == mask(u64::MAX, width)
}

fn int_min(width: u32) -> u64 {
    1_u64 << (width - 1)
}

fn signed_overflow(kind: ArithUbKind, lhs: u64, rhs: Option<u64>, width: u32) -> bool {
    let lhs = to_signed(lhs, width);
    let value = match kind {
        ArithUbKind::Sadd => lhs + to_signed(rhs.expect("checked rhs"), width),
        ArithUbKind::Ssub => lhs - to_signed(rhs.expect("checked rhs"), width),
        ArithUbKind::Smul => lhs * to_signed(rhs.expect("checked rhs"), width),
        ArithUbKind::Sneg => -lhs,
        ArithUbKind::Udiv | ArithUbKind::Sdiv | ArithUbKind::Urem | ArithUbKind::Srem => {
            return false;
        }
    };

    let (min, max) = signed_range(width);
    value < min || value > max
}

fn signed_range(width: u32) -> (i128, i128) {
    (-(1_i128 << (width - 1)), (1_i128 << (width - 1)) - 1)
}

fn to_signed(value: u64, width: u32) -> i128 {
    let value = mask(value, width);
    let sign_bit = 1_u64 << (width - 1);
    if value & sign_bit == 0 {
        value as i128
    } else {
        value as i128 - (1_i128 << width)
    }
}

fn sorted_witness(env: &HashMap<String, u64>) -> Vec<(String, u64)> {
    let mut witness = env
        .iter()
        .map(|(name, value)| (name.clone(), *value))
        .collect::<Vec<_>>();
    witness.sort_by(|a, b| a.0.cmp(&b.0));
    witness
}

#[cfg(test)]
mod tests {
    use super::{
        FsymAYSolverAdapter, FsymFunctionOutcome, FsymSolverEscalationConfig,
        FsymSolverEscalationReport, FsymSolverStatus, FsymSummary,
    };
    use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay};
    use crate::fsym_arith::ArithUbKind;
    use crate::fsym_trust_ir::{
        FsymTrustIrDiagnostic, FsymTrustIrDiagnosticKind, FsymTrustIrReport, FsymTrustIrSkip,
        FsymTrustIrSkipReason, FsymTrustIrSolverCandidate, FsymTrustIrSolverObligation,
        FsymTrustIrUnknown,
    };
    use crate::lowering_proof::ProofObligation;
    use crate::smt::SmtExpr;

    fn empty_report(function: &str) -> FsymTrustIrReport {
        FsymTrustIrReport {
            scanned_functions: 1,
            scanned_function_names: vec![function.to_string()],
            ..FsymTrustIrReport::default()
        }
    }

    #[test]
    fn summarizes_no_concrete_ub_function() {
        let summary = FsymSummary::from_trust_ir_report(empty_report("safe_fn"));

        assert_eq!(summary.functions.len(), 1);
        assert_eq!(summary.functions[0].function, "safe_fn");
        assert_eq!(
            summary.functions[0].outcome,
            FsymFunctionOutcome::NoConcreteUb
        );
    }

    #[test]
    fn summarizes_concrete_ub_function() {
        let mut report = empty_report("ub_fn");
        report.diagnostics.push(FsymTrustIrDiagnostic {
            kind: FsymTrustIrDiagnosticKind::NullDeref,
            module: "m".to_string(),
            function: "ub_fn".to_string(),
            block: 2,
            inst_index: 3,
            span: None,
            message: "null pointer dereference".to_string(),
            witness: vec![("p".to_string(), 0)],
        });

        let summary = FsymSummary::from_trust_ir_report(report);

        assert_eq!(summary.functions.len(), 1);
        assert_eq!(
            summary.functions[0].outcome,
            FsymFunctionOutcome::ConcreteUb
        );
        assert_eq!(summary.functions[0].module.as_deref(), Some("m"));
        assert_eq!(summary.functions[0].diagnostics[0].block, 2);
    }

    #[test]
    fn summarizes_skipped_function() {
        let mut report = FsymTrustIrReport::default();
        report.skipped_functions.push(FsymTrustIrSkip {
            function: "loop_fn".to_string(),
            reason: FsymTrustIrSkipReason::Loop,
            detail: "control-flow graph contains a cycle".to_string(),
        });

        let summary = FsymSummary::from_trust_ir_report(report);

        assert_eq!(summary.functions.len(), 1);
        assert_eq!(summary.functions[0].outcome, FsymFunctionOutcome::Skipped);
        assert_eq!(
            summary.functions[0].skip.as_ref().unwrap().reason,
            FsymTrustIrSkipReason::Loop
        );
    }

    #[test]
    fn summarizes_unknown_obligations_for_solver_escalation() {
        let mut report = empty_report("unknown_fn");
        report.unknown_obligations.push(FsymTrustIrUnknown {
            kind: FsymTrustIrDiagnosticKind::Arithmetic,
            label: "unknown_fn bb4 inst7 arithmetic".to_string(),
            module: "m".to_string(),
            function: "unknown_fn".to_string(),
            block: 4,
            inst_index: 7,
            reason: "no witness found in evaluator; escalate to SMT".to_string(),
            path_guards: vec!["g0".to_string(), "(= x y)".to_string()],
            candidate_expression: Some("add side condition: x, y".to_string()),
            solver_candidate: None,
        });

        let summary = FsymSummary::from_trust_ir_report(report);

        assert_eq!(
            summary.functions[0].outcome,
            FsymFunctionOutcome::UnknownObligations
        );
        let obligation = &summary.functions[0].unknown_obligations[0];
        assert_eq!(obligation.label, "unknown_fn bb4 inst7 arithmetic");
        assert_eq!(obligation.block, 4);
        assert_eq!(obligation.inst_index, 7);
        assert_eq!(obligation.path_guards, ["g0", "(= x y)"]);
        assert_eq!(
            obligation.candidate_expression.as_deref(),
            Some("add side condition: x, y")
        );
    }

    #[test]
    fn reports_summary_counters_for_corpus_gates() {
        let mut report = empty_report("safe_fn");
        report.scanned_function_names.push("ub_fn".to_string());
        report.scanned_function_names.push("unknown_fn".to_string());
        report.diagnostics.push(FsymTrustIrDiagnostic {
            kind: FsymTrustIrDiagnosticKind::NullDeref,
            module: "m".to_string(),
            function: "ub_fn".to_string(),
            block: 0,
            inst_index: 0,
            span: None,
            message: "null pointer dereference".to_string(),
            witness: vec![("p".to_string(), 0)],
        });
        report.unknown_obligations.push(FsymTrustIrUnknown {
            kind: FsymTrustIrDiagnosticKind::Arithmetic,
            label: "unknown_fn bb0 inst1 arithmetic".to_string(),
            module: "m".to_string(),
            function: "unknown_fn".to_string(),
            block: 0,
            inst_index: 1,
            reason: "no witness found in evaluator; escalate to SMT".to_string(),
            path_guards: vec!["true".to_string()],
            candidate_expression: Some("sadd side condition: x, y".to_string()),
            solver_candidate: None,
        });
        report.skipped_functions.push(FsymTrustIrSkip {
            function: "loop_fn".to_string(),
            reason: FsymTrustIrSkipReason::Loop,
            detail: "loop header bb1 is not a conditional static-bound check".to_string(),
        });

        let counters = FsymSummary::from_trust_ir_report(report).counters();

        assert_eq!(counters.scanned, 3);
        assert_eq!(counters.skipped, 1);
        assert_eq!(counters.unknown, 1);
        assert_eq!(counters.concrete_ub, 1);
    }

    fn summary_with_unknown(
        kind: FsymTrustIrDiagnosticKind,
        path_guards: Vec<String>,
        candidate_expression: Option<String>,
        solver_candidate: Option<FsymTrustIrSolverCandidate>,
    ) -> FsymSummary {
        let mut report = empty_report("unknown_fn");
        report.unknown_obligations.push(FsymTrustIrUnknown {
            kind,
            label: "unknown_fn bb0 inst0".to_string(),
            module: "m".to_string(),
            function: "unknown_fn".to_string(),
            block: 0,
            inst_index: 0,
            reason: "no witness found in evaluator; escalate to SMT".to_string(),
            path_guards,
            candidate_expression,
            solver_candidate,
        });
        FsymSummary::from_trust_ir_report(report)
    }

    fn null_candidate(ptr: SmtExpr, ptr_width: u32, guard: SmtExpr) -> FsymTrustIrSolverCandidate {
        FsymTrustIrSolverCandidate {
            path_guards: vec![guard],
            obligation: FsymTrustIrSolverObligation::NullDeref { ptr, ptr_width },
        }
    }

    fn arithmetic_candidate(
        kind: ArithUbKind,
        lhs: SmtExpr,
        rhs: Option<SmtExpr>,
        width: u32,
        guard: SmtExpr,
    ) -> FsymTrustIrSolverCandidate {
        FsymTrustIrSolverCandidate {
            path_guards: vec![guard],
            obligation: FsymTrustIrSolverObligation::Arithmetic {
                kind,
                lhs,
                rhs,
                width,
            },
        }
    }

    fn oob_candidate(
        byte_offset: SmtExpr,
        object_size_bytes: SmtExpr,
        access_size_bytes: u64,
        width: u32,
        guard: SmtExpr,
    ) -> FsymTrustIrSolverCandidate {
        FsymTrustIrSolverCandidate {
            path_guards: vec![guard],
            obligation: FsymTrustIrSolverObligation::OutOfBounds {
                byte_offset,
                object_size_bytes,
                access_size_bytes,
                width,
            },
        }
    }

    fn enabled_config() -> FsymSolverEscalationConfig {
        FsymSolverEscalationConfig::enabled()
    }

    fn ay_test_config() -> AYConfig {
        AYConfig::default().with_timeout(10_000)
    }

    fn ay_timeout(_obligation: &ProofObligation, _config: &AYConfig) -> AYResult {
        AYResult::Timeout
    }

    fn ay_unknown(_obligation: &ProofObligation, _config: &AYConfig) -> AYResult {
        AYResult::Unknown("unsupported fragment".to_string())
    }

    fn ay_error(_obligation: &ProofObligation, _config: &AYConfig) -> AYResult {
        AYResult::Error("synthetic solver failure".to_string())
    }

    fn ay_solver_unsat(_obligation: &ProofObligation, _config: &AYConfig) -> AYResult {
        AYResult::SolverUnsat
    }

    fn ay_verified(_obligation: &ProofObligation, _config: &AYConfig) -> AYResult {
        AYResult::Verified
    }

    #[test]
    fn solver_escalation_is_default_off() {
        let x = SmtExpr::var("x", 2);
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::NullDeref,
            vec!["true".to_string()],
            Some("x".to_string()),
            Some(null_candidate(x, 2, SmtExpr::bool_const(true))),
        );

        let report =
            summary.escalate_unknown_obligations_locally(&FsymSolverEscalationConfig::default());

        assert!(!report.enabled);
        assert!(report.results.is_empty());
    }

    #[test]
    fn local_solver_proves_guarded_null_unknown_safe() {
        let x = SmtExpr::var("x", 2);
        let guard = x.clone().eq_expr(SmtExpr::bv_const(0, 2)).not_expr();
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::NullDeref,
            vec![guard.to_string()],
            Some("x".to_string()),
            Some(null_candidate(x, 2, guard)),
        );

        let report = summary.escalate_unknown_obligations_locally(&enabled_config());

        assert!(report.enabled);
        assert_eq!(report.results.len(), 1);
        assert_eq!(report.results[0].status, FsymSolverStatus::ProvenSafe);
        assert_eq!(report.results[0].status.as_str(), "proven_safe");
        assert!(report.results[0].witness.is_empty());
    }

    #[test]
    fn local_solver_reports_concrete_null_ub() {
        let x = SmtExpr::var("x", 2);
        let guard = x.clone().eq_expr(SmtExpr::bv_const(0, 2));
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::NullDeref,
            vec![guard.to_string()],
            Some("x".to_string()),
            Some(null_candidate(x, 2, guard)),
        );

        let report = summary.escalate_unknown_obligations_locally(&enabled_config());

        assert_eq!(report.results[0].status, FsymSolverStatus::ConcreteUb);
        assert_eq!(report.results[0].status.as_str(), "concrete_ub");
        assert_eq!(report.results[0].witness, [("x".to_string(), 0)]);
    }

    #[test]
    fn local_solver_rejects_unsupported_without_typed_candidate() {
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::OutOfBounds,
            vec!["true".to_string()],
            Some("offset".to_string()),
            None,
        );

        let report = summary.escalate_unknown_obligations_locally(&enabled_config());

        assert_eq!(report.results[0].status, FsymSolverStatus::Unsupported);
        assert_eq!(report.results[0].status.as_str(), "unsupported");
    }

    #[test]
    fn local_solver_classifies_timeout_when_state_budget_is_too_small() {
        let x = SmtExpr::var("x", 8);
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::NullDeref,
            vec!["true".to_string()],
            Some("x".to_string()),
            Some(null_candidate(x, 8, SmtExpr::bool_const(true))),
        );
        let config = FsymSolverEscalationConfig {
            enabled: true,
            max_variables: 4,
            max_states: 10,
        };

        let report = summary.escalate_unknown_obligations_locally(&config);

        assert_eq!(report.results[0].status, FsymSolverStatus::Timeout);
        assert_eq!(report.results[0].status.as_str(), "timeout");
    }

    #[test]
    fn local_solver_classifies_solver_error_for_conflicting_widths() {
        let guard = SmtExpr::var("x", 4).eq_expr(SmtExpr::bv_const(0, 4));
        let ptr = SmtExpr::var("x", 8);
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::NullDeref,
            vec![guard.to_string()],
            Some("x".to_string()),
            Some(null_candidate(ptr, 8, guard)),
        );

        let report = summary.escalate_unknown_obligations_locally(&enabled_config());

        assert_eq!(report.results[0].status, FsymSolverStatus::SolverError);
        assert_eq!(report.results[0].status.as_str(), "solver_error");
    }

    #[test]
    fn local_solver_handles_small_arithmetic_overflow_candidate() {
        let x = SmtExpr::var("x", 2);
        let y = SmtExpr::var("y", 2);
        let guard = x.clone().eq_expr(SmtExpr::bv_const(0, 2));
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::Arithmetic,
            vec![guard.to_string()],
            Some("sadd side condition: x, y".to_string()),
            Some(arithmetic_candidate(
                ArithUbKind::Sadd,
                x,
                Some(y),
                2,
                guard,
            )),
        );

        let report = summary.escalate_unknown_obligations_locally(&enabled_config());

        assert_eq!(report.results[0].status, FsymSolverStatus::ProvenSafe);
    }

    #[test]
    fn local_solver_proves_symbolic_oob_safe_and_removes_unknown_count() {
        let offset = SmtExpr::var("i", 4);
        let guard = offset.clone().bvule(SmtExpr::bv_const(4, 4));
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::OutOfBounds,
            vec![guard.to_string()],
            Some("bounds side condition: offset=i, object_size=8, access_size=4".to_string()),
            Some(oob_candidate(offset, SmtExpr::bv_const(8, 4), 4, 4, guard)),
        );

        let before = summary.counters();
        let report = summary.escalate_unknown_obligations_locally(&enabled_config());
        let after = summary.counters_after_solver_escalation(&report);

        assert_eq!(before.unknown, 1);
        assert_eq!(report.results[0].status, FsymSolverStatus::ProvenSafe);
        assert_eq!(report.remaining_unknown_count(), 0);
        assert_eq!(after.unknown, 0);
        assert_eq!(after.concrete_ub, 0);
    }

    #[test]
    fn local_solver_reports_symbolic_oob_concrete_ub() {
        let offset = SmtExpr::var("i", 4);
        let guard = offset.clone().eq_expr(SmtExpr::bv_const(5, 4));
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::OutOfBounds,
            vec![guard.to_string()],
            Some("bounds side condition: offset=i, object_size=8, access_size=4".to_string()),
            Some(oob_candidate(offset, SmtExpr::bv_const(8, 4), 4, 4, guard)),
        );

        let report = summary.escalate_unknown_obligations_locally(&enabled_config());
        let after = summary.counters_after_solver_escalation(&report);

        assert_eq!(report.results[0].status, FsymSolverStatus::ConcreteUb);
        assert_eq!(report.results[0].status.as_str(), "concrete_ub");
        assert_eq!(report.results[0].witness, [("i".to_string(), 5)]);
        assert_eq!(report.concrete_ub_count(), 1);
        assert_eq!(after.unknown, 0);
        assert_eq!(after.concrete_ub, 1);
    }

    #[test]
    fn local_solver_keeps_oob_timeout_and_unsupported_as_remaining_unknowns() {
        let timeout_offset = SmtExpr::var("i", 8);
        let timeout_summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::OutOfBounds,
            vec!["true".to_string()],
            Some("bounds side condition: offset=i, object_size=8, access_size=4".to_string()),
            Some(oob_candidate(
                timeout_offset,
                SmtExpr::bv_const(8, 8),
                4,
                8,
                SmtExpr::bool_const(true),
            )),
        );
        let timeout_config = FsymSolverEscalationConfig {
            enabled: true,
            max_variables: 4,
            max_states: 10,
        };

        let timeout_report = timeout_summary.escalate_unknown_obligations_locally(&timeout_config);
        let timeout_after = timeout_summary.counters_after_solver_escalation(&timeout_report);

        assert_eq!(timeout_report.results[0].status, FsymSolverStatus::Timeout);
        assert_eq!(timeout_report.remaining_unknown_count(), 1);
        assert_eq!(timeout_after.unknown, 1);
        assert_eq!(timeout_after.concrete_ub, 0);

        let unsupported_offset = SmtExpr::var("wide", 65);
        let unsupported_summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::OutOfBounds,
            vec!["true".to_string()],
            Some("bounds side condition: offset=wide, object_size=8, access_size=4".to_string()),
            Some(oob_candidate(
                unsupported_offset,
                SmtExpr::bv_const(8, 65),
                4,
                65,
                SmtExpr::bool_const(true),
            )),
        );

        let unsupported_report =
            unsupported_summary.escalate_unknown_obligations_locally(&enabled_config());
        let unsupported_after =
            unsupported_summary.counters_after_solver_escalation(&unsupported_report);

        assert_eq!(
            unsupported_report.results[0].status,
            FsymSolverStatus::Unsupported
        );
        assert_eq!(unsupported_report.remaining_unknown_count(), 1);
        assert_eq!(unsupported_after.unknown, 1);
        assert_eq!(unsupported_after.concrete_ub, 0);
    }

    // Thread-local capture of the LAST (obligation, result) the fsym AY
    // adapter discharged — the certification-gap probe (crate::formal_gap)
    // needs the exact obligation to confirm a diagnostic, and the adapter
    // builds it internally. `capturing_verify_with_ay` is behavior-identical
    // to the production `verify_with_ay` check fn.
    thread_local! {
        static LAST_FSYM_AY: std::cell::RefCell<Option<(ProofObligation, AYResult)>> =
            const { std::cell::RefCell::new(None) };
    }

    fn capturing_verify_with_ay(obligation: &ProofObligation, config: &AYConfig) -> AYResult {
        let result = verify_with_ay(obligation, config);
        LAST_FSYM_AY.with(|slot| {
            *slot.borrow_mut() = Some((obligation.clone(), result.clone()));
        });
        result
    }

    /// `Some(reason)` iff the first escalation result is `Unsupported` and
    /// the captured live discharge is EXACTLY the confirmed certification
    /// gap; every other shape returns `None` and the guarded test falls
    /// through to its original assertions.
    fn fsym_certification_gap(report: &FsymSolverEscalationReport) -> Option<String> {
        if report.results.first()?.status != FsymSolverStatus::Unsupported {
            return None;
        }
        let (obligation, result) = LAST_FSYM_AY.with(|slot| slot.borrow_mut().take())?;
        crate::formal_gap::confirmed_certification_gap(&obligation, &ay_test_config(), &result)
    }

    #[test]
    fn ay_solver_proves_guarded_null_unknown_safe() {
        if !crate::ay_bridge::z3_available() {
            return;
        }
        let x = SmtExpr::var("x", 64);
        let guard = x.clone().eq_expr(SmtExpr::bv_const(0, 64)).not_expr();
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::NullDeref,
            vec![guard.to_string()],
            Some("x".to_string()),
            Some(null_candidate(x, 64, guard)),
        );

        // Same chain as `escalate_unknown_obligations_with_ay`, with the
        // production `verify_with_ay` check wrapped to capture the exact
        // obligation for the certification-gap probe.
        // Clear any stale capture from a previous test on this reused
        // thread before the live escalation runs.
        LAST_FSYM_AY.with(|slot| slot.borrow_mut().take());
        let adapter = FsymAYSolverAdapter::with_checker(ay_test_config(), capturing_verify_with_ay);
        let report = summary.escalate_unknown_obligations_with(&enabled_config(), &adapter);

        // Certification-gap guard (crate::formal_gap): skip LOUDLY on the
        // exact fail-closed gap diagnostics only.
        if let Some(reason) = fsym_certification_gap(&report) {
            crate::formal_gap::print_gap_skip(
                "ay_solver_proves_guarded_null_unknown_safe",
                &reason,
            );
            return;
        }

        assert!(report.enabled);
        assert_eq!(report.results.len(), 1);
        assert_eq!(report.results[0].status, FsymSolverStatus::ProvenSafe);
        assert!(report.results[0].detail.contains("ay proved"));
        assert!(report.results[0].witness.is_empty());
    }

    #[test]
    fn ay_solver_proves_symbolic_oob_safe() {
        if !crate::ay_bridge::z3_available() {
            return;
        }
        let offset = SmtExpr::var("i", 4);
        let guard = offset.clone().bvule(SmtExpr::bv_const(4, 4));
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::OutOfBounds,
            vec![guard.to_string()],
            Some("bounds side condition: offset=i, object_size=8, access_size=4".to_string()),
            Some(oob_candidate(offset, SmtExpr::bv_const(8, 4), 4, 4, guard)),
        );

        // Same chain as `escalate_unknown_obligations_with_ay`, with the
        // production `verify_with_ay` check wrapped to capture the exact
        // obligation for the certification-gap probe.
        // Clear any stale capture from a previous test on this reused
        // thread before the live escalation runs.
        LAST_FSYM_AY.with(|slot| slot.borrow_mut().take());
        let adapter = FsymAYSolverAdapter::with_checker(ay_test_config(), capturing_verify_with_ay);
        let report = summary.escalate_unknown_obligations_with(&enabled_config(), &adapter);
        let after = summary.counters_after_solver_escalation(&report);

        // Certification-gap guard (crate::formal_gap): skip LOUDLY on the
        // exact fail-closed gap diagnostics only.
        if let Some(reason) = fsym_certification_gap(&report) {
            crate::formal_gap::print_gap_skip("ay_solver_proves_symbolic_oob_safe", &reason);
            return;
        }

        assert_eq!(report.results[0].status, FsymSolverStatus::ProvenSafe);
        assert_eq!(report.remaining_unknown_count(), 0);
        assert_eq!(after.unknown, 0);
    }

    #[test]
    fn ay_solver_reports_symbolic_oob_ub_witness() {
        let offset = SmtExpr::var("i", 4);
        let guard = offset.clone().eq_expr(SmtExpr::bv_const(5, 4));
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::OutOfBounds,
            vec![guard.to_string()],
            Some("bounds side condition: offset=i, object_size=8, access_size=4".to_string()),
            Some(oob_candidate(offset, SmtExpr::bv_const(8, 4), 4, 4, guard)),
        );

        let report =
            summary.escalate_unknown_obligations_with_ay(&enabled_config(), ay_test_config());
        let after = summary.counters_after_solver_escalation(&report);

        assert_eq!(report.results[0].status, FsymSolverStatus::ConcreteUb);
        assert_eq!(report.results[0].witness, [("i".to_string(), 5)]);
        assert_eq!(after.unknown, 0);
        assert_eq!(after.concrete_ub, 1);
    }

    #[test]
    fn ay_solver_reports_arithmetic_ub_witness() {
        let x = SmtExpr::var("x", 2);
        let y = SmtExpr::var("y", 2);
        let guard = x
            .clone()
            .eq_expr(SmtExpr::bv_const(1, 2))
            .and_expr(y.clone().eq_expr(SmtExpr::bv_const(1, 2)));
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::Arithmetic,
            vec![guard.to_string()],
            Some("sadd side condition: x, y".to_string()),
            Some(arithmetic_candidate(
                ArithUbKind::Sadd,
                x,
                Some(y),
                2,
                guard,
            )),
        );

        let report =
            summary.escalate_unknown_obligations_with_ay(&enabled_config(), ay_test_config());

        assert_eq!(report.results[0].status, FsymSolverStatus::ConcreteUb);
        assert!(report.results[0].detail.contains("ay found"));
        assert_eq!(
            report.results[0].witness,
            [("x".to_string(), 1), ("y".to_string(), 1)]
        );
    }

    #[test]
    fn ay_solver_rejects_uaf_as_unsupported() {
        let x = SmtExpr::var("x", 64);
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::UseAfterFree,
            vec!["true".to_string()],
            Some("x".to_string()),
            Some(null_candidate(x, 64, SmtExpr::bool_const(true))),
        );

        let report =
            summary.escalate_unknown_obligations_with_ay(&enabled_config(), ay_test_config());

        assert_eq!(report.results[0].status, FsymSolverStatus::Unsupported);
        assert!(report.results[0].detail.contains("bounds obligations"));
    }

    #[test]
    fn ay_solver_maps_uncertified_timeout_unknown_and_error_to_stable_statuses() {
        let x = SmtExpr::var("x", 64);
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::NullDeref,
            vec!["true".to_string()],
            Some("x".to_string()),
            Some(null_candidate(x, 64, SmtExpr::bool_const(true))),
        );
        let timeout_adapter = FsymAYSolverAdapter::with_checker(ay_test_config(), ay_timeout);
        let unknown_adapter = FsymAYSolverAdapter::with_checker(ay_test_config(), ay_unknown);
        let error_adapter = FsymAYSolverAdapter::with_checker(ay_test_config(), ay_error);
        let solver_unsat_adapter =
            FsymAYSolverAdapter::with_checker(ay_test_config(), ay_solver_unsat);

        let timeout_report =
            summary.escalate_unknown_obligations_with(&enabled_config(), &timeout_adapter);
        let unknown_report =
            summary.escalate_unknown_obligations_with(&enabled_config(), &unknown_adapter);
        let error_report =
            summary.escalate_unknown_obligations_with(&enabled_config(), &error_adapter);
        let solver_unsat_report =
            summary.escalate_unknown_obligations_with(&enabled_config(), &solver_unsat_adapter);

        assert_eq!(timeout_report.results[0].status, FsymSolverStatus::Timeout);
        assert_eq!(
            unknown_report.results[0].status,
            FsymSolverStatus::Unsupported
        );
        assert_eq!(
            error_report.results[0].status,
            FsymSolverStatus::SolverError
        );
        assert_eq!(
            solver_unsat_report.results[0].status,
            FsymSolverStatus::Unsupported
        );
        assert!(
            solver_unsat_report.results[0]
                .detail
                .contains("independently accepted")
        );
    }

    #[test]
    fn ay_solver_adapter_accepts_injected_verified_result() {
        let x = SmtExpr::var("x", 64);
        let summary = summary_with_unknown(
            FsymTrustIrDiagnosticKind::NullDeref,
            vec!["true".to_string()],
            Some("x".to_string()),
            Some(null_candidate(x, 64, SmtExpr::bool_const(true))),
        );
        let adapter = FsymAYSolverAdapter::with_checker(ay_test_config(), ay_verified);

        let report = summary.escalate_unknown_obligations_with(&enabled_config(), &adapter);

        assert_eq!(report.results[0].status, FsymSolverStatus::ProvenSafe);
    }
}
