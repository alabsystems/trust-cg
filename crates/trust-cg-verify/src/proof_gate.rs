// trust-cg-verify/proof_gate.rs - Strict formal-proof gate (P0)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// P0 of the proof-gap program: make formal SMT discharge the DEFAULT gate.
//
// The existing verification entry points (`VerificationRunner::run_auto`,
// `select_auto_mode`) silently DOWNGRADE to mock/statistical verification when
// no SMT solver is available: `select_auto_mode()` returns
// `AYVerificationMode::MockOnly` and the runner reports `VerificationStrength::
// Statistical` / `Exhaustive` results as "passing". For 32/64-bit obligations
// statistical mock is 100K random samples (see `lowering_proof::DEFAULT_SAMPLE_
// COUNT`), which is NOT a formal proof and has hidden ~17 miscompiles' worth of
// gaps in the surrounding (non-SMT) code.
//
// This module adds a *fail-closed* gate that:
//   1. ERRORS (never downgrades) when no external ay/Z3 solver is available.
//   2. Treats an obligation as passing ONLY if it is formally `AYResult::Verified`
//      via the ay solver. A statistical-mock-only pass does NOT count.
//   3. Surfaces Timeout / Unknown / Error / CounterExample as gate FAILURES,
//      each enumerated with its category and detail.
//
// It is built on the real ay bridge:
//   - `ay_bridge::z3_available()`  — CLI solver detection.
//   - `ay_bridge::verify_with_ay(&obligation, &config)` — formal discharge.
//     Dispatches to the external solver subprocess and returns `AYResult`.
//   - `AYResult::Verified` is the ONLY outcome that counts as a formal proof.
//
// ---------------------------------------------------------------------------
// TRUSTED COMPUTING BASE (TCB) — read before relying on a `Verified` verdict.
// ---------------------------------------------------------------------------
// A `Verified` from this gate is only as sound as the components it trusts.
// The gate's TCB explicitly INCLUDES:
//   1. The ay/z3 solver itself (it answers sat/unsat).
//   2. `ay_bridge::verify_with_ay` and the SMT-LIB2 emission it drives. The
//      local bitvector simplifier (`ay_bridge::prepare_formula_for_smt` ->
//      `simplify_solver_expr`) still runs BEFORE the solver to help it, but is
//      no longer trusted to *decide* an obligation by itself — see below.
//
// CLOSED TCB CAVEAT (the simplifier can no longer mint a `Verified` alone):
//   The gate proves a lowering correct by asking the solver whether the NEGATED
//   equivalence (trust_ir != machine) is UNSAT. If `simplify_solver_expr` folded
//   the negated-equivalence body down to a degenerate constant `false` (e.g. via
//   an unsound rewrite rule), the solver would receive an effective
//   `(assert false)`, return `unsat`, and the gate would report `Verified` for
//   an obligation it NEVER actually checked — a false negative (an unsound pass).
//   This is now GUARDED in ay_bridge (mitigation (b) from the original triage):
//   `verify_with_ay` detects, via `ay_bridge::simplifier_alone_proved_unsat`,
//   the case where the solver-oriented simplifier ALONE collapsed the formula to
//   constant `false` (i.e. the *bounded-quantifier-expanded* raw form was not
//   already `false`). In that case it does NOT trust the simplified form: it
//   re-emits the UN-simplified raw negated equivalence (bounded quantifiers
//   still expanded — a sound mechanical unroll) and requires the SOLVER to
//   return `unsat` on it. Only a SOLVER `unsat` on the real formula yields
//   `Verified`; a satisfiable formula the simplifier wrongly folded would now
//   surface as a CounterExample (gate failure), never a pass. The fast
//   simplified path is kept for every non-degenerate obligation. A genuinely
//   tautological obligation (raw form already constant `false`) is the real
//   formula and is still trusted, which is sound.
//   (The guard lives in ay_bridge, not here, because this module sees only the
//   final `AYResult`, not the simplified SMT body.)
//
// Reference: crates/trust-cg-verify/src/verification_runner.rs (select_auto_mode),
//            crates/trust-cg-verify/src/ay_bridge.rs (z3_available, verify_with_ay,
//            prepare_formula_for_smt, simplify_solver_expr,
//            simplifier_alone_proved_unsat, generate_smt2_query_raw,
//            AYConfig, AYResult, ProofDatabaseAYReport),
//            crates/trust-cg-verify/src/proof_database.rs (ProofDatabase).

//! Strict formal-proof gate.
//!
//! Unlike [`select_auto_mode`], which downgrades to mock verification when no
//! solver is present, [`GateConfig::discharge`] *fails closed*: it requires a
//! real SMT solver and counts an obligation as passing only when ay reports
//! [`AYResult::Verified`].
//!
//! [`select_auto_mode`]: crate::verification_runner::select_auto_mode
//! [`AYResult::Verified`]: crate::ay_bridge::AYResult::Verified
//!
//! # Example
//!
//! ```rust,no_run
//! use trust_cg_verify::proof_database::ProofDatabase;
//! use trust_cg_verify::proof_gate::GateConfig;
//!
//! let db = ProofDatabase::new();
//! // Fails closed if no solver is present, or if any obligation is not
//! // formally Valid, or fell back to statistical mock.
//! GateConfig::strict().discharge(&db).expect("formal gate must pass");
//! ```

use std::time::{Duration, Instant};

use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay, z3_available};
use crate::proof_database::{ProofCategory, ProofDatabase};

/// Per-obligation solver timeout the STRICT gate grants, in milliseconds (120 s).
///
/// This is deliberately larger than [`crate::ay_bridge::DEFAULT_AY_TIMEOUT_MS`]
/// (30 s). A handful of full-database obligations are *semantically correct* but
/// *capacity-bound* — they are heavy for a bit-blasting solver yet discharge
/// given a longer budget (e.g. the high-half of a 128-bit multiply, and the
/// I64-disjoint store/load non-interference proof). 30 s timed them out; 120 s
/// lets them finish.
///
/// SOUNDNESS: raising the budget NEVER turns a wrong obligation into a pass — a
/// timeout is still surfaced as [`AYResult::Timeout`] and counted as a gate
/// FAILURE (see [`GateObligationResult::is_formally_valid`]). A longer budget
/// only gives a *correct* obligation more time to be proved `unsat`; it cannot
/// make a *satisfiable* (counterexample-bearing) obligation report `Verified`.
///
/// Override at runtime via `TRUST_CG_AY_TIMEOUT_MS` (honored by
/// [`AYConfig::default`]); [`GateConfig::strict`] then re-applies this floor
/// only when the environment did not already ask for a *larger* budget, so an
/// operator can extend but not silently shrink the strict gate's budget.
pub const STRICT_GATE_TIMEOUT_MS: u64 = 120_000;

// ---------------------------------------------------------------------------
// GateOutcome: per-obligation formal outcome
// ---------------------------------------------------------------------------

/// Why a single obligation did NOT pass the strict gate.
///
/// Anything other than [`AYResult::Verified`] is a gate failure. This enum
/// records *which* non-formal outcome occurred so the report can distinguish a
/// genuine miscompile (counterexample) from a solver capacity problem
/// (timeout/unknown) — both of which still fail the gate, never silently pass.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum GateFailureKind {
    /// The solver found a satisfying assignment to the negated equivalence:
    /// a concrete counterexample. This is the strongest signal of a real
    /// lowering bug.
    CounterExample,
    /// The solver ran but timed out before deciding. A timeout is NOT a pass.
    Timeout,
    /// The solver returned `unknown` (incomplete theory, resource limit, etc.).
    /// [`GateObligationResult::failure_class`] promotes proof-authority rejection
    /// and internal-error reasons to a hard soundness failure.
    Unknown,
    /// The solver errored (parse failure, missing binary at call time, etc.).
    Error,
}

impl GateFailureKind {
    /// Stable short label for reports/logs.
    pub fn label(&self) -> &'static str {
        match self {
            GateFailureKind::CounterExample => "COUNTEREXAMPLE",
            GateFailureKind::Timeout => "TIMEOUT",
            GateFailureKind::Unknown => "UNKNOWN",
            GateFailureKind::Error => "ERROR",
        }
    }

    /// Coarse classification of this failure for reporting.
    ///
    /// Distinguishes a *soundness* failure (the solver actively disproved the
    /// obligation, or could not even be run) from a *solver-capacity* failure
    /// (the solver ran but did not finish in budget). BOTH still fail the gate
    /// — neither ever counts as a pass — but a capacity failure is an explicit,
    /// non-silent "formally pending" status rather than evidence of a bug.
    pub fn class(&self) -> FailureClass {
        match self {
            // A counterexample is a concrete disproof; an error means the solver
            // could not run the check at all. Either is a hard soundness signal.
            GateFailureKind::CounterExample | GateFailureKind::Error => FailureClass::Soundness,
            // Timeout / Unknown: the solver ran but ran out of budget/decidability.
            // The obligation is neither proved nor disproved — formally PENDING.
            GateFailureKind::Timeout | GateFailureKind::Unknown => FailureClass::SolverCapacity,
        }
    }
}

/// Coarse category of a non-`Verified` gate outcome.
///
/// The strict gate NEVER treats either class as a pass (only [`AYResult::Verified`]
/// passes). This split exists purely so a report can separate a genuine
/// soundness failure (a real or unrunnable obligation) from an explicit,
/// non-silent "formally pending (solver capacity)" status, and so CI can triage
/// the full-database floor down to a SMALL, explicitly-categorized set without
/// swallowing a timeout as success.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FailureClass {
    /// The solver disproved the obligation (counterexample) or could not run the
    /// check (error). A bug or a broken environment — must be fixed.
    Soundness,
    /// The solver ran but did not decide within budget (timeout) or returned an
    /// ordinary incompleteness/resource `unknown`. Proof-authority rejection and
    /// internal-error unknown reasons are promoted to [`Self::Soundness`]. A
    /// capacity-bound obligation is reported as formally PENDING, never passed.
    SolverCapacity,
}

impl FailureClass {
    /// Stable short label for reports/logs.
    pub fn label(&self) -> &'static str {
        match self {
            FailureClass::Soundness => "SOUNDNESS",
            FailureClass::SolverCapacity => "PENDING(solver-capacity)",
        }
    }
}

/// Outcome of discharging a single obligation through the strict gate.
#[derive(Debug, Clone)]
pub struct GateObligationResult {
    /// Obligation name.
    pub name: String,
    /// Obligation category.
    pub category: ProofCategory,
    /// The raw ay outcome.
    pub ay_result: AYResult,
    /// Time taken to discharge this obligation.
    pub duration: Duration,
}

impl GateObligationResult {
    /// True iff this obligation was formally proved (`AYResult::Verified`).
    ///
    /// This is the ONLY passing outcome. A statistical-mock pass is impossible
    /// here because the strict gate never invokes the mock evaluator.
    pub fn is_formally_valid(&self) -> bool {
        matches!(self.ay_result, AYResult::Verified)
    }

    /// Classify a non-passing outcome, or `None` if formally valid.
    pub fn failure_kind(&self) -> Option<GateFailureKind> {
        match self.ay_result {
            AYResult::Verified => None,
            AYResult::SolverUnsat => Some(GateFailureKind::Unknown),
            AYResult::CounterExample(_) => Some(GateFailureKind::CounterExample),
            AYResult::Timeout => Some(GateFailureKind::Timeout),
            AYResult::Unknown(_) => Some(GateFailureKind::Unknown),
            AYResult::Error(_) => Some(GateFailureKind::Error),
        }
    }

    /// Coarse class of a non-passing outcome, or `None` if formally valid.
    ///
    /// A [`FailureClass::SolverCapacity`] result is formally PENDING, not a pass:
    /// it still fails the gate (`is_formally_valid()` is false), but the report
    /// can list it separately from a genuine [`FailureClass::Soundness`] failure.
    /// AY's stable `self-check-rejected`, legacy `proof-trusted`, and
    /// `internal-error` unknown reasons are not capacity failures: they mean the
    /// proof authority rejected a computed verdict or the solver malfunctioned,
    /// so this method promotes them to `Soundness` fail-closed.
    pub fn failure_class(&self) -> Option<FailureClass> {
        match &self.ay_result {
            AYResult::Unknown(reason) if unknown_is_hard_failure(reason) => {
                Some(FailureClass::Soundness)
            }
            _ => self.failure_kind().map(|kind| kind.class()),
        }
    }

    /// Human-readable failure detail (counterexample assignment, reason text).
    pub fn detail(&self) -> String {
        match &self.ay_result {
            AYResult::Verified => "VERIFIED".to_string(),
            AYResult::SolverUnsat => {
                "SOLVER UNSAT (UNCERTIFIED): no independently accepted exact proof".to_string()
            }
            AYResult::CounterExample(cex) => format!(
                "COUNTEREXAMPLE: {}",
                cex.iter()
                    .map(|(n, v)| format!("{} = {:#x}", n, v))
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            AYResult::Timeout => "TIMEOUT".to_string(),
            AYResult::Unknown(msg) => format!("UNKNOWN: {}", msg),
            AYResult::Error(msg) => format!("ERROR: {}", msg),
        }
    }
}

/// AY reason-unknown markers that describe a broken/rejected authority path,
/// not search incompleteness or resource exhaustion. AY deliberately exposes
/// `self-check-rejected` as a greppable soundness-gate result; treating it as
/// solver capacity would allow a caught wrong answer to enter a PENDING ledger.
fn unknown_is_hard_failure(reason: &str) -> bool {
    let reason = reason.to_ascii_lowercase();
    reason.contains("self-check-rejected")
        || reason.contains("proof-trusted")
        || reason.contains("internal-error")
}

// ---------------------------------------------------------------------------
// GateError: fail-closed errors
// ---------------------------------------------------------------------------

/// Reason the strict gate failed.
///
/// Distinct from a per-obligation failure: a [`GateError`] is the overall
/// verdict returned by [`GateConfig::discharge`]. The strict gate returns
/// `Err` rather than a downgraded "pass" so callers (tests, CI) cannot
/// accidentally treat the absence of a solver as success.
#[derive(Debug, Clone)]
pub enum GateError {
    /// No SMT solver was available and the gate is configured to require one.
    ///
    /// This is the central P0 fix: where `select_auto_mode()` would have
    /// returned `MockOnly`, the strict gate fails here instead.
    NoSolver {
        /// Whether an internal native-ay adapter was compiled in.
        /// Always false in the v0.1.0 public Cargo surface.
        native_ay_compiled: bool,
        /// Diagnostic describing where solvers were searched.
        detail: String,
    },
    /// The database was empty; there was nothing to prove.
    EmptyDatabase,
    /// At least one obligation was not formally `Verified`.
    ///
    /// Carries the full report so the caller can enumerate every offending
    /// obligation (counterexamples, timeouts, unknowns, errors).
    NotAllVerified(GateReport),
}

impl std::fmt::Display for GateError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GateError::NoSolver {
                native_ay_compiled,
                detail,
            } => write!(
                f,
                "strict proof gate FAILED: no SMT solver available (native ay compiled: {}). {} \
                 The gate refuses to downgrade to statistical mock verification. \
                 Install an `ay` or `z3` binary on PATH and re-run.",
                native_ay_compiled, detail
            ),
            GateError::EmptyDatabase => {
                write!(f, "strict proof gate FAILED: proof database is empty")
            }
            GateError::NotAllVerified(report) => write!(
                f,
                "strict proof gate FAILED: {}/{} obligations not formally Verified \
                 ({} SOUNDNESS, {} PENDING(solver-capacity))\n{}",
                report.not_verified(),
                report.total(),
                report.count_failure_class(FailureClass::Soundness),
                report.count_failure_class(FailureClass::SolverCapacity),
                report.failure_summary()
            ),
        }
    }
}

impl std::error::Error for GateError {}

// ---------------------------------------------------------------------------
// GateReport
// ---------------------------------------------------------------------------

/// Result of a full strict-gate run over a [`ProofDatabase`].
#[derive(Debug, Clone)]
pub struct GateReport {
    /// Per-obligation outcomes.
    pub results: Vec<GateObligationResult>,
    /// Whether the native ay API was compiled in for this run.
    pub native_ay_compiled: bool,
    /// Solver identity string (`ay_bridge::solver_info()`), for the run header.
    pub solver_info: String,
    /// Total wall-clock duration.
    pub total_duration: Duration,
}

/// Independent-proof evidence accounting for one gate run.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ProofEvidenceSummary {
    /// Obligations promoted to `Verified` by an independently accepted proof.
    pub checked_accepted: usize,
    /// AY emitted an explicitly holey/trusted-step certificate.
    pub holey: usize,
    /// An exact proof artifact was present but the checker rejected it.
    pub checker_rejected: usize,
    /// AY reported UNSAT but no proof/checker was available.
    pub missing: usize,
    /// A raw solver-only UNSAT escaped promotion (never formal authority).
    pub solver_unsat_uncertified: usize,
    /// Timeout/solver-unknown outcomes unrelated to proof evidence.
    pub capacity_or_other_pending: usize,
}

impl ProofEvidenceSummary {
    /// Proof-evidence failures that a proof-bearing success gate must reject.
    pub fn failures(self) -> usize {
        self.holey + self.checker_rejected + self.missing + self.solver_unsat_uncertified
    }

    /// Exact proof artifacts observed (accepted, holey, or checker-rejected).
    pub fn artifacts_emitted(self) -> usize {
        self.checked_accepted + self.holey + self.checker_rejected
    }
}

impl GateReport {
    /// Total obligations discharged.
    pub fn total(&self) -> usize {
        self.results.len()
    }

    /// Number of obligations that were formally `Verified`.
    pub fn verified(&self) -> usize {
        self.results
            .iter()
            .filter(|r| r.is_formally_valid())
            .count()
    }

    /// Number of obligations that were NOT formally `Verified`.
    pub fn not_verified(&self) -> usize {
        self.total() - self.verified()
    }

    /// Separate solver outcomes from independently checked proof evidence.
    pub fn proof_evidence_summary(&self) -> ProofEvidenceSummary {
        let mut summary = ProofEvidenceSummary::default();
        for result in &self.results {
            match &result.ay_result {
                AYResult::Verified => summary.checked_accepted += 1,
                AYResult::SolverUnsat => summary.solver_unsat_uncertified += 1,
                AYResult::Unknown(reason) => {
                    let lower = reason.to_ascii_lowercase();
                    if lower.contains("incomplete ay proof certificate")
                        || lower.contains("unusable ay proof evidence")
                        || lower.contains("holey")
                    {
                        summary.holey += 1;
                    } else if lower.contains("rejected or could not fully verify") {
                        summary.checker_rejected += 1;
                    } else if lower.contains("no independent clean/carcara checker")
                        || lower.contains("no readable alethe proof")
                        || lower.contains("empty alethe proof")
                    {
                        summary.missing += 1;
                    } else {
                        summary.capacity_or_other_pending += 1;
                    }
                }
                AYResult::Timeout => summary.capacity_or_other_pending += 1,
                AYResult::CounterExample(_) | AYResult::Error(_) => {}
            }
        }
        summary
    }

    /// Count obligations by failure kind.
    pub fn count_failures(&self, kind: GateFailureKind) -> usize {
        self.results
            .iter()
            .filter(|r| r.failure_kind() == Some(kind.clone()))
            .count()
    }

    /// Count non-verified obligations in a given [`FailureClass`].
    pub fn count_failure_class(&self, class: FailureClass) -> usize {
        self.results
            .iter()
            .filter(|r| r.failure_class() == Some(class))
            .count()
    }

    /// True iff EVERY obligation was formally `Verified`.
    pub fn all_verified(&self) -> bool {
        !self.results.is_empty() && self.results.iter().all(|r| r.is_formally_valid())
    }

    /// All non-verified obligations.
    pub fn failures(&self) -> Vec<&GateObligationResult> {
        self.results
            .iter()
            .filter(|r| !r.is_formally_valid())
            .collect()
    }

    /// Non-verified obligations in a given [`FailureClass`].
    pub fn failures_in_class(&self, class: FailureClass) -> Vec<&GateObligationResult> {
        self.results
            .iter()
            .filter(|r| r.failure_class() == Some(class))
            .collect()
    }

    /// Hard SOUNDNESS failures: counterexamples and solver errors.
    ///
    /// These are the only failures that indicate a bug (or a broken solver
    /// environment) rather than a capacity limit. A green *formal floor* is
    /// defined as zero soundness failures (capacity-pending obligations are
    /// reported separately and never as a pass).
    pub fn soundness_failures(&self) -> Vec<&GateObligationResult> {
        self.failures_in_class(FailureClass::Soundness)
    }

    /// Formally PENDING obligations (timeout / unknown): semantically expected
    /// to be correct but capacity-bound. Reported explicitly and separately;
    /// NEVER counted as a pass.
    pub fn solver_capacity_pending(&self) -> Vec<&GateObligationResult> {
        self.failures_in_class(FailureClass::SolverCapacity)
    }

    /// True iff there is at least one hard [`FailureClass::Soundness`] failure.
    ///
    /// This is the predicate CI should use to triage the full-database floor:
    /// `!has_soundness_failure()` means every non-verified obligation is an
    /// explicit, capacity-bound PENDING entry — a small, categorized set — and
    /// not a miscompile. It does NOT mean the gate passed: [`Self::all_verified`]
    /// (the only pass predicate) is still false while any pending entry remains.
    pub fn has_soundness_failure(&self) -> bool {
        self.results
            .iter()
            .any(|r| r.failure_class() == Some(FailureClass::Soundness))
    }

    /// Multi-line summary of every non-verified obligation.
    pub fn failure_summary(&self) -> String {
        self.summary_of(&self.failures())
    }

    /// Multi-line summary of just the formally-PENDING (solver-capacity)
    /// obligations, each tagged with its class so a reader cannot mistake a
    /// pending entry for a pass.
    pub fn pending_summary(&self) -> String {
        self.summary_of(&self.solver_capacity_pending())
    }

    fn summary_of(&self, results: &[&GateObligationResult]) -> String {
        let mut lines = Vec::new();
        for &r in results {
            let class = r.failure_class().map_or("VERIFIED", |c| c.label());
            lines.push(format!(
                "  [{}] [{}] {} -- {}",
                class,
                r.category.name(),
                r.name,
                r.detail()
            ));
        }
        lines.join("\n")
    }
}

impl std::fmt::Display for GateReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Strict Proof Gate Report")?;
        writeln!(f, "========================")?;
        writeln!(f, "Solver:  {}", self.solver_info)?;
        writeln!(f, "Native ay compiled: {}", self.native_ay_compiled)?;
        let status = if self.all_verified() { "PASS" } else { "FAIL" };
        writeln!(
            f,
            "Result:  {} ({}/{} formally Verified)",
            status,
            self.verified(),
            self.total()
        )?;
        writeln!(
            f,
            "Failures: {} counterexample, {} timeout, {} unknown, {} error",
            self.count_failures(GateFailureKind::CounterExample),
            self.count_failures(GateFailureKind::Timeout),
            self.count_failures(GateFailureKind::Unknown),
            self.count_failures(GateFailureKind::Error),
        )?;
        // Explicit, non-silent split: hard soundness failures vs. capacity-bound
        // PENDING. Neither is a pass; this only helps triage the formal floor.
        writeln!(
            f,
            "Classified: {} SOUNDNESS (counterexample/error), {} PENDING(solver-capacity) (timeout/unknown)",
            self.count_failure_class(FailureClass::Soundness),
            self.count_failure_class(FailureClass::SolverCapacity),
        )?;
        writeln!(f, "Duration: {:.3}s", self.total_duration.as_secs_f64())?;
        let failures = self.failures();
        if !failures.is_empty() {
            writeln!(f)?;
            writeln!(f, "Non-verified obligations:")?;
            writeln!(f, "{}", self.failure_summary())?;
            // Re-state the pending set on its own so a reader never has to infer
            // that a timeout was NOT swallowed as a pass.
            let pending = self.solver_capacity_pending();
            if !pending.is_empty() {
                writeln!(f)?;
                writeln!(
                    f,
                    "Formally PENDING (solver-capacity; NOT passed, still fails the gate):"
                )?;
                write!(f, "{}", self.pending_summary())?;
            }
        }
        Ok(())
    }
}

// ---------------------------------------------------------------------------
// GateConfig
// ---------------------------------------------------------------------------

/// Configuration for the strict formal-proof gate.
///
/// The key difference from [`crate::verification_runner::select_auto_mode`] is
/// `require_solver`: when `true`, [`Self::discharge`] returns
/// [`GateError::NoSolver`] instead of silently falling back to mock evaluation.
///
/// Note: [`AYConfig`] derives neither `Debug` nor `Clone`, so `GateConfig`
/// intentionally derives neither.
pub struct GateConfig {
    /// ay/z3 solver configuration (timeout, model production, binary path).
    pub ay_config: AYConfig,
    /// If `true`, the gate ERRORS when no solver is available rather than
    /// downgrading. Strict mode sets this `true`.
    pub require_solver: bool,
}

impl Default for GateConfig {
    fn default() -> Self {
        Self::strict()
    }
}

impl GateConfig {
    /// Strict, fail-closed gate: requires a solver and counts only formal
    /// `Verified` outcomes as passing. This is the P0 default.
    ///
    /// The per-obligation solver budget is raised to [`STRICT_GATE_TIMEOUT_MS`]
    /// (120 s) so the small set of *semantically-correct but capacity-bound*
    /// full-database obligations (e.g. 128-bit multiply high-half, I64-disjoint
    /// store/load non-interference) discharge instead of timing out at the 30 s
    /// default. An operator may extend the budget further (or to "no timeout")
    /// via `TRUST_CG_AY_TIMEOUT_MS`, but cannot silently shrink it below the
    /// strict floor — see [`strict_gate_budget`].
    pub fn strict() -> Self {
        Self {
            ay_config: AYConfig::default().with_timeout(strict_gate_budget()),
            require_solver: true,
        }
    }

    /// Strict gate with a custom ay configuration (e.g. a longer timeout).
    pub fn strict_with_ay(ay_config: AYConfig) -> Self {
        Self {
            ay_config,
            require_solver: true,
        }
    }

    /// Whether a usable solver backend is present.
    ///
    /// True when an external solver binary is discoverable via
    /// [`z3_available`]. The native adapter is not part of v0.1.0.
    pub fn solver_available(&self) -> bool {
        native_ay_compiled() || z3_available()
    }

    /// Discharge every obligation in `db` formally and fail closed.
    ///
    /// Returns:
    /// - `Err(GateError::NoSolver)` if `require_solver` and no solver is present.
    /// - `Err(GateError::EmptyDatabase)` if `db` has no obligations.
    /// - `Err(GateError::NotAllVerified(report))` if any obligation is not
    ///   formally `Verified` (counterexample / timeout / unknown / error).
    /// - `Ok(report)` only when EVERY obligation is `AYResult::Verified`.
    ///
    /// Every obligation is sent through [`verify_with_ay`], which uses the
    /// external solver subprocess in v0.1.0. The mock evaluator is never
    /// consulted, so a statistical-only "pass" cannot satisfy this gate.
    ///
    /// This probes the real environment via [`Self::solver_available`] and
    /// delegates to [`Self::discharge_with_availability`]. The latter is the
    /// testable core: it takes the solver-availability decision as a parameter
    /// so the no-solver fail-closed contract can be asserted UNCONDITIONALLY,
    /// on every machine, regardless of whether a solver happens to be installed.
    pub fn discharge(&self, db: &ProofDatabase) -> Result<GateReport, GateError> {
        self.discharge_with_availability(db, self.solver_available())
    }

    /// Testable core of [`Self::discharge`] with the solver-availability
    /// decision INJECTED rather than probed.
    ///
    /// P0 TEST-GAP FIX: the most important guarantee of this gate — "no solver
    /// => `Err(NoSolver)`, never a downgraded pass" — could previously only be
    /// asserted on a machine with NO solver installed. On every normal dev/CI
    /// box (which has a solver) the test early-returned and the guarantee was
    /// never exercised. By taking `available` as a parameter, a test can pass
    /// `available = false` and assert `Err(GateError::NoSolver)` deterministically
    /// on ANY machine. Passing `available = false` short-circuits BEFORE any
    /// solver call, so no real solver is ever invoked.
    ///
    /// `available` MUST be a faithful answer to "is a usable solver backend
    /// present?"; production callers obtain it from [`Self::solver_available`].
    pub fn discharge_with_availability(
        &self,
        db: &ProofDatabase,
        available: bool,
    ) -> Result<GateReport, GateError> {
        if self.require_solver && !available {
            return Err(GateError::NoSolver {
                native_ay_compiled: native_ay_compiled(),
                detail: format!(
                    "solver available = {}, z3_available() = {}, solver_info = {:?}",
                    available,
                    z3_available(),
                    crate::ay_bridge::solver_info()
                ),
            });
        }

        if db.is_empty() {
            return Err(GateError::EmptyDatabase);
        }

        let start = Instant::now();
        let results: Vec<GateObligationResult> = db
            .all()
            .iter()
            .map(|cp| {
                let proof_start = Instant::now();
                // Formal path only. In v0.1.0 `verify_with_ay` dispatches to
                // the external solver CLI, never to statistical evaluation.
                let ay_result = verify_with_ay(&cp.obligation, &self.ay_config);
                GateObligationResult {
                    name: cp.obligation.name.clone(),
                    category: cp.category,
                    ay_result,
                    duration: proof_start.elapsed(),
                }
            })
            .collect();
        let total_duration = start.elapsed();

        let report = GateReport {
            results,
            native_ay_compiled: native_ay_compiled(),
            solver_info: crate::ay_bridge::solver_info(),
            total_duration,
        };

        if report.all_verified() {
            Ok(report)
        } else {
            Err(GateError::NotAllVerified(report))
        }
    }
}

/// Whether the internal native-ay adapter is compiled into this build.
///
/// The v0.1.0 Cargo surface deliberately leaves this adapter disabled and uses
/// the external solver path. The field remains in reports for schema stability.
pub const fn native_ay_compiled() -> bool {
    false
}

/// The per-obligation solver budget (ms) the STRICT gate grants `verify_with_ay`.
///
/// Floors the environment-resolved [`AYConfig::default`] timeout at
/// [`STRICT_GATE_TIMEOUT_MS`] so that:
/// - a default run uses the 120 s strict budget (lets capacity-bound, correct
///   obligations discharge), and
/// - an operator may *raise* it via `TRUST_CG_AY_TIMEOUT_MS` (a larger value, or
///   `0` meaning "no timeout"), but cannot silently *shrink* it below the strict
///   floor — which would re-introduce the very capacity timeouts this gate is
///   tuned to avoid.
///
/// `0` (no timeout) is treated as the largest possible budget and is preserved.
pub fn strict_gate_budget() -> u64 {
    let env_budget = AYConfig::default().timeout_ms;
    if env_budget == 0 {
        // 0 == "no timeout" in the ay convention: strictly more budget than any
        // finite floor, so honor the operator's unbounded request.
        0
    } else {
        env_budget.max(STRICT_GATE_TIMEOUT_MS)
    }
}

// ---------------------------------------------------------------------------
// Tests (lib-level unit tests; the heavy gate integration test lives in
// tests/proof_gate_strict.rs)
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn cex(name: &str) -> GateObligationResult {
        GateObligationResult {
            name: name.to_string(),
            category: ProofCategory::Arithmetic,
            ay_result: AYResult::CounterExample(vec![("a".to_string(), 0x2a)]),
            duration: Duration::from_millis(1),
        }
    }

    fn verified(name: &str) -> GateObligationResult {
        GateObligationResult {
            name: name.to_string(),
            category: ProofCategory::Arithmetic,
            ay_result: AYResult::Verified,
            duration: Duration::from_millis(1),
        }
    }

    fn report(results: Vec<GateObligationResult>) -> GateReport {
        GateReport {
            results,
            native_ay_compiled: native_ay_compiled(),
            solver_info: "test-solver".to_string(),
            total_duration: Duration::from_millis(2),
        }
    }

    #[test]
    fn verified_is_the_only_pass() {
        assert!(verified("ok").is_formally_valid());
        assert!(!cex("bad").is_formally_valid());

        let timeout = GateObligationResult {
            name: "to".to_string(),
            category: ProofCategory::Division,
            ay_result: AYResult::Timeout,
            duration: Duration::from_millis(1),
        };
        // Critical: a timeout must NOT count as a pass.
        assert!(!timeout.is_formally_valid());
        assert_eq!(timeout.failure_kind(), Some(GateFailureKind::Timeout));

        let unknown = GateObligationResult {
            name: "uk".to_string(),
            category: ProofCategory::Division,
            ay_result: AYResult::Unknown("incomplete".to_string()),
            duration: Duration::from_millis(1),
        };
        assert!(!unknown.is_formally_valid());
        assert_eq!(unknown.failure_kind(), Some(GateFailureKind::Unknown));

        let solver_unsat = GateObligationResult {
            name: "uncertified".to_string(),
            category: ProofCategory::Arithmetic,
            ay_result: AYResult::SolverUnsat,
            duration: Duration::from_millis(1),
        };
        assert!(!solver_unsat.is_formally_valid());
        assert_eq!(solver_unsat.failure_kind(), Some(GateFailureKind::Unknown));
        assert!(solver_unsat.detail().contains("UNCERTIFIED"));
    }

    #[test]
    fn proof_evidence_summary_never_hides_uncertified_or_holey_unsat() {
        let outcome = |name: &str, ay_result: AYResult| GateObligationResult {
            name: name.to_string(),
            category: ProofCategory::Arithmetic,
            ay_result,
            duration: Duration::from_millis(1),
        };
        let r = report(vec![
            verified("checked"),
            outcome("raw", AYResult::SolverUnsat),
            outcome(
                "holey",
                AYResult::Unknown("incomplete AY proof certificate: unproved_steps=1".to_string()),
            ),
            outcome(
                "rejected",
                AYResult::Unknown(
                    "checker rejected or could not fully verify the exact Alethe proof".to_string(),
                ),
            ),
            outcome(
                "missing",
                AYResult::Unknown(
                    "AY reported UNSAT but no independent Clean/Carcara checker is available"
                        .to_string(),
                ),
            ),
            outcome("timeout", AYResult::Timeout),
        ]);
        let evidence = r.proof_evidence_summary();
        assert_eq!(evidence.checked_accepted, 1);
        assert_eq!(evidence.holey, 1);
        assert_eq!(evidence.checker_rejected, 1);
        assert_eq!(evidence.missing, 1);
        assert_eq!(evidence.solver_unsat_uncertified, 1);
        assert_eq!(evidence.capacity_or_other_pending, 1);
        assert_eq!(evidence.artifacts_emitted(), 3);
        assert_eq!(evidence.failures(), 4);
        assert_eq!(r.verified(), 1, "only independently checked proof may pass");
    }

    #[test]
    fn all_verified_requires_nonempty() {
        // An empty result set must not be reported as "all verified".
        let empty = report(vec![]);
        assert!(!empty.all_verified());

        let good = report(vec![verified("a"), verified("b")]);
        assert!(good.all_verified());
        assert_eq!(good.verified(), 2);
        assert_eq!(good.not_verified(), 0);
    }

    #[test]
    fn failure_counts_and_summary() {
        let r = report(vec![verified("ok"), cex("bug")]);
        assert!(!r.all_verified());
        assert_eq!(r.not_verified(), 1);
        assert_eq!(r.count_failures(GateFailureKind::CounterExample), 1);
        let summary = r.failure_summary();
        assert!(summary.contains("bug"));
        assert!(summary.contains("a = 0x2a"));
    }

    #[test]
    fn empty_database_fails_closed() {
        let db = ProofDatabase::from_proofs(vec![]);
        let err = GateConfig::strict().discharge(&db);
        // Either NoSolver (no solver present) or EmptyDatabase — never Ok.
        // We assert it never returns Ok on an empty DB, which is the
        // fail-closed contract.
        assert!(err.is_err(), "empty DB must never produce Ok");
    }

    #[test]
    fn no_solver_error_is_descriptive() {
        let err = GateError::NoSolver {
            native_ay_compiled: false,
            detail: "z3_available() = false".to_string(),
        };
        let msg = format!("{}", err);
        assert!(msg.contains("no SMT solver"));
        assert!(msg.contains("refuses to downgrade"));
        assert!(msg.contains("ay` or `z3"));
    }

    #[test]
    fn native_flag_tracks_feature() {
        assert!(!native_ay_compiled());
    }

    // -----------------------------------------------------------------------
    // Residual close: full-DB gate timeout budget + explicit, non-silent
    // formally-PENDING(solver-capacity) category.
    // -----------------------------------------------------------------------

    fn timeout(name: &str) -> GateObligationResult {
        GateObligationResult {
            name: name.to_string(),
            category: ProofCategory::Arithmetic,
            ay_result: AYResult::Timeout,
            duration: Duration::from_millis(1),
        }
    }

    fn unknown(name: &str) -> GateObligationResult {
        GateObligationResult {
            name: name.to_string(),
            category: ProofCategory::Division,
            ay_result: AYResult::Unknown("incomplete".to_string()),
            duration: Duration::from_millis(1),
        }
    }

    fn authority_rejected_unknown(name: &str, reason: &str) -> GateObligationResult {
        GateObligationResult {
            name: name.to_string(),
            category: ProofCategory::Division,
            ay_result: AYResult::Unknown(reason.to_string()),
            duration: Duration::from_millis(1),
        }
    }

    fn error(name: &str) -> GateObligationResult {
        GateObligationResult {
            name: name.to_string(),
            category: ProofCategory::Arithmetic,
            ay_result: AYResult::Error("solver unavailable".to_string()),
            duration: Duration::from_millis(1),
        }
    }

    #[test]
    fn strict_gate_grants_raised_timeout_budget() {
        // The strict gate must pass `verify_with_ay` a per-obligation budget of
        // at least STRICT_GATE_TIMEOUT_MS (120 s) so the capacity-bound but
        // semantically-correct obligations discharge instead of timing out at
        // the 30 s default.
        assert_eq!(STRICT_GATE_TIMEOUT_MS, 120_000);
        let gate = GateConfig::strict();
        assert!(
            gate.ay_config.timeout_ms >= STRICT_GATE_TIMEOUT_MS || gate.ay_config.timeout_ms == 0,
            "strict gate must grant >= {} ms (or 0 = no timeout), got {}",
            STRICT_GATE_TIMEOUT_MS,
            gate.ay_config.timeout_ms
        );
    }

    #[test]
    fn failure_class_splits_capacity_from_soundness() {
        // Timeout and ordinary incomplete Unknown are capacity-bound -> PENDING.
        assert_eq!(
            timeout("t").failure_class(),
            Some(FailureClass::SolverCapacity)
        );
        assert_eq!(
            unknown("u").failure_class(),
            Some(FailureClass::SolverCapacity)
        );
        // A proof-authority rejection is a caught wrong answer, not capacity.
        for reason in [
            "(:reason-unknown (incomplete self-check-rejected))",
            "(:reason-unknown (incomplete proof-trusted))",
            "(:reason-unknown internal-error)",
        ] {
            let rejected = authority_rejected_unknown("rejected", reason);
            assert_eq!(
                rejected.failure_kind(),
                Some(GateFailureKind::Unknown),
                "the raw solver outcome remains Unknown"
            );
            assert_eq!(
                rejected.failure_class(),
                Some(FailureClass::Soundness),
                "authority/internal unknown must fail hard: {reason}"
            );
            assert_eq!(report(vec![rejected]).soundness_failures().len(), 1);
        }
        // Counterexample and Error are also hard soundness failures.
        assert_eq!(cex("c").failure_class(), Some(FailureClass::Soundness));
        assert_eq!(error("e").failure_class(), Some(FailureClass::Soundness));
        // A verified obligation has no failure class.
        assert_eq!(verified("ok").failure_class(), None);
        // Match the underlying kind's classification.
        assert_eq!(
            GateFailureKind::Timeout.class(),
            FailureClass::SolverCapacity
        );
        assert_eq!(
            GateFailureKind::Unknown.class(),
            FailureClass::SolverCapacity
        );
        assert_eq!(
            GateFailureKind::CounterExample.class(),
            FailureClass::Soundness
        );
        assert_eq!(GateFailureKind::Error.class(), FailureClass::Soundness);
    }

    #[test]
    fn timeout_is_pending_never_a_pass() {
        // A report with ONLY a capacity-bound timeout: it is formally PENDING,
        // explicitly categorized, and surfaced separately — but it is NEVER a
        // pass and NEVER a soundness failure. This is the core anti-swallow
        // guarantee: a timeout must not be counted as success.
        let r = report(vec![verified("ok"), timeout("slow_but_correct")]);
        assert!(
            !r.all_verified(),
            "a timeout must keep all_verified() false"
        );
        assert!(
            !r.has_soundness_failure(),
            "a pure-timeout report has no soundness failure"
        );
        assert_eq!(r.count_failure_class(FailureClass::SolverCapacity), 1);
        assert_eq!(r.count_failure_class(FailureClass::Soundness), 0);
        assert_eq!(r.solver_capacity_pending().len(), 1);
        assert_eq!(r.solver_capacity_pending()[0].name, "slow_but_correct");

        // The pending obligation is explicitly tagged so it cannot be mistaken
        // for a pass, and the discharge contract still fails closed on it.
        let pending = r.pending_summary();
        assert!(pending.contains("PENDING(solver-capacity)"));
        assert!(pending.contains("slow_but_correct"));
    }

    #[test]
    fn soundness_failure_is_distinguished_from_pending() {
        // A counterexample alongside a timeout: the report must separate the two.
        // has_soundness_failure() is the predicate CI uses to tell a miscompile
        // (must fix) from a capacity-bound pending entry (formally pending).
        let r = report(vec![cex("real_bug"), timeout("slow"), verified("ok")]);
        assert!(r.has_soundness_failure());
        assert_eq!(r.count_failure_class(FailureClass::Soundness), 1);
        assert_eq!(r.count_failure_class(FailureClass::SolverCapacity), 1);
        assert_eq!(r.soundness_failures().len(), 1);
        assert_eq!(r.soundness_failures()[0].name, "real_bug");

        // Both still fail the gate; neither is a pass.
        assert!(!r.all_verified());

        // The error message enumerates both classes so triage is explicit.
        let err = GateError::NotAllVerified(r);
        let msg = format!("{}", err);
        assert!(msg.contains("SOUNDNESS"));
        assert!(msg.contains("PENDING(solver-capacity)"));
    }

    #[test]
    fn all_verified_has_no_soundness_failure_and_no_pending() {
        let r = report(vec![verified("a"), verified("b")]);
        assert!(r.all_verified());
        assert!(!r.has_soundness_failure());
        assert!(r.solver_capacity_pending().is_empty());
        assert!(r.soundness_failures().is_empty());
    }
}
