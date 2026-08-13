// trust-cg-verify/verification_runner.rs - Bulk proof verification with reporting
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Wires the ProofDatabase into the verification pipeline. Provides
// VerificationRunner for running all proofs in the database and
// producing comprehensive reports with per-category breakdowns,
// timing, and failure details.
//
// Reference: crates/trust-cg-verify/src/proof_database.rs,
//            crates/trust-cg-verify/src/verify.rs

//! Bulk proof verification runner.
//!
//! [`VerificationRunner`] takes a [`ProofDatabase`] and verifies every proof
//! obligation, producing a [`VerificationRunReport`] with pass/fail counts,
//! per-category breakdowns, duration tracking, and failure details.
//!
//! # Example
//!
//! ```rust,no_run
//! use trust_cg_verify::proof_database::ProofDatabase;
//! use trust_cg_verify::verification_runner::VerificationRunner;
//!
//! let db = ProofDatabase::new();
//! let runner = VerificationRunner::new(&db);
//! let report = runner.run_all();
//! assert!(report.all_passed());
//! println!("{}", report);
//! ```

use std::time::{Duration, Instant};

// use rayon::prelude::*

use crate::ay_bridge::{AYConfig, AYResult};
use crate::lowering_proof::{VerificationConfig, verify_by_evaluation_with_config};
use crate::proof_database::{CategorizedProof, ProofCategory, ProofDatabase};
use crate::verify::{VerificationResult, VerificationStrength};

// ---------------------------------------------------------------------------
// AYVerificationMode: selects verification backend
// ---------------------------------------------------------------------------

/// Selects the verification backend for [`VerificationRunner`].
///
/// - [`MockOnly`]: Use mock evaluation only.
///   Fast but provides statistical (not formal) verification for 32/64-bit.
/// - [`AYCli`]: Use the z3/ay CLI to attempt formal discharge of every
///   supported represented obligation. Requires a solver binary and is slower;
///   unavailable, timeout, and unknown results are not proofs.
/// - [`MockThenAY`]: Run mock evaluation first as a fast pre-check, then
///   verify proofs that pass mock with z3/ay for formal confirmation.
///   Best of both worlds: fast failure detection + formal proofs.
/// - [`Auto`]: Auto-select the best available backend at runtime.
///   Prefers mock-plus-ay verification when a solver is available and
///   falls back to mock-only verification otherwise.
///
/// [`MockOnly`]: AYVerificationMode::MockOnly
/// [`AYCli`]: AYVerificationMode::AYCli
/// [`MockThenAY`]: AYVerificationMode::MockThenAY
/// [`Auto`]: AYVerificationMode::Auto
pub enum AYVerificationMode {
    /// Use mock evaluation only.
    MockOnly,
    /// Use z3/ay CLI for formal verification.
    AYCli(AYConfig),
    /// Use mock as fast pre-check, then ay for proofs that pass mock.
    MockThenAY(AYConfig),
    /// Auto-select the best available backend at runtime.
    ///
    /// Uses [`MockThenAY`] with the external solver CLI when a solver binary is
    /// available on the system, otherwise falls back to [`MockOnly`].
    ///
    /// [`MockThenAY`]: AYVerificationMode::MockThenAY
    /// [`MockOnly`]: AYVerificationMode::MockOnly
    Auto,
}

/// Select the best verification mode available in the current environment.
///
/// Checks whether an SMT solver binary (ay or z3) is available on `PATH`
/// or in well-known build locations. When a solver is found, returns
/// [`AYVerificationMode::MockThenAY`] with default configuration so that
/// mock evaluation runs as a fast pre-check followed by formal SMT proof.
/// Otherwise returns [`AYVerificationMode::MockOnly`].
pub fn select_auto_mode() -> AYVerificationMode {
    if crate::ay_bridge::z3_available() {
        AYVerificationMode::MockThenAY(AYConfig::default())
    } else {
        AYVerificationMode::MockOnly
    }
}

// ---------------------------------------------------------------------------
// VerificationRunResult: result for a single proof in a run
// ---------------------------------------------------------------------------

/// Result of verifying a single proof obligation during a run.
#[derive(Debug, Clone)]
pub struct VerificationRunResult {
    /// Human-readable proof name.
    pub name: String,
    /// Category this proof belongs to.
    pub category: ProofCategory,
    /// The verification outcome.
    pub result: VerificationResult,
    /// Verification strength level applied.
    pub strength: VerificationStrength,
    /// Time taken to verify this proof.
    pub duration: Duration,
    /// STRICT (task #61): whether the underlying obligation is structurally
    /// DEGENERATE (`trust_ir_expr == aarch64_expr`). Captured at construction
    /// from the obligation — PURELY STRUCTURAL, never from a name ledger. A
    /// degenerate obligation that evaluates `Valid` proves nothing and is
    /// excluded from every genuinely-proven tally.
    pub is_degenerate: bool,
}

impl VerificationRunResult {
    /// Returns true if the proof passed (Valid).
    pub fn is_valid(&self) -> bool {
        matches!(self.result, VerificationResult::Valid)
    }

    /// STRICT HONESTY (task #61): true if this proof's obligation is structurally
    /// DEGENERATE (`trust_ir_expr == aarch64_expr`) — an `X == X` self-equality
    /// that evaluates `Valid` trivially and proves NOTHING (model-consistency
    /// only). PURELY STRUCTURAL: no name ledger. Such a result is NOT genuine
    /// evidence of a correct lowering and is EXCLUDED from any "genuinely
    /// verified" headline count (reported separately as degenerate debt).
    pub fn is_degenerate_debt(&self) -> bool {
        self.is_degenerate
    }

    /// STRICT HONESTY (task #61): true only if the proof passed AND is
    /// non-degenerate — i.e. it is genuine evidence of a correct lowering.
    pub fn is_genuinely_valid(&self) -> bool {
        self.is_valid() && !self.is_degenerate_debt()
    }

    /// Returns true if the proof found a counterexample (Invalid).
    pub fn is_invalid(&self) -> bool {
        matches!(self.result, VerificationResult::Invalid { .. })
    }

    /// Returns true if the result was inconclusive (Unknown).
    pub fn is_unknown(&self) -> bool {
        matches!(self.result, VerificationResult::Unknown { .. })
    }
}

// ---------------------------------------------------------------------------
// CategoryBreakdown: per-category statistics
// ---------------------------------------------------------------------------

/// Per-category verification statistics.
#[derive(Debug, Clone)]
pub struct CategoryBreakdown {
    /// The category.
    pub category: ProofCategory,
    /// Total proofs in this category.
    pub total: usize,
    /// Number that passed.
    pub passed: usize,
    /// Number that failed.
    pub failed: usize,
    /// Number inconclusive.
    pub unknown: usize,
    /// Total time spent verifying proofs in this category.
    pub duration: Duration,
}

// ---------------------------------------------------------------------------
// FailedProofDetail: details about a failed proof
// ---------------------------------------------------------------------------

/// Details about a failed or inconclusive proof.
#[derive(Debug, Clone)]
pub struct FailedProofDetail {
    /// Proof name.
    pub name: String,
    /// Category.
    pub category: ProofCategory,
    /// Counterexample string (for Invalid results) or reason (for Unknown).
    pub detail: String,
}

// ---------------------------------------------------------------------------
// VerificationRunReport: comprehensive verification report
// ---------------------------------------------------------------------------

/// Comprehensive report from running all proofs in the database.
///
/// Includes aggregate statistics, per-category breakdowns, timing, and
/// details for any failed or inconclusive proofs.
#[derive(Debug, Clone)]
pub struct VerificationRunReport {
    /// All individual proof results.
    pub results: Vec<VerificationRunResult>,
    /// Total wall-clock time for the entire run.
    pub total_duration: Duration,
}

impl VerificationRunReport {
    /// Total number of proofs verified.
    pub fn total(&self) -> usize {
        self.results.len()
    }

    /// Number of proofs that passed (Valid). NOTE: this is the RAW pass count and
    /// includes degenerate-debt proofs that evaluate `Valid` trivially. For the
    /// HONEST "genuinely proven" headline use [`Self::genuinely_passed`]; the
    /// difference is [`Self::degenerate_debt_count`].
    pub fn passed(&self) -> usize {
        self.results.iter().filter(|r| r.is_valid()).count()
    }

    /// STRICT HONESTY (task #61): number of proofs that GENUINELY passed —
    /// `Valid` AND structurally non-degenerate (`trust_ir_expr != aarch64_expr`).
    /// This EXCLUDES the degenerate `X == X` self-equalities (which prove
    /// nothing) from the "verified" count. This is the honest headline;
    /// `passed()` is the inflated raw count.
    pub fn genuinely_passed(&self) -> usize {
        self.results
            .iter()
            .filter(|r| r.is_genuinely_valid())
            .count()
    }

    /// STRICT HONESTY (task #61): number of `Valid` results that are structurally
    /// degenerate (`trust_ir_expr == aarch64_expr`). Reported SEPARATELY; NOT
    /// counted as genuinely proven. `passed() == genuinely_passed() +
    /// degenerate_debt_count()` (for the `Valid` subset).
    pub fn degenerate_debt_count(&self) -> usize {
        self.results
            .iter()
            .filter(|r| r.is_valid() && r.is_degenerate_debt())
            .count()
    }

    /// Number of proofs that failed (Invalid).
    pub fn failed(&self) -> usize {
        self.results.iter().filter(|r| r.is_invalid()).count()
    }

    /// Number of proofs that were inconclusive (Unknown).
    pub fn unknown(&self) -> usize {
        self.results.iter().filter(|r| r.is_unknown()).count()
    }

    /// Returns true if NO proof was disproved or left unknown — i.e. zero
    /// soundness failures. This is the "nothing broke" check; it admits
    /// degenerate X==X bindings (which are `Valid` but prove nothing). For the
    /// STRICT "fully proven" predicate use [`Self::all_genuinely_passed`].
    pub fn all_passed(&self) -> bool {
        self.failed() == 0 && self.unknown() == 0
    }

    /// STRICT proven-honesty (task #61): true iff every proof GENUINELY passed —
    /// `Valid` AND non-degenerate. A degenerate `Valid` (X==X model-consistency)
    /// does NOT satisfy this, so a database that keeps any degenerate obligation
    /// is honestly NOT fully proven.
    pub fn all_genuinely_passed(&self) -> bool {
        self.results.iter().all(|r| r.is_genuinely_valid())
    }

    /// Per-category breakdown of results.
    pub fn by_category(&self) -> Vec<CategoryBreakdown> {
        ProofCategory::all_categories()
            .iter()
            .filter_map(|cat| {
                let cat_results: Vec<&VerificationRunResult> =
                    self.results.iter().filter(|r| r.category == *cat).collect();
                if cat_results.is_empty() {
                    return None;
                }
                let total = cat_results.len();
                // STRICT (task #61): per-category `passed` credits ONLY genuinely
                // valid (non-degenerate) results — a degenerate X==X that
                // evaluates Valid proves nothing and never counts as passed.
                let passed = cat_results
                    .iter()
                    .filter(|r| r.is_genuinely_valid())
                    .count();
                let failed = cat_results.iter().filter(|r| r.is_invalid()).count();
                let unknown = cat_results.iter().filter(|r| r.is_unknown()).count();
                let duration: Duration = cat_results.iter().map(|r| r.duration).sum();
                Some(CategoryBreakdown {
                    category: *cat,
                    total,
                    passed,
                    failed,
                    unknown,
                    duration,
                })
            })
            .collect()
    }

    /// Details of all failed proofs (Invalid results).
    pub fn failed_details(&self) -> Vec<FailedProofDetail> {
        self.results
            .iter()
            .filter_map(|r| match &r.result {
                VerificationResult::Invalid { counterexample } => Some(FailedProofDetail {
                    name: r.name.clone(),
                    category: r.category,
                    detail: counterexample.clone(),
                }),
                VerificationResult::Unknown { reason } => Some(FailedProofDetail {
                    name: r.name.clone(),
                    category: r.category,
                    detail: format!("Unknown: {}", reason),
                }),
                VerificationResult::Valid => None,
            })
            .collect()
    }

    /// Number of proofs verified with exhaustive strength.
    pub fn exhaustive_count(&self) -> usize {
        self.results
            .iter()
            .filter(|r| matches!(r.strength, VerificationStrength::Exhaustive))
            .count()
    }

    /// Number of proofs verified with statistical strength.
    pub fn statistical_count(&self) -> usize {
        self.results
            .iter()
            .filter(|r| matches!(r.strength, VerificationStrength::Statistical { .. }))
            .count()
    }
}

impl std::fmt::Display for VerificationRunReport {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Verification Run Report")?;
        writeln!(f, "======================")?;
        writeln!(f)?;

        // Summary line. PASS means ZERO soundness failures (nothing disproved or
        // left unknown). STRICT proven-honesty (task #61) is reported separately
        // below as the GENUINELY-proven count (degenerate X==X excluded). A DB that
        // keeps degenerate model-consistency obligations is still PASS (no
        // disproof) but is honestly NOT fully proven — see `genuinely_passed`.
        let status = if self.failed() == 0 && self.unknown() == 0 {
            "PASS"
        } else {
            "FAIL"
        };
        writeln!(
            f,
            "Result: {} ({}/{} GENUINELY proven, {} failed, {} unknown)",
            status,
            self.genuinely_passed(),
            self.total(),
            self.failed(),
            self.unknown()
        )?;
        writeln!(f, "Duration: {:.3}s", self.total_duration.as_secs_f64())?;
        // STRICT HONESTY (task #61): split the raw `Valid` count into GENUINELY
        // proven vs degenerate debt (X==X self-equalities that prove nothing). The
        // degenerate-debt count is NOT genuine evidence and is shown separately.
        writeln!(
            f,
            "Genuinely proven: {} (degenerate debt excluded: {} — X==X self-equalities that prove nothing)",
            self.genuinely_passed(),
            self.degenerate_debt_count()
        )?;
        writeln!(
            f,
            "Strength: {} exhaustive, {} statistical",
            self.exhaustive_count(),
            self.statistical_count()
        )?;
        writeln!(f)?;

        // Per-category breakdown
        writeln!(f, "Per-category breakdown:")?;
        for bd in &self.by_category() {
            let cat_status = if bd.failed == 0 && bd.unknown == 0 {
                "OK"
            } else {
                "FAIL"
            };
            writeln!(
                f,
                "  {:25} {:>3}/{:>3} passed  [{:>4}]  ({:.3}s)",
                bd.category.name(),
                bd.passed,
                bd.total,
                cat_status,
                bd.duration.as_secs_f64()
            )?;
        }

        // Failed proof details
        let failures = self.failed_details();
        if !failures.is_empty() {
            writeln!(f)?;
            writeln!(f, "Failed proofs:")?;
            for detail in &failures {
                writeln!(
                    f,
                    "  [{}] {} -- {}",
                    detail.category.name(),
                    detail.name,
                    detail.detail
                )?;
            }
        }

        Ok(())
    }
}

// ---------------------------------------------------------------------------
// VerificationRunner
// ---------------------------------------------------------------------------

/// Bulk verification runner backed by a [`ProofDatabase`].
///
/// Verifies proof obligations from the database using mock evaluation
/// ([`verify_by_evaluation`]) and collects results into a
/// [`VerificationRunReport`].
///
/// # Parallel execution
///
/// [`run_parallel`] distributes proofs across `std::thread` worker threads
/// for faster wall-clock time on multi-core machines.
pub struct VerificationRunner<'a> {
    db: &'a ProofDatabase,
    config: VerificationConfig,
}

impl<'a> VerificationRunner<'a> {
    /// Create a runner with default verification configuration.
    pub fn new(db: &'a ProofDatabase) -> Self {
        Self {
            db,
            config: VerificationConfig::default(),
        }
    }

    /// Create a runner with custom verification configuration.
    pub fn with_config(db: &'a ProofDatabase, config: VerificationConfig) -> Self {
        Self { db, config }
    }

    /// Verify every proof in the database sequentially.
    ///
    /// Returns a comprehensive report with per-proof results, category
    /// breakdowns, timing, and failure details.
    pub fn run_all(&self) -> VerificationRunReport {
        let start = Instant::now();
        let results: Vec<VerificationRunResult> =
            self.db.all().iter().map(|cp| self.verify_one(cp)).collect();
        let total_duration = start.elapsed();
        VerificationRunReport {
            results,
            total_duration,
        }
    }

    /// Verify all proofs in a single category.
    ///
    /// Returns a list of (proof_name, VerificationResult) pairs.
    pub fn run_category(&self, cat: ProofCategory) -> Vec<(String, VerificationResult)> {
        self.db
            .by_category(cat)
            .iter()
            .map(|cp| {
                let name = cp.obligation.name.clone();
                let result = verify_by_evaluation_with_config(&cp.obligation, &self.config);
                (name, result)
            })
            .collect()
    }

    /// Verify every proof in the database in parallel using `std::thread`.
    ///
    /// Distributes proofs across `threads` worker threads. Each thread
    /// processes a contiguous chunk of the proof list.
    ///
    /// # Panics
    ///
    /// Panics if `threads` is 0.
    pub fn run_parallel(&self, threads: usize) -> VerificationRunReport {
        assert!(threads > 0, "thread count must be >= 1");

        let start = Instant::now();
        let all_proofs = self.db.all();

        if threads == 1 || all_proofs.len() <= 1 {
            return self.run_all();
        }

        // Clone proofs and config for thread ownership.
        let proofs: Vec<CategorizedProof> = all_proofs.to_vec();
        let config = self.config.clone();
        let chunk_size = proofs.len().div_ceil(threads);

        // Keep each chunk's proof identities (name, category) alongside its
        // worker handle so that, if the worker panics, we can synthesize a
        // fail-closed Unknown verdict for EVERY proof in the dropped chunk
        // rather than silently losing them from `results`. A dropped proof must
        // not vacuously satisfy `all_passed()`.
        #[allow(clippy::type_complexity)]
        let handles: Vec<(
            Vec<(String, ProofCategory)>,
            std::thread::JoinHandle<Vec<VerificationRunResult>>,
        )> = proofs
            .chunks(chunk_size)
            .map(|chunk| {
                let chunk_owned: Vec<CategorizedProof> = chunk.to_vec();
                let chunk_identities: Vec<(String, ProofCategory)> = chunk_owned
                    .iter()
                    .map(|cp| (cp.obligation.name.clone(), cp.category))
                    .collect();
                let thread_config = config.clone();
                let handle = std::thread::spawn(move || {
                    chunk_owned
                        .iter()
                        .map(|cp| {
                            let proof_start = Instant::now();
                            let strength = VerificationStrength::for_obligation_with_config(
                                &cp.obligation,
                                &thread_config,
                            );
                            let result =
                                verify_by_evaluation_with_config(&cp.obligation, &thread_config);
                            let duration = proof_start.elapsed();
                            VerificationRunResult {
                                name: cp.obligation.name.clone(),
                                category: cp.category,
                                result,
                                strength,
                                duration,
                                is_degenerate: cp.obligation.is_degenerate(),
                            }
                        })
                        .collect()
                });
                (chunk_identities, handle)
            })
            .collect();

        let mut results = Vec::with_capacity(proofs.len());
        for (chunk_identities, handle) in handles {
            match handle.join() {
                Ok(chunk_results) => results.extend(chunk_results),
                Err(_) => {
                    // FAIL-CLOSED: a verification worker thread panicked. Rather
                    // than drop that chunk's proofs (which would let the
                    // survivors vacuously satisfy `all_passed()` / shrink
                    // `total()`), synthesize one Unknown verdict per proof in the
                    // panicked chunk so every dropped proof surfaces as
                    // not-passed. `verify_by_evaluation` is not expected to
                    // panic, but a dropped obligation must never read as a pass.
                    for (name, category) in chunk_identities {
                        results.push(VerificationRunResult {
                            name,
                            category,
                            result: VerificationResult::Unknown {
                                reason: "verification worker thread panicked".to_string(),
                            },
                            // Conservative: a panicked worker proved nothing.
                            strength: VerificationStrength::Statistical { sample_count: 0 },
                            duration: Duration::default(),
                            // Unknown verdict; degeneracy is moot but a panicked
                            // worker proved nothing, so it is never genuinely valid.
                            is_degenerate: false,
                        });
                    }
                }
            }
        }

        let total_duration = start.elapsed();
        VerificationRunReport {
            results,
            total_duration,
        }
    }

    /// Verify every proof in the database using a z3/ay CLI solver.
    ///
    /// Each proof is sent to the solver as an SMT-LIB2 query. The result
    /// is mapped to [`VerificationResult`] and the strength is set to
    /// [`VerificationStrength::Formal`] for all proofs verified this way.
    ///
    /// # Graceful degradation
    ///
    /// If no solver is available, all proofs will report
    /// `VerificationResult::Unknown` with a descriptive reason.
    pub fn run_with_ay(&self, ay_config: &AYConfig) -> VerificationRunReport {
        let start = Instant::now();
        let results: Vec<VerificationRunResult> = self
            .db
            .all()
            .iter()
            .map(|cp| {
                let proof_start = Instant::now();
                let ay_result = crate::ay_bridge::verify_with_cli(&cp.obligation, ay_config);
                let duration = proof_start.elapsed();
                let (result, strength) = ay_result_to_verification_result(&ay_result);
                VerificationRunResult {
                    name: cp.obligation.name.clone(),
                    category: cp.category,
                    result,
                    strength,
                    duration,
                    is_degenerate: cp.obligation.is_degenerate(),
                }
            })
            .collect();
        let total_duration = start.elapsed();
        VerificationRunReport {
            results,
            total_duration,
        }
    }

    /// Verify proofs using the best available backend, selected automatically.
    ///
    /// Uses [`select_auto_mode`] to detect whether an SMT solver binary is
    /// available. When one is found, runs mock evaluation as a fast pre-check
    /// then promotes passing proofs to formal ay verification. When no solver
    /// is found, falls back to mock evaluation only.
    ///
    /// This is the recommended entry point for callers that want the strongest
    /// verification available without manual configuration.
    pub fn run_auto(&self) -> VerificationRunReport {
        let mode = select_auto_mode();
        self.run_with_mode(&mode)
    }

    /// Verify proofs using the specified [`AYVerificationMode`].
    ///
    /// - [`AYVerificationMode::MockOnly`]: equivalent to [`run_all()`].
    /// - [`AYVerificationMode::AYCli`]: equivalent to [`run_with_ay()`].
    /// - [`AYVerificationMode::MockThenAY`]: run mock evaluation first;
    ///   for proofs that pass mock, re-verify with ay for formal strength.
    ///   Proofs that fail mock are reported immediately without ay.
    /// - [`AYVerificationMode::Auto`]: equivalent to [`run_auto()`].
    ///
    /// [`run_all()`]: VerificationRunner::run_all
    /// [`run_with_ay()`]: VerificationRunner::run_with_ay
    /// [`run_auto()`]: VerificationRunner::run_auto
    pub fn run_with_mode(&self, mode: &AYVerificationMode) -> VerificationRunReport {
        match mode {
            AYVerificationMode::MockOnly => self.run_all(),
            AYVerificationMode::AYCli(ay_config) => self.run_with_ay(ay_config),
            AYVerificationMode::Auto => self.run_auto(),
            AYVerificationMode::MockThenAY(ay_config) => {
                let start = Instant::now();
                let results: Vec<VerificationRunResult> = self
                    .db
                    .all()
                    .iter()
                    .map(|cp| {
                        let proof_start = Instant::now();
                        // Step 1: fast mock pre-check
                        let mock_result =
                            verify_by_evaluation_with_config(&cp.obligation, &self.config);
                        match &mock_result {
                            VerificationResult::Valid => {
                                // Step 2: promote to formal with ay
                                let ay_result =
                                    crate::ay_bridge::verify_with_cli(&cp.obligation, ay_config);
                                let duration = proof_start.elapsed();
                                let (result, strength) =
                                    ay_result_to_verification_result(&ay_result);
                                VerificationRunResult {
                                    name: cp.obligation.name.clone(),
                                    category: cp.category,
                                    result,
                                    strength,
                                    duration,
                                    is_degenerate: cp.obligation.is_degenerate(),
                                }
                            }
                            _ => {
                                // Mock already found a problem -- no need for ay
                                let duration = proof_start.elapsed();
                                let strength = VerificationStrength::for_obligation_with_config(
                                    &cp.obligation,
                                    &self.config,
                                );
                                VerificationRunResult {
                                    name: cp.obligation.name.clone(),
                                    category: cp.category,
                                    result: mock_result,
                                    strength,
                                    duration,
                                    is_degenerate: cp.obligation.is_degenerate(),
                                }
                            }
                        }
                    })
                    .collect();
                let total_duration = start.elapsed();
                VerificationRunReport {
                    results,
                    total_duration,
                }
            }
        }
    }

    /// Verify a single categorized proof obligation.
    fn verify_one(&self, cp: &CategorizedProof) -> VerificationRunResult {
        let start = Instant::now();
        let strength =
            VerificationStrength::for_obligation_with_config(&cp.obligation, &self.config);
        let result = verify_by_evaluation_with_config(&cp.obligation, &self.config);
        let duration = start.elapsed();
        VerificationRunResult {
            name: cp.obligation.name.clone(),
            category: cp.category,
            result,
            strength,
            duration,
            is_degenerate: cp.obligation.is_degenerate(),
        }
    }
}

/// Convert a [`AYResult`] to a ([`VerificationResult`], [`VerificationStrength`]) pair.
///
/// - `Verified` -> `(Valid, Formal)`
/// - `SolverUnsat` -> `(Unknown, Formal)` (UNSAT lacked checked proof authority)
/// - `CounterExample` -> `(Invalid, Formal)`
/// - `Timeout` -> `(Unknown, Formal)` (solver ran but couldn't decide)
/// - `Unknown` -> `(Unknown, Formal)` (solver explicitly reported unknown)
/// - `Error` -> `(Unknown, Formal)` (solver error, not a mock limitation)
fn ay_result_to_verification_result(
    ay_result: &AYResult,
) -> (VerificationResult, VerificationStrength) {
    match ay_result {
        AYResult::Verified => (VerificationResult::Valid, VerificationStrength::Formal),
        AYResult::SolverUnsat => (
            VerificationResult::Unknown {
                reason: "ay returned UNSAT without an independently accepted exact proof"
                    .to_string(),
            },
            VerificationStrength::Formal,
        ),
        AYResult::CounterExample(cex) => {
            let cex_str = cex
                .iter()
                .map(|(n, v)| format!("{} = {:#x}", n, v))
                .collect::<Vec<_>>()
                .join(", ");
            (
                VerificationResult::Invalid {
                    counterexample: cex_str,
                },
                VerificationStrength::Formal,
            )
        }
        AYResult::Timeout => (
            VerificationResult::Unknown {
                reason: "z3/ay solver timed out".to_string(),
            },
            VerificationStrength::Formal,
        ),
        AYResult::Unknown(msg) => (
            VerificationResult::Unknown {
                reason: format!("z3/ay solver returned unknown: {}", msg),
            },
            VerificationStrength::Formal,
        ),
        AYResult::Error(msg) => (
            VerificationResult::Unknown {
                reason: format!("z3/ay solver error: {}", msg),
            },
            VerificationStrength::Formal,
        ),
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const RUNNER_TEST_SAMPLE_COUNT: u64 = 256;
    const RUNNER_CATEGORY_SAMPLE_LIMIT: usize = 8;

    fn runner_test_config() -> VerificationConfig {
        VerificationConfig::with_sample_count(RUNNER_TEST_SAMPLE_COUNT)
    }

    fn representative_runner_database() -> ProofDatabase {
        let full_db = ProofDatabase::new();
        let config = runner_test_config();
        let mut subset = Vec::new();

        for cat in ProofCategory::all_categories() {
            let proofs = full_db.by_category(*cat);
            let proof = proofs
                .iter()
                .copied()
                .find(|proof| {
                    matches!(
                        VerificationStrength::for_obligation_with_config(
                            &proof.obligation,
                            &config,
                        ),
                        VerificationStrength::Exhaustive
                    )
                })
                .or_else(|| proofs.first().copied())
                .cloned()
                .unwrap_or_else(|| panic!("Category {:?} ({}) has 0 proofs", cat, cat.name()));
            subset.push(proof);
        }

        ProofDatabase::from_proofs(subset)
    }

    fn category_runner_database(cat: ProofCategory) -> ProofDatabase {
        let full_db = ProofDatabase::new();
        let subset: Vec<_> = full_db
            .by_category(cat)
            .into_iter()
            .take(RUNNER_CATEGORY_SAMPLE_LIMIT)
            .cloned()
            .collect();
        assert!(
            !subset.is_empty(),
            "Category {:?} ({}) has 0 proofs",
            cat,
            cat.name()
        );
        ProofDatabase::from_proofs(subset)
    }

    fn strength_mix_runner_database() -> ProofDatabase {
        let full_db = ProofDatabase::new();
        let config = runner_test_config();
        let exhaustive = full_db
            .all()
            .iter()
            .find(|proof| {
                matches!(
                    VerificationStrength::for_obligation_with_config(&proof.obligation, &config),
                    VerificationStrength::Exhaustive
                )
            })
            .cloned()
            .expect("runner tests need at least one exhaustive proof");
        let statistical = full_db
            .all()
            .iter()
            .find(|proof| {
                matches!(
                    VerificationStrength::for_obligation_with_config(&proof.obligation, &config),
                    VerificationStrength::Statistical { .. }
                )
            })
            .cloned()
            .expect("runner tests need at least one statistical proof");

        ProofDatabase::from_proofs(vec![exhaustive, statistical])
    }

    fn bounded_runner(db: &ProofDatabase) -> VerificationRunner<'_> {
        VerificationRunner::with_config(db, runner_test_config())
    }

    // =======================================================================
    // Run all proofs -- they should all pass
    // =======================================================================

    #[test]
    fn test_run_all_passes() {
        let db = representative_runner_database();
        let runner = bounded_runner(&db);
        let report = runner.run_all();

        assert!(report.all_passed(), "Not all proofs passed:\n{}", report);
        assert_eq!(report.total(), db.len());
        assert_eq!(report.failed(), 0);
        assert_eq!(report.unknown(), 0);
    }

    // =======================================================================
    // Category filtering works
    // =======================================================================

    #[test]
    fn test_run_category_arithmetic() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);
        let results = runner.run_category(ProofCategory::Arithmetic);

        let expected_count = db.count_by_category(ProofCategory::Arithmetic);
        assert_eq!(
            results.len(),
            expected_count,
            "run_category(Arithmetic) returned {} results, expected {}",
            results.len(),
            expected_count
        );
        for (name, result) in &results {
            assert!(
                matches!(result, VerificationResult::Valid),
                "Arithmetic proof '{}' did not pass: {:?}",
                name,
                result
            );
        }
    }

    #[test]
    fn test_run_category_memory() {
        let db = category_runner_database(ProofCategory::Memory);
        let runner = bounded_runner(&db);
        let results = runner.run_category(ProofCategory::Memory);

        let expected_count = db.count_by_category(ProofCategory::Memory);
        assert_eq!(results.len(), expected_count);
        for (name, result) in &results {
            assert!(
                matches!(result, VerificationResult::Valid),
                "Memory proof '{}' failed: {:?}",
                name,
                result
            );
        }
    }

    #[test]
    fn test_run_category_every_category_passes() {
        let db = representative_runner_database();
        let runner = bounded_runner(&db);
        for cat in ProofCategory::all_categories() {
            let results = runner.run_category(*cat);
            let expected = db.count_by_category(*cat);
            assert_eq!(
                results.len(),
                expected,
                "Category {:?}: expected {} proofs, got {}",
                cat,
                expected,
                results.len()
            );
            for (name, result) in &results {
                assert!(
                    matches!(result, VerificationResult::Valid),
                    "Category {:?}, proof '{}' failed: {:?}",
                    cat,
                    name,
                    result
                );
            }
        }
    }

    // =======================================================================
    // Report Display formatting
    // =======================================================================

    #[test]
    fn test_report_display_contains_key_fields() {
        let full_db = ProofDatabase::new();
        let mut subset = Vec::new();
        subset.extend(
            full_db
                .by_category(ProofCategory::Arithmetic)
                .into_iter()
                .take(2)
                .cloned(),
        );
        subset.extend(
            full_db
                .by_category(ProofCategory::Memory)
                .into_iter()
                .take(2)
                .cloned(),
        );
        let db = ProofDatabase::from_proofs(subset);
        let runner = bounded_runner(&db);
        let report = runner.run_all();
        let text = format!("{}", report);

        assert!(text.contains("Verification Run Report"), "missing header");
        assert!(text.contains("Result: PASS"), "expected PASS status");
        assert!(text.contains("Duration:"), "missing duration");
        assert!(
            text.contains("Per-category breakdown:"),
            "missing breakdown"
        );
        assert!(text.contains("Arithmetic"), "missing Arithmetic category");
        assert!(text.contains("Memory"), "missing Memory category");
        // Should not contain "Failed proofs:" section since all pass
        assert!(
            !text.contains("Failed proofs:"),
            "unexpected failure section when all proofs pass"
        );
    }

    #[test]
    fn test_report_display_shows_strength() {
        let db = strength_mix_runner_database();
        let runner = bounded_runner(&db);
        let report = runner.run_all();
        let text = format!("{}", report);

        assert!(text.contains("exhaustive"), "missing exhaustive count");
        assert!(text.contains("statistical"), "missing statistical count");
    }

    // =======================================================================
    // Proof count matches ProofDatabase.summary()
    // =======================================================================

    #[test]
    fn test_report_count_matches_summary() {
        let db = representative_runner_database();
        let summary = db.summary();
        let runner = bounded_runner(&db);
        let report = runner.run_all();

        assert_eq!(
            report.total(),
            summary.total,
            "report total ({}) != summary total ({})",
            report.total(),
            summary.total
        );

        // Verify per-category counts match
        let breakdowns = report.by_category();
        for (cat, expected_count) in &summary.by_category {
            if *expected_count == 0 {
                continue;
            }
            let bd = breakdowns.iter().find(|b| b.category == *cat);
            assert!(
                bd.is_some(),
                "category {:?} missing from report breakdown",
                cat
            );
            assert_eq!(
                bd.unwrap().total,
                *expected_count,
                "category {:?}: report has {} proofs, summary has {}",
                cat,
                bd.unwrap().total,
                expected_count
            );
        }
    }

    // =======================================================================
    // Parallel verification
    // =======================================================================

    #[test]
    fn test_run_parallel_matches_sequential() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        assert!(
            db.len() >= 5,
            "need at least 5 Arithmetic proofs for meaningful parallel test, got {}",
            db.len()
        );
        let runner = bounded_runner(&db);

        let sequential = runner.run_all();
        let parallel = runner.run_parallel(4);

        assert_eq!(
            sequential.total(),
            parallel.total(),
            "parallel run returned different proof count"
        );
        assert_eq!(
            sequential.passed(),
            parallel.passed(),
            "parallel run has different pass count"
        );
        assert!(
            parallel.all_passed(),
            "parallel run should pass all proofs:\n{}",
            parallel
        );
    }

    #[test]
    fn test_run_parallel_single_thread() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);
        let report = runner.run_parallel(1);

        assert_eq!(report.total(), db.len());
        assert!(report.all_passed());
    }

    // =======================================================================
    // Duration tracking
    // =======================================================================

    #[test]
    fn test_duration_is_tracked() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);
        let report = runner.run_all();

        // Total duration should be positive
        assert!(
            report.total_duration > Duration::ZERO,
            "total_duration should be > 0"
        );

        // Each proof should have a duration recorded
        assert!(
            report
                .results
                .iter()
                .all(|r| r.duration <= report.total_duration + Duration::from_millis(10)),
            "no individual proof should take longer than the total run"
        );

        // Sum of per-proof durations should approximate total duration
        // (may differ slightly due to loop overhead)
        let sum: Duration = report.results.iter().map(|r| r.duration).sum();
        assert!(
            sum <= report.total_duration + Duration::from_millis(100),
            "sum of per-proof durations ({:?}) should not vastly exceed total ({:?})",
            sum,
            report.total_duration
        );
    }

    // =======================================================================
    // CategoryBreakdown correctness
    // =======================================================================

    #[test]
    fn test_category_breakdown_sums_to_total() {
        let report = VerificationRunReport {
            results: vec![
                VerificationRunResult {
                    name: "arith_ok".to_string(),
                    category: ProofCategory::Arithmetic,
                    result: VerificationResult::Valid,
                    strength: VerificationStrength::Exhaustive,
                    duration: Duration::from_millis(1),
                    is_degenerate: false,
                },
                VerificationRunResult {
                    name: "arith_unknown".to_string(),
                    category: ProofCategory::Arithmetic,
                    result: VerificationResult::Unknown {
                        reason: "solver timeout".to_string(),
                    },
                    strength: VerificationStrength::Formal,
                    duration: Duration::from_millis(2),
                    is_degenerate: false,
                },
                VerificationRunResult {
                    name: "memory_fail".to_string(),
                    category: ProofCategory::Memory,
                    result: VerificationResult::Invalid {
                        counterexample: "addr=0".to_string(),
                    },
                    strength: VerificationStrength::Statistical { sample_count: 32 },
                    duration: Duration::from_millis(3),
                    is_degenerate: false,
                },
            ],
            total_duration: Duration::from_millis(6),
        };

        let breakdowns = report.by_category();
        let bd_total: usize = breakdowns.iter().map(|b| b.total).sum();
        assert_eq!(
            bd_total,
            report.total(),
            "sum of category totals ({}) != report total ({})",
            bd_total,
            report.total()
        );
    }

    // =======================================================================
    // Custom config
    // =======================================================================

    #[test]
    fn test_custom_config_runner() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        let config = VerificationConfig::with_sample_count(1_000);
        let runner = VerificationRunner::with_config(&db, config);

        // With fewer samples, should still pass (these proofs are correct)
        // but run faster
        let report = runner.run_all();
        assert_eq!(report.total(), db.len());
        assert!(report.all_passed());
    }

    // =======================================================================
    // FailedProofDetail -- test with synthetic data
    // =======================================================================

    #[test]
    fn test_failed_details_empty_when_all_pass() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);
        let report = runner.run_all();

        let failures = report.failed_details();
        assert!(
            failures.is_empty(),
            "expected no failure details, got {}",
            failures.len()
        );
    }

    #[test]
    fn test_failed_details_with_synthetic_failure() {
        // Construct a report with a synthetic failure
        let report = VerificationRunReport {
            results: vec![
                VerificationRunResult {
                    name: "good_proof".to_string(),
                    category: ProofCategory::Arithmetic,
                    result: VerificationResult::Valid,
                    strength: VerificationStrength::Exhaustive,
                    duration: Duration::from_millis(10),
                    is_degenerate: false,
                },
                VerificationRunResult {
                    name: "bad_proof".to_string(),
                    category: ProofCategory::Division,
                    result: VerificationResult::Invalid {
                        counterexample: "a=0, b=0".to_string(),
                    },
                    strength: VerificationStrength::Statistical {
                        sample_count: 100_000,
                    },
                    duration: Duration::from_millis(50),
                    is_degenerate: false,
                },
                VerificationRunResult {
                    name: "unknown_proof".to_string(),
                    category: ProofCategory::Memory,
                    result: VerificationResult::Unknown {
                        reason: "timeout".to_string(),
                    },
                    strength: VerificationStrength::Exhaustive,
                    duration: Duration::from_millis(5000),
                    is_degenerate: false,
                },
            ],
            total_duration: Duration::from_millis(5060),
        };

        assert_eq!(report.total(), 3);
        assert_eq!(report.passed(), 1);
        assert_eq!(report.failed(), 1);
        assert_eq!(report.unknown(), 1);
        assert!(!report.all_passed());

        let failures = report.failed_details();
        assert_eq!(failures.len(), 2); // Invalid + Unknown
        assert_eq!(failures[0].name, "bad_proof");
        assert!(failures[0].detail.contains("a=0"));
        assert_eq!(failures[1].name, "unknown_proof");
        assert!(failures[1].detail.contains("timeout"));

        // Display should contain failure section
        let text = format!("{}", report);
        assert!(text.contains("Result: FAIL"));
        assert!(text.contains("Failed proofs:"));
        assert!(text.contains("bad_proof"));
    }

    // =======================================================================
    // ay_result_to_verification_result unit tests
    // =======================================================================

    #[test]
    fn test_ay_result_to_verification_result_verified() {
        let (result, strength) = ay_result_to_verification_result(&AYResult::Verified);
        assert!(matches!(result, VerificationResult::Valid));
        assert_eq!(strength, VerificationStrength::Formal);
    }

    #[test]
    fn test_ay_result_to_verification_result_solver_unsat_is_not_valid() {
        let (result, strength) = ay_result_to_verification_result(&AYResult::SolverUnsat);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(strength, VerificationStrength::Formal);
        if let VerificationResult::Unknown { reason } = result {
            assert!(reason.contains("independently accepted"));
        }
    }

    #[test]
    fn test_ay_result_to_verification_result_counterexample() {
        let cex = AYResult::CounterExample(vec![("a".to_string(), 42)]);
        let (result, strength) = ay_result_to_verification_result(&cex);
        assert!(matches!(result, VerificationResult::Invalid { .. }));
        assert_eq!(strength, VerificationStrength::Formal);
        if let VerificationResult::Invalid { counterexample } = result {
            assert!(counterexample.contains("a = 0x2a"));
        }
    }

    #[test]
    fn test_ay_result_to_verification_result_timeout() {
        let (result, strength) = ay_result_to_verification_result(&AYResult::Timeout);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(strength, VerificationStrength::Formal);
    }

    #[test]
    fn test_ay_result_to_verification_result_unknown() {
        let unknown = AYResult::Unknown("(:reason-unknown incomplete)".to_string());
        let (result, strength) = ay_result_to_verification_result(&unknown);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(strength, VerificationStrength::Formal);
        if let VerificationResult::Unknown { reason } = result {
            assert!(reason.contains("returned unknown"));
            assert!(reason.contains("incomplete"));
        }
    }

    #[test]
    fn test_ay_result_to_verification_result_error() {
        let err = AYResult::Error("parse failure".to_string());
        let (result, strength) = ay_result_to_verification_result(&err);
        assert!(matches!(result, VerificationResult::Unknown { .. }));
        assert_eq!(strength, VerificationStrength::Formal);
        if let VerificationResult::Unknown { reason } = result {
            assert!(reason.contains("parse failure"));
        }
    }

    // =======================================================================
    // run_with_ay integration test (requires z3)
    // =======================================================================

    #[test]
    fn test_run_with_ay_arithmetic_subset() {
        if !crate::ay_bridge::z3_available() {
            return;
        }

        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);
        let ay_config = AYConfig::default();
        let report = runner.run_with_ay(&ay_config);

        assert_eq!(report.total(), db.len());
        assert!(
            report.all_passed(),
            "Not all Arithmetic proofs passed via ay:\n{}",
            report
        );

        // All proofs should have Formal strength
        for r in &report.results {
            assert_eq!(
                r.strength,
                VerificationStrength::Formal,
                "Proof '{}' should have Formal strength",
                r.name
            );
        }
    }

    // =======================================================================
    // run_with_mode tests
    // =======================================================================

    #[test]
    fn test_run_with_mode_mock_only() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);

        let report = runner.run_with_mode(&AYVerificationMode::MockOnly);
        assert_eq!(report.total(), db.len());
        assert!(report.all_passed());
    }

    #[test]
    fn test_run_with_mode_ay_cli() {
        if !crate::ay_bridge::z3_available() {
            return;
        }

        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);

        let ay_config = AYConfig::default();
        let report = runner.run_with_mode(&AYVerificationMode::AYCli(ay_config));
        assert_eq!(report.total(), db.len());
        assert!(report.all_passed());
    }

    #[test]
    fn test_run_with_mode_mock_then_ay() {
        if !crate::ay_bridge::z3_available() {
            return;
        }

        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);

        let ay_config = AYConfig::default();
        let report = runner.run_with_mode(&AYVerificationMode::MockThenAY(ay_config));
        assert_eq!(report.total(), db.len());
        assert!(report.all_passed());

        // Proofs that pass both mock and ay should have Formal strength
        for r in &report.results {
            assert_eq!(
                r.strength,
                VerificationStrength::Formal,
                "Proof '{}' should be promoted to Formal strength after ay confirmation",
                r.name
            );
        }
    }

    // =======================================================================
    // run_auto and select_auto_mode tests
    // =======================================================================

    #[test]
    fn test_select_auto_mode_returns_valid_mode() {
        let mode = select_auto_mode();
        // Must be either MockOnly or MockThenAY depending on solver availability.
        match &mode {
            AYVerificationMode::MockOnly => {
                assert!(
                    !crate::ay_bridge::z3_available(),
                    "select_auto_mode returned MockOnly but z3 is available"
                );
            }
            AYVerificationMode::MockThenAY(_) => {
                assert!(
                    crate::ay_bridge::z3_available(),
                    "select_auto_mode returned MockThenAY but z3 is not available"
                );
            }
            _ => panic!("select_auto_mode should return MockOnly or MockThenAY"),
        }
    }

    #[test]
    fn test_run_auto_arithmetic_subset() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);

        let report = runner.run_auto();
        assert_eq!(report.total(), db.len());
        assert!(
            report.all_passed(),
            "run_auto failed on arithmetic subset:\n{}",
            report
        );
    }

    #[test]
    fn test_run_with_mode_auto() {
        let db = category_runner_database(ProofCategory::Arithmetic);
        let runner = bounded_runner(&db);

        let report = runner.run_with_mode(&AYVerificationMode::Auto);
        assert_eq!(report.total(), db.len());
        assert!(report.all_passed());
    }
}
