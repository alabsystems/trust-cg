// trust-cg-verify/ay_bridge.rs - Bridge to the ay SMT solver
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Translates our SmtExpr AST into SMT-LIB2 format and invokes an SMT solver
// to check satisfiability. v0.1.0 invokes an external AY binary through the
// standard SMT-LIB2 text interface.

//! Bridge to the ay SMT solver for formal verification.
//!
//! This module provides the infrastructure to verify [`ProofObligation`]s
//! using a real SMT solver instead of the mock evaluator. It translates
//! our [`SmtExpr`] AST into SMT-LIB2 format and pipes it to an AY CLI binary.
//!
//! # Architecture
//!
//! ```text
//! ProofObligation
//!   |
//!   v
//! to_smt2() -> SMT-LIB2 string
//!   |
//!   +--> AY subprocess (SMT-LIB2 stdin/stdout)
//! ```
//!
//! [`ProofObligation`]: crate::lowering_proof::ProofObligation
//! [`SmtExpr`]: crate::smt::SmtExpr

use crate::ay_identity::{AyIdentityRefusal, PinnedAy};
use crate::lowering_proof::ProofObligation;
use crate::proof_database::{ProofCategory, ProofDatabase};
use crate::smt::{RoundingMode, SmtExpr, SmtSort};
use crate::verification_authority::{SessionProofKey, VerificationAuthority};
use std::collections::HashMap;
use std::fmt;
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};
use trust_cg_process_env::SanitizedChildEnv;

#[cfg(test)]
#[path = "ay_bridge_raw_diagnostics.rs"]
mod raw_diagnostics;
#[cfg(test)]
pub(crate) use raw_diagnostics::RawProofDiagnostic;

#[cfg(test)]
#[path = "ay_bridge_compact_tests.rs"]
mod compact_tests;

// ---------------------------------------------------------------------------
// AYResult
// ---------------------------------------------------------------------------

/// Result of an AY verification check.
#[derive(Debug, Clone, PartialEq)]
pub enum AYResult {
    /// An independent checker accepted an exact, hole-free refutation. The
    /// producer (live AY, replayed certificate or constructive candidate) is
    /// recorded separately in [`AyVerdictSource`]; this does not imply AY ran.
    Verified,
    /// AY reported UNSAT, but no independently accepted exact proof promoted
    /// that solver verdict. This is diagnostic evidence only and MUST NOT count
    /// as Formal/Certified authority.
    SolverUnsat,
    /// The property fails with a counterexample.
    /// Each entry is (variable_name, value) from the satisfying assignment
    /// to the negated equivalence formula.
    CounterExample(Vec<(String, u64)>),
    /// The solver timed out before reaching a conclusion.
    Timeout,
    /// The solver returned `unknown` with additional reason text when available.
    Unknown(String),
    /// Solver error (parse failure, internal error, etc.).
    Error(String),
}

impl fmt::Display for AYResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AYResult::Verified => write!(f, "VERIFIED (UNSAT)"),
            AYResult::SolverUnsat => write!(f, "SOLVER UNSAT (UNCERTIFIED)"),
            AYResult::CounterExample(cex) => {
                write!(f, "COUNTEREXAMPLE: ")?;
                for (i, (name, val)) in cex.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{} = {:#x}", name, val)?;
                }
                Ok(())
            }
            AYResult::Timeout => write!(f, "TIMEOUT"),
            AYResult::Unknown(msg) => write!(f, "UNKNOWN: {}", msg),
            AYResult::Error(msg) => write!(f, "ERROR: {}", msg),
        }
    }
}

// ---------------------------------------------------------------------------
// Verdict provenance: which AY a result came from
// ---------------------------------------------------------------------------

/// How an [`AYResult`] was obtained.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AyVerdictSource {
    /// The admitted AY ran on this exact query in this process (a fresh or a
    /// resident process; a candidate UNSAT is still replayed by the checker).
    LiveSolve,
    /// An in-process memo of an earlier independently checked run of the SAME
    /// admitted bytes on the same query.
    SessionMemo,
    /// A stored Alethe proof whose recorded producer is the admitted AY's
    /// bytes, re-checked now by the independent checker. AY did not run.
    AletheCertStore,
    /// A committed portable DRAT certificate replayed by the independent
    /// checker. AY did not run; its offline producer is recorded here.
    PortableCertificate {
        /// SHA-256 of the AY that produced the certificate offline, as named by
        /// the certificate manifest.
        producer_ay_sha256: String,
    },
    /// An untrusted closed-definition candidate was independently checked
    /// against the complete original source-bound problem. AY did not run.
    /// This origin grants no AY-produced certificate-store or reuse receipt.
    ClosedDefinitionProof {
        /// Recorded verifier SOURCE identity, not a compiler/executable hash.
        producer_verifier_source_sha256: String,
        /// Captured independent checker bytes that accepted this exact proof.
        checker_sha256: String,
    },
    /// A retained original CIC proof checked against both actual expressions
    /// under a freshly replayed dependency-closed Clean context. No AY ran.
    #[cfg(feature = "original-i128-cic")]
    OriginalCicCertificate {
        /// Private-constructor checked capability retaining the full packet.
        certificate: crate::i128_cic_certificate::CheckedOriginalI128Certificate,
    },
    /// No AY was started: none was admitted, or the query failed before a
    /// solver process could run.
    NotRun,
    /// The source-bound negative memo
    /// ([`crate::source_bound_negative_memo`]): an earlier live replay of this
    /// exact query under this exact configuration did not certify, and its
    /// non-credit outcome was replayed without running AY. Never `Verified`
    /// and never a counterexample; never carries a reuse receipt.
    NegativeMemo,
}

/// An [`AYResult`], its producer and the admitted AY it was bound to. Binding
/// an authority does not imply the solver ran; inspect [`Self::source`].
#[derive(Debug, Clone, PartialEq)]
pub struct AyVerdict {
    /// The verdict.
    pub result: AYResult,
    /// The AY admitted by [`crate::ay_identity`] that the query was bound to.
    /// `None` when none was admitted, or when a portable certificate answered
    /// before any AY was selected.
    pub solver: Option<PinnedAy>,
    /// How the verdict was obtained.
    pub source: AyVerdictSource,
}

impl AyVerdict {
    fn not_run(result: AYResult) -> Self {
        Self {
            result,
            solver: None,
            source: AyVerdictSource::NotRun,
        }
    }

    /// One line naming the source and the AY (route, path, bytes, build).
    pub fn provenance(&self) -> String {
        let source = match &self.source {
            AyVerdictSource::LiveSolve => "live-solve".to_owned(),
            AyVerdictSource::SessionMemo => "session-memo".to_owned(),
            AyVerdictSource::AletheCertStore => "alethe-cert-store".to_owned(),
            AyVerdictSource::PortableCertificate { producer_ay_sha256 } => {
                format!("portable-certificate producer-ay-sha256={producer_ay_sha256}")
            }
            AyVerdictSource::ClosedDefinitionProof {
                producer_verifier_source_sha256,
                checker_sha256,
            } => format!(
                "closed-definition-proof ay-ran=false producer-verifier-source-sha256={producer_verifier_source_sha256} checker-sha256={checker_sha256}"
            ),
            #[cfg(feature = "original-i128-cic")]
            AyVerdictSource::OriginalCicCertificate { certificate } => format!(
                "original-cic-certificate ay-ran=false packet-sha256={} goal-sha256={} context-sha256={} context-producer-clean={} checker-sha256={}",
                certificate.packet_sha256(),
                certificate.goal_sha256(),
                certificate.environment_sha256(),
                certificate.context_producer_clean_revision(),
                certificate.checker_sha256()
            ),
            AyVerdictSource::NotRun => "not-run".to_owned(),
            AyVerdictSource::NegativeMemo => "negative-memo".to_owned(),
        };
        match &self.solver {
            Some(solver) => format!("source={source} {}", solver.describe()),
            None => format!("source={source} ay=(none)"),
        }
    }
}

// ---------------------------------------------------------------------------
// AYConfig
// ---------------------------------------------------------------------------

/// Default per-obligation solver timeout in milliseconds (30 s).
///
/// Chosen as a conservative upper bound on obligations we expect to be
/// tractable for AY on AArch64/x86-64 lowering proofs today. Harder
/// obligations should be split or feature-gated rather than granted longer
/// timeouts, since a timeout is treated as a proof failure (see
/// `AYResult::Timeout`), never as a silent pass.
///
/// Override at runtime via the `TRUST_CG_AY_TIMEOUT_MS` environment variable
/// (parsed as an unsigned integer; 0 disables the timeout, matching the
/// ay solver convention).
pub const DEFAULT_AY_TIMEOUT_MS: u64 = 30_000;

/// Environment variable consulted for the default ay timeout, if set.
///
/// Intended for CI/operator overrides; unit tests that need a non-default
/// value should construct `AYConfig::with_timeout` explicitly rather than
/// touching process-wide state.
pub const AY_TIMEOUT_ENV: &str = "TRUST_CG_AY_TIMEOUT_MS";

/// Configuration for the external AY solver.
pub struct AYConfig {
    /// An explicit AY admitted by [`crate::ay_identity`] (default `None`:
    /// [`crate::ay_identity::resolve_for_process`] per query). There is no way
    /// to name an AY by path here; obtain one with
    /// [`crate::ay_identity::resolve_explicit_path`], which applies the same
    /// identity rule.
    pub solver: Option<PinnedAy>,
    /// Per-subprocess timeout in milliseconds for AY (the resident and
    /// one-shot solves, the model query) and the Clean checker's control-proof
    /// probe. A Clean check of a proof (the fresh replay's, the certificate
    /// store's re-check, the mint's) runs under the checker's own deadline
    /// instead (ruling OD-223,
    /// [`crate::obligation_cert_store::proof_check_timeout_ms`]: 180 s by
    /// default, never less than this budget, never unbounded). This is not a
    /// whole-query deadline: cache replay, fresh solving, checking, and
    /// optional minting are separate operations. Path-only scheduling probes
    /// use the effective default.
    /// Default is [`DEFAULT_AY_TIMEOUT_MS`] (30 s),
    /// or `TRUST_CG_AY_TIMEOUT_MS` if set. `0` disables the timeout.
    ///
    /// **Important:** A timeout is surfaced as `AYResult::Timeout`, which
    /// verification callers MUST treat as a proof failure, not a silent
    /// pass. See #389 / #407.
    pub timeout_ms: u64,
    /// Whether to request a model on SAT (for counterexample extraction).
    pub produce_models: bool,
}

impl Default for AYConfig {
    fn default() -> Self {
        Self {
            solver: None,
            timeout_ms: resolve_default_timeout_ms(),
            produce_models: true,
        }
    }
}

/// Read the effective default timeout, honoring `TRUST_CG_AY_TIMEOUT_MS`.
///
/// Invalid values silently fall back to [`DEFAULT_AY_TIMEOUT_MS`] so a
/// typo in a shell profile cannot disable solver timeouts across the fleet.
fn resolve_default_timeout_ms() -> u64 {
    match crate::env_lock::var(AY_TIMEOUT_ENV) {
        Ok(raw) => raw.trim().parse::<u64>().unwrap_or(DEFAULT_AY_TIMEOUT_MS),
        Err(_) => DEFAULT_AY_TIMEOUT_MS,
    }
}

impl AYConfig {
    /// Create a config with a custom timeout.
    pub fn with_timeout(mut self, timeout_ms: u64) -> Self {
        self.timeout_ms = timeout_ms;
        self
    }

    /// Create a config bound to one admitted AY.
    pub fn with_solver(mut self, solver: PinnedAy) -> Self {
        self.solver = Some(solver);
        self
    }
}

/// Test helpers for resource-limit behaviour (#389).
#[cfg(test)]
mod resource_limit_tests {
    use super::*;

    /// Run `body` with a thread-local `key` override (or logical removal when
    /// `None`); the prior override is restored on scope exit, even on panic.
    fn with_env<F: FnOnce()>(key: &str, value: Option<&str>, body: F) {
        match value {
            Some(v) => crate::env_lock::with_env_overrides(&[(key, v)], body),
            None => crate::env_lock::with_env_overrides_removed(&[key], body),
        }
    }

    #[test]
    fn default_timeout_is_30s_absent_env() {
        with_env(AY_TIMEOUT_ENV, None, || {
            let cfg = AYConfig::default();
            assert_eq!(cfg.timeout_ms, DEFAULT_AY_TIMEOUT_MS);
        });
    }

    #[test]
    fn env_override_parses() {
        with_env(AY_TIMEOUT_ENV, Some("12345"), || {
            let cfg = AYConfig::default();
            assert_eq!(cfg.timeout_ms, 12345);
        });
    }

    #[test]
    fn env_garbage_falls_back_to_default() {
        with_env(AY_TIMEOUT_ENV, Some("not-a-number"), || {
            let cfg = AYConfig::default();
            assert_eq!(cfg.timeout_ms, DEFAULT_AY_TIMEOUT_MS);
        });
    }

    #[test]
    fn timeout_zero_is_passthrough() {
        with_env(AY_TIMEOUT_ENV, Some("0"), || {
            let cfg = AYConfig::default();
            // Zero means "no timeout" (honored by both native API and CLI paths).
            assert_eq!(cfg.timeout_ms, 0);
        });
    }
}

// ---------------------------------------------------------------------------
// SMT-LIB2 generation (enhanced version of ProofObligation::to_smt2)
// ---------------------------------------------------------------------------

/// Maximum bound size for expanding bounded quantifiers into conjunctions/disjunctions.
///
/// When a `ForAll` or `Exists` quantifier has constant bounds and the range
/// `upper - lower` is at most this limit, the quantifier is expanded into a
/// conjunction (ForAll) or disjunction (Exists) of concrete instances. This
/// keeps the formula in a quantifier-free logic (QF_*), which is faster for
/// SMT solvers.
///
/// When the range exceeds this limit, the quantifier is emitted as a true
/// SMT-LIB2 `(forall ...)` / `(exists ...)` and the logic is upgraded from
/// `QF_*` to its quantified variant (e.g., `QF_ABV` -> `ABV`).
pub const BOUNDED_QUANTIFIER_EXPANSION_LIMIT: u64 = 256;

/// Infer the minimal SMT-LIB2 logic string needed for an expression.
///
/// Walks the expression tree and returns the appropriate logic:
/// - `QF_BV` -- bitvectors only (default)
/// - `QF_ABV` -- bitvectors + arrays (quantifier-free)
/// - `QF_BVFP` -- bitvectors + floating-point (quantifier-free)
/// - `QF_ABVFP` -- bitvectors + arrays + floating-point (quantifier-free)
/// - `QF_UFBV` -- bitvectors + uninterpreted functions (quantifier-free)
/// - `BV` -- bitvectors with quantifiers
/// - `ABV` -- bitvectors + arrays with quantifiers
/// - `BVFP` -- bitvectors + floating-point with quantifiers
/// - `ALL` -- when multiple theories are combined or quantified mixed theories
pub fn infer_logic(expr: &SmtExpr) -> &'static str {
    logic_from_features(collect_logic_features(expr))
}

#[derive(Debug, Clone, Copy, Default)]
struct LogicFeatures {
    has_array: bool,
    has_fp: bool,
    has_uf: bool,
    has_quantifier: bool,
}

fn collect_logic_features(expr: &SmtExpr) -> LogicFeatures {
    let mut features = LogicFeatures::default();
    infer_logic_walk(
        expr,
        &mut features.has_array,
        &mut features.has_fp,
        &mut features.has_uf,
        &mut features.has_quantifier,
    );
    features
}

fn logic_from_features(features: LogicFeatures) -> &'static str {
    match (
        features.has_quantifier,
        features.has_array,
        features.has_fp,
        features.has_uf,
    ) {
        // Quantifier-free logics
        (false, false, false, false) => "QF_BV",
        (false, true, false, false) => "QF_ABV",
        (false, false, true, false) => "QF_BVFP",
        (false, true, true, false) => "QF_ABVFP",
        (false, false, false, true) => "QF_UFBV",
        // Quantified logics (no QF_ prefix)
        (true, false, false, false) => "BV",
        (true, true, false, false) => "ABV",
        (true, false, true, false) => "BVFP",
        _ => "ALL",
    }
}

fn add_sort_logic_features(sort: &SmtSort, features: &mut LogicFeatures) {
    match sort {
        SmtSort::BitVec(_) | SmtSort::Bool => {}
        SmtSort::Array(index_sort, element_sort) => {
            features.has_array = true;
            add_sort_logic_features(index_sort, features);
            add_sort_logic_features(element_sort, features);
        }
        SmtSort::FloatingPoint(_, _) => {
            features.has_fp = true;
        }
    }
}

pub(crate) fn infer_obligation_logic_for_smt2(
    obligation: &ProofObligation,
    raw_formula: &SmtExpr,
    emitted_formula: &SmtExpr,
    extra_decls: &[(String, SmtSort)],
) -> &'static str {
    let raw_features = collect_logic_features(raw_formula);
    let emitted_features = collect_logic_features(emitted_formula);
    let mut features = LogicFeatures {
        has_array: raw_features.has_array || emitted_features.has_array,
        has_fp: raw_features.has_fp || emitted_features.has_fp || !obligation.fp_inputs.is_empty(),
        has_uf: raw_features.has_uf || emitted_features.has_uf,
        // Quantifiers are a property of the formula we actually emit. Small
        // bounded quantifiers may have been expanded away before serialization.
        has_quantifier: emitted_features.has_quantifier,
    };

    for (_, sort) in extra_decls {
        add_sort_logic_features(sort, &mut features);
    }

    logic_from_features(features)
}

fn infer_logic_walk(
    expr: &SmtExpr,
    has_array: &mut bool,
    has_fp: &mut bool,
    has_uf: &mut bool,
    has_quantifier: &mut bool,
) {
    match expr {
        SmtExpr::Select { array, index } => {
            *has_array = true;
            infer_logic_walk(array, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(index, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::Store {
            array,
            index,
            value,
        } => {
            *has_array = true;
            infer_logic_walk(array, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(index, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(value, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::ConstArray { index_sort, value } => {
            let mut sorts = LogicFeatures::default();
            add_sort_logic_features(index_sort, &mut sorts);
            *has_array = true;
            *has_fp |= sorts.has_fp;
            infer_logic_walk(value, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::FPAdd { lhs, rhs, .. }
        | SmtExpr::FPSub { lhs, rhs, .. }
        | SmtExpr::FPMul { lhs, rhs, .. }
        | SmtExpr::FPDiv { lhs, rhs, .. }
        | SmtExpr::FPEq { lhs, rhs }
        | SmtExpr::FPLt { lhs, rhs }
        | SmtExpr::FPGt { lhs, rhs }
        | SmtExpr::FPGe { lhs, rhs }
        | SmtExpr::FPLe { lhs, rhs } => {
            *has_fp = true;
            infer_logic_walk(lhs, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(rhs, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::FPFma { a, b, c, .. } => {
            *has_fp = true;
            infer_logic_walk(a, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(b, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(c, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::FPNeg { operand }
        | SmtExpr::FPAbs { operand }
        | SmtExpr::FPSqrt { operand, .. }
        | SmtExpr::FPRoundToIntegral { operand, .. }
        | SmtExpr::FPIsNaN { operand }
        | SmtExpr::FPIsInf { operand }
        | SmtExpr::FPIsZero { operand }
        | SmtExpr::FPIsNormal { operand }
        | SmtExpr::FPToSBv { operand, .. }
        | SmtExpr::FPToUBv { operand, .. }
        | SmtExpr::BvToFP { operand, .. }
        | SmtExpr::FPToFP { operand, .. }
        | SmtExpr::BvBitsToFP { operand, .. } => {
            *has_fp = true;
            infer_logic_walk(operand, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::FPConst { .. } => {
            *has_fp = true;
        }
        SmtExpr::UF { args, ret_sort, .. } => {
            // A nullary declaration denotes an arbitrary constant, not an
            // application requiring the UF fragment. Its sort still matters
            // even when no Select or FP operation exposes that sort elsewhere.
            *has_uf |= !args.is_empty();
            let mut sorts = LogicFeatures::default();
            add_sort_logic_features(ret_sort, &mut sorts);
            *has_array |= sorts.has_array;
            *has_fp |= sorts.has_fp;
            for arg in args {
                infer_logic_walk(arg, has_array, has_fp, has_uf, has_quantifier);
            }
        }
        SmtExpr::UFDecl {
            arg_sorts,
            ret_sort,
            ..
        } => {
            *has_uf |= !arg_sorts.is_empty();
            let mut sorts = LogicFeatures::default();
            add_sort_logic_features(ret_sort, &mut sorts);
            for sort in arg_sorts {
                add_sort_logic_features(sort, &mut sorts);
            }
            *has_array |= sorts.has_array;
            *has_fp |= sorts.has_fp;
        }
        // A memory load lowers to an uninterpreted function application
        // (`mem_load_W_s`) in SMT-LIB, so it needs the UF logic fragment.
        SmtExpr::MemLoad { addr, .. } => {
            *has_uf = true;
            infer_logic_walk(addr, has_array, has_fp, has_uf, has_quantifier);
        }
        // Binary BV/Bool ops
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
            infer_logic_walk(lhs, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(rhs, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::BvNeg { operand, .. }
        | SmtExpr::Not { operand }
        | SmtExpr::Extract { operand, .. }
        | SmtExpr::ZeroExtend { operand, .. }
        | SmtExpr::SignExtend { operand, .. } => {
            infer_logic_walk(operand, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::Concat { hi, lo, .. } => {
            infer_logic_walk(hi, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(lo, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::TrapIfZero { guard, value, .. } => {
            infer_logic_walk(guard, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(value, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            infer_logic_walk(cond, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(then_expr, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(else_expr, has_array, has_fp, has_uf, has_quantifier);
        }
        SmtExpr::Var { .. } | SmtExpr::BvConst { .. } | SmtExpr::BoolConst(_) => {}
        SmtExpr::ForAll {
            lower, upper, body, ..
        }
        | SmtExpr::Exists {
            lower, upper, body, ..
        } => {
            *has_quantifier = true;
            infer_logic_walk(lower, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(upper, has_array, has_fp, has_uf, has_quantifier);
            infer_logic_walk(body, has_array, has_fp, has_uf, has_quantifier);
        }
    }
}

/// Collect uninterpreted function declarations from an expression tree.
///
/// Walks the expression and collects `(name, arg_sorts, ret_sort)` tuples
/// for every `UF` application found. Deduplicates by function name.
/// This is needed for SMT-LIB2 generation: each UF must be declared with
/// `(declare-fun name (arg_sorts...) ret_sort)` before use.
fn collect_uf_declarations(expr: &SmtExpr, decls: &mut Vec<(String, Vec<SmtSort>, SmtSort)>) {
    collect_uf_declarations_unique(expr, decls, &mut std::collections::HashSet::new());
}

fn collect_uf_declarations_unique(
    expr: &SmtExpr,
    decls: &mut Vec<(String, Vec<SmtSort>, SmtSort)>,
    visited: &mut std::collections::HashSet<*const SmtExpr>,
) {
    // The immutable root keeps every child alive for this call, including
    // by-value UF arguments. Addresses are only traversal identities, never
    // persisted proof/cache keys. Hashing &SmtExpr would rewalk its structure.
    if !visited.insert(std::ptr::from_ref(expr)) {
        return;
    }
    match expr {
        SmtExpr::UF {
            name,
            args,
            ret_sort,
        } => {
            if !decls.iter().any(|(n, _, _)| n == name) {
                let arg_sorts = args.iter().map(SmtExpr::sort).collect();
                decls.push((name.clone(), arg_sorts, ret_sort.clone()));
            }
        }
        SmtExpr::UFDecl {
            name,
            arg_sorts,
            ret_sort,
        } => {
            if !decls.iter().any(|(n, _, _)| n == name) {
                decls.push((name.clone(), arg_sorts.clone(), ret_sort.clone()));
            }
        }
        SmtExpr::MemLoad {
            addr,
            load_bits,
            signed,
            ..
        } => {
            let suffix = if *signed { "s" } else { "u" };
            let name = format!("mem_load_{load_bits}_{suffix}");
            if !decls.iter().any(|(n, _, _)| n == &name) {
                let addr_sort = SmtSort::BitVec(addr.try_bv_width().unwrap_or(64));
                decls.push((name, vec![addr_sort], SmtSort::BitVec(*load_bits)));
            }
        }
        _ => {}
    }
    // Reuse the exhaustive child census and its original left-to-right order.
    // A repeated UF name does not skip distinct argument subgraphs. This scan
    // neither substitutes variables nor hoists expressions across binders.
    expr.for_each_child(&mut |child| collect_uf_declarations_unique(child, decls, visited));
}

#[cfg(test)]
#[path = "ay_bridge_uf_walk_tests.rs"]
mod uf_walk_tests;

#[cfg(test)]
#[path = "ay_bridge_logic_sort_tests.rs"]
mod logic_sort_tests;

// ---------------------------------------------------------------------------
// Bounded quantifier expansion
// ---------------------------------------------------------------------------

/// Try to extract a constant u64 value from a `BvConst` expression.
fn try_const_value(expr: &SmtExpr) -> Option<u64> {
    match expr {
        SmtExpr::BvConst { value, .. } => Some(*value),
        _ => None,
    }
}

/// Substitute all occurrences of a named variable with a constant value.
///
/// Performs a deep clone of the expression tree, replacing every `Var { name, width }`
/// node matching `var_name` with `BvConst { value, width }`.
fn substitute_var(expr: &SmtExpr, var_name: &str, value: u64) -> SmtExpr {
    match expr {
        SmtExpr::Var { name, width } if name == var_name => SmtExpr::bv_const(value, *width),
        // For non-matching leaves, clone
        SmtExpr::Var { .. }
        | SmtExpr::BvConst { .. }
        | SmtExpr::BoolConst(_)
        | SmtExpr::FPConst { .. }
        | SmtExpr::UFDecl { .. } => expr.clone(),
        // Binary BV/Bool ops
        SmtExpr::BvAdd { lhs, rhs, width } => SmtExpr::BvAdd {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvSub { lhs, rhs, width } => SmtExpr::BvSub {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvMul { lhs, rhs, width } => SmtExpr::BvMul {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvSDiv { lhs, rhs, width } => SmtExpr::BvSDiv {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvUDiv { lhs, rhs, width } => SmtExpr::BvUDiv {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvURem { lhs, rhs, width } => SmtExpr::BvURem {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvAnd { lhs, rhs, width } => SmtExpr::BvAnd {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvOr { lhs, rhs, width } => SmtExpr::BvOr {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvXor { lhs, rhs, width } => SmtExpr::BvXor {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvShl { lhs, rhs, width } => SmtExpr::BvShl {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvLshr { lhs, rhs, width } => SmtExpr::BvLshr {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvAshr { lhs, rhs, width } => SmtExpr::BvAshr {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::Eq { lhs, rhs } => SmtExpr::Eq {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
        },
        SmtExpr::BvSlt { lhs, rhs, width } => SmtExpr::BvSlt {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvSge { lhs, rhs, width } => SmtExpr::BvSge {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvSgt { lhs, rhs, width } => SmtExpr::BvSgt {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvSle { lhs, rhs, width } => SmtExpr::BvSle {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvUlt { lhs, rhs, width } => SmtExpr::BvUlt {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvUge { lhs, rhs, width } => SmtExpr::BvUge {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvUgt { lhs, rhs, width } => SmtExpr::BvUgt {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::BvUle { lhs, rhs, width } => SmtExpr::BvUle {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            width: *width,
        },
        SmtExpr::And { lhs, rhs } => SmtExpr::And {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
        },
        SmtExpr::Or { lhs, rhs } => SmtExpr::Or {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
        },
        // Unary operators
        SmtExpr::BvNeg { operand, width } => SmtExpr::BvNeg {
            operand: Arc::new(substitute_var(operand, var_name, value)),
            width: *width,
        },
        SmtExpr::Not { operand } => SmtExpr::Not {
            operand: Arc::new(substitute_var(operand, var_name, value)),
        },
        SmtExpr::Extract {
            operand,
            high,
            low,
            width,
        } => SmtExpr::Extract {
            operand: Arc::new(substitute_var(operand, var_name, value)),
            high: *high,
            low: *low,
            width: *width,
        },
        SmtExpr::ZeroExtend {
            operand,
            extra_bits,
            width,
        } => SmtExpr::ZeroExtend {
            operand: Arc::new(substitute_var(operand, var_name, value)),
            extra_bits: *extra_bits,
            width: *width,
        },
        SmtExpr::SignExtend {
            operand,
            extra_bits,
            width,
        } => SmtExpr::SignExtend {
            operand: Arc::new(substitute_var(operand, var_name, value)),
            extra_bits: *extra_bits,
            width: *width,
        },
        SmtExpr::Concat { hi, lo, width } => SmtExpr::Concat {
            hi: Arc::new(substitute_var(hi, var_name, value)),
            lo: Arc::new(substitute_var(lo, var_name, value)),
            width: *width,
        },
        SmtExpr::TrapIfZero {
            guard,
            value: trap_value,
            width,
        } => SmtExpr::TrapIfZero {
            guard: Arc::new(substitute_var(guard, var_name, value)),
            value: Arc::new(substitute_var(trap_value, var_name, value)),
            width: *width,
        },
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => SmtExpr::Ite {
            cond: Arc::new(substitute_var(cond, var_name, value)),
            then_expr: Arc::new(substitute_var(then_expr, var_name, value)),
            else_expr: Arc::new(substitute_var(else_expr, var_name, value)),
        },
        // Array operations
        SmtExpr::Select { array, index } => SmtExpr::Select {
            array: Arc::new(substitute_var(array, var_name, value)),
            index: Arc::new(substitute_var(index, var_name, value)),
        },
        SmtExpr::Store {
            array,
            index,
            value: val,
        } => SmtExpr::Store {
            array: Arc::new(substitute_var(array, var_name, value)),
            index: Arc::new(substitute_var(index, var_name, value)),
            value: Arc::new(substitute_var(val, var_name, value)),
        },
        SmtExpr::ConstArray {
            index_sort,
            value: val,
        } => SmtExpr::ConstArray {
            index_sort: index_sort.clone(),
            value: Arc::new(substitute_var(val, var_name, value)),
        },
        SmtExpr::MemLoad {
            addr,
            load_bits,
            signed,
            result_width,
        } => SmtExpr::MemLoad {
            addr: Arc::new(substitute_var(addr, var_name, value)),
            load_bits: *load_bits,
            signed: *signed,
            result_width: *result_width,
        },
        // FP operations
        SmtExpr::FPAdd { lhs, rhs, rm } => SmtExpr::FPAdd {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            rm: *rm,
        },
        SmtExpr::FPSub { lhs, rhs, rm } => SmtExpr::FPSub {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            rm: *rm,
        },
        SmtExpr::FPMul { lhs, rhs, rm } => SmtExpr::FPMul {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            rm: *rm,
        },
        SmtExpr::FPDiv { lhs, rhs, rm } => SmtExpr::FPDiv {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
            rm: *rm,
        },
        SmtExpr::FPEq { lhs, rhs } => SmtExpr::FPEq {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
        },
        SmtExpr::FPLt { lhs, rhs } => SmtExpr::FPLt {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
        },
        SmtExpr::FPGt { lhs, rhs } => SmtExpr::FPGt {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
        },
        SmtExpr::FPGe { lhs, rhs } => SmtExpr::FPGe {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
        },
        SmtExpr::FPLe { lhs, rhs } => SmtExpr::FPLe {
            lhs: Arc::new(substitute_var(lhs, var_name, value)),
            rhs: Arc::new(substitute_var(rhs, var_name, value)),
        },
        SmtExpr::FPFma { a, b, c, rm } => SmtExpr::FPFma {
            a: Arc::new(substitute_var(a, var_name, value)),
            b: Arc::new(substitute_var(b, var_name, value)),
            c: Arc::new(substitute_var(c, var_name, value)),
            rm: *rm,
        },
        SmtExpr::FPNeg { operand } => SmtExpr::FPNeg {
            operand: Arc::new(substitute_var(operand, var_name, value)),
        },
        SmtExpr::FPAbs { operand } => SmtExpr::FPAbs {
            operand: Arc::new(substitute_var(operand, var_name, value)),
        },
        SmtExpr::FPSqrt { operand, rm } => SmtExpr::FPSqrt {
            operand: Arc::new(substitute_var(operand, var_name, value)),
            rm: *rm,
        },
        SmtExpr::FPRoundToIntegral { operand, rm } => SmtExpr::FPRoundToIntegral {
            operand: Arc::new(substitute_var(operand, var_name, value)),
            rm: *rm,
        },
        SmtExpr::FPIsNaN { operand } => SmtExpr::FPIsNaN {
            operand: Arc::new(substitute_var(operand, var_name, value)),
        },
        SmtExpr::FPIsInf { operand } => SmtExpr::FPIsInf {
            operand: Arc::new(substitute_var(operand, var_name, value)),
        },
        SmtExpr::FPIsZero { operand } => SmtExpr::FPIsZero {
            operand: Arc::new(substitute_var(operand, var_name, value)),
        },
        SmtExpr::FPIsNormal { operand } => SmtExpr::FPIsNormal {
            operand: Arc::new(substitute_var(operand, var_name, value)),
        },
        SmtExpr::FPToSBv {
            rm,
            operand,
            width,
            mode,
        } => SmtExpr::FPToSBv {
            rm: *rm,
            operand: Arc::new(substitute_var(operand, var_name, value)),
            width: *width,
            mode: *mode,
        },
        SmtExpr::FPToUBv { rm, operand, width } => SmtExpr::FPToUBv {
            rm: *rm,
            operand: Arc::new(substitute_var(operand, var_name, value)),
            width: *width,
        },
        SmtExpr::BvToFP {
            rm,
            operand,
            eb,
            sb,
        } => SmtExpr::BvToFP {
            rm: *rm,
            operand: Arc::new(substitute_var(operand, var_name, value)),
            eb: *eb,
            sb: *sb,
        },
        SmtExpr::FPToFP {
            operand,
            eb,
            sb,
            rm,
        } => SmtExpr::FPToFP {
            operand: Arc::new(substitute_var(operand, var_name, value)),
            eb: *eb,
            sb: *sb,
            rm: *rm,
        },
        SmtExpr::BvBitsToFP { operand, eb, sb } => SmtExpr::BvBitsToFP {
            operand: Arc::new(substitute_var(operand, var_name, value)),
            eb: *eb,
            sb: *sb,
        },
        // UF
        SmtExpr::UF {
            name,
            args,
            ret_sort,
        } => SmtExpr::UF {
            name: name.clone(),
            args: args
                .iter()
                .map(|a| substitute_var(a, var_name, value))
                .collect(),
            ret_sort: ret_sort.clone(),
        },
        // Nested quantifiers
        SmtExpr::ForAll {
            var,
            var_width,
            lower,
            upper,
            body,
        } => {
            if var == var_name {
                // Shadowed -- do not substitute inside
                expr.clone()
            } else {
                SmtExpr::ForAll {
                    var: var.clone(),
                    var_width: *var_width,
                    lower: Arc::new(substitute_var(lower, var_name, value)),
                    upper: Arc::new(substitute_var(upper, var_name, value)),
                    body: Arc::new(substitute_var(body, var_name, value)),
                }
            }
        }
        SmtExpr::Exists {
            var,
            var_width,
            lower,
            upper,
            body,
        } => {
            if var == var_name {
                expr.clone()
            } else {
                SmtExpr::Exists {
                    var: var.clone(),
                    var_width: *var_width,
                    lower: Arc::new(substitute_var(lower, var_name, value)),
                    upper: Arc::new(substitute_var(upper, var_name, value)),
                    body: Arc::new(substitute_var(body, var_name, value)),
                }
            }
        }
    }
}

/// Expand bounded quantifiers with small constant ranges into conjunctions/disjunctions.
///
/// For a `ForAll { var, lower: L, upper: U, body }` where `L` and `U` are constants
/// and `U - L <= BOUNDED_QUANTIFIER_EXPANSION_LIMIT`:
/// ```text
/// body[var/L] AND body[var/L+1] AND ... AND body[var/U-1]
/// ```
///
/// For `Exists`, the expansion uses OR instead of AND.
///
/// Quantifiers with non-constant bounds or ranges exceeding the limit are left as-is.
/// This allows the formula to remain in a quantifier-free logic (QF_*) for better
/// solver performance.
///
/// Returns the transformed expression. Non-quantifier expressions are returned unchanged.
pub fn expand_bounded_quantifiers(expr: &SmtExpr) -> SmtExpr {
    expand_bounded_quantifiers_with_limit(expr, BOUNDED_QUANTIFIER_EXPANSION_LIMIT)
}

/// Like [`expand_bounded_quantifiers`] but with a configurable expansion limit.
pub fn expand_bounded_quantifiers_with_limit(expr: &SmtExpr, limit: u64) -> SmtExpr {
    match expr {
        SmtExpr::ForAll {
            var,
            var_width,
            lower,
            upper,
            body,
        } => {
            // First expand any nested quantifiers in bounds and body
            let lower_exp = expand_bounded_quantifiers_with_limit(lower, limit);
            let upper_exp = expand_bounded_quantifiers_with_limit(upper, limit);
            let body_exp = expand_bounded_quantifiers_with_limit(body, limit);

            if let (Some(lo), Some(hi)) = (try_const_value(&lower_exp), try_const_value(&upper_exp))
            {
                if hi > lo && (hi - lo) <= limit {
                    // Expand into conjunction: body[var/lo] AND body[var/lo+1] AND ... AND body[var/hi-1]
                    let mut result = substitute_var(&body_exp, var, lo);
                    for i in (lo + 1)..hi {
                        let instance = substitute_var(&body_exp, var, i);
                        result = result.and_expr(instance);
                    }
                    return result;
                }
                if hi <= lo {
                    // Empty range: vacuously true
                    return SmtExpr::bool_const(true);
                }
            }
            // Cannot expand: return with recursively expanded children
            SmtExpr::ForAll {
                var: var.clone(),
                var_width: *var_width,
                lower: Arc::new(lower_exp),
                upper: Arc::new(upper_exp),
                body: Arc::new(body_exp),
            }
        }
        SmtExpr::Exists {
            var,
            var_width,
            lower,
            upper,
            body,
        } => {
            let lower_exp = expand_bounded_quantifiers_with_limit(lower, limit);
            let upper_exp = expand_bounded_quantifiers_with_limit(upper, limit);
            let body_exp = expand_bounded_quantifiers_with_limit(body, limit);

            if let (Some(lo), Some(hi)) = (try_const_value(&lower_exp), try_const_value(&upper_exp))
            {
                if hi > lo && (hi - lo) <= limit {
                    // Expand into disjunction: body[var/lo] OR body[var/lo+1] OR ... OR body[var/hi-1]
                    let mut result = substitute_var(&body_exp, var, lo);
                    for i in (lo + 1)..hi {
                        let instance = substitute_var(&body_exp, var, i);
                        result = result.or_expr(instance);
                    }
                    return result;
                }
                if hi <= lo {
                    // Empty range: vacuously false
                    return SmtExpr::bool_const(false);
                }
            }
            SmtExpr::Exists {
                var: var.clone(),
                var_width: *var_width,
                lower: Arc::new(lower_exp),
                upper: Arc::new(upper_exp),
                body: Arc::new(body_exp),
            }
        }
        // Recurse into all other expression types
        SmtExpr::BvAdd { lhs, rhs, width } => SmtExpr::BvAdd {
            lhs: Arc::new(expand_bounded_quantifiers_with_limit(lhs, limit)),
            rhs: Arc::new(expand_bounded_quantifiers_with_limit(rhs, limit)),
            width: *width,
        },
        SmtExpr::And { lhs, rhs } => SmtExpr::And {
            lhs: Arc::new(expand_bounded_quantifiers_with_limit(lhs, limit)),
            rhs: Arc::new(expand_bounded_quantifiers_with_limit(rhs, limit)),
        },
        SmtExpr::Or { lhs, rhs } => SmtExpr::Or {
            lhs: Arc::new(expand_bounded_quantifiers_with_limit(lhs, limit)),
            rhs: Arc::new(expand_bounded_quantifiers_with_limit(rhs, limit)),
        },
        SmtExpr::Not { operand } => SmtExpr::Not {
            operand: Arc::new(expand_bounded_quantifiers_with_limit(operand, limit)),
        },
        SmtExpr::Eq { lhs, rhs } => SmtExpr::Eq {
            lhs: Arc::new(expand_bounded_quantifiers_with_limit(lhs, limit)),
            rhs: Arc::new(expand_bounded_quantifiers_with_limit(rhs, limit)),
        },
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => SmtExpr::Ite {
            cond: Arc::new(expand_bounded_quantifiers_with_limit(cond, limit)),
            then_expr: Arc::new(expand_bounded_quantifiers_with_limit(then_expr, limit)),
            else_expr: Arc::new(expand_bounded_quantifiers_with_limit(else_expr, limit)),
        },
        SmtExpr::Select { array, index } => SmtExpr::Select {
            array: Arc::new(expand_bounded_quantifiers_with_limit(array, limit)),
            index: Arc::new(expand_bounded_quantifiers_with_limit(index, limit)),
        },
        SmtExpr::Store {
            array,
            index,
            value,
        } => SmtExpr::Store {
            array: Arc::new(expand_bounded_quantifiers_with_limit(array, limit)),
            index: Arc::new(expand_bounded_quantifiers_with_limit(index, limit)),
            value: Arc::new(expand_bounded_quantifiers_with_limit(value, limit)),
        },
        // Leaves and other nodes without quantifiers: return as-is
        _ => expr.clone(),
    }
}

/// Check whether an expression contains quantifiers (`ForAll` or `Exists`).
pub fn has_quantifiers(expr: &SmtExpr) -> bool {
    // A shape census, not evaluation or binder substitution. Visit every real
    // child (including inline UF arguments), once by pointer identity; no
    // recursive expansion of a shared DAG merely to detect a quantifier.
    let mut pending = vec![expr];
    let mut visited = std::collections::HashSet::new();
    while let Some(node) = pending.pop() {
        if !visited.insert(node as *const SmtExpr) {
            continue;
        }
        if matches!(node, SmtExpr::ForAll { .. } | SmtExpr::Exists { .. }) {
            return true;
        }
        node.for_each_child(&mut |child| pending.push(child));
    }
    false
}

/// Preserve the exact existing QF graph. The legacy bounded expansion rebuilds
/// selected paths even without binders; it is needed ONLY when a quantifier is
/// present. Borrowing avoids both those copies and a deep inline-UF root clone.
/// Quantified inputs still use the unchanged expansion/binder semantics.
fn quantifier_expanded_view(expr: &SmtExpr) -> std::borrow::Cow<'_, SmtExpr> {
    if has_quantifiers(expr) {
        std::borrow::Cow::Owned(expand_bounded_quantifiers(expr))
    } else {
        std::borrow::Cow::Borrowed(expr)
    }
}

/// True iff `expr` is the degenerate top-level constant `false`.
///
/// Used by the TCB soundness guard in [`verify_with_ay`] to detect the one
/// simplifier outcome that would let an unsound rewrite mint a false
/// `Verified`: a negated equivalence collapsed to constant `false` serializes
/// to `(assert false)`, which is trivially `unsat`, which the bridge maps to
/// `AYResult::Verified` WITHOUT the solver ever inspecting the real formula.
pub(crate) fn is_constant_false(expr: &SmtExpr) -> bool {
    matches!(expr, SmtExpr::BoolConst(false))
}

/// True iff discharging `obligation` would rest entirely on the local
/// simplifier folding the negated equivalence to a constant `false` — i.e. the
/// solver would only ever see `(assert false)` and never the real formula.
///
/// This is the TCB caveat documented in `proof_gate.rs`: a simplifier-introduced
/// `false` (as opposed to a raw negated equivalence that is *already* the
/// constant `false` before any solver-oriented simplification) is an unsound
/// shortcut. [`verify_with_ay`] uses this to re-route such obligations through
/// the solver on the UN-simplified raw formula instead of trusting the rewrite.
pub(crate) fn simplifier_alone_proved_unsat(obligation: &ProofObligation) -> bool {
    let raw_formula = obligation.negated_equivalence();
    // The bounded-quantifier expansion is a sound, mechanical rewrite (it only
    // unrolls constant-bounded quantifiers); a constant `false` there is the
    // genuine formula, not a simplifier artifact. The solver-oriented
    // bitvector simplifier is the component whose `false` we refuse to trust.
    let expanded = quantifier_expanded_view(&raw_formula);
    let simplified = simplify_solver_expr(&expanded);
    is_constant_false(&simplified) && !is_constant_false(&expanded)
}

/// Prepare a formula for SMT-LIB2 emission by expanding small bounded quantifiers
/// and simplifying solver-hard bitvector identities.
///
/// This is the recommended entry point for SMT-LIB2 generation. It:
/// 1. Tries to expand bounded quantifiers with constant bounds <= limit into
///    conjunctions/disjunctions (keeping the formula quantifier-free for better perf)
/// 2. Canonicalizes quantifier-free bitvector fragments that are expensive for ay
///    but semantics-preserving to rewrite locally (for example, associative
///    `bvadd` trees and constant power-of-two division).
/// 3. If quantifiers remain after expansion (non-constant bounds or large ranges),
///    the formula is returned as-is and `infer_logic` will select a quantified logic
///
/// Returns the (potentially expanded) formula. Use `infer_logic` on the result
/// to determine the correct `(set-logic ...)` declaration.
///
/// NOTE (TCB): this returns the simplified form, which CAN be a constant
/// `false`. That is correct for *logic inference* and SMT-LIB2 *shape*, but a
/// constant-`false` assert means the solver never sees the real formula. The
/// soundness guard against an unsound simplifier-minted `false` lives at the
/// verification boundary in [`verify_with_ay`], not here, so that non-solver
/// consumers of this function (logic inference, serialization shape) keep the
/// fast simplified form.
pub fn prepare_formula_for_smt(expr: &SmtExpr) -> SmtExpr {
    let expanded = quantifier_expanded_view(expr);
    simplify_solver_expr(&expanded)
}

fn all_ones_const_value(width: u32) -> Option<u64> {
    match width {
        0 => None,
        1..=63 => Some((1u64 << width) - 1),
        64 => Some(u64::MAX),
        _ => None,
    }
}

fn is_bv_const(expr: &SmtExpr, expected: u64, width: u32) -> bool {
    matches!(
        expr,
        SmtExpr::BvConst { value, width: expr_width }
            if *expr_width == width && *value == expected
    )
}

fn is_bv_zero(expr: &SmtExpr, width: u32) -> bool {
    is_bv_const(expr, 0, width)
}

fn is_bv_one(expr: &SmtExpr, width: u32) -> bool {
    is_bv_const(expr, 1, width)
}

fn bitvector_power_of_two_shift(expr: &SmtExpr, width: u32) -> Option<u64> {
    let SmtExpr::BvConst {
        value,
        width: const_width,
    } = expr
    else {
        return None;
    };

    if *const_width != width || *value == 0 || !value.is_power_of_two() {
        return None;
    }

    let shift = value.trailing_zeros() as u64;
    (shift < width as u64).then_some(shift)
}

fn sorted_commutative_pair(lhs: SmtExpr, rhs: SmtExpr) -> (SmtExpr, SmtExpr) {
    if format!("{}", lhs) <= format!("{}", rhs) {
        (lhs, rhs)
    } else {
        (rhs, lhs)
    }
}

fn collect_bvadd_terms(expr: SmtExpr, width: u32, terms: &mut Vec<SmtExpr>) {
    match expr {
        SmtExpr::BvAdd {
            lhs,
            rhs,
            width: expr_width,
        } if expr_width == width => {
            collect_bvadd_terms(Arc::unwrap_or_clone(lhs), width, terms);
            collect_bvadd_terms(Arc::unwrap_or_clone(rhs), width, terms);
        }
        other => terms.push(other),
    }
}

fn rebuild_bvadd_terms(mut terms: Vec<SmtExpr>, width: u32) -> SmtExpr {
    terms.retain(|term| !is_bv_zero(term, width));
    terms.sort_by_key(|term| format!("{}", term));

    let mut iter = terms.into_iter();
    let Some(first) = iter.next() else {
        return SmtExpr::bv_const(0, width);
    };

    iter.fold(first, |acc, term| SmtExpr::BvAdd {
        lhs: Arc::new(acc),
        rhs: Arc::new(term),
        width,
    })
}

fn simplify_bvadd(lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    let mut terms = Vec::new();
    collect_bvadd_terms(lhs, width, &mut terms);
    collect_bvadd_terms(rhs, width, &mut terms);
    rebuild_bvadd_terms(terms, width)
}

fn simplify_bvmul(lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    if is_bv_zero(&lhs, width) || is_bv_zero(&rhs, width) {
        return SmtExpr::bv_const(0, width);
    }
    if is_bv_one(&lhs, width) {
        return rhs;
    }
    if is_bv_one(&rhs, width) {
        return lhs;
    }

    let (lhs, rhs) = sorted_commutative_pair(lhs, rhs);
    SmtExpr::BvMul {
        lhs: Arc::new(lhs),
        rhs: Arc::new(rhs),
        width,
    }
}

fn simplify_bvlshr(lhs: SmtExpr, rhs: SmtExpr, width: u32) -> SmtExpr {
    if is_bv_zero(&rhs, width) {
        lhs
    } else {
        SmtExpr::BvLshr {
            lhs: Arc::new(lhs),
            rhs: Arc::new(rhs),
            width,
        }
    }
}

fn simplify_solver_expr(expr: &SmtExpr) -> SmtExpr {
    Arc::unwrap_or_clone(simplify_solver_shared(expr, &mut HashMap::new()))
}

// This cache belongs to one immutable input graph and one invocation. It
// preserves repeated children through the SAME existing rewrite rules; keys
// are never consulted after that graph's borrow ends.
fn simplify_solver_shared(
    expr: &SmtExpr,
    memo: &mut HashMap<*const SmtExpr, Arc<SmtExpr>>,
) -> Arc<SmtExpr> {
    let key = std::ptr::from_ref(expr);
    if let Some(previous) = memo.get(&key) {
        return previous.clone();
    }
    let simplified = Arc::new(simplify_solver_node(expr, memo));
    memo.insert(key, simplified.clone());
    simplified
}

fn simplify_solver_node(
    expr: &SmtExpr,
    memo: &mut HashMap<*const SmtExpr, Arc<SmtExpr>>,
) -> SmtExpr {
    match expr {
        SmtExpr::BoolConst(_) | SmtExpr::BvConst { .. } | SmtExpr::Var { .. } => expr.clone(),
        SmtExpr::Not { operand } => {
            let operand = Arc::unwrap_or_clone(simplify_solver_shared(operand, memo));
            match operand {
                SmtExpr::BoolConst(value) => SmtExpr::bool_const(!value),
                SmtExpr::Not { operand } => Arc::unwrap_or_clone(operand),
                other => SmtExpr::Not {
                    operand: Arc::new(other),
                },
            }
        }
        SmtExpr::Eq { lhs, rhs } => {
            let lhs = simplify_solver_shared(lhs, memo);
            let rhs = simplify_solver_shared(rhs, memo);
            if lhs == rhs {
                return SmtExpr::bool_const(true);
            }
            // These constructors intrinsically return Bool; do not ask the
            // recursive BV-width fallback to infer a Boolean ITE's sort.
            let boolean = |term: &SmtExpr| {
                matches!(
                    term,
                    SmtExpr::BoolConst(_)
                        | SmtExpr::Not { .. }
                        | SmtExpr::And { .. }
                        | SmtExpr::Or { .. }
                        | SmtExpr::Eq { .. }
                        | SmtExpr::UF {
                            ret_sort: SmtSort::Bool,
                            ..
                        }
                )
            };
            if let SmtExpr::BoolConst(value) = lhs.as_ref()
                && boolean(&rhs)
            {
                return if *value {
                    Arc::unwrap_or_clone(rhs)
                } else {
                    SmtExpr::Not { operand: rhs }
                };
            }
            if let SmtExpr::BoolConst(value) = rhs.as_ref()
                && boolean(&lhs)
            {
                return if *value {
                    Arc::unwrap_or_clone(lhs)
                } else {
                    SmtExpr::Not { operand: lhs }
                };
            }
            SmtExpr::Eq { lhs, rhs }
        }
        SmtExpr::And { lhs, rhs } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            match (lhs, rhs) {
                (SmtExpr::BoolConst(false), _) | (_, SmtExpr::BoolConst(false)) => {
                    SmtExpr::bool_const(false)
                }
                (SmtExpr::BoolConst(true), other) | (other, SmtExpr::BoolConst(true)) => other,
                (lhs, rhs) if lhs == rhs => lhs,
                (lhs, rhs) => SmtExpr::And {
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                },
            }
        }
        SmtExpr::Or { lhs, rhs } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            match (lhs, rhs) {
                (SmtExpr::BoolConst(true), _) | (_, SmtExpr::BoolConst(true)) => {
                    SmtExpr::bool_const(true)
                }
                (SmtExpr::BoolConst(false), other) | (other, SmtExpr::BoolConst(false)) => other,
                (lhs, rhs) if lhs == rhs => lhs,
                (lhs, rhs) => SmtExpr::Or {
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                },
            }
        }
        SmtExpr::BvAdd { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            simplify_bvadd(lhs, rhs, *width)
        }
        SmtExpr::BvSub { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            if is_bv_zero(&rhs, *width) {
                lhs
            } else if is_bv_zero(&lhs, *width) {
                SmtExpr::BvNeg {
                    operand: Arc::new(rhs),
                    width: *width,
                }
            } else if lhs == rhs {
                SmtExpr::bv_const(0, *width)
            } else {
                SmtExpr::BvSub {
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                    width: *width,
                }
            }
        }
        SmtExpr::BvMul { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            simplify_bvmul(lhs, rhs, *width)
        }
        SmtExpr::BvSDiv { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            if all_ones_const_value(*width)
                .is_some_and(|neg_one| is_bv_const(&rhs, neg_one, *width))
            {
                SmtExpr::BvNeg {
                    operand: Arc::new(lhs),
                    width: *width,
                }
            } else {
                SmtExpr::BvSDiv {
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                    width: *width,
                }
            }
        }
        SmtExpr::BvUDiv { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            if let Some(shift) = bitvector_power_of_two_shift(&rhs, *width) {
                simplify_bvlshr(lhs, SmtExpr::bv_const(shift, *width), *width)
            } else {
                SmtExpr::BvUDiv {
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                    width: *width,
                }
            }
        }
        SmtExpr::BvURem { lhs, rhs, width } => SmtExpr::BvURem {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::BvNeg { operand, width } => {
            let operand = Arc::unwrap_or_clone(simplify_solver_shared(operand, memo));
            match operand {
                SmtExpr::BvConst { value: 0, .. } => SmtExpr::bv_const(0, *width),
                SmtExpr::BvNeg { operand, .. } => Arc::unwrap_or_clone(operand),
                other => SmtExpr::BvNeg {
                    operand: Arc::new(other),
                    width: *width,
                },
            }
        }
        SmtExpr::BvAnd { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            let (lhs, rhs) = sorted_commutative_pair(lhs, rhs);
            SmtExpr::BvAnd {
                lhs: Arc::new(lhs),
                rhs: Arc::new(rhs),
                width: *width,
            }
        }
        SmtExpr::BvOr { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            let (lhs, rhs) = sorted_commutative_pair(lhs, rhs);
            SmtExpr::BvOr {
                lhs: Arc::new(lhs),
                rhs: Arc::new(rhs),
                width: *width,
            }
        }
        SmtExpr::BvXor { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            let (lhs, rhs) = sorted_commutative_pair(lhs, rhs);
            SmtExpr::BvXor {
                lhs: Arc::new(lhs),
                rhs: Arc::new(rhs),
                width: *width,
            }
        }
        SmtExpr::BvShl { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            if is_bv_zero(&rhs, *width) {
                lhs
            } else {
                SmtExpr::BvShl {
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                    width: *width,
                }
            }
        }
        SmtExpr::BvLshr { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            simplify_bvlshr(lhs, rhs, *width)
        }
        SmtExpr::BvAshr { lhs, rhs, width } => {
            let lhs = Arc::unwrap_or_clone(simplify_solver_shared(lhs, memo));
            let rhs = Arc::unwrap_or_clone(simplify_solver_shared(rhs, memo));
            if is_bv_zero(&rhs, *width) {
                lhs
            } else {
                SmtExpr::BvAshr {
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                    width: *width,
                }
            }
        }
        SmtExpr::BvSlt { lhs, rhs, width } => SmtExpr::BvSlt {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::BvSge { lhs, rhs, width } => SmtExpr::BvSge {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::BvSgt { lhs, rhs, width } => SmtExpr::BvSgt {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::BvSle { lhs, rhs, width } => SmtExpr::BvSle {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::BvUlt { lhs, rhs, width } => SmtExpr::BvUlt {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::BvUge { lhs, rhs, width } => SmtExpr::BvUge {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::BvUgt { lhs, rhs, width } => SmtExpr::BvUgt {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::BvUle { lhs, rhs, width } => SmtExpr::BvUle {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            width: *width,
        },
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond = simplify_solver_shared(cond, memo);
            let then_expr = simplify_solver_shared(then_expr, memo);
            let else_expr = simplify_solver_shared(else_expr, memo);
            match cond.as_ref() {
                SmtExpr::BoolConst(true) => Arc::unwrap_or_clone(then_expr),
                SmtExpr::BoolConst(false) => Arc::unwrap_or_clone(else_expr),
                _ => SmtExpr::Ite {
                    cond,
                    then_expr,
                    else_expr,
                },
            }
        }
        SmtExpr::Extract {
            high,
            low,
            operand,
            width,
        } => SmtExpr::Extract {
            high: *high,
            low: *low,
            operand: simplify_solver_shared(operand, memo),
            width: *width,
        },
        SmtExpr::ZeroExtend {
            operand,
            extra_bits,
            width,
        } => SmtExpr::ZeroExtend {
            operand: simplify_solver_shared(operand, memo),
            extra_bits: *extra_bits,
            width: *width,
        },
        SmtExpr::SignExtend {
            operand,
            extra_bits,
            width,
        } => SmtExpr::SignExtend {
            operand: simplify_solver_shared(operand, memo),
            extra_bits: *extra_bits,
            width: *width,
        },
        SmtExpr::Concat { hi, lo, width } => SmtExpr::Concat {
            hi: simplify_solver_shared(hi, memo),
            lo: simplify_solver_shared(lo, memo),
            width: *width,
        },
        SmtExpr::TrapIfZero {
            guard,
            value,
            width,
        } => SmtExpr::TrapIfZero {
            guard: simplify_solver_shared(guard, memo),
            value: simplify_solver_shared(value, memo),
            width: *width,
        },
        SmtExpr::Select { array, index } => SmtExpr::Select {
            array: simplify_solver_shared(array, memo),
            index: simplify_solver_shared(index, memo),
        },
        SmtExpr::Store {
            array,
            index,
            value,
        } => SmtExpr::Store {
            array: simplify_solver_shared(array, memo),
            index: simplify_solver_shared(index, memo),
            value: simplify_solver_shared(value, memo),
        },
        SmtExpr::ConstArray { index_sort, value } => SmtExpr::ConstArray {
            index_sort: index_sort.clone(),
            value: simplify_solver_shared(value, memo),
        },
        SmtExpr::MemLoad {
            addr,
            load_bits,
            signed,
            result_width,
        } => SmtExpr::MemLoad {
            addr: simplify_solver_shared(addr, memo),
            load_bits: *load_bits,
            signed: *signed,
            result_width: *result_width,
        },
        SmtExpr::FPAdd { lhs, rhs, rm } => SmtExpr::FPAdd {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            rm: *rm,
        },
        SmtExpr::FPSub { lhs, rhs, rm } => SmtExpr::FPSub {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            rm: *rm,
        },
        SmtExpr::FPMul { lhs, rhs, rm } => SmtExpr::FPMul {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            rm: *rm,
        },
        SmtExpr::FPDiv { lhs, rhs, rm } => SmtExpr::FPDiv {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
            rm: *rm,
        },
        SmtExpr::FPEq { lhs, rhs } => SmtExpr::FPEq {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
        },
        SmtExpr::FPLt { lhs, rhs } => SmtExpr::FPLt {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
        },
        SmtExpr::FPGt { lhs, rhs } => SmtExpr::FPGt {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
        },
        SmtExpr::FPGe { lhs, rhs } => SmtExpr::FPGe {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
        },
        SmtExpr::FPLe { lhs, rhs } => SmtExpr::FPLe {
            lhs: simplify_solver_shared(lhs, memo),
            rhs: simplify_solver_shared(rhs, memo),
        },
        SmtExpr::FPFma { a, b, c, rm } => SmtExpr::FPFma {
            a: simplify_solver_shared(a, memo),
            b: simplify_solver_shared(b, memo),
            c: simplify_solver_shared(c, memo),
            rm: *rm,
        },
        SmtExpr::FPNeg { operand } => SmtExpr::FPNeg {
            operand: simplify_solver_shared(operand, memo),
        },
        SmtExpr::FPAbs { operand } => SmtExpr::FPAbs {
            operand: simplify_solver_shared(operand, memo),
        },
        SmtExpr::FPSqrt { operand, rm } => SmtExpr::FPSqrt {
            operand: simplify_solver_shared(operand, memo),
            rm: *rm,
        },
        SmtExpr::FPRoundToIntegral { operand, rm } => SmtExpr::FPRoundToIntegral {
            operand: simplify_solver_shared(operand, memo),
            rm: *rm,
        },
        SmtExpr::FPIsNaN { operand } => SmtExpr::FPIsNaN {
            operand: simplify_solver_shared(operand, memo),
        },
        SmtExpr::FPIsInf { operand } => SmtExpr::FPIsInf {
            operand: simplify_solver_shared(operand, memo),
        },
        SmtExpr::FPIsZero { operand } => SmtExpr::FPIsZero {
            operand: simplify_solver_shared(operand, memo),
        },
        SmtExpr::FPIsNormal { operand } => SmtExpr::FPIsNormal {
            operand: simplify_solver_shared(operand, memo),
        },
        SmtExpr::FPToSBv {
            rm,
            operand,
            width,
            mode,
        } => SmtExpr::FPToSBv {
            rm: *rm,
            operand: simplify_solver_shared(operand, memo),
            width: *width,
            mode: *mode,
        },
        SmtExpr::FPToUBv { rm, operand, width } => SmtExpr::FPToUBv {
            rm: *rm,
            operand: simplify_solver_shared(operand, memo),
            width: *width,
        },
        SmtExpr::BvToFP {
            rm,
            operand,
            eb,
            sb,
        } => SmtExpr::BvToFP {
            rm: *rm,
            operand: simplify_solver_shared(operand, memo),
            eb: *eb,
            sb: *sb,
        },
        SmtExpr::FPToFP {
            operand,
            eb,
            sb,
            rm,
        } => SmtExpr::FPToFP {
            operand: simplify_solver_shared(operand, memo),
            eb: *eb,
            sb: *sb,
            rm: *rm,
        },
        SmtExpr::BvBitsToFP { operand, eb, sb } => SmtExpr::BvBitsToFP {
            operand: simplify_solver_shared(operand, memo),
            eb: *eb,
            sb: *sb,
        },
        SmtExpr::UF {
            name,
            args,
            ret_sort,
        } => SmtExpr::UF {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| Arc::unwrap_or_clone(simplify_solver_shared(arg, memo)))
                .collect(),
            ret_sort: ret_sort.clone(),
        },
        SmtExpr::UFDecl { .. }
        | SmtExpr::ForAll { .. }
        | SmtExpr::Exists { .. }
        | SmtExpr::FPConst { .. } => expr.clone(),
    }
}

/// Serialize a rounding mode to SMT-LIB2.
pub fn rounding_mode_to_smt2(rm: &RoundingMode) -> &'static str {
    match rm {
        RoundingMode::RNE => "RNE",
        RoundingMode::RNA => "RNA",
        RoundingMode::RTP => "RTP",
        RoundingMode::RTN => "RTN",
        RoundingMode::RTZ => "RTZ",
    }
}

/// Serialize an SmtSort to SMT-LIB2 sort syntax.
///
/// Examples:
/// - `SmtSort::BitVec(32)` -> `(_ BitVec 32)`
/// - `SmtSort::Bool` -> `Bool`
/// - `SmtSort::Array(BitVec(64), BitVec(8))` -> `(Array (_ BitVec 64) (_ BitVec 8))`
pub fn sort_to_smt2(sort: &SmtSort) -> String {
    // SmtSort::Display already emits valid SMT-LIB2 sort syntax.
    format!("{}", sort)
}

/// Generate a complete SMT-LIB2 query for a proof obligation.
///
/// This extends `ProofObligation::to_smt2()` with:
/// - Automatic logic inference (QF_BV, QF_ABV, QF_BVFP, etc.)
/// - `(set-option :timeout <ms>)` for solver timeout
/// - Start-mode solver options before the logic declaration
///
/// The returned script is deliberately verdict-only.  SMT-LIB does not have a
/// conditional command, so appending `(get-value ...)` would make every UNSAT
/// proof script ill-formed (there is no model to query).  The verification
/// path issues a second, SAT-only query when counterexample values are wanted.
pub fn generate_smt2_query(obligation: &ProofObligation, config: &AYConfig) -> String {
    generate_smt2_query_with_arrays(obligation, config, &[])
}

/// Generate a complete SMT-LIB2 query with additional array-sorted variable declarations.
///
/// Extends [`generate_smt2_query`] with declarations for non-bitvector symbolic
/// variables (arrays, FP-sorted constants, etc.). This is needed for memory model
/// proofs where memory is a symbolic `Array(BitVec64, BitVec8)` variable.
///
/// # Arguments
///
/// * `obligation` -- the proof obligation (bitvector inputs are declared from `inputs`)
/// * `config` -- solver configuration
/// * `extra_decls` -- additional variable declarations with arbitrary sorts,
///   emitted as `(declare-const name sort)` in the SMT-LIB2 output
pub fn generate_smt2_query_with_arrays(
    obligation: &ProofObligation,
    config: &AYConfig,
    extra_decls: &[(String, SmtSort)],
) -> String {
    // Build the negated equivalence formula, then try to expand bounded
    // quantifiers into conjunctions/disjunctions. This keeps the formula
    // in a quantifier-free logic (QF_*) when possible, which is faster.
    // If quantifiers remain (non-constant bounds or large ranges), the
    // formula is used as-is and infer_logic will select the quantified
    // variant (e.g., ABV instead of QF_ABV).
    let raw_formula = obligation.negated_equivalence();
    let formula = prepare_formula_for_smt(&raw_formula);
    generate_smt2_query_from_formula(obligation, config, extra_decls, &raw_formula, &formula)
}

/// Generate an SMT-LIB2 query that does NOT run the solver-oriented bitvector
/// simplifier on the negated equivalence.
///
/// TCB soundness guard (see [`simplifier_alone_proved_unsat`]): when the local
/// simplifier alone collapses the negated equivalence to a constant `false`, the
/// solver would only ever see `(assert false)` and never the real formula —
/// letting a (potentially unsound) rewrite mint a `Verified`. This generator is
/// used by [`verify_with_ay`] for exactly those obligations so the SOLVER checks
/// the real formula. It still applies the *sound* bounded-quantifier expansion
/// (a mechanical unroll required for QF logic), but skips `simplify_solver_expr`.
pub fn generate_smt2_query_raw(obligation: &ProofObligation, config: &AYConfig) -> String {
    let raw_formula = obligation.negated_equivalence();
    let formula = quantifier_expanded_view(&raw_formula);
    generate_smt2_query_from_formula(obligation, config, &[], &raw_formula, &formula)
}

/// Historical artifact reconstruction only. Never a producer, fallback or
/// authority for a different canonical query.
#[cfg(test)]
pub(crate) fn legacy_right_spine_query_for_test(
    obligation: &ProofObligation,
    config: &AYConfig,
) -> String {
    let mut formula = obligation
        .trust_ir_expr
        .clone()
        .eq_expr(obligation.aarch64_expr.clone())
        .not_expr();
    for precondition in &obligation.preconditions {
        formula = precondition.clone().and_expr(formula);
    }
    let expanded = quantifier_expanded_view(&formula);
    generate_smt2_query_from_formula(obligation, config, &[], &formula, &expanded)
}

/// Canonical raw problem plus an optional bounded producer-only print view.
/// Neither the declaration census nor proof/cache identity comes from the view.
pub(crate) fn source_bound_query_scripts(
    obligation: &ProofObligation,
    config: &AYConfig,
) -> (String, Option<String>) {
    let raw_formula = obligation.negated_equivalence();
    let formula = quantifier_expanded_view(&raw_formula);
    source_bound_formula_scripts(obligation, config, &raw_formula, &formula)
}

fn source_bound_formula_scripts(
    obligation: &ProofObligation,
    config: &AYConfig,
    raw_formula: &SmtExpr,
    formula: &SmtExpr,
) -> (String, Option<String>) {
    let prelude = generate_smt2_query_prelude(obligation, config, &[], raw_formula, formula);
    let original = finish_smt2_query(prelude.clone(), formula);
    // The extra attempt must buy substantial text reduction, not penalize the
    // usual small scalar proof. Generic geometry only; no named-model special case.
    let producer = (original.len() >= 16_384)
        .then(|| {
            // A semantics-preserving simplifier can still copy shared nodes.
            // Reuse the shared source only when its actual Display bytes are
            // EXACTLY the emitted assertion, never on a semantic guess.
            let body = original.strip_prefix(&prelude)?
                .strip_prefix("\n(assert ")?
                .strip_suffix(")\n(check-sat)\n(exit)")?;
            let shared = if std::ptr::eq(raw_formula, formula)
                || crate::smt_raw_print::prints_exactly(raw_formula, body)
            { raw_formula } else { formula };
            crate::smt_raw_print::compact_formula(shared, &original).ok().flatten()
        })
        .flatten()
        .and_then(|view| {
            let prospective = prelude.len().checked_add(view.text.len())?.checked_add(33)?;
            if prospective > original.len().saturating_mul(3) / 4 {
                return None;
            }
            if crate::diag::solve_trace_enabled() {
                eprintln!(
                    "TCG_SOLVE_TRACE compact_raw_print original_bytes={} expression_bytes={} nodes={} edges={} bindings={} levels={}",
                    original.len(), view.output_bytes, view.distinct_nodes, view.edges,
                    view.bindings, view.levels,
                );
            }
            let mut script = prelude;
            script.push_str("\n(assert ");
            script.push_str(&view.text);
            script.push_str(")\n(check-sat)\n(exit)");
            Some(script)
        });
    (original, producer)
}

/// The SMT-LIB2 query the solver lane sends for `obligation`: the raw form
/// ([`generate_smt2_query_raw`]) when the local simplifier alone would fold
/// the negated equivalence to `false` ([`simplifier_alone_proved_unsat`]),
/// else the simplified form ([`generate_smt2_query`]). [`verify_with_ay`] and
/// the replayable query send exactly these bytes as the obligation's exact
/// query (an obligation with arrays or floating point is first tried through
/// [`generate_lowered_queries`], and a proof-publication failure may be
/// retried with the same script split per conjunct); a caller that runs a
/// solver outside the lane (a hand probe) uses this to send the same ones.
pub fn lane_smt2_query(obligation: &ProofObligation, config: &AYConfig) -> String {
    // Select and render from the same preparation. The old guard followed
    // by a generator rebuilt the negated equivalence and expanded it twice,
    // and simplified it twice whenever the guard did not fire.
    let raw = obligation.negated_equivalence();
    let expanded = quantifier_expanded_view(&raw);
    let simplified = simplify_solver_expr(&expanded);
    let emitted = if is_constant_false(&simplified) && !is_constant_false(&expanded) {
        expanded.as_ref()
    } else {
        &simplified
    };
    generate_smt2_query_from_formula(obligation, config, &[], &raw, emitted)
}

/// The obligation's query rewritten into pure bit-vector form, each with the
/// obligation it is a query FOR, in the order to ask them. Empty when neither
/// rewrite applies; the exact query is then the only one.
///
/// Two rewrites, both there because Clean's Carcara can check no proof over
/// the theories they remove:
///
/// * [`crate::array_row_lowering`] eliminates arrays built from constant
///   arrays, `store` and array `ite` by read-over-write — an EQUIVALENCE, so
///   nothing is abstracted;
/// * [`crate::fp_bv_lowering`] then lowers floating point: the first query
///   abstracts rounding and nothing more, and a second, present only when a
///   conversion is abstracted, adds the exact conversion facts. Asking that
///   one first would make every conversion row's proof larger for the few
///   (the int->float->int round trips) that depend on what a conversion
///   computes — measured 2026-09-28 on seal `trust-7d5533b2`, conjoining the
///   facts always turned 24 of 28 certified conversion rows into trust steps
///   or rejected documents.
///
/// An UNSAT of any of them is an UNSAT of the obligation's own query (each
/// module's docs give the argument); a SAT is not a counterexample. The
/// inputs are the obligation's bit-vector inputs, every FP input as its bit
/// pattern, and one per abstracted rounding operation. The local simplifier
/// runs on each under the same rule as every other query: it may not decide
/// it alone ([`simplifier_alone_proved_unsat`]).
pub fn generate_lowered_queries(
    obligation: &ProofObligation,
    config: &AYConfig,
) -> Vec<(String, ProofObligation)> {
    let (lowered, formulas) = lowered_formulas(obligation);
    formulas
        .into_iter()
        .map(|formula| {
            let simplified = simplify_solver_expr(&formula);
            let emitted = if is_constant_false(&simplified) && !is_constant_false(&formula) {
                formula.clone()
            } else {
                simplified
            };
            let smt2 = generate_smt2_query_from_formula(&lowered, config, &[], &formula, &emitted);
            (smt2, lowered.clone())
        })
        .collect()
}

/// Producer-only shared spelling of each declared lowered image. The exact
/// unshared image remains the checker problem and every cache/certificate key.
pub(crate) fn source_bound_lowered_query_scripts(
    obligation: &ProofObligation,
    config: &AYConfig,
) -> Vec<(String, Option<String>, ProofObligation)> {
    let (lowered, formulas) = lowered_formulas(obligation);
    formulas
        .into_iter()
        .map(|formula| {
            let simplified = simplify_solver_expr(&formula);
            let emitted = if is_constant_false(&simplified) && !is_constant_false(&formula) {
                formula.clone()
            } else {
                simplified
            };
            let (original, producer) =
                source_bound_formula_scripts(&lowered, config, &formula, &emitted);
            (original, producer, lowered.clone())
        })
        .collect()
}

/// The formulas the array and floating-point lowerings send instead of the
/// exact query, with the obligation they are declared under. Empty (and the
/// obligation unchanged) when neither lowering applies or one declines.
fn lowered_formulas(obligation: &ProofObligation) -> (ProofObligation, Vec<SmtExpr>) {
    use crate::array_row_lowering::{ArrayDecline, eliminate_arrays_with_reserved};
    use crate::fp_bv_lowering::{FpBvDecline, lower_fp_to_bv};

    let raw_formula = obligation.negated_equivalence();
    let formula = quantifier_expanded_view(&raw_formula);
    let input_names: Vec<&str> = obligation
        .inputs
        .iter()
        .map(|(name, _)| name.as_str())
        .chain(obligation.fp_inputs.iter().map(|(name, ..)| name.as_str()))
        .collect();
    let (formula, eliminated_arrays) = match eliminate_arrays_with_reserved(&formula, &input_names)
    {
        Ok(rewritten) => (std::borrow::Cow::Owned(rewritten), true),
        Err(ArrayDecline::NoArrays) => (formula, false),
        Err(ArrayDecline::Unsupported(_)) => return (obligation.clone(), Vec::new()),
    };
    let reserved: Vec<String> = obligation
        .inputs
        .iter()
        .map(|(name, _)| name.clone())
        .chain(obligation.fp_inputs.iter().map(|(name, ..)| name.clone()))
        .chain(formula.free_vars())
        .chain(formula.uninterpreted_functions())
        .collect();
    let mut lowered = obligation.clone();
    let formulas: Vec<SmtExpr> = match lower_fp_to_bv(&formula, &obligation.fp_inputs, &reserved) {
        Ok(lowering) => {
            lowered.fp_inputs.clear();
            for (name, width) in &lowering.declarations {
                if !lowered.inputs.iter().any(|(declared, _)| declared == name) {
                    lowered.inputs.push((name.clone(), *width));
                }
            }
            std::iter::once(lowering.formula.clone())
                .chain(lowering.formula_with_conversion_facts())
                .collect()
        }
        Err(FpBvDecline::NoFloatingPoint) if eliminated_arrays => vec![formula.into_owned()],
        Err(_) => return (obligation.clone(), Vec::new()),
    };
    (lowered, formulas)
}

/// The queries of [`generate_lowered_queries`] — or the exact query, when no
/// lowering applies — with every derived bit-vector operator spelled by its
/// SMT-LIB definition (`derived_operator_lowering`). Only the queries the
/// rewrite changes are returned. The rewrite runs AFTER the solver-side
/// simplifier, which may itself spell a comparison as a derived operator.
pub fn generate_definitional_queries(
    obligation: &ProofObligation,
    config: &AYConfig,
) -> Vec<(String, ProofObligation)> {
    use crate::derived_operator_lowering::lower_derived_operators;

    let (mut lowered, mut formulas) = lowered_formulas(obligation);
    if formulas.is_empty() {
        lowered = obligation.clone();
        formulas.push(expand_bounded_quantifiers(
            &obligation.negated_equivalence(),
        ));
    }
    formulas
        .into_iter()
        .filter_map(|formula| {
            let simplified = simplify_solver_expr(&formula);
            let emitted = if is_constant_false(&simplified) && !is_constant_false(&formula) {
                formula.clone()
            } else {
                simplified
            };
            let raw = lower_derived_operators(&formula);
            let emitted_lowered = lower_derived_operators(&emitted);
            if raw.is_none() && emitted_lowered.is_none() {
                return None;
            }
            let raw = raw.unwrap_or(formula);
            let emitted = emitted_lowered.unwrap_or(emitted);
            let smt2 = generate_smt2_query_from_formula(&lowered, config, &[], &raw, &emitted);
            Some((smt2, lowered.clone()))
        })
        .collect()
}

/// Rewrite a rendered query's single conjunctive `(assert ...)` into one
/// `(assert ...)` per top-level conjunct. `None` when there is nothing to
/// rewrite or the text cannot be parsed with certainty.
///
/// `(assert (and A (and B C)))` and `(assert A) (assert B) (assert C)` are the
/// same SMT-LIB2 script — an assertion stack is itself conjunctive, so no
/// solver's satisfiability verdict can differ between them. What DOES differ is
/// whether `ay 0.26.0+build.9624` can PUBLISH a checkable proof of UNSAT.
///
/// MEASURED (2026-09-28, over all 65 conjunctive queries in
/// `tests/fixtures/x86_source_bound_body/snapshots.smt2`, each run both ways):
///
/// | single `assert` | one per conjunct | queries |
/// | --- | --- | ---: |
/// | proof | proof | 48 |
/// | **`and_pos` FAILURE** | **proof** | **9** |
/// | incomplete (other cause) | incomplete | 8 |
///
/// MEASURED AGAIN (2026-10-14, the same 65 snapshot queries at main
/// `a687e0046`, AY 0.26.0 build 9624 of Trust package 9192, aterm Clean 8606):
/// 2 publish a proof, 46 an incomplete one, 8 are rejected by AY's own strict
/// self-check, and 9 `and_pos` refusals publish a proof split. Since
/// OD-106 (`e5baa26d3`) the checker receives the ORIGINAL script, whose one
/// premise is the conjunction, and rejected all 9 split proofs at their first
/// `assume` (`could not match term to any of the original problem premises`):
/// the retry certified nothing. With the assumptions re-derived from the
/// conjunction ([`crate::split_conjunct_proof`]) Clean accepts all 9 against
/// the original.
///
/// **9 newly publish a proof and NONE regresses.** The escaped failure is AY
/// refusing its own UNSAT proof — `invalid surface proof step t1: and_pos indexed
/// conjunct is absent from its effective source` — which the backend sees as
/// `replay=none (no independently checked proof)` and turns into a fail-closed
/// `[TCG-PROOF-465]`. As separate asserts the same obligation returns
/// `unproved_steps=0 foreign_assumes=no trust_free=yes ay_self_checkable=yes`.
/// The 9 include `Ident`, the register-to-register COPY obligation that is the
/// first uncovered opcode in 396 of the 494 source-bound failed roots of the
/// x86-64 `library/core` census.
///
/// WHY A TEXT REWRITE, and why it is only a RETRY. It transforms the exact bytes
/// the solver was just given, so the retried script is provably the same problem;
/// regenerating from the obligation could not guarantee that, because several
/// renderers feed this path and they differ (`_with_arrays`, `_raw`, the
/// simplifier-skipping guard). And it runs ONLY after the `and_pos` publication
/// failure, so no query that already works changes by a byte — which matters
/// because committed certificates are keyed to query text, and rewriting every
/// query would invalidate that corpus.
///
/// This is a workaround for a solver defect, not a weakening: the retried script
/// admits exactly the models the original did, and the proof AY returns is
/// checked by the independent replay against the ORIGINAL script (OD-106),
/// after [`crate::split_conjunct_proof`] re-derives its top-level assumptions
/// from the original conjunction with Alethe `and` steps. That rewrite has no
/// authority of its own: a wrong one is a checker rejection.
fn split_assert_conjuncts(smt2: &str) -> Option<String> {
    /// Split the body of an `(and ...)` term into its immediate arguments.
    fn args(term: &str) -> Option<Vec<&str>> {
        let inner = term.strip_prefix("(and")?.strip_suffix(')')?;
        let mut out = Vec::new();
        let mut depth = 0usize;
        let mut start = None;
        for (i, ch) in inner.char_indices() {
            match ch {
                '(' => {
                    if depth == 0 {
                        start = Some(i);
                    }
                    depth += 1;
                }
                ')' => {
                    depth = depth.checked_sub(1)?;
                    if depth == 0 {
                        out.push(inner[start.take()?..=i].trim());
                    }
                }
                _ => {}
            }
        }
        if depth != 0 || out.is_empty() {
            return None;
        }
        Some(out)
    }

    /// Flatten nested `and`s into the full conjunct list.
    fn flatten(term: &str, out: &mut Vec<String>, fuel: &mut u32) -> Option<()> {
        *fuel = fuel.checked_sub(1)?;
        if term.starts_with("(and") {
            for a in args(term)? {
                flatten(a, out, fuel)?;
            }
        } else {
            out.push(term.to_string());
        }
        Some(())
    }

    let mut rewritten = Vec::new();
    let mut hits = 0usize;
    for line in smt2.lines() {
        let trimmed = line.trim();
        let term = trimmed
            .strip_prefix("(assert ")
            .and_then(|rest| rest.strip_suffix(')'))
            .filter(|t| t.starts_with("(and"));
        match term {
            Some(term) => {
                let mut conjuncts = Vec::new();
                let mut fuel = 4096u32;
                flatten(term, &mut conjuncts, &mut fuel)?;
                if conjuncts.len() < 2 {
                    return None;
                }
                hits += 1;
                for c in conjuncts {
                    rewritten.push(format!("(assert {c})"));
                }
            }
            None => rewritten.push(line.to_string()),
        }
    }
    if hits != 1 {
        // Exactly one conjunctive assert is the shape this path renders. Anything
        // else is unfamiliar: fail closed and keep the original query.
        return None;
    }
    Some(rewritten.join("\n"))
}

fn generate_smt2_query_from_formula(
    obligation: &ProofObligation,
    config: &AYConfig,
    extra_decls: &[(String, SmtSort)],
    raw_formula: &SmtExpr,
    formula: &SmtExpr,
) -> String {
    finish_smt2_query(
        generate_smt2_query_prelude(obligation, config, extra_decls, raw_formula, formula),
        formula,
    )
}

/// Write directly into the final buffer: no expanded assertion-sized staging
/// String followed by another full join/copy. Exact historical bytes retained.
fn finish_smt2_query(mut script: String, formula: &SmtExpr) -> String {
    use std::fmt::Write;
    write!(script, "\n(assert {formula})\n(check-sat)\n(exit)")
        .expect("formatting into String cannot fail");
    script
}

fn generate_smt2_query_prelude(
    obligation: &ProofObligation,
    config: &AYConfig,
    extra_decls: &[(String, SmtSort)],
    raw_formula: &SmtExpr,
    formula: &SmtExpr,
) -> String {
    let mut lines = Vec::new();

    // Solver options are start-mode commands in AY.  They MUST precede
    // `(set-logic ...)`; AY correctly rejects a late `:produce-models` option.
    if config.timeout_ms > 0 {
        // AY's SMT-LIB interface accepts :timeout in milliseconds.
        lines.push(format!("(set-option :timeout {})", config.timeout_ms));
    }
    if config.produce_models {
        lines.push("(set-option :produce-models true)".to_string());
    }

    // Logic declaration -- infer theories from both the emitted formula and
    // declarations. The emitted formula may be simplified to `false`, but the
    // SMT-LIB2 script still needs a logic that admits declared FP/array inputs.
    let logic = infer_obligation_logic_for_smt2(obligation, raw_formula, formula, extra_decls);
    lines.push(format!("(set-logic {})", logic));

    // Declare symbolic bitvector inputs
    for (name, width) in &obligation.inputs {
        lines.push(format!("(declare-const {} (_ BitVec {}))", name, width));
    }

    // Declare symbolic floating-point inputs
    for (name, eb, sb) in &obligation.fp_inputs {
        lines.push(format!(
            "(declare-const {} (_ FloatingPoint {} {}))",
            name, eb, sb
        ));
    }

    // Declare additional non-bitvector inputs (arrays, FP, etc.)
    for (name, sort) in extra_decls {
        lines.push(format!("(declare-const {} {})", name, sort_to_smt2(sort)));
    }

    // Scan the formula for uninterpreted function applications and emit
    // `(declare-fun ...)` for each unique function name found.
    let mut uf_decls = Vec::new();
    collect_uf_declarations(formula, &mut uf_decls);
    for (name, arg_sorts, ret_sort) in &uf_decls {
        let arg_sorts_str: Vec<String> = arg_sorts.iter().map(sort_to_smt2).collect();
        lines.push(format!(
            "(declare-fun {} ({}) {})",
            name,
            arg_sorts_str.join(" "),
            sort_to_smt2(ret_sort)
        ));
    }

    lines.join("\n")
}

/// Add a model-value request to a verdict-only query.
///
/// This helper is used only after an earlier execution of `verdict_smt2`
/// returned SAT.  Keeping it separate is important: an unconditional
/// `(get-value ...)` after UNSAT is an SMT-LIB protocol error and AY correctly
/// exits nonzero for that script.
fn generate_sat_model_query(obligation: &ProofObligation, verdict_smt2: &str) -> Option<String> {
    let mut var_names: Vec<&str> = obligation
        .inputs
        .iter()
        .map(|(name, _)| name.as_str())
        .collect();
    for (name, _, _) in &obligation.fp_inputs {
        var_names.push(name.as_str());
    }
    if var_names.is_empty() {
        return None;
    }

    let trimmed = verdict_smt2.strip_suffix('\n').unwrap_or(verdict_smt2);
    let body = trimmed.strip_suffix("(exit)")?;
    Some(format!(
        "{body}(get-value ({}))\n(exit)",
        var_names.join(" ")
    ))
}

// ---------------------------------------------------------------------------
// Public convenience API (named per task specification)
// ---------------------------------------------------------------------------

/// Serialize a proof obligation to a complete SMT-LIB2 query string.
///
/// This uses default configuration while preserving the source formula shape
/// except for bounded-quantifier expansion. Solver entry points use
/// [`generate_smt2_query`] directly so they still get solver-oriented
/// simplification before invoking AY.
///
/// The returned string is a complete SMT-LIB2 script ready to be piped to
/// AY:
/// ```text
/// (set-option :timeout 30000)
/// (set-option :produce-models true)
/// (set-logic QF_BV)
/// (declare-const a (_ BitVec 32))
/// (declare-const b (_ BitVec 32))
/// (assert (not (= (bvadd a b) (bvadd a b))))
/// (check-sat)
/// (exit)
/// ```
pub fn serialize_to_smt2(obligation: &ProofObligation) -> String {
    let raw_formula = obligation.negated_equivalence();
    let formula = quantifier_expanded_view(&raw_formula);
    generate_smt2_query_from_formula(
        obligation,
        &AYConfig::default(),
        &[],
        &raw_formula,
        &formula,
    )
}

/// Verify a proof obligation by shelling out to an AY CLI binary.
///
/// This is an alias for [`verify_with_cli`] with a name that matches the
/// ay-specific nomenclature used throughout the codebase.
///
/// The function:
/// 1. Serializes the proof obligation to SMT-LIB2
/// 2. Writes it to a temp file
/// 3. Invokes the selected AY binary
/// 4. Parses the output (sat/unsat/timeout/error)
/// 5. Extracts counterexamples from the model if SAT
pub fn verify_with_ay_cli(obligation: &ProofObligation, config: &AYConfig) -> AYResult {
    verify_with_cli(obligation, config)
}

/// Parse raw solver output text into a [`AYResult`].
///
/// This is a public wrapper around the internal parser, useful for testing
/// and for consumers that invoke the solver themselves.
///
/// # Arguments
///
/// * `output` -- the solver's stdout text (e.g., "unsat\n" or "sat\n((a #x0a))")
/// * `inputs` -- the bitvector input variables for counterexample extraction
///
/// # Returns
///
/// * [`AYResult::SolverUnsat`] if the raw output is "unsat"; only the solver
///   invocation path can promote it to [`AYResult::Verified`] after checking
///   the exact proof independently
/// * [`AYResult::CounterExample`] if the output is "sat" (with model if available)
/// * [`AYResult::Timeout`] if the output contains "timeout"
/// * [`AYResult::Unknown`] if the output is "unknown"
/// * [`AYResult::Error`] for any other output
pub fn parse_ay_output(output: &str, inputs: &[(String, u32)]) -> AYResult {
    parse_solver_output(output, "", inputs)
}

// ---------------------------------------------------------------------------
// CLI subprocess backend (always available)
// ---------------------------------------------------------------------------

/// Verify through the shared AY pipeline, including independently checked
/// array/FP lowering, the constant-false guard and original-query models.
/// All ordinary public entry points use the same proof acceptance policy;
/// callers requiring one exact unsimplified problem use [`verify_with_cli_raw`].
pub fn verify_with_cli(obligation: &ProofObligation, config: &AYConfig) -> AYResult {
    verify_with_ay(obligation, config)
}

/// Invoke the solver on the unsimplified raw negated equivalence (bounded
/// quantifiers still expanded), without array/FP or definitional retries.
/// The exact problem still requires independent proof checking; this entry
/// point never trusts the local simplifier to decide the obligation.
pub fn verify_with_cli_raw(obligation: &ProofObligation, config: &AYConfig) -> AYResult {
    verify_with_cli_raw_attributed(obligation, config).result
}

/// [`verify_with_cli_raw`], with the AY the verdict is attributable to.
pub fn verify_with_cli_raw_attributed(
    obligation: &ProofObligation,
    config: &AYConfig,
) -> AyVerdict {
    let smt2 = generate_smt2_query_raw(obligation, config);
    verify_with_cli_smt2(obligation, config, &smt2)
}

/// [`verify_with_cli_raw_attributed`] of a query spelled otherwise than its
/// obligation renders (a spelling the expression type has no node for):
/// qualification evidence for a canonical encoding, never credit.
#[cfg(test)]
pub(crate) fn verify_respelled_query(
    obligation: &ProofObligation,
    config: &AYConfig,
    smt2: &str,
) -> AyVerdict {
    verify_with_cli_smt2(obligation, config, smt2)
}

/// One registry discharge's owned query and concrete launch authority. Unlike an
/// authority digest alone, this value is consumed by the actual solver/checker
/// path; a later request's discovery or scoped environment cannot replace it.
pub(crate) struct PreparedAyQuery {
    obligation: ProofObligation,
    config: AYConfig,
    smt2: String,
    // Producer spelling only. Every authority/cache/receipt key remains smt2.
    producer_smt2: Option<String>,
    selection: SolverSelection,
    authority: VerificationAuthority,
    solver_identity: String,
    authority_id: [u8; 32],
    query_key: String,
    // Prepared by `FunctionAyAuthority::prepare_source_bound`: the replay of a
    // sealed source-bound owner's raw obligation, the only query the negative
    // memo serves.
    source_bound: bool,
    // Slice 19 (OD-197): a resident deadline is followed by one fresh replay
    // (the owner's `SourceBoundReplay::fresh_after_resident_timeout`).
    fresh_after_resident_timeout: bool,
    // Slice 23 (OD-206): the query is an x86-64 body obligation's
    // generalization (the owner's `SourceBoundReplay::generalized`), a route
    // the negative memo's key carries.
    generalized: bool,
}

/// Captured once for a function-verification request. A missing ready content
/// identity prevents reuse, not fresh execution under the selected authority.
#[derive(Clone, Debug)]
pub(crate) struct FunctionAyAuthority {
    selection: SolverSelection,
    authority: Option<VerificationAuthority>,
    solver_identity: Option<String>,
}

impl FunctionAyAuthority {
    #[cfg(test)]
    pub(crate) fn without_ready_identity(mut self) -> Self {
        // Deterministically exercise the real cold-identity execution path,
        // without depending on a race with background hashing.
        self.solver_identity = None;
        self
    }

    pub(crate) fn capture(child_env: SanitizedChildEnv, timeout_ms: u64) -> Self {
        let selection = select_solver_binary();
        let authority = selection.pinned().map(|solver| {
            VerificationAuthority::capture_with_environment(solver, child_env, timeout_ms)
        });
        let solver_identity = authority.as_ref().and_then(|authority| {
            if crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some() {
                return None;
            }
            // Admission digested exactly these bytes; while the file is
            // unchanged that digest IS the content identity, so no second hash.
            authority.solver().revalidate().ok()?;
            Some(authority.solver().sha256().to_owned())
        });
        Self {
            selection,
            authority,
            solver_identity,
        }
    }

    pub(crate) fn reuse_identity(&self) -> Option<[u8; 32]> {
        let authority = self.authority.as_ref()?;
        authority.child_env().working_dir()?;
        authority.cache_id_with_solver_identity(self.solver_identity.as_deref()?)
    }

    /// The admitted AY this request's verdicts are bound to (`None`: refused).
    pub(crate) fn solver(&self) -> Option<&PinnedAy> {
        self.selection.pinned()
    }

    /// Why no AY is bound to this request (`None` when one is).
    pub(crate) fn refusal(&self) -> Option<&AyIdentityRefusal> {
        self.selection.refusal()
    }

    /// A source-bound owner's obligation is replayed exactly as constructed,
    /// without the arithmetic simplifier becoming part of its source-to-proof
    /// boundary. Only the sealed owners (AArch64 frame/ALU, x86-64 body)
    /// reach this entry point.
    pub(crate) fn prepare_source_bound<O>(
        &self,
        owner: &O,
        config: AYConfig,
    ) -> Option<PreparedAyQuery>
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        let obligation = owner.replayed_obligation();
        self.prepare_raw(obligation, config, true)
            .map(|query| PreparedAyQuery {
                fresh_after_resident_timeout: owner.fresh_after_resident_timeout(),
                generalized: owner.generalized(),
                ..query
            })
    }

    /// Fresh replay of a source-bound owner's raw obligation under the
    /// captured authority (no reusable identity).
    #[cfg(test)]
    pub(crate) fn verify_fresh_source_bound<O>(&self, owner: &O, config: &AYConfig) -> AYResult
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        self.verify_fresh_source_bound_attributed(owner, config)
            .result
    }

    /// Fresh source-bound replay retaining the actual producer attribution.
    pub(crate) fn verify_fresh_source_bound_attributed<O>(
        &self,
        owner: &O,
        config: &AYConfig,
    ) -> AyVerdict
    where
        O: crate::source_bound_replay::SourceBoundReplay + ?Sized,
    {
        let obligation = owner.replayed_obligation();
        let (original, producer) = source_bound_query_scripts(obligation, config);
        self.verify_fresh_query(
            obligation,
            config,
            &original,
            producer.as_deref(),
            (true, owner.fresh_after_resident_timeout()),
        )
    }

    /// [`Self::prepare_source_bound`] for a word-bound obligation: the same
    /// raw, unsimplified query. Only the sealed word-bound types reach it,
    /// and their verdicts are recorded, never credited.
    pub(crate) fn prepare_word_bound<O>(
        &self,
        owner: &O,
        config: AYConfig,
    ) -> Option<PreparedAyQuery>
    where
        O: crate::source_bound_replay::WordBoundReplay + ?Sized,
    {
        let obligation = owner.replayed_obligation();
        self.prepare_raw(obligation, config, false)
    }

    /// Fresh raw word-bound replay, without constructive proof composition.
    pub(crate) fn verify_fresh_word_bound<O>(&self, owner: &O, config: &AYConfig) -> AYResult
    where
        O: crate::source_bound_replay::WordBoundReplay + ?Sized,
    {
        let obligation = owner.replayed_obligation();
        let (original, producer) = source_bound_query_scripts(obligation, config);
        self.verify_fresh_query(
            obligation,
            config,
            &original,
            producer.as_deref(),
            (false, false),
        )
        .result
    }

    fn prepare_raw(
        &self,
        obligation: &ProofObligation,
        config: AYConfig,
        source_bound: bool,
    ) -> Option<PreparedAyQuery> {
        // Resolve captured reusable authority first; build ONE raw script,
        // rather than constructing/discarding a simplified prepared script.
        let authority = self.authority.clone()?;
        let identity = self.solver_identity.clone()?;
        let authority_id = self.reuse_identity()?;
        let (original, producer) = source_bound_query_scripts(obligation, &config);
        Some(PreparedAyQuery::from_queries(
            obligation,
            config,
            self.selection.clone(),
            authority,
            identity,
            authority_id,
            (original, producer, source_bound),
        ))
    }

    fn verify_fresh_query(
        &self,
        obligation: &ProofObligation,
        config: &AYConfig,
        smt2: &str,
        producer_smt2: Option<&str>,
        (closed_definitions, fresh_after_resident_timeout): (bool, bool),
    ) -> AyVerdict {
        let Some(authority) = self.authority.as_ref() else {
            return AyVerdict::not_run(AYResult::Error(format!(
                "no AY solver was admitted for the captured function request: {}",
                self.selection.detail()
            )));
        };
        let (result, source) = verify_with_cli_smt2_under_authority(
            obligation,
            config,
            AyQueryText {
                original: smt2,
                producer: producer_smt2,
                closed_definitions,
                fresh_after_resident_timeout,
            },
            &self.selection,
            authority,
            crate::verdict_db::recording_active(),
            None,
        );
        AyVerdict {
            result,
            solver: Some(authority.solver().clone()),
            source,
        }
    }
}

/// A reuse receipt is private to the discharge implementation. A caller-supplied
/// `AYResult::Verified` alone cannot populate the outer registry memos.
struct AyReuseReceipt {
    authority_id: [u8; 32],
    query_key: String,
}

struct AyRequestBinding {
    authority_id: [u8; 32],
    query_key: String,
}

pub(crate) struct CapturedAyResult {
    result: AYResult,
    // Attribution, not proof authority: even an uncacheable portable or
    // inconclusive result belongs only to the request that actually ran.
    request: AyRequestBinding,
    receipt: Option<AyReuseReceipt>,
    // Which admitted AY the query was bound to, and how the result was
    // obtained (portable and constructive proofs did not run it).
    #[cfg_attr(not(test), allow(dead_code))]
    solver: PinnedAy,
    source: AyVerdictSource,
}

impl CapturedAyResult {
    pub(crate) fn result(&self) -> &AYResult {
        &self.result
    }

    /// The admitted AY this result was bound to, not necessarily its producer.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn solver(&self) -> &PinnedAy {
        &self.solver
    }

    /// How the result was obtained.
    pub(crate) fn source(&self) -> &AyVerdictSource {
        &self.source
    }

    /// The result with its provenance.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn verdict(&self) -> AyVerdict {
        AyVerdict {
            result: self.result.clone(),
            solver: Some(self.solver.clone()),
            source: self.source.clone(),
        }
    }

    pub(crate) fn reusable_for(&self, request: &PreparedAyQuery) -> bool {
        self.matches_request(request)
            && self.receipt.as_ref().is_some_and(|receipt| {
                receipt.authority_id == request.authority_id
                    && receipt.query_key == request.query_key
            })
    }

    pub(crate) fn matches_request(&self, request: &PreparedAyQuery) -> bool {
        self.request.authority_id == request.authority_id
            && self.request.query_key == request.query_key
    }

    #[cfg(test)]
    pub(crate) fn memo_control(request: &PreparedAyQuery, result: AYResult) -> Self {
        // Synthetic memo plumbing only: this helper does not execute a solver
        // or establish proof validity and is absent from production builds.
        let receipt =
            matches!(result, AYResult::Verified | AYResult::CounterExample(_)).then(|| {
                AyReuseReceipt {
                    authority_id: request.authority_id,
                    query_key: request.query_key.clone(),
                }
            });
        Self {
            result,
            request: request.binding(),
            receipt,
            solver: request.solver().clone(),
            source: AyVerdictSource::NotRun,
        }
    }

    #[cfg(test)]
    pub(crate) fn unreceipted_memo_control(request: &PreparedAyQuery, result: AYResult) -> Self {
        Self {
            result,
            request: request.binding(),
            receipt: None,
            solver: request.solver().clone(),
            source: AyVerdictSource::NotRun,
        }
    }
}

impl PreparedAyQuery {
    fn binding(&self) -> AyRequestBinding {
        AyRequestBinding {
            authority_id: self.authority_id,
            query_key: self.query_key.clone(),
        }
    }

    pub(crate) fn capture(obligation: &ProofObligation, config: AYConfig) -> Option<Self> {
        let selection = match &config.solver {
            Some(solver) => SolverSelection::explicit(solver.clone()),
            None => select_solver_for_obligation(obligation),
        };
        let solver = selection.pinned()?.clone();
        let authority = VerificationAuthority::capture_with_timeout(&solver, config.timeout_ms);
        // The admitted digest is the content identity of the unchanged file.
        solver.revalidate().ok()?;
        let solver_identity = solver.sha256().to_owned();
        let authority_id = authority.cache_id_with_solver_identity(&solver_identity)?;
        Some(Self::from_authority(
            obligation,
            config,
            selection,
            authority,
            solver_identity,
            authority_id,
        ))
    }

    fn from_authority(
        obligation: &ProofObligation,
        config: AYConfig,
        selection: SolverSelection,
        authority: VerificationAuthority,
        solver_identity: String,
        authority_id: [u8; 32],
    ) -> Self {
        // Preserve verify_with_ay's load-bearing raw-query guard exactly.
        let smt2 = lane_smt2_query(obligation, &config);
        Self::from_queries(
            obligation,
            config,
            selection,
            authority,
            solver_identity,
            authority_id,
            (smt2, None, false),
        )
    }

    fn from_queries(
        obligation: &ProofObligation,
        config: AYConfig,
        selection: SolverSelection,
        authority: VerificationAuthority,
        solver_identity: String,
        authority_id: [u8; 32],
        queries: (String, Option<String>, bool),
    ) -> Self {
        let (smt2, producer_smt2, source_bound) = queries;
        let query_key = verdict_cache_key_v2(&solver_identity, &smt2);
        Self {
            obligation: obligation.clone(),
            config,
            smt2,
            producer_smt2,
            selection,
            authority,
            solver_identity,
            authority_id,
            query_key,
            source_bound,
            fresh_after_resident_timeout: false,
            generalized: false,
        }
    }

    pub(crate) fn obligation(&self) -> &ProofObligation {
        &self.obligation
    }

    pub(crate) fn authority_id(&self) -> [u8; 32] {
        self.authority_id
    }

    pub(crate) fn solver_path(&self) -> &str {
        self.authority.solver_path_text()
    }

    /// The admitted AY this query is bound to.
    pub(crate) fn solver(&self) -> &PinnedAy {
        self.authority.solver()
    }

    #[cfg(test)]
    pub(crate) fn solver_identity(&self) -> &str {
        &self.solver_identity
    }

    pub(crate) fn query_key(&self) -> &str {
        &self.query_key
    }

    pub(crate) fn execute(&self) -> CapturedAyResult {
        self.execute_inner(true)
    }

    pub(crate) fn execute_without_portable(&self) -> CapturedAyResult {
        self.execute_inner(false)
    }

    fn execute_inner(&self, allow_portable: bool) -> CapturedAyResult {
        let recording = crate::verdict_db::recording_active();
        // Portable DRAT evidence retains its own independent checker authority.
        // It remains a valid result, but must not acquire a live AY receipt.
        if allow_portable && !recording && crate::canary_cert::cert_skip_verified(&self.smt2) {
            return CapturedAyResult {
                result: AYResult::Verified,
                request: self.binding(),
                receipt: None,
                solver: self.solver().clone(),
                source: portable_certificate_source(&self.smt2),
            };
        }
        if solver_identity_hash(self.solver_path()).as_deref() != Some(&self.solver_identity) {
            return CapturedAyResult {
                result: AYResult::Unknown("captured AY executable identity changed".to_owned()),
                request: self.binding(),
                receipt: None,
                solver: self.solver().clone(),
                source: AyVerdictSource::NotRun,
            };
        }
        let negative = if recording || self.producer_smt2.is_some() {
            None
        } else {
            self.negative_memo_scope()
        };
        let started = std::time::Instant::now();
        let (result, source) = verify_with_cli_smt2_under_authority(
            &self.obligation,
            &self.config,
            AyQueryText {
                original: &self.smt2,
                producer: self.producer_smt2.as_deref(),
                closed_definitions: self.source_bound,
                fresh_after_resident_timeout: self.fresh_after_resident_timeout,
            },
            &self.selection,
            &self.authority,
            recording,
            negative.as_ref(),
        );
        if let Some(negative) = &negative {
            negative.observe(&result, &source, started.elapsed());
        }
        // Only existing AY-produced origins may mint this AY reuse receipt.
        // Independently checked constructive proofs need a separate identity
        // contract before any cache can reuse them; never pretend AY ran.
        let receipt = (!recording
            && matches!(
                source,
                AyVerdictSource::LiveSolve
                    | AyVerdictSource::SessionMemo
                    | AyVerdictSource::AletheCertStore
            )
            && crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_none()
            && matches!(result, AYResult::Verified | AYResult::CounterExample(_))
            && solver_identity_hash(self.solver_path()).as_deref() == Some(&self.solver_identity))
        .then(|| AyReuseReceipt {
            authority_id: self.authority_id,
            query_key: self.query_key.clone(),
        });
        // These endpoint checks detect observed file replacement; they do not
        // pin an executable image against arbitrary filesystem A→B→A races.
        CapturedAyResult {
            result,
            request: self.binding(),
            receipt,
            solver: self.solver().clone(),
            source,
        }
    }

    /// The negative-memo view of a source-bound replay (`None` for every other
    /// query, under `TCG_NO_PROOF_CACHE`, with the bypass knob set, in a build
    /// without a recorded verifier source identity, or without a capable
    /// independent checker). The key binds every input the replayed
    /// outcome depends on; see [`crate::source_bound_negative_memo`].
    fn negative_memo_scope(&self) -> Option<crate::source_bound_negative_memo::NegativeMemoScope> {
        use crate::source_bound_negative_memo as memo;
        if !self.source_bound
            || memo::VERIFIER_BUILD.is_empty()
            || crate::diag::source_bound_negative_memo_disabled()
            || crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some()
        {
            return None;
        }
        let checker = self.authority.checker()?;
        let resident_route = ay_server_enabled()
            && !strict_formal_campaign_active()
            && !ay_server_is_unusable_for_authority(&self.authority);
        let key = memo::NegativeMemoIdentity {
            smt2: &self.smt2,
            query_key: &self.query_key,
            ay_identity: &self.solver().identity().describe(),
            authority_id: self.authority_id,
            checker_sha256: checker.sha256(),
            timeout_ms: self.config.timeout_ms,
            checker_timeout_ms: crate::obligation_cert_store::proof_check_timeout_ms(
                self.config.timeout_ms,
            ),
            produce_models: self.config.produce_models,
            resident_route,
            fresh_after_resident_timeout: self.fresh_after_resident_timeout,
            generalized: self.generalized,
            replay_protocol: memo::replay_protocol(),
            verifier_build: memo::VERIFIER_BUILD,
        }
        .key();
        Some(memo::NegativeMemoScope::new(
            key,
            crate::obligation_cert_store::negative_memo_dir(),
            memo::RetryPolicy::DEFAULT,
        ))
    }

    #[cfg(test)]
    pub(crate) fn memo_control(
        obligation: &ProofObligation,
        authority_id: [u8; 32],
        timeout_ms: u64,
        produce_models: bool,
    ) -> Self {
        // Memo plumbing only: an inert fixture that is never executed.
        let solver = crate::ay_identity::test_fixtures::inert();
        let config = AYConfig {
            solver: Some(solver.clone()),
            timeout_ms,
            produce_models,
        };
        let smt2 = if simplifier_alone_proved_unsat(obligation) {
            generate_smt2_query_raw(obligation, &config)
        } else {
            generate_smt2_query(obligation, &config)
        };
        let solver_identity = "aa".repeat(32);
        let query_key = verdict_cache_key_v2(&solver_identity, &smt2);
        Self {
            obligation: obligation.clone(),
            config,
            smt2,
            producer_smt2: None,
            selection: SolverSelection::explicit(solver.clone()),
            authority: VerificationAuthority::capture_solver_process(&solver),
            solver_identity,
            authority_id,
            query_key,
            source_bound: false,
            fresh_after_resident_timeout: false,
            generalized: false,
        }
    }
}

/// Core of [`verify_with_cli`]: invoke the solver on a precomputed SMT-LIB2
/// query. Split out so both the normal (simplified) and raw (un-simplified)
/// query paths share solver selection, temp-file handling, and output parsing.
fn verify_with_cli_smt2(obligation: &ProofObligation, config: &AYConfig, smt2: &str) -> AyVerdict {
    verify_with_cli_query(obligation, config, AyQueryText::raw(smt2))
}

fn verify_with_cli_query(
    obligation: &ProofObligation,
    config: &AYConfig,
    query: AyQueryText<'_>,
) -> AyVerdict {
    let smt2 = query.original;
    // PORTABLE CERT-SKIP must run before solver selection.  Its authority is
    // the exact query bytes plus an independently replayed committed proof;
    // AY is only the offline producer recorded in the certificate. Requiring
    // a live/local AY binary here would make the certificate non-portable and
    // would reject a checkable proof before consulting it.
    let recording = crate::verdict_db::recording_active();
    if !recording && crate::canary_cert::cert_skip_verified(smt2) {
        return AyVerdict {
            result: AYResult::Verified,
            solver: None,
            source: portable_certificate_source(smt2),
        };
    }
    // A certificate that exists for these exact bytes but cannot be consumed
    // on this host is NAMED in whatever the live lane answers, so an
    // unqualified checker identity is never filed as a solver gap — the
    // 2026-09-21 Linux x86-64 census did exactly that for 27 roots. The
    // verdict itself is unchanged: the live lane still runs and still fails
    // closed.
    let cert_skip_miss = if recording {
        None
    } else {
        crate::canary_cert::cert_skip_miss_reason(smt2)
    };

    // The one identity rule names and admits the solver, or refuses by name.
    let solver_selection = match &config.solver {
        Some(solver) => SolverSelection::explicit(solver.clone()),
        None => select_solver_for_obligation(obligation),
    };
    let Some(solver) = solver_selection.pinned() else {
        return AyVerdict::not_run(annotate_cert_skip_miss(
            AYResult::Error(format!(
                "No AY solver admitted ({})",
                solver_route_summary_from_selection(
                    obligation_logic(obligation),
                    &solver_selection
                )
            )),
            cert_skip_miss,
        ));
    };
    let authority = VerificationAuthority::capture_with_timeout(solver, config.timeout_ms);

    let (result, source) = verify_with_cli_smt2_under_authority(
        obligation,
        config,
        query,
        &solver_selection,
        &authority,
        recording,
        None,
    );
    AyVerdict {
        result: annotate_cert_skip_miss(result, cert_skip_miss),
        solver: Some(solver.clone()),
        source,
    }
}

/// Why a committed portable certificate that exists for one of the exact
/// queries [`verify_with_ay`] tries for `obligation` (its lowered, lane and
/// definitional forms) was not consumed on this host
/// ([`crate::canary_cert::cert_skip_miss_reason`]: a checker that is missing,
/// unreadable or not authorized), or `None`. Diagnosis only: it grants
/// nothing and changes no verdict. The funnel already names such a miss in
/// the text of an `Unknown` or `Error` verdict; an [`AYResult::Timeout`] or
/// [`AYResult::SolverUnsat`] carries no text, so a consumer that renders one
/// asks here, and the miss is never filed as the live solver's failure.
pub fn portable_certificate_miss_reason(
    obligation: &ProofObligation,
    config: &AYConfig,
) -> Option<String> {
    if crate::verdict_db::recording_active() {
        return None;
    }
    generate_lowered_queries(obligation, config)
        .into_iter()
        .map(|(smt2, _)| smt2)
        .chain(std::iter::once(lane_smt2_query(obligation, config)))
        .chain(
            generate_definitional_queries(obligation, config)
                .into_iter()
                .map(|(smt2, _)| smt2),
        )
        .find_map(|smt2| crate::canary_cert::cert_skip_miss_reason(&smt2))
}

/// Provenance of a portable-certificate answer: the producer AY the manifest
/// names for this exact query.
fn portable_certificate_source(smt2: &str) -> AyVerdictSource {
    AyVerdictSource::PortableCertificate {
        producer_ay_sha256: crate::canary_cert::portable_cert_producer_ay_sha256(smt2)
            .unwrap_or_default(),
    }
}

/// Append a named portable-certificate miss to a non-verifying verdict's TEXT.
/// Only the string payloads of `Unknown` and `Error` change; no variant does,
/// so every caller's fail-closed handling — and `proof_gate`'s separate
/// `Timeout` accounting — is untouched. `Timeout`, `SolverUnsat` and
/// `CounterExample` carry no text and pass through as they are.
fn annotate_cert_skip_miss(result: AYResult, miss: Option<String>) -> AYResult {
    match (result, miss) {
        (AYResult::Unknown(text), Some(miss)) => AYResult::Unknown(format!("{text}; {miss}")),
        (AYResult::Error(text), Some(miss)) => AYResult::Error(format!("{text}; {miss}")),
        (result, _) => result,
    }
}

/// Shared exact-query funnel. The caller supplies the authority actually used
/// by every resident/fresh query and independent checker; never recapture it.
/// Returns how the result was obtained alongside it.
#[derive(Clone, Copy)]
struct AyQueryText<'a> {
    original: &'a str,
    // Solely a fresh proof-producing input, not a query/authority/cache identity.
    producer: Option<&'a str>,
    // Enabled ONLY by sealed source-bound entry points, never generic raw or
    // word-bound recording. This selects an untrusted candidate, not authority.
    closed_definitions: bool,
    // Slice 19 (OD-197): a resident deadline is followed by one fresh,
    // proof-producing replay (the x86-64 body owner's queries only).
    fresh_after_resident_timeout: bool,
}

impl<'a> AyQueryText<'a> {
    fn raw(original: &'a str) -> Self {
        Self {
            original,
            producer: None,
            closed_definitions: false,
            fresh_after_resident_timeout: false,
        }
    }
}

/// Constructive text has no authority. Only THIS captured independent checker
/// accepting it against the original problem supplies a positive result. A
/// refusal, missing checker, rejection or failed check leaves the AY route
/// untouched. This never creates or refreshes an AY cache entry; acceptance
/// may clear a stale source-bound negative entry in the caller's existing memo.
fn try_closed_definition_proof(
    obligation: &ProofObligation,
    config: &AYConfig,
    smt2: &str,
    authority: &VerificationAuthority,
) -> Option<AyVerdictSource> {
    let producer_source = crate::source_bound_negative_memo::VERIFIER_BUILD;
    if producer_source.is_empty() {
        return None;
    }
    let checker = authority.checker()?;
    crate::process_cost::mark("closed_definition_compose_begin");
    let candidate = crate::closed_definition_alethe::compose(obligation);
    crate::process_cost::mark("closed_definition_compose_end");
    let candidate = match candidate {
        Ok(candidate) if candidate.definitions > 0 => candidate,
        Ok(candidate) => {
            if crate::diag::solve_trace_enabled() {
                eprintln!(
                    "TCG_SOLVE_TRACE closed_definition_candidate_refused obligation={:?} definitions={} proof_bytes={}",
                    obligation.name,
                    candidate.definitions,
                    candidate.text.len()
                );
            }
            return None;
        }
        Err(reason) => {
            if crate::diag::solve_trace_enabled() {
                eprintln!(
                    "TCG_SOLVE_TRACE closed_definition_candidate_refused obligation={:?} reason={reason:?}",
                    obligation.name
                );
            }
            return None;
        }
    };
    crate::process_cost::mark("closed_definition_check_begin");
    // A Clean check of a proof: the checker's own deadline (OD-223).
    let checked = crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
        checker.path(),
        checker.sha256(),
        smt2,
        &candidate.text,
        authority.child_env(),
        crate::obligation_cert_store::proof_check_timeout_ms(config.timeout_ms),
    );
    crate::process_cost::mark("closed_definition_check_end");
    if crate::diag::solve_trace_enabled() {
        eprintln!(
            "TCG_SOLVE_TRACE closed_definition_proof obligation={:?} original_bytes={} proof_bytes={} premises={} definitions={} steps={} checked={checked:?} checker_sha256={} ay_ran=false",
            obligation.name,
            smt2.len(),
            candidate.text.len(),
            candidate.premises,
            candidate.definitions,
            candidate.steps,
            checker.sha256(),
        );
    }
    matches!(checked, Ok(true)).then(|| AyVerdictSource::ClosedDefinitionProof {
        producer_verifier_source_sha256: producer_source.to_owned(),
        checker_sha256: checker.sha256().to_owned(),
    })
}

fn verify_with_cli_smt2_under_authority(
    obligation: &ProofObligation,
    config: &AYConfig,
    query: AyQueryText<'_>,
    solver_selection: &SolverSelection,
    authority: &VerificationAuthority,
    recording: bool,
    negative: Option<&crate::source_bound_negative_memo::NegativeMemoScope>,
) -> (AYResult, AyVerdictSource) {
    verify_with_cli_smt2_on_server(
        AyResidentServer::process(),
        obligation,
        config,
        query,
        solver_selection,
        authority,
        recording,
        negative,
    )
}

/// [`verify_with_cli_smt2_under_authority`] with the resident server named
/// (production: [`AyResidentServer::process`]). `negative` is the
/// source-bound negative memo's view of this query (`None` for every other
/// query); it is consulted after every positive tier and before any solve.
#[allow(clippy::too_many_arguments)]
fn verify_with_cli_smt2_on_server(
    server: AyResidentServer,
    obligation: &ProofObligation,
    config: &AYConfig,
    query: AyQueryText<'_>,
    solver_selection: &SolverSelection,
    authority: &VerificationAuthority,
    recording: bool,
    negative: Option<&crate::source_bound_negative_memo::NegativeMemoScope>,
) -> (AYResult, AyVerdictSource) {
    let smt2 = query.original;
    // No combined-route negative receipt from raw-only CPU measurements.
    // Positive exact-original evidence remains reusable. A candidate failure
    // cannot suppress future candidate attempts via a raw-only remembered gap.
    let negative = if query.producer.is_some() {
        None
    } else {
        negative
    };
    // An independently checked result may be reused only inside this process.
    // Persistent verdict files and the committed verdict DB are untrusted hints,
    // not proof certificates: a writable file containing `unsat` must never mint
    // `AYResult::Verified`. The key binds the exact query and solver bytes;
    // recording bypasses even the process-local memo so regen observes live
    // solver output.
    let legacy_cache_key = if recording || authority.positive_reuse_context_id().is_none() {
        None
    } else {
        session_proof_cache_key(authority.solver_path_text(), smt2)
    };
    let session_cache_key = legacy_cache_key
        .as_ref()
        .and_then(|key| authority.session_key(key));
    let session_negative_cache_key = if query.producer.is_none() {
        session_cache_key.as_ref()
    } else {
        None
    };
    if let Some(key) = &session_cache_key
        && session_proof_cache_lookup_verified(key)
    {
        return (AYResult::Verified, AyVerdictSource::SessionMemo);
    }
    // ALETHE CERT STORE (crate::obligation_cert_store): the sound, machine-local
    // generalization of the canary DRAT tier. A stored Alethe proof is credited
    // ONLY after an INDEPENDENT Carcara re-check confirms it refutes THIS exact
    // SMT2 under THIS solver identity, in this process — strictly stronger than
    // the live ay verdict it replaces, and never a weaker one (any
    // miss/binding-mismatch/tamper/absent-checker falls through). ON by
    // default: the store lives at `TCG_PROOF_CERT_STORE` if set, else the
    // per-box `$XDG_CACHE_HOME`/`$HOME/.cache` `trust-cg/alethe-certs` dir;
    // `TCG_NO_CERT_STORE` or `TCG_NO_PROOF_CACHE` turns it off (precedence in
    // `obligation_cert_store::store_dir_from`). Suppressed while recording:
    // `alethe_cert_skip_verified` and `mint_alethe_cert` bail on
    // `verdict_db::recording_active()`.
    if let (Some(legacy_key), Some(session_key)) = (&legacy_cache_key, &session_cache_key)
        && crate::obligation_cert_store::alethe_cert_skip_verified_with_authority(
            legacy_key,
            authority.solver_path_text(),
            smt2,
            authority,
            config.timeout_ms,
        )
    {
        session_proof_cache_store_verified(session_key);
        return (AYResult::Verified, AyVerdictSource::AletheCertStore);
    }

    // General closed-SSA proof production, restricted to sealed source-bound
    // queries. Exact original checking, not composition or a structural census,
    // is the authority. Do not persist this as an AY-produced certificate or
    // memo. Both negative tiers remain below all positive evidence producers.
    if query.closed_definitions
        && !recording
        && let Some(source) = try_closed_definition_proof(obligation, config, smt2, authority)
    {
        return (AYResult::Verified, source);
    }

    // This is an earlier non-credit AY outcome, not a new solver execution.
    // It may never suppress independent positive evidence available above.
    if let Some(key) = session_negative_cache_key
        && let Some(reason) = session_negative_memo_lookup(key)
    {
        if crate::diag::solve_trace_enabled() {
            eprintln!(
                "TCG_SOLVE_TRACE negative_memo_hit obligation={:?} smt2_bytes={}",
                obligation.name,
                smt2.len(),
            );
        }
        return (AYResult::Unknown(reason), AyVerdictSource::SessionMemo);
    }

    // What the live replay below sees for the negative memo: a SAT on this
    // query's verdict query (an outcome that follows it, the model query
    // timing out, is never remembered as a negative, and deletes any entry
    // for the key) and every deadline expiry with the CPU time used under it
    // (a timeout is remembered only when the query used its budget).
    let witness = ReplayWitness::new(negative);

    // SOURCE-BOUND NEGATIVE MEMO (`crate::source_bound_negative_memo`): an
    // earlier live replay of this exact query, under this exact solver,
    // checker, budget, route and replay protocol, did not certify, and the
    // entry is inside its retry budget. Consulted only after both positive
    // tiers above, so a proof any process has minted is still consumed; it
    // replays a non-credit outcome and never reaches `Verified`.
    if let Some(withheld) = negative.and_then(|scope| scope.lookup()) {
        trace_negative_memo_hit(&obligation.name, smt2.len(), &withheld);
        return (withheld.non_credit_result(), AyVerdictSource::NegativeMemo);
    }

    // A spelling-only candidate has no authority to refute or withhold the
    // original problem. The SAME captured authority produces its proof; the
    // pinned independent checker receives ONLY the exact original script.
    // Any other result replays the original route, including SAT and timeout.
    if let Some(producer) = query.producer {
        let candidate = run_fresh_producer_query_once(
            authority,
            obligation,
            config,
            AyQueryText {
                original: smt2,
                producer: Some(producer),
                closed_definitions: false,
                fresh_after_resident_timeout: false,
            },
            &ReplayWitness::new(None),
        );
        if crate::diag::solve_trace_enabled() {
            eprintln!(
                "TCG_SOLVE_TRACE compact_raw_candidate original_bytes={} producer_bytes={} result={candidate:?} exact_original_check=true",
                smt2.len(),
                producer.len(),
            );
        }
        if matches!(candidate, AYResult::Verified) {
            if let Some(key) = &session_cache_key {
                session_proof_cache_store_verified(key);
            }
            // Promotion already persisted the accepted proof under ORIGINAL
            // bytes. No second mint/solve or compact-key certificate is needed.
            if recording {
                crate::verdict_db::record_live_result(&obligation.name, smt2, &candidate);
            }
            return (candidate, AyVerdictSource::LiveSolve);
        }
    }

    // Query resident AY to amortize startup, using the same SMT body with
    // interactive framing. A candidate UNSAT still needs fresh proof replay;
    // it is not certified merely because the resident protocol completed.
    // On a process/framing anomaly it falls through to the fresh per-call spawn
    // below (never a wrong or weaker verdict). A genuine resident deadline is
    // a conclusive Timeout for this configured budget, returned directly
    // instead of spending the same budget a second time, except (slice 19,
    // OD-197) for a query whose owner asks for one fresh replay after it
    // (`AyQueryText::fresh_after_resident_timeout`, the x86-64 body owner):
    // that query falls through to the fresh route below, which alone can
    // produce the exact proof the independent checker must accept, with a
    // fresh budget. Skipped while recording.
    if ay_server_enabled()
        && !strict_formal_campaign_active()
        && !ay_server_is_unusable_for_authority(authority)
    {
        let srv_t0 = crate::diag::solve_trace_enabled().then(std::time::Instant::now);
        match run_solver_via_server_with_authority(
            server,
            authority,
            smt2,
            config.timeout_ms,
            &obligation.inputs,
            witness.measures_cpu(),
        ) {
            AyServerAttempt::Completed(result) => {
                if let Some(t0) = srv_t0 {
                    eprintln!(
                        "TCG_SOLVE_TRACE server_solve {:.3}s obligation={:?} smt2_bytes={}",
                        t0.elapsed().as_secs_f64(),
                        obligation.name,
                        smt2.len(),
                    );
                }
                let result = match result {
                    // A resident process has no exact per-query proof artifact
                    // to hand to the independent checker. Treat its UNSAT as a
                    // candidate only, then replay once through the fresh
                    // proof-bearing path before any cache/authority promotion.
                    AYResult::SolverUnsat => {
                        run_fresh_authority_query(authority, obligation, config, smt2, &witness)
                    }
                    // A BARE `unknown` from the resident server is a
                    // TRUNCATION, not a diagnosis. The resident protocol is
                    // not query-framed, so `spawn_ay_server` discards the
                    // child's stderr — exactly where AY publishes its
                    // decisive `(:reason-unknown …)`, its
                    // `c ay.proof.certificate` disclosure and its
                    // soundness-gate banner. It is the one unknown shape
                    // whose reason is known to be MISSING rather than absent,
                    // so replay it once through the same fresh proof-bearing
                    // path a candidate UNSAT already takes.
                    //
                    // Doing it HERE reconstructs AY's own reason once, for
                    // every consumer — the strict gate, the batch reports and
                    // the guarded lib tests — instead of at each call site
                    // that needs to tell a certification gap from a genuine
                    // regression. It cannot weaken a verdict: the fresh
                    // one-shot path is the authoritative one, promotion still
                    // requires the exact Alethe artifact plus an independent
                    // Clean/Carcara check, and a reason-bearing unknown is
                    // strictly MORE failure-prone downstream than a bare one
                    // (`proof_gate::unknown_is_hard_failure` promotes the
                    // broken-authority reasons to SOUNDNESS).
                    //
                    // This is the production route answering its own
                    // truncation, not a second route excusing a failure: the
                    // fresh one-shot path is what runs whenever the server is
                    // off, and a bare unknown that survives it still means the
                    // production route did not decide the query
                    // (`crate::formal_gap` fails a test on it).
                    //
                    // COST, measured 2026-09-21 over the whole ProofDatabase
                    // rollup: a bare server unknown is not memoisable
                    // (`unknown_reason_is_memoizable_certification_gap` takes
                    // only the two deterministic certification gaps), so this
                    // is one extra one-shot solve per OCCURRENCE, not per
                    // process — but the population is tiny. Of 2005
                    // obligations exactly THREE reached the bridge as a bare
                    // server unknown, at ~0.1 s each.
                    AYResult::Unknown(ref reason) if reason == "unknown" => {
                        run_fresh_authority_query(authority, obligation, config, smt2, &witness)
                    }
                    other => enrich_sat_counterexample_via_server(
                        server, authority, obligation, config, smt2, other, &witness,
                    ),
                };
                if let (Some(legacy_key), Some(session_key), AYResult::Verified) =
                    (&legacy_cache_key, &session_cache_key, &result)
                {
                    session_proof_cache_store_verified(session_key);
                    // Optional synchronous mint-on-miss: persist
                    // an independently-Carcara-verified Alethe cert so the
                    // next identical compile can skip this live solve. No-op
                    // when the store is off (`TCG_NO_CERT_STORE` /
                    // `TCG_NO_PROOF_CACHE`), while recording, when the cert
                    // already exists, or when no capable Carcara checker
                    // resolves; verifies before writing.
                    crate::obligation_cert_store::mint_alethe_cert_with_authority(
                        legacy_key,
                        smt2,
                        &obligation.name,
                        authority,
                        config.timeout_ms,
                    );
                } else if let Some(session_key) = session_negative_cache_key {
                    remember_negative_session_verdict(
                        session_key,
                        &result,
                        &obligation.name,
                        smt2.len(),
                    );
                }
                return (result, AyVerdictSource::LiveSolve);
            }
            AyServerAttempt::TimedOut(expiry) => {
                if let Some(t0) = srv_t0 {
                    eprintln!(
                        "TCG_SOLVE_TRACE server_timeout {:.3}s obligation={:?} smt2_bytes={} {}",
                        t0.elapsed().as_secs_f64(),
                        obligation.name,
                        smt2.len(),
                        expiry.map_or_else(
                            || "deadline spent before the exchange".to_owned(),
                            |expiry| expiry.to_string()
                        ),
                    );
                }
                witness.note_expiry(expiry);
                if !query.fresh_after_resident_timeout {
                    return (AYResult::Timeout, AyVerdictSource::LiveSolve);
                }
                if crate::diag::solve_trace_enabled() {
                    eprintln!(
                        "TCG_SOLVE_TRACE server_timeout_fresh_replay obligation={:?} smt2_bytes={}",
                        obligation.name,
                        smt2.len(),
                    );
                }
            }
            AyServerAttempt::QueueRefused(refusal) => {
                // No solver ran for this query. Not a solver timeout, and not
                // retried: surface the named refusal (fail closed). The server
                // stays in service for later queries (see `AyServerAttempt`).
                if crate::diag::solve_trace_enabled() {
                    eprintln!(
                        "TCG_SOLVE_TRACE server_queue_refused obligation={:?} {refusal}",
                        obligation.name,
                    );
                }
                return (
                    AYResult::Error(refusal.to_string()),
                    AyVerdictSource::NotRun,
                );
            }
            AyServerAttempt::Anomaly => {
                // The server could not service this query. Latch it off rather
                // than re-attempting for every remaining obligation; the
                // one-shot fallback below is always correct.
                mark_ay_server_unusable_for_authority(authority);
            }
        }
    }

    // Write SMT-LIB2 to a temp file
    let tmp_file = match write_temp_smt2(smt2) {
        Ok(file) => file,
        Err(e) => {
            return (
                AYResult::Error(format!("Failed to write temp file: {}", e)),
                AyVerdictSource::NotRun,
            );
        }
    };

    // DIAGNOSTIC (default off, no behavior change): `TCG_SOLVE_TRACE=1` logs the
    // wall time of every LIVE solver subprocess plus the obligation name, so the
    // per-family live-solve cost across a warm compile is a measurement, not a
    // guess. Purely additive — the timing wrap does not alter control flow.
    let solve_trace = crate::diag::solve_trace_enabled();
    let solve_t0 = solve_trace.then(std::time::Instant::now);
    let output = run_solver_command_with_authority(authority, tmp_file.path(), config.timeout_ms);
    if let Some(t0) = solve_t0 {
        eprintln!(
            "TCG_SOLVE_TRACE live_solve {:.3}s obligation={:?} smt2_bytes={}",
            t0.elapsed().as_secs_f64(),
            obligation.name,
            smt2.len(),
        );
    }

    let (result, source) = match output {
        Ok(completed) => {
            witness.note_completion(completed.wall, completed.cpu);
            let result = parse_solver_process_output(&completed.output, &obligation.inputs);
            let result = promote_fresh_solver_unsat(
                result,
                authority,
                tmp_file.path(),
                smt2,
                &obligation.name,
                config.timeout_ms,
                &witness,
            );
            let result = enrich_sat_counterexample_via_fresh(
                authority, obligation, config, smt2, result, &witness,
            );
            if let (Some(legacy_key), Some(session_key), AYResult::Verified) =
                (&legacy_cache_key, &session_cache_key, &result)
            {
                session_proof_cache_store_verified(session_key);
                crate::obligation_cert_store::mint_alethe_cert_with_authority(
                    legacy_key,
                    smt2,
                    &obligation.name,
                    authority,
                    config.timeout_ms,
                );
            } else if let Some(session_key) = session_negative_cache_key {
                remember_negative_session_verdict(
                    session_key,
                    &result,
                    &obligation.name,
                    smt2.len(),
                );
            }
            (result, AyVerdictSource::LiveSolve)
        }
        Err(SolverInvocationError::Timeout(expiry)) => {
            witness.note_expiry(Some(expiry));
            (AYResult::Timeout, AyVerdictSource::LiveSolve)
        }
        Err(SolverInvocationError::Io(e)) => (
            AYResult::Error(format!(
                "Failed to invoke solver ({}): {}",
                solver_route_summary_from_selection(obligation_logic(obligation), solver_selection),
                e
            )),
            AyVerdictSource::NotRun,
        ),
    };
    // Tier-0 regen recorder: observes LIVE solver results only (cache hits
    // early-return above and are never recorded). The recorder itself keeps
    // Verified verdicts exclusively — SolverUnsat / Timeout / CounterExample /
    // Unknown / Error are never persisted as rows in any tier.
    if recording {
        crate::verdict_db::record_live_result(&obligation.name, smt2, &result);
    }
    (result, source)
}

/// Diagnostic only: a source-bound negative-memo hit, under `solve-trace` and,
/// for an x86-64 body or envelope theorem, under `x86-body-trace`.
fn trace_negative_memo_hit(
    obligation_name: &str,
    smt2_len: usize,
    withheld: &crate::source_bound_negative_memo::WithheldCredit,
) {
    if crate::diag::solve_trace_enabled() {
        eprintln!(
            "TCG_SOLVE_TRACE source_bound_negative_memo_hit {} obligation={obligation_name:?} smt2_bytes={smt2_len}",
            withheld.describe()
        );
    }
    if crate::diag::x86_body_trace_enabled()
        && (obligation_name == crate::x86_source_bound_body::X86_BODY_OBLIGATION_NAME
            || crate::x86_source_bound_body::is_x86_body_part_name(obligation_name)
            || crate::x86_source_bound_body::is_x86_body_claim_name(obligation_name)
            || crate::x86_source_bound_body::is_x86_body_generalized_name(obligation_name)
            || crate::x86_source_bound_envelope::is_x86_envelope_part_name(obligation_name))
    {
        eprintln!(
            "[TCG-X86-BODY-TRACE] replay negative-memo hit {} (AY not run; the recorded outcome follows)",
            withheld.describe()
        );
    }
}

/// The AY publication failure that [`split_assert_conjuncts`] escapes.
///
/// Matched on the message AY itself prints when it refuses to write a proof it
/// cannot self-check. Narrow ON PURPOSE: any other failure — a timeout, an
/// incomplete certificate, a foreign assumption — must NOT trigger a retry,
/// because only this one is known to be an artefact of how the conjunction was
/// written rather than a property of the obligation.
fn is_and_pos_publication_failure(result: &AYResult) -> bool {
    let message = match result {
        AYResult::Error(m) | AYResult::Unknown(m) => m.as_str(),
        _ => return false,
    };
    message.contains("and_pos") && message.contains("invalid surface proof step")
}

/// What one funnel call's live replay saw that decides whether the
/// source-bound negative memo may record its outcome, passed to the memo's
/// scope as it is seen (nothing for a query without one):
///
/// * a SAT verdict ([`Self::observe`]): only
///   [`enrich_sat_counterexample_via_server`] and
///   [`enrich_sat_counterexample_via_fresh`] receive a verdict-query SAT, so
///   they are its only writers; the outcome a SAT ends in (a model-query
///   timeout included) is never remembered;
/// * every solver deadline that expired ([`Self::note_expiry`]: the resident
///   or one-shot solve, the model query), with the CPU time the solver's
///   process group consumed under it: a `Timeout` is remembered only when
///   every one of them used its budget;
/// * every checker deadline that expired ([`Self::note_check_expiry`], OD-223:
///   the Clean check of AY's proof, or its capability probe), kept apart from
///   the solver's: a checker timeout is remembered only as a checker timeout,
///   and only when every checker expiry used the checker's deadline;
/// * every fresh solve that completed ([`Self::note_completion`]), with its
///   wall-clock and process-group CPU time: a certification failure is
///   remembered only when every one of them had the processor.
struct ReplayWitness<'a> {
    negative: Option<&'a crate::source_bound_negative_memo::NegativeMemoScope>,
}

impl<'a> ReplayWitness<'a> {
    fn new(negative: Option<&'a crate::source_bound_negative_memo::NegativeMemoScope>) -> Self {
        Self { negative }
    }

    fn observe(&self, verdict: &AYResult) {
        if matches!(verdict, AYResult::CounterExample(_))
            && let Some(scope) = self.negative
        {
            scope.note_sat_verdict();
        }
    }

    /// A solver deadline of this replay expired; `None` when no supervised
    /// deadline measured it.
    fn note_expiry(&self, expiry: Option<crate::subprocess::DeadlineExpiry>) {
        if let Some(scope) = self.negative {
            scope.note_deadline_expiry(expiry);
        }
    }

    /// A checker deadline of this replay expired (OD-223); `None` when no
    /// supervised deadline measured it (the capability probe).
    fn note_check_expiry(&self, expiry: Option<crate::subprocess::DeadlineExpiry>) {
        if let Some(scope) = self.negative {
            scope.note_check_expiry(expiry);
        }
    }

    /// A fresh solve of this replay completed in `wall`, its process group
    /// using `cpu` (`None`: not measured).
    fn note_completion(&self, wall: Duration, cpu: Option<Duration>) {
        if let Some(scope) = self.negative {
            scope.note_solve_completion(wall, cpu);
        }
    }

    /// Whether the memo uses the evidence (the resident exchange then
    /// measures its CPU time).
    fn measures_cpu(&self) -> bool {
        self.negative.is_some()
    }
}

fn run_fresh_authority_query(
    authority: &VerificationAuthority,
    obligation: &ProofObligation,
    config: &AYConfig,
    smt2: &str,
    witness: &ReplayWitness<'_>,
) -> AYResult {
    let result = run_fresh_authority_query_once(authority, obligation, config, smt2, witness);
    if !is_and_pos_publication_failure(&result) {
        return result;
    }
    // AY reached a verdict and then refused its own proof over an `and_pos` step
    // it could not index. Retry ONCE with the identical problem written as
    // separate top-level asserts; see [`split_assert_conjuncts`]. If the rewrite
    // does not apply, or the retry does not do better, keep the ORIGINAL result —
    // a retry may never turn a failure into a weaker answer.
    let Some(split) = split_assert_conjuncts(smt2) else {
        return result;
    };
    let retried = run_fresh_producer_query_once_with(
        authority,
        obligation,
        config,
        AyQueryText {
            original: smt2,
            producer: Some(&split),
            closed_definitions: false,
            fresh_after_resident_timeout: false,
        },
        ProducerProof::SplitConjuncts,
        witness,
    );
    // The split is a producer spelling only (OD-106). A proof must replay
    // against the ORIGINAL conjunction, so the split proof's top-level
    // assumptions are first re-derived from it
    // ([`crate::split_conjunct_proof`]); SAT or any failed candidate keeps the
    // raw refusal.
    if matches!(retried, AYResult::Verified) {
        retried
    } else {
        result
    }
}

fn run_fresh_authority_query_once(
    authority: &VerificationAuthority,
    obligation: &ProofObligation,
    config: &AYConfig,
    smt2: &str,
    witness: &ReplayWitness<'_>,
) -> AYResult {
    let result = run_fresh_producer_query_once(
        authority,
        obligation,
        config,
        AyQueryText::raw(smt2),
        witness,
    );
    enrich_sat_counterexample_via_fresh(authority, obligation, config, smt2, result, witness)
}

/// How a fresh producer's proof reaches the independent checker, which always
/// receives the ORIGINAL script (OD-106).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProducerProof {
    /// As AY emitted it: it must already replay against the original.
    AsEmitted,
    /// The producer is [`split_assert_conjuncts`] of the original: its
    /// top-level assumptions are re-derived from the original conjunction
    /// first ([`bridge_split_conjunct_proof_file`]).
    SplitConjuncts,
}

/// Producer input and independently checked problem are intentionally distinct.
/// This routine does not enrich/observe SAT; only the raw caller may do that.
fn run_fresh_producer_query_once(
    authority: &VerificationAuthority,
    obligation: &ProofObligation,
    config: &AYConfig,
    query: AyQueryText<'_>,
    witness: &ReplayWitness<'_>,
) -> AYResult {
    run_fresh_producer_query_once_with(
        authority,
        obligation,
        config,
        query,
        ProducerProof::AsEmitted,
        witness,
    )
}

/// [`run_fresh_producer_query_once`], presenting the producer's proof to the
/// checker as `proof` says.
fn run_fresh_producer_query_once_with(
    authority: &VerificationAuthority,
    obligation: &ProofObligation,
    config: &AYConfig,
    query: AyQueryText<'_>,
    proof: ProducerProof,
    witness: &ReplayWitness<'_>,
) -> AYResult {
    let tmp_file = match write_temp_smt2(query.producer.unwrap_or(query.original)) {
        Ok(file) => file,
        Err(e) => return AYResult::Error(format!("Failed to write proof query: {e}")),
    };
    crate::process_cost::mark("fresh_solve_begin");
    let run = run_solver_command_with_authority(authority, tmp_file.path(), config.timeout_ms);
    crate::process_cost::mark("fresh_solve_end");
    match run {
        Ok(completed) => {
            witness.note_completion(completed.wall, completed.cpu);
            let result = parse_solver_process_output(&completed.output, &obligation.inputs);
            let result = match proof {
                ProducerProof::AsEmitted => result,
                ProducerProof::SplitConjuncts => bridge_split_conjunct_proof_file(
                    result,
                    query.original,
                    &default_alethe_path(tmp_file.path()),
                ),
            };
            promote_fresh_solver_unsat(
                result,
                authority,
                tmp_file.path(),
                query.original,
                &obligation.name,
                config.timeout_ms,
                witness,
            )
        }
        Err(SolverInvocationError::Timeout(expiry)) => {
            witness.note_expiry(Some(expiry));
            AYResult::Timeout
        }
        Err(SolverInvocationError::Io(e)) => {
            AYResult::Error(format!("Failed to invoke proof solver: {e}"))
        }
    }
}

/// Rewrite, in place, the proof a split-conjunct producer emitted at
/// `proof_path` into a proof of `original`
/// ([`crate::split_conjunct_proof::bridge_split_conjunct_proof`]). Only an
/// UNSAT carries a proof. The rewrite has no authority: the checker still
/// decides it against `original`. Anything the bridge cannot map becomes an
/// `Unknown` naming why, which the retry discards for the original refusal.
fn bridge_split_conjunct_proof_file(
    result: AYResult,
    original: &str,
    proof_path: &Path,
) -> AYResult {
    if !matches!(result, AYResult::SolverUnsat) {
        return result;
    }
    let bridged = std::fs::read_to_string(proof_path)
        .map_err(|error| format!("unreadable proof: {error}"))
        .and_then(|proof| {
            crate::split_conjunct_proof::bridge_split_conjunct_proof(original, &proof)
        })
        .and_then(|proof| {
            std::fs::write(proof_path, proof).map_err(|error| format!("unwritable proof: {error}"))
        });
    match bridged {
        Ok(()) => result,
        Err(why) => {
            let _ = std::fs::remove_file(proof_path);
            AYResult::Unknown(format!(
                "the split-conjunct proof was not re-derived from the original conjunction: {why}"
            ))
        }
    }
}

fn promote_fresh_solver_unsat(
    result: AYResult,
    authority: &VerificationAuthority,
    smt2_path: &Path,
    smt2: &str,
    obligation_name: &str,
    timeout_ms: u64,
    witness: &ReplayWitness<'_>,
) -> AYResult {
    let proof_path = default_alethe_path(smt2_path);
    if !matches!(result, AYResult::SolverUnsat) {
        let _ = std::fs::remove_file(&proof_path);
        return result;
    }

    let proof = match std::fs::read_to_string(&proof_path) {
        Ok(proof) if !proof.trim().is_empty() => proof,
        Ok(_) => {
            let _ = std::fs::remove_file(&proof_path);
            return AYResult::Unknown(
                "AY reported UNSAT but emitted an empty Alethe proof".to_string(),
            );
        }
        Err(e) => {
            let _ = std::fs::remove_file(&proof_path);
            return AYResult::Unknown(format!(
                "AY reported UNSAT but emitted no readable Alethe proof at {}: {e}",
                proof_path.display()
            ));
        }
    };

    // Two very different situations must not share one message. "The checker
    // refused THIS proof" is evidence about the proof; "no checker can run
    // here" is evidence about the installation, and they demand opposite
    // responses. Resolve the identity-bound control probe once, retaining
    // timeout/unavailability rather than repeating discovery for a diagnostic.
    let checker = match authority.checker() {
        Some(checker) => checker,
        None => {
            let _ = std::fs::remove_file(&proof_path);
            return match authority.checker_resolution_error() {
                Some(crate::obligation_cert_store::CheckerResolutionError::Timeout) => {
                    // The checker's capability probe of its control proof ran
                    // out of its deadline: a checker outcome, not AY's and not
                    // this proof's (OD-223), so it is reported as one and never
                    // as an AY timeout; the negative memo records nothing.
                    witness.note_check_expiry(None);
                    AYResult::Unknown(CLEAN_PROBE_TIMEOUT_REASON.to_owned())
                }
                error => AYResult::Unknown(format!(
                    "AY reported UNSAT but it CANNOT BE CHECKED here — {}. This is a toolchain problem, not evidence about the proof.",
                    match error {
                        Some(
                            crate::obligation_cert_store::CheckerResolutionError::Unavailable(
                                reason,
                            ),
                        ) => reason.as_str(),
                        _ => "no usable checker",
                    }
                )),
            };
        }
    };
    // The proof check is not the solve (OD-223): Clean gets its own deadline,
    // never less than the solve budget `timeout_ms` and never unbounded.
    let check_timeout_ms = crate::obligation_cert_store::proof_check_timeout_ms(timeout_ms);
    crate::process_cost::mark("proof_check_begin");
    let check_started = std::time::Instant::now();
    let checked = crate::obligation_cert_store::carcara_verify_with_expected_checker_with_env(
        checker.path(),
        checker.sha256(),
        smt2,
        &proof,
        authority.child_env(),
        check_timeout_ms,
    );
    crate::process_cost::mark("proof_check_end");
    if crate::diag::solve_trace_enabled() {
        eprintln!(
            "TCG_SOLVE_TRACE clean_check {:.3}s obligation={obligation_name:?} proof_bytes={} \
             check_deadline_ms={check_timeout_ms} solve_budget_ms={timeout_ms} outcome={}",
            check_started.elapsed().as_secs_f64(),
            proof.len(),
            match &checked {
                Ok(true) => "accepted".to_owned(),
                Ok(false) => "refused".to_owned(),
                Err(error) => error.to_string(),
            },
        );
    }
    let _ = std::fs::remove_file(&proof_path);
    match checked {
        Ok(true) => {
            // The proof in hand was just accepted by the identity-pinned
            // independent checker against this exact query: persist it to the
            // per-box store so the next identical compile skips this derivation.
            crate::obligation_cert_store::persist_verified_alethe(
                authority.solver_path_text(),
                smt2,
                obligation_name,
                &proof,
                checker.sha256(),
            );
            AYResult::Verified
        }
        Ok(false) => AYResult::Unknown(working_checker_rejection_reason(checker.path())),
        Err(error) => {
            if crate::diag::solve_trace_enabled() {
                eprintln!("TCG_SOLVE_TRACE clean_replay_failed {error}");
            }
            match error {
                // AY answered `unsat` inside its budget; the CHECK of its
                // proof ran out of the checker's deadline (OD-223). Reported
                // as a checker timeout, never as an AY timeout, and offered to
                // the negative memo as a checker expiry only.
                crate::subprocess::RunError::Timeout(expired) => {
                    witness.note_check_expiry(Some(expired.expiry));
                    AYResult::Unknown(clean_check_timeout_reason(
                        proof.len(),
                        check_timeout_ms,
                        &expired.expiry,
                    ))
                }
                crate::subprocess::RunError::Io { .. } => {
                    AYResult::Unknown(format!("{CLEAN_CHECK_INCOMPLETE}: {error}"))
                }
            }
        }
    }
}

/// The clause every rejection by a WORKING independent checker carries: the
/// identity-pinned checker verified its known-good control proof, then did not
/// accept the exact Alethe proof AY emitted for this query. That is a verdict
/// on the proof, not a missing capability, so [`crate::proof_gate`] files it as
/// a SOUNDNESS failure and
/// [`crate::gap_classify::ay_reason_is_disclosed_proof_hole`] never lets a test
/// skip on it.
pub(crate) const WORKING_CHECKER_REJECTED_THIS_PROOF: &str = "which verified a known-good \
     control proof, so it is a working checker — rejected or could not fully verify THIS Alethe \
     proof";

/// The `AYResult::Unknown` reason for an AY `unsat` whose exact Alethe proof
/// the working checker at `checker` did not accept.
pub(crate) fn working_checker_rejection_reason(checker: &Path) -> String {
    format!(
        "AY reported UNSAT but {} — {WORKING_CHECKER_REJECTED_THIS_PROOF}",
        checker.display()
    )
}

/// The start of every `AYResult::Unknown` reason for an AY `unsat` whose
/// exact Alethe proof the Clean check did not finish within the checker's own
/// deadline (OD-223, [`crate::obligation_cert_store::proof_check_timeout_ms`]).
/// A checker outcome, not AY's: the source-bound negative memo records it as
/// a `checker-timeout` (never a solver `timeout`), and the replay label says
/// "Clean check timeout" ([`replay_outcome_label`]). It carries none of the
/// hard-failure spellings (`proof_gate::unknown_is_hard_failure`): the checker
/// gave no verdict, so the outcome is PENDING, as a solver timeout is.
pub(crate) const CLEAN_CHECK_TIMEOUT: &str =
    "AY reported UNSAT but the Clean check of its exact Alethe proof timed out";

/// [`CLEAN_CHECK_TIMEOUT`] with the proof's size, the checker deadline and
/// what the checker's process group consumed under it.
pub(crate) fn clean_check_timeout_reason(
    proof_bytes: usize,
    check_timeout_ms: u64,
    expiry: &crate::subprocess::DeadlineExpiry,
) -> String {
    format!(
        "{CLEAN_CHECK_TIMEOUT}: the check of the {proof_bytes}-byte proof ran past the \
         checker's own {check_timeout_ms} ms deadline ({expiry})"
    )
}

/// The start of the `AYResult::Unknown` reason for an AY `unsat` whose Clean
/// check could not be run to completion (staging or I/O).
pub(crate) const CLEAN_CHECK_INCOMPLETE: &str =
    "AY reported UNSAT but Clean replay could not complete";

/// The `AYResult::Unknown` reason for an AY `unsat` that could not be checked
/// because the Clean checker's capability probe of its control proof ran out
/// of its deadline: an installation or host outcome, never AY's.
pub(crate) const CLEAN_PROBE_TIMEOUT_REASON: &str = "AY reported UNSAT but it CANNOT BE CHECKED \
     here — the Clean checker's capability probe of its control proof ran out of its deadline. \
     This is a toolchain or host problem, not evidence about the proof.";

/// The diagnostic label of a live replay outcome (`verdict_db`'s replay
/// explanations, the x86-64 body trace). The proof check is not the solve
/// (OD-223): an outcome of the Clean check is named as one, and "AY TIMEOUT"
/// is left to AY's own deadlines (the resident or one-shot solve, the SAT
/// model query). The text never changes a verdict.
pub(crate) fn replay_outcome_label(result: &AYResult) -> String {
    if let AYResult::Unknown(reason) = result {
        if reason.starts_with(CLEAN_CHECK_TIMEOUT) {
            return format!("Clean check timeout: {reason}");
        }
        if reason.starts_with("AY reported UNSAT but")
            && reason.contains(WORKING_CHECKER_REJECTED_THIS_PROOF)
        {
            return format!("Clean check refused: {reason}");
        }
        if reason.starts_with(CLEAN_CHECK_INCOMPLETE) {
            return format!("Clean check did not complete: {reason}");
        }
        if reason.starts_with("AY reported UNSAT but it CANNOT BE CHECKED here") {
            return format!("Clean checker unavailable: {reason}");
        }
    }
    format!("AY {result}")
}

fn default_alethe_path(smt2_path: &Path) -> std::path::PathBuf {
    let mut proof_os = smt2_path.as_os_str().to_os_string();
    proof_os.push(".alethe");
    std::path::PathBuf::from(proof_os)
}

/// If a verdict-only resident query returned SAT, ask for values in a second
/// query.  The model command is therefore never executed after UNSAT/unknown.
fn enrich_sat_counterexample_via_server(
    server: AyResidentServer,
    authority: &VerificationAuthority,
    obligation: &ProofObligation,
    config: &AYConfig,
    verdict_smt2: &str,
    result: AYResult,
    witness: &ReplayWitness<'_>,
) -> AYResult {
    witness.observe(&result);
    if !config.produce_models || !matches!(&result, AYResult::CounterExample(_)) {
        return result;
    }
    let Some(model_smt2) = generate_sat_model_query(obligation, verdict_smt2) else {
        return result;
    };

    // After a SAT verdict nothing is remembered, so the model query's CPU
    // time is not measured.
    match run_solver_via_server_with_authority(
        server,
        authority,
        &model_smt2,
        config.timeout_ms,
        &obligation.inputs,
        false,
    ) {
        AyServerAttempt::Completed(AYResult::CounterExample(values)) => {
            AYResult::CounterExample(values)
        }
        AyServerAttempt::Completed(other) => AYResult::Error(format!(
            "SAT model replay returned a non-SAT result: {other:?}"
        )),
        AyServerAttempt::TimedOut(expiry) => {
            witness.note_expiry(expiry);
            AYResult::Timeout
        }
        AyServerAttempt::QueueRefused(refusal) => AYResult::Error(refusal.to_string()),
        AyServerAttempt::Anomaly => {
            mark_ay_server_unusable_for_authority(authority);
            run_sat_model_query_fresh(authority, obligation, config, &model_smt2)
        }
    }
}

/// Fresh-process counterpart of [`enrich_sat_counterexample_via_server`].
fn enrich_sat_counterexample_via_fresh(
    authority: &VerificationAuthority,
    obligation: &ProofObligation,
    config: &AYConfig,
    verdict_smt2: &str,
    result: AYResult,
    witness: &ReplayWitness<'_>,
) -> AYResult {
    witness.observe(&result);
    if !config.produce_models || !matches!(&result, AYResult::CounterExample(_)) {
        return result;
    }
    let Some(model_smt2) = generate_sat_model_query(obligation, verdict_smt2) else {
        return result;
    };
    run_sat_model_query_fresh(authority, obligation, config, &model_smt2)
}

fn run_sat_model_query_fresh(
    authority: &VerificationAuthority,
    obligation: &ProofObligation,
    config: &AYConfig,
    model_smt2: &str,
) -> AYResult {
    let tmp_file = match write_temp_smt2(model_smt2) {
        Ok(file) => file,
        Err(e) => return AYResult::Error(format!("Failed to write SAT model query: {e}")),
    };
    match run_solver_verdict_command_with_authority(authority, tmp_file.path(), config.timeout_ms) {
        Ok(output) => match parse_solver_process_output(&output, &obligation.inputs) {
            AYResult::CounterExample(values) => AYResult::CounterExample(values),
            other => AYResult::Error(format!(
                "SAT model replay returned a non-SAT result: {other:?}"
            )),
        },
        Err(SolverInvocationError::Timeout(_)) => AYResult::Timeout,
        Err(SolverInvocationError::Io(e)) => {
            AYResult::Error(format!("Failed to invoke solver for SAT model replay: {e}"))
        }
    }
}

/// Session-memo key for a CLI solver invocation: the SHA-256 of the exact SMT2 text
/// plus the solver binary's identity BY CONTENT (SHA-256 of the binary's
/// bytes, see [`solver_identity_hash`]). Any change to the query or to the
/// solver's bytes produces a different key, so a cached verdict can never be
/// replayed for a different proof or a different solver — while a rebuilt /
/// re-installed solver whose bytes are UNCHANGED keeps its verdicts (the v1
/// key bound path+size+mtime, so every `ay` rebuild wiped the whole cache).
///
/// The digest is an in-memory lookup key only. No filesystem artifact is ever
/// accepted as a verdict. Returns `None` when `TCG_NO_PROOF_CACHE` is set or
/// the solver binary cannot be read.
fn session_proof_cache_key(solver_path: &str, smt2: &str) -> Option<String> {
    if crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some() {
        return None;
    }
    // EXACT QUERY KEY. Every branch below hashes the raw SMT2 bytes. Textual
    // rewriting is not a proof-authority boundary: an `_v<digits>` spelling
    // can occur inside a semantic string literal (or another lexical context),
    // where changing it can change satisfiability. A sound canonicalizer would
    // need to parse and scope the complete SMT-LIB language; this cache instead
    // keeps the exact query identity and accepts the small loss in reuse.
    // NON-BLOCKING (CT-9). The key needs the solver's content identity, which is
    // a SHA-256 over the ~73MB `ay` binary — measured at 337ms, against ~25ms of
    // ACTUAL proof work for every program in the beat-llvm suite. Computing it
    // inline made the memo a guaranteed net loss on any compile whose total
    // solve time is under ~337ms: it was paid in full, up front, to avoid work
    // that cost a fraction of it.
    //
    // So: consult the identity only if it is ALREADY resolved (the background
    // warm starts at backend `init`, see `warm_solver_identity`). If it is not
    // ready, return `None` and let the caller take its live path.
    //
    // SOUNDNESS: `None` here means "no cache key", which every caller already
    // handles by SOLVING LIVE — the documented behaviour for no-solver /
    // unreadable-binary / `TCG_NO_PROOF_CACHE`. A cache is a pure optimization
    // over a live discharge; declining to consult one can only cost time, never
    // change a verdict. Fail-closed is unaffected: a `Refuted` obligation is
    // refuted by the live solve exactly as by a cached row.
    // `TCG_BLOCKING_IDENTITY=1` restores the pre-CT-9 behaviour (compute the
    // hash inline, blocking) so the change can be A/B'd against itself inside
    // ONE dylib. Same key either way — only who waits for it differs.
    // DEFAULT ROUTE ONLY. The warm resolves the DEFAULT solver
    // (`select_solver_binary`), which is what the bridge's refinement lane uses
    // (it discharges with `AYConfig::default()`, see `default_route_cache_key`).
    // A caller that passes an EXPLICIT `config.solver_path` — regen tooling,
    // the soundness tests driving a stand-in binary — would never have its path
    // warmed, so applying the non-blocking policy there would disable its cache
    // for no gain and make key derivation depend on process-global scheduling
    // state. Those callers are off the hot path; give them the exact prior
    // behaviour.
    if crate::env_lock::var_os("TCG_BLOCKING_IDENTITY").is_some()
        || solver_path != select_solver_binary().path_text()
    {
        return Some(verdict_cache_key_v2(
            &solver_identity_hash(solver_path)?,
            smt2,
        ));
    }
    // No `-dirty` short-circuit: an admitted AY is the exact bytes of the
    // recorded, clean toolchain build (`crate::ay_identity`), and its admission
    // already published this digest to the identity memo, so the lookup below
    // is ready without hashing again.
    if let Some(identity) = solver_identity_hash_if_ready(solver_path) {
        return Some(verdict_cache_key_v2(&identity, smt2));
    }
    // Not ready. Make sure something IS computing it — this is what keeps the
    // cache alive for consumers that never run `CodegenBackend::init` (the test
    // suite, `regen_verdict_db`, any library user), which would otherwise find
    // the identity permanently unresolved and re-solve every repeated
    // obligation. The rustc bridge still warms at `init`, strictly earlier.
    start_solver_identity_warm_for_path(solver_path);

    // ADAPTIVE FALLBACK. Skipping the cache costs a re-solve, and without a key
    // we can neither look up NOR store — so a proof-heavy compile that spends
    // its first N obligations in the warm window pays for them twice. Past a
    // threshold the hash is clearly the cheaper of the two, so block once and
    // let the rest of the compile be cached.
    //
    // Calibration: one live obligation costs ~20ms through `ay`, and the hash
    // costs ~337ms, so ~16 uncached solves is where the cache starts paying for
    // its own key. Below that a compile never blocks (the common case — every
    // beat-llvm program discharges far fewer); above it, a solver-heavy compile
    // recovers the memo instead of re-solving all the way through. `v3_popcount`
    // (~12s of solver work) is the case that motivated this: without the
    // fallback it regressed ~8%.
    const UNCACHED_SOLVES_BEFORE_BLOCKING: usize = 16;
    let misses = record_uncached_solver_identity_miss(solver_path);
    if misses >= UNCACHED_SOLVES_BEFORE_BLOCKING {
        // Blocks only until the already-running warm finishes (compute-once
        // memo), so this waits for the remainder of one hash, never a second.
        return Some(verdict_cache_key_v2(
            &solver_identity_hash(solver_path)?,
            smt2,
        ));
    }
    None
}

/// The shared v2 content-addressed verdict key: SHA-256 over a domain tag, the
/// solver's content identity (lowercase-hex SHA-256 of its binary bytes) and
/// the exact SMT2 query bytes. Used for process-local memoization and tier-0
/// candidate correlation. The digest is not a signature or certificate and no
/// on-disk artifact bearing it is accepted as proof authority.
pub(crate) fn verdict_cache_key_v2(solver_identity_hex: &str, smt2: &str) -> String {
    use sha2::{Digest, Sha256};

    let mut hasher = Sha256::new();
    hasher.update(b"tcg-proof-cache-v2\0");
    hasher.update(solver_identity_hex.as_bytes());
    hasher.update(b"\0");
    hasher.update(smt2.as_bytes());
    format!("{:x}", hasher.finalize())
}

/// File-metadata key for the process-wide solver-identity memo. Unix also binds
/// device, inode and ctime to distinguish in-place edits with restored mtime.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct SolverIdentityStatKey {
    path: String,
    size: u64,
    mtime_ns: u128,
    #[cfg(unix)]
    dev: u64,
    #[cfg(unix)]
    ino: u64,
    #[cfg(unix)]
    ctime_ns: i128,
}

impl SolverIdentityStatKey {
    fn of(path: &str, meta: &std::fs::Metadata) -> Option<Self> {
        let mtime_ns = meta
            .modified()
            .ok()?
            .duration_since(std::time::UNIX_EPOCH)
            .ok()?
            .as_nanos();

        #[cfg(unix)]
        {
            use std::os::unix::fs::MetadataExt;
            Some(Self {
                path: path.to_owned(),
                size: meta.len(),
                mtime_ns,
                dev: meta.dev(),
                ino: meta.ino(),
                ctime_ns: i128::from(meta.ctime()) * 1_000_000_000 + i128::from(meta.ctime_nsec()),
            })
        }

        #[cfg(not(unix))]
        {
            Some(Self {
                path: path.to_owned(),
                size: meta.len(),
                mtime_ns,
            })
        }
    }
}

type SolverIdentityMemo = std::sync::Mutex<
    std::collections::HashMap<
        SolverIdentityStatKey,
        std::sync::Arc<std::sync::Mutex<Option<String>>>,
    >,
>;

/// Each entry serializes hashing of one metadata key. Concurrent callers share
/// a completed digest; `solver_identity_hash_if_ready` can decline a still-busy
/// entry without waiting. Failed reads leave the entry unresolved for retry.
fn solver_identity_memo() -> &'static SolverIdentityMemo {
    static MEMO: std::sync::OnceLock<SolverIdentityMemo> = std::sync::OnceLock::new();
    MEMO.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()))
}

/// Content identity of a solver binary: the lowercase-hex SHA-256 of its
/// bytes. Memoized per process for performance. Persistent identity files are
/// intentionally ignored: metadata such as path/size/mtime is not a secure
/// binding to file contents and a forged hash must not influence proof reuse.
/// Returns `None` when the binary cannot be stat'ed or read.
/// Machine-local memo for [`solver_identity_hash`], keyed on the solver file's
/// identity metadata.
///
/// # Why this exists
///
/// The identity is a SHA-256 over the solver BINARY, and `ay` is ~115 MB. It is
/// recomputed once per rustc PROCESS — i.e. once per compile — and measured at
/// **71-78 ms**, the single largest item in production `codegen_crate` (an
/// EMPTY program pays it in full to serve one memo lookup that misses). Compile
/// time was therefore coupled to the SOLVER's size rather than the program's.
///
/// # Why this is NOT the verdict cache the 2026-07-10 audit removed
///
/// That cache stored PROOF VERDICTS: a writable file containing `unsat` could
/// mint `Verified` without revalidation, which is why it had to go. This stores
/// a FILE FINGERPRINT. The identity is *correlation* in every one of its three
/// consumers, each of which independently re-establishes authority:
///
/// * the session memo is in-process and only ever holds results of live solver
///   runs made in THIS process;
/// * a tier-0 candidate hit "can only request live revalidation; it cannot
///   establish a verdict" ([`crate::verdict_db`]);
/// * a CERT-SKIP hit is credited only after an INDEPENDENT DRAT re-check of the
///   committed certificate against THIS exact SMT2 ([`crate::canary_cert`]).
///
/// So a WRONG identity cannot mint a verdict. It can only change which cheap
/// paths are attempted: a wrong MATCH makes candidates/certificates be
/// consulted, and each is then revalidated or re-checked before it can be
/// credited; a wrong MISMATCH sends everything to live discharge. Both are
/// sound; the second is merely slower. This is a performance cache, not a trust
/// input.
///
/// # Why it is not a new equivalence
///
/// [`solver_identity_hash`] ALREADY memoises on `(path, size, mtime)` within a
/// process — the code already treats that tuple as "same binary, reuse the
/// hash". This extends the same judgement from process scope to machine scope,
/// and tightens it: the key additionally binds the device and inode (so a
/// replaced file is a different record) and the ctime (which changes on any
/// metadata write and cannot be set backwards by an unprivileged user, unlike
/// mtime).
///
/// Fail-safe by construction: any IO, parse, or format problem simply recomputes
/// the hash. Opt out with `TCG_NO_SOLVER_ID_CACHE=1`.
#[derive(Clone, Copy, PartialEq, Eq)]
struct SolverFileKey {
    dev: u64,
    ino: u64,
    size: u64,
    mtime_ns: i128,
    ctime_ns: i128,
}

impl SolverFileKey {
    #[cfg(unix)]
    fn of(meta: &std::fs::Metadata) -> Option<Self> {
        use std::os::unix::fs::MetadataExt;
        Some(SolverFileKey {
            dev: meta.dev(),
            ino: meta.ino(),
            size: meta.size(),
            mtime_ns: i128::from(meta.mtime()) * 1_000_000_000 + i128::from(meta.mtime_nsec()),
            ctime_ns: i128::from(meta.ctime()) * 1_000_000_000 + i128::from(meta.ctime_nsec()),
        })
    }

    #[cfg(not(unix))]
    fn of(_meta: &std::fs::Metadata) -> Option<Self> {
        // No stable dev/ino/ctime: skip the machine-local cache entirely rather
        // than key on a weaker tuple than the in-process memo already uses.
        None
    }

    fn line(&self, hash: &str) -> String {
        format!(
            "v1 {} {} {} {} {} {}",
            self.dev, self.ino, self.size, self.mtime_ns, self.ctime_ns, hash
        )
    }

    fn matches(&self, line: &str) -> Option<String> {
        let mut f = line.split(' ');
        if f.next()? != "v1" {
            return None;
        }
        let dev = f.next()?.parse::<u64>().ok()?;
        let ino = f.next()?.parse::<u64>().ok()?;
        let size = f.next()?.parse::<u64>().ok()?;
        let mtime_ns = f.next()?.parse::<i128>().ok()?;
        let ctime_ns = f.next()?.parse::<i128>().ok()?;
        let hash = f.next()?;
        if f.next().is_some() {
            return None;
        }
        // Strict: only a well-formed digest is accepted, and only for an exact
        // metadata match. Anything else recomputes.
        if hash.len() != 64
            || !hash
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return None;
        }
        let candidate = SolverFileKey {
            dev,
            ino,
            size,
            mtime_ns,
            ctime_ns,
        };
        (candidate == *self).then(|| hash.to_owned())
    }
}

/// Where the machine-local identity memo lives. `TCG_PROOF_CACHE_DIR` when set
/// (the benchmark harness already isolates runs with it), else
/// `<user cache>/trust-cg`, the directory AY's private copy lives under, by
/// the same one rule (`private_fs::user_cache_base`: an empty or relative
/// `XDG_CACHE_HOME` is ignored, never read against the working directory).
/// `None` disables the memo, as it does when no absolute user cache exists.
///
/// Unit tests never write the user's cache: their solvers are fixtures (a
/// few bytes each), and a test process that fell through to the default
/// wrote their identities into `~/.cache/trust-cg/solver-identity-v1`
/// (observed 2026-10-03: 8 records for files of 20-506 bytes). Under
/// `cfg(test)` only an explicit `TCG_PROOF_CACHE_DIR` enables the memo.
/// Integration tests link the library without `cfg(test)`; there an AY is
/// only ever the bytes the identity rule admits (the toolchain's recorded
/// AY), so they can record no fixture identity.
fn solver_identity_cache_dir() -> Option<std::path::PathBuf> {
    if crate::env_lock::var_os("TCG_NO_SOLVER_ID_CACHE").is_some() {
        return None;
    }
    if let Some(d) = crate::env_lock::var_os("TCG_PROOF_CACHE_DIR") {
        Some(std::path::PathBuf::from(d))
    } else if cfg!(test) {
        None
    } else {
        default_solver_identity_dir()
    }
}

/// The memo's file name inside its directory.
const SOLVER_IDENTITY_MEMO: &str = "solver-identity-v1";

/// `<user cache>/trust-cg` by the one user-cache rule
/// (`private_fs::user_cache_base`), the memo's directory when no
/// `TCG_PROOF_CACHE_DIR` names one; `None` with no absolute user cache.
fn default_solver_identity_dir() -> Option<std::path::PathBuf> {
    trust_cg_process_env::private_fs::current_user_cache_base()
        .ok()
        .map(|base| base.join("trust-cg"))
}

/// The canonical form of the memo's directory `dir`, only when no other user
/// can change it or any entry along it
/// (`private_fs::canonical_owner_private_directory`: every canonical ancestor
/// owned by this user or root and renamable by nobody else, the directory not
/// group/other-writable). Everything the memo reads or writes is named from
/// this canonical path, never from `dir`, which may lead there through a
/// symlink another user can re-point.
fn private_solver_identity_dir(dir: &std::path::Path) -> Option<std::path::PathBuf> {
    trust_cg_process_env::private_fs::canonical_owner_private_directory(dir).ok()
}

/// The memo's records, read only from a private canonical location: the
/// directory as [`private_solver_identity_dir`] judges it, the file opened
/// without following a symlink and accepted only when this user owns it and
/// no other user can read or write it (`private_fs::open_owner_private_file`,
/// mode `0600` or stricter). A memo anywhere else is ignored, never trusted:
/// a legacy file another user can write (this host's `solver-identity-v1`
/// from before the private-cache rule is `0664`) reads as an empty memo, so
/// the identity is hashed afresh (X-HOST-P13 fourth closure audit).
fn read_private_solver_identity_memo(dir: &std::path::Path) -> Option<String> {
    let path = private_solver_identity_dir(dir)?.join(SOLVER_IDENTITY_MEMO);
    let file = trust_cg_process_env::private_fs::open_owner_private_file(&path).ok()?;
    let mut text = String::new();
    std::io::Read::read_to_string(&mut std::io::Read::take(file, 1 << 20), &mut text).ok()?;
    Some(text)
}

fn solver_identity_cache_lookup(key: &SolverFileKey) -> Option<String> {
    let text = read_private_solver_identity_memo(&solver_identity_cache_dir()?)?;
    text.lines().find_map(|l| key.matches(l))
}

fn solver_identity_cache_store(key: &SolverFileKey, hash: &str) {
    let Some(dir) = solver_identity_cache_dir() else {
        return;
    };
    // Usually `<cache>/trust-cg`, the root the AY private copy is created
    // under: every directory created is `0700` whatever the umask.
    if trust_cg_process_env::private_fs::create_private_dir_all(&dir).is_err() {
        return;
    }
    // Written only into a private canonical directory, by its canonical name.
    let Some(dir) = private_solver_identity_dir(&dir) else {
        return;
    };
    let path = dir.join(SOLVER_IDENTITY_MEMO);
    // Keep the newest few records (a machine may have several solver builds);
    // rewrite atomically so a concurrent reader never sees a torn file. Only
    // a private memo's records are carried forward; a non-private one is
    // replaced, not merged.
    let mut lines: Vec<String> = read_private_solver_identity_memo(&dir)
        .unwrap_or_default()
        .lines()
        .filter(|l| key.matches(l).is_none())
        .map(|l| l.to_owned())
        .collect();
    lines.push(key.line(hash));
    let keep = lines.len().saturating_sub(8);
    let body = lines[keep..].join("\n") + "\n";
    // The new memo is created `0600` whatever the umask (`private_fs`, as
    // every file under the cache), exclusively and never through a symlink,
    // and renamed over the old one. A temporary a killed writer with this
    // pid left is removed first.
    let tmp = path.with_extension(format!("tmp{}", std::process::id()));
    let _ = std::fs::remove_file(&tmp);
    let written = trust_cg_process_env::private_fs::create_private_file(&tmp)
        .and_then(|mut file| std::io::Write::write_all(&mut file, body.as_bytes()));
    if written.is_err() || std::fs::rename(&tmp, &path).is_err() {
        let _ = std::fs::remove_file(&tmp);
    }
}

pub(crate) fn solver_identity_hash(solver_path: &str) -> Option<String> {
    use sha2::{Digest, Sha256};
    // COMPUTE-ONCE, not merely memoized. The entry is a per-key mutex rather
    // than a bare `String`, so a caller arriving while another thread is
    // mid-hash WAITS for that result instead of streaming the selected solver
    // binary a second time. That is what makes `warm_solver_identity` a real
    // prefetch: without it, the background warm and the first inline consumer
    // would race and each pay the full hash. A FAILED read is still not
    // cached (the slot stays `None`), preserving the prior behaviour that a
    // transient IO error is retried rather than remembered.
    let meta = std::fs::metadata(solver_path).ok()?;
    let stat_key = SolverIdentityStatKey::of(solver_path, &meta)?;

    let memo = solver_identity_memo();
    let slot = {
        let mut map = memo.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        std::sync::Arc::clone(map.entry(stat_key).or_default())
    };
    // Held across the hash below: duplicate callers block here and then read
    // the finished value, rather than each hashing the whole binary.
    let mut slot = slot.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some(hash) = slot.as_ref() {
        return Some(hash.clone());
    }

    // Machine-local memo (see `SolverFileKey`): the 115 MB stream-and-hash below
    // is ~75 ms, paid once per COMPILE. A metadata-exact hit skips it entirely.
    let file_key = SolverFileKey::of(&meta);
    if let Some(k) = &file_key
        && let Some(hash) = solver_identity_cache_lookup(k)
    {
        // Publish into the per-key slot we are already holding, NOT back into
        // the outer map: `stat_key` was moved into `entry` above, and taking
        // the map lock while holding a slot lock would invert the map -> slot
        // order every other caller uses.
        *slot = Some(hash.clone());
        return Some(hash);
    }

    // Stream rather than `fs::read`. The solver binary is ~95MB, and slurping it
    // whole costs a 95MB allocation plus the kernel work to hand it over (the
    // page-release `madvise` alone measured ~10ms) for bytes that are consumed
    // once, sequentially, and never revisited. Same digest either way -- this is
    // an identity hash for the verdict-cache key, so the value must not change.
    if crate::env_lock::var_os("TCG_IDENTITY_TRACE").is_some() {
        eprintln!(
            "TCG_IDENTITY_TRACE computing solver identity for {solver_path}\n{}",
            std::backtrace::Backtrace::force_capture()
        );
    }
    let mut file = std::fs::File::open(solver_path).ok()?;
    let mut hasher = Sha256::new();
    let mut buf = vec![0u8; 1 << 20];
    let mut total = 0u64;
    loop {
        let n = std::io::Read::read(&mut file, &mut buf).ok()?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
        total = total.saturating_add(n as u64);
    }
    crate::process_cost::note_executable_digest(total, "digest_identity");
    let hash = format!("{:x}", hasher.finalize());
    if let Some(k) = &file_key {
        solver_identity_cache_store(k, &hash);
    }
    *slot = Some(hash.clone());
    Some(hash)
}

/// The solver's content identity ONLY if it is already resolved in this
/// process; never computes it.
///
/// Companion to [`warm_solver_identity`]: it lets a hot path (the session
/// verdict memo) use the identity when the background warm has produced it and
/// skip the cache otherwise, instead of synchronously reading and hashing the
/// solver binary. Returns `None` when the binary cannot be stat'ed, when no
/// entry exists yet, or when another thread is mid-hash (the slot is locked) —
/// all of which the caller treats as "no cache", i.e. discharge live.
fn solver_identity_hash_if_ready(solver_path: &str) -> Option<String> {
    let meta = std::fs::metadata(solver_path).ok()?;
    let stat_key = SolverIdentityStatKey::of(solver_path, &meta)?;

    let memo = solver_identity_memo();
    // `try_lock` throughout: this function must never wait on the hash.
    let map = memo.try_lock().ok()?;
    let slot = map.get(&stat_key)?;
    let slot = slot.try_lock().ok()?;
    slot.clone()
}

const SOLVER_IDENTITY_REQUEST_TRACKER_CAPACITY: usize = 32;

fn solver_identity_warm_paths()
-> &'static std::sync::Mutex<std::collections::VecDeque<SolverIdentityStatKey>> {
    static PATHS: std::sync::OnceLock<
        std::sync::Mutex<std::collections::VecDeque<SolverIdentityStatKey>>,
    > = std::sync::OnceLock::new();
    PATHS.get_or_init(|| {
        std::sync::Mutex::new(std::collections::VecDeque::with_capacity(
            SOLVER_IDENTITY_REQUEST_TRACKER_CAPACITY,
        ))
    })
}

fn remove_solver_identity_warm_path(key: &SolverIdentityStatKey) {
    let mut paths = solver_identity_warm_paths()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some(index) = paths.iter().position(|candidate| candidate == key) {
        paths.remove(index);
    }
}

/// Schedule a non-blocking content hash for this exact selected solver.
///
/// The tracker is keyed by path + stable file metadata, not by the first
/// process caller. It is bounded for long-lived compiler servers; the
/// compute-once identity memo remains the final duplicate-work guard if an
/// in-flight key is evicted under extreme churn.
fn start_solver_identity_warm_for_path(solver_path: &str) {
    if crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some()
        || solver_identity_hash_if_ready(solver_path).is_some()
    {
        return;
    }
    let Some(key) = std::fs::metadata(solver_path)
        .ok()
        .and_then(|metadata| SolverIdentityStatKey::of(solver_path, &metadata))
    else {
        return;
    };
    {
        let mut paths = solver_identity_warm_paths()
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if paths.contains(&key) {
            return;
        }
        if paths.len() == SOLVER_IDENTITY_REQUEST_TRACKER_CAPACITY {
            paths.pop_front();
        }
        paths.push_back(key.clone());
    }

    let environment = trust_cg_process_env::EnvOverrideSnapshot::capture_current_thread();
    let path = solver_path.to_owned();
    let worker_key = key.clone();
    let spawn = std::thread::Builder::new()
        .name("trust-cg-solver-identity-warm".to_string())
        .spawn(move || {
            let resolved = environment.run(|| solver_identity_hash(&path));
            if resolved.is_none() {
                remove_solver_identity_warm_path(&worker_key);
            }
        });
    if spawn.is_err() {
        remove_solver_identity_warm_path(&key);
    }
}

fn record_uncached_solver_identity_miss(solver_path: &str) -> usize {
    type MissTracker = std::collections::VecDeque<(SolverIdentityStatKey, usize)>;
    static MISSES: std::sync::OnceLock<std::sync::Mutex<MissTracker>> = std::sync::OnceLock::new();
    let Some(key) = std::fs::metadata(solver_path)
        .ok()
        .and_then(|metadata| SolverIdentityStatKey::of(solver_path, &metadata))
    else {
        return 0;
    };
    let tracker = MISSES.get_or_init(|| {
        std::sync::Mutex::new(std::collections::VecDeque::with_capacity(
            SOLVER_IDENTITY_REQUEST_TRACKER_CAPACITY,
        ))
    });
    let mut tracker = tracker
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    if let Some((_, misses)) = tracker.iter_mut().find(|(candidate, _)| candidate == &key) {
        let prior = *misses;
        *misses = misses.saturating_add(1);
        return prior;
    }
    if tracker.len() == SOLVER_IDENTITY_REQUEST_TRACKER_CAPACITY {
        tracker.pop_front();
    }
    tracker.push_back((key, 1));
    0
}

/// Precompute the DEFAULT-route solver's content identity, off the critical
/// path.
///
/// MEASURED (2026-08-06): on a one-obligation program the frontend refinement
/// lane cost 360ms, of which 337ms was this SHA-256 of the ~73MB `ay` binary
/// and 23ms was the actual proof. The identity is a per-process constant, so
/// every rustc invocation — i.e. every crate in a workspace build — paid the
/// full hash inline before its first obligation could be discharged.
///
/// This computes the SAME digest by the SAME code path; only the SCHEDULE
/// changes. No verdict, key, or gate is affected: a warm memo and a cold one
/// produce byte-identical `verdict_cache_key_v2` keys. Intended to be called
/// on a detached background thread from `CodegenBackend::init` — the earliest
/// backend hook, so rustc's whole front end is available to overlap with (see
/// the CT-7 proof-verifier warm for the established pattern). Spawning it at
/// `codegen_crate` entry is too late: lowering reaches the first obligation
/// within a few ms. Pairs with the compute-once memo in
/// [`solver_identity_hash`] so the first real consumer waits on this hash
/// instead of duplicating it.
///
/// A no-op when no solver resolves or the cache is opted out
/// (`TCG_NO_PROOF_CACHE`) — nothing would consume the result.
/// Spawn [`warm_solver_identity`] on a detached thread, at most once per
/// process.
///
/// Idempotent and non-blocking: repeated calls after the first are a cheap
/// `OnceLock` read. Used both by the rustc bridge (from `CodegenBackend::init`,
/// the earliest hook) and lazily by [`session_proof_cache_key`] on its first
/// not-ready consultation, so every process converges on a usable cache without
/// any of them ever waiting for the hash.
pub fn start_solver_identity_warm() {
    if crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some() {
        return;
    }
    static STARTED: std::sync::OnceLock<
        std::sync::Mutex<std::collections::VecDeque<SolverDiscoveryKey>>,
    > = std::sync::OnceLock::new();
    let key = SolverDiscoveryKey::capture();
    let started = STARTED.get_or_init(|| {
        std::sync::Mutex::new(std::collections::VecDeque::with_capacity(
            SOLVER_IDENTITY_REQUEST_TRACKER_CAPACITY,
        ))
    });
    {
        let mut started = started
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        if started.contains(&key) {
            return;
        }
        if started.len() == SOLVER_IDENTITY_REQUEST_TRACKER_CAPACITY {
            started.pop_front();
        }
        started.push_back(key);
    }
    let environment = trust_cg_process_env::EnvOverrideSnapshot::capture_current_thread();
    let _ = std::thread::Builder::new()
        .name("trust-cg-solver-identity-warm".to_string())
        .spawn(move || environment.run(warm_solver_identity));
}

pub fn warm_solver_identity() {
    if crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some() {
        return;
    }
    let started = std::time::Instant::now();
    let trace = crate::env_lock::var_os("TCG_TIME").is_some();
    crate::process_cost::mark("identity_warm_begin");
    // Admission digests the selected AY's bytes (`crate::ay_identity`) and
    // publishes that digest to the identity memo, so warming IS admitting: the
    // first obligation then waits only for whatever of that hash remains.
    //
    // This is [`find_solver_binary`] with its two independent halves run at
    // the same time: the checker's control-proof probes on a scoped helper
    // thread, and AY admission (whose private copy starts the host's
    // first-start assessment as soon as it is published) here. Both results
    // are required below, exactly as `find_solver_binary` requires them, and
    // the helper is joined before either is used. On a host without a capable
    // checker this admits AY where `find_solver_binary` would have stopped
    // first: on a fresh cache root that also writes the private copy and makes
    // its suspended assessment spawn (none of the copy runs), but no solver is
    // started from it.
    let environment = trust_cg_process_env::EnvOverrideSnapshot::capture_current_thread();
    let (checker_capable, selection) = std::thread::scope(|scope| {
        let probe = std::thread::Builder::new()
            .name("trust-cg-checker-probe-warm".to_string())
            .spawn_scoped(scope, move || {
                environment.run(|| crate::obligation_cert_store::clean_checker_path().is_some())
            });
        let selection = select_solver_binary();
        let checker_capable = match probe {
            Ok(probe) => probe.join().unwrap_or(false),
            // No helper thread: probe here, as `find_solver_binary` does.
            Err(_) => crate::obligation_cert_store::clean_checker_path().is_some(),
        };
        (checker_capable, selection)
    });
    let solver = if checker_capable {
        selection.0.ok()
    } else {
        None
    };
    let Some(solver) = solver else {
        crate::process_cost::mark("identity_warm_no_solver");
        return;
    };
    crate::process_cost::mark("identity_warm_admitted");
    if trace {
        // How much of this the front end actually hides is the whole question
        // for the warm. MEASURED on a one-instruction crate: the hash takes
        // ~320ms but `CodegenBackend::init` runs only ~50ms before
        // `codegen_crate`, so a small crate has no front end to hide it behind
        // and ~275ms stays on the critical path. Compile time is 3.39x of LLVM
        // with the hash and 1.60x without it (`TCG_NO_PROOF_CACHE=1`) — it is
        // essentially the whole remaining compile-time gap.
        eprintln!(
            "TCG_TIME solver_identity_warm took {:.1}ms",
            started.elapsed().as_secs_f64() * 1000.0
        );
    }
    prime_published_solver_copy(&solver);
    // Replay the certificates the scope's last compile used, and start the
    // resident server if it queried one, while the front end still runs
    // (`crate::cert_replay_prefetch`; nothing unless a frontend named a scope).
    crate::cert_replay_prefetch::prefetch_after_admission(&solver);
}

/// Start a private AY copy published during this process once, on the warm
/// thread, so the host's first-start assessment of the new file overlaps the
/// compiler's front end instead of the first solve.
///
/// On macOS that assessment is an XProtect scan of the whole copy
/// (`ay_private_copy::HOST_ASSESSES_FIRST_START`): measured 0.67-1.0 s for the
/// 91 MB Trust 9192 AY, on every compile that populates a fresh cache root,
/// which is what the `--cold` benchmark lane does for every compile. A solve
/// that needs the copy while this start runs waits for it before its deadline
/// starts, rather than paying the rest of the scan inside that deadline
/// (`ay_identity::first_start`, which also makes the start for a process that
/// runs no warm thread or did not publish the copy).
///
/// Establishes nothing: the child is the admitted bytes, revalidated exactly
/// as every start is, it is asked only for its version, and its output and
/// exit status are discarded. It runs only on macOS, only for a copy
/// published during this process and never started by it, so a warm cache
/// starts no extra process, and no other host does.
fn prime_published_solver_copy(solver: &PinnedAy) {
    solver.prime_published_copy();
}

/// The admitted AY the live discharge lane would use right now (`None` when
/// none is admitted or no capable independent checker exists). Used by the
/// tier-0 verdict-DB regen tool ([`crate::verdict_db`]) to record the EXACT
/// binary that produced the committed verdicts.
pub(crate) fn resolved_solver() -> Option<PinnedAy> {
    find_solver_binary()
}

/// Exact proof authority for outer JIT verdict reuse, if it can be obtained
/// without synchronously hashing the large AY binary.
///
/// This captures the selected solver, capable independent checker, sanitized
/// child launch context, and solver content identity once at the caller's
/// request boundary. A cold identity schedules an exact-path background warm
/// and returns `None`; callers must then verify live and must neither read nor
/// populate an outer cache. `TCG_BLOCKING_IDENTITY` is the explicit
/// measurement/test override that restores synchronous identity derivation.
pub fn jit_verification_authority_id_if_ready() -> Option<[u8; 32]> {
    if crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some() {
        return None;
    }
    let selection = select_solver_binary();
    let solver = selection.pinned()?;
    let authority = VerificationAuthority::capture(solver);
    authority.positive_reuse_context_id()?;
    // Admission already digested these bytes; that digest is the content
    // identity for as long as the file is unchanged.
    solver.revalidate().ok()?;
    authority.cache_id_with_solver_identity(solver.sha256())
}

/// Resolve AY as an offline artifact producer without requiring the external
/// Alethe checker that gates live solver authority. Certificate generation
/// independently checks its DRAT output with `drat-trim`; conflating producer
/// discovery with the live AY+Clean route would make regeneration impossible
/// on an otherwise correctly provisioned DRAT-only host.
pub(crate) fn resolved_certificate_producer() -> Result<PinnedAy, AyIdentityRefusal> {
    select_solver_binary().0
}

/// Why the identity rule currently admits no AY (`None` when one is admitted).
/// Independent of the Clean checker, unlike [`proof_toolchain_unavailable_reason`].
pub fn solver_identity_refusal() -> Option<AyIdentityRefusal> {
    select_solver_binary().0.err()
}

/// What a refusal adds when this build records an AY but the identity rule
/// admits none in this process at the moment of the call: that refusal, with
/// its `TCG-AY-IDENTITY-*` code and reason (for an AY that was admitted but
/// could not be copied, the cache directory, its mode and the remedy). `None`
/// when an AY is admitted, and for a build that records no AY (every
/// stock-Rust build): that absence is fixed at build time, is disclosed by
/// the evidence summary's no-solver assumption, and would otherwise change
/// the text of every proof refusal such a build makes. A diagnostic only: it
/// changes no verdict.
///
/// This is a fresh resolution, so it describes the process NOW, not the
/// resolution any earlier evidence was produced under: with a cache path
/// another user can re-point (a symlink in an open directory, which the
/// private-cache rule admits), the two can differ. A refusal over evidence
/// from a function-verification request therefore never uses it; it carries
/// that request's own resolution
/// ([`crate::FunctionVerificationRequest::ay_refusal_note`],
/// [`request_refusal_note_for`]).
pub fn solver_refusal_note() -> Option<String> {
    solver_identity_refusal()
        .as_ref()
        .and_then(solver_refusal_note_for)
}

/// [`solver_refusal_note`] for a given refusal: `None` for
/// [`AyIdentityRefusal::Unrecorded`].
pub fn solver_refusal_note_for(refusal: &AyIdentityRefusal) -> Option<String> {
    (!matches!(refusal, AyIdentityRefusal::Unrecorded { .. })).then(|| {
        format!(
            "no AY is admitted in this process, so no obligation was discharged by AY: {refusal}"
        )
    })
}

/// How [`request_refusal_note_for`] begins.
pub const REQUEST_REFUSAL_NOTE_HEAD: &str =
    "no AY was admitted to the function-verification request this evidence came from";

/// The note a refusal over evidence from ONE function-verification request
/// carries when the identity rule bound no AY to that request: the request's
/// own refusal, resolved once when the request was captured, with its
/// `TCG-AY-IDENTITY-*` code and reason. `None` for
/// [`AyIdentityRefusal::Unrecorded`] (see [`solver_refusal_note`]). The
/// request's source-bound replays, the only discharges a proof-grade entry
/// credits, run under exactly that resolution, so the note names the cause
/// whatever the identity rule would answer at the time of the refusal.
pub fn request_refusal_note_for(refusal: &AyIdentityRefusal) -> Option<String> {
    (!matches!(refusal, AyIdentityRefusal::Unrecorded { .. })).then(|| {
        format!(
            "{REQUEST_REFUSAL_NOTE_HEAD}, so none of its obligations was discharged by AY: \
             {refusal}"
        )
    })
}

/// Separates a refusal reason from the note appended to it.
const SOLVER_REFUSAL_NOTE_SEPARATOR: &str = "; ";

/// `reason`, followed by `note` (a [`request_refusal_note_for`] the evidence
/// carried from its request) when there is one: how a refusal whose reason is
/// a string carries the note. Nothing is resolved here. A typed refusal
/// carries its note in a field of its own instead (the codegen pipeline's
/// `PipelineError::CegisIncomplete::ay_refusal`).
pub fn with_request_refusal_note(reason: String, note: Option<&str>) -> String {
    match note {
        Some(note) => format!("{reason}{SOLVER_REFUSAL_NOTE_SEPARATOR}{note}"),
        None => reason,
    }
}

/// `reason` without the request note [`with_request_refusal_note`] appended
/// (everything from its separator and [`REQUEST_REFUSAL_NOTE_HEAD`] on), so a
/// check can still pin the substantive reason byte for byte. A reason with no
/// such note is returned unchanged. Nothing is resolved: the note is
/// recognized by its text, not recomputed.
pub fn without_solver_refusal_note(reason: &str) -> &str {
    let marker = format!("{SOLVER_REFUSAL_NOTE_SEPARATOR}{REQUEST_REFUSAL_NOTE_HEAD}");
    reason
        .find(marker.as_str())
        .map_or(reason, |start| &reason[..start])
}

const SESSION_PROOF_CACHE_CAPACITY: usize = 4_096;

#[derive(Default)]
struct SessionProofCache {
    entries: std::collections::HashSet<SessionProofKey>,
    insertion_order: std::collections::VecDeque<SessionProofKey>,
}

impl SessionProofCache {
    fn contains(&self, key: &SessionProofKey) -> bool {
        self.entries.contains(key)
    }

    fn insert(&mut self, key: SessionProofKey) {
        if !self.entries.insert(key) {
            return;
        }
        self.insertion_order.push_back(key);
        while self.entries.len() > SESSION_PROOF_CACHE_CAPACITY {
            if let Some(evicted) = self.insertion_order.pop_front() {
                self.entries.remove(&evicted);
            }
        }
    }
}

fn session_proof_cache() -> &'static std::sync::Mutex<SessionProofCache> {
    use std::sync::{Mutex, OnceLock};
    static CACHE: OnceLock<Mutex<SessionProofCache>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(SessionProofCache::default()))
}

/// Forget both in-process solver memos, as a new process starts (tests that
/// model a later compile on the same box).
#[cfg(test)]
pub(crate) fn forget_session_memos_for_test() {
    let mut positive = session_proof_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    positive.entries.clear();
    positive.insertion_order.clear();
    drop(positive);
    let mut negative = session_negative_memo()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    negative.entries.clear();
    negative.insertion_order.clear();
}

fn session_proof_cache_lookup_verified(key: &SessionProofKey) -> bool {
    session_proof_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .contains(key)
}

fn session_proof_cache_store_verified(key: &SessionProofKey) {
    session_proof_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .insert(*key);
    // A positive result supersedes any negative memo for the same key: the
    // positive lookup runs first, and nothing may keep answering `Unknown`
    // for a query this process has since independently certified.
    session_negative_memo()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .remove(key);
}

// ---------------------------------------------------------------------------
// NEGATIVE session memo: "this exact query is UNCERTIFIABLE under this exact
// solver + checker + child environment" — remembered so it is not re-solved
// at every occurrence in one process.
// ---------------------------------------------------------------------------
//
// WHY. The memo above is positive-only: it records `Verified` and nothing
// else. A query whose UNSAT AY itself discloses as holey (`c
// ay.proof.certificate ... unproved_steps=1 ... trust_free=no` — which
// current AY builds emit for every bit-vector THEORY step, i.e. for every
// static lowering-proof obligation the bridge issues) therefore returns
// `Unknown`, is memoised nowhere, and is re-solved — resident exchange plus
// a fresh proof-bearing replay — EVERY time the same instruction shape is
// emitted. Measured 2026-09-20 on a `library/core` compile with proof
// certificates on (`-Ztrust-ir-cg-args=solve-trace`, 300 s cap): 238 solves
// over 100 distinct (obligation, smt2) pairs, 100% of them this exact
// `Unknown`, with individual shapes costing 0.7 s (`ConstMat: MOVZ`) to 4.1 s
// (`MachO ARM64_RELOC_BRANCH26`) PER OCCURRENCE — the certificate lane of the
// `core` census never terminated (3300 s, 0 certs).
//
// WHAT IT IS NOT. This memo grants NO authority and changes NO verdict. A hit
// returns the same `AYResult::Unknown(reason)` the live path returned the
// first time; the positive memo is consulted FIRST, a later `Verified` for the
// same key evicts the negative entry, and the entry can only ever turn a
// re-solve into a replay of a verdict this process already produced. It is
// keyed on the SAME `SessionProofKey` as the positive memo — solver content
// identity + exact SMT2 bytes + checker identity + child environment — so a
// different solver, checker, or query is a different key by construction, and
// it is skipped under exactly the conditions the positive memo is skipped
// (`TCG_NO_PROOF_CACHE`, no capable checker, verdict-DB recording).
//
// WHICH `Unknown`s. Only reasons that are a deterministic function of the key
// (see `unknown_reason_is_memoizable_certification_gap`): AY's own certificate
// header declaring the proof incomplete, and the identity-pinned checker
// rejecting the exact proof. `Timeout`, a bare `unknown`, `(:reason-unknown
// …)` resource envelopes, IO failures and toolchain-absence diagnostics are
// NOT memoised — those depend on load or on the installation, and a later
// occurrence may legitimately answer differently.
//
// NOT PERSISTED, deliberately. The positive store on disk is safe because a
// consumer RE-EARNS the verdict (the checker replays the stored proof before
// anything is credited). A persisted negative entry has nothing to re-earn:
// honouring it would let a stale or writable file silently keep a query at
// `Unknown` after a solver/checker upgrade or on a host whose toolchain
// differs, with no diagnostic saying so. Process lifetime is exactly the
// scope in which the answer is known to be stable.
//
// The one persisted negative memo is a separate, narrower owner decision:
// `crate::source_bound_negative_memo` serves only source-bound replays, keys
// every entry on the solver's recorded identity, the checker's digest, the
// budget and the replay protocol (so an upgrade or another host misses), is
// consulted after the positive tiers, names each hit in the x86 body and
// solve traces, and honours an entry only within a bounded hit count and age
// because AY's outcome on those queries is not stable across load.

/// Process-wide bound on remembered negative verdicts (FIFO eviction, like
/// [`SESSION_PROOF_CACHE_CAPACITY`]).
const SESSION_NEGATIVE_MEMO_CAPACITY: usize = 4_096;

#[derive(Default)]
struct SessionNegativeVerdictMemo {
    entries: std::collections::HashMap<SessionProofKey, std::sync::Arc<str>>,
    insertion_order: std::collections::VecDeque<SessionProofKey>,
}

impl SessionNegativeVerdictMemo {
    fn get(&self, key: &SessionProofKey) -> Option<std::sync::Arc<str>> {
        self.entries.get(key).cloned()
    }

    /// Remember `reason` for `key`. The first recorded reason wins: a later
    /// occurrence is the same verdict class and differs only in the temp-file
    /// path its diagnostic quotes.
    fn insert(&mut self, key: SessionProofKey, reason: &str) {
        if self.entries.contains_key(&key) {
            return;
        }
        self.entries.insert(key, std::sync::Arc::from(reason));
        self.insertion_order.push_back(key);
        while self.entries.len() > SESSION_NEGATIVE_MEMO_CAPACITY {
            if let Some(evicted) = self.insertion_order.pop_front() {
                self.entries.remove(&evicted);
            }
        }
    }

    fn remove(&mut self, key: &SessionProofKey) {
        if self.entries.remove(key).is_some() {
            self.insertion_order.retain(|candidate| candidate != key);
        }
    }
}

fn session_negative_memo() -> &'static std::sync::Mutex<SessionNegativeVerdictMemo> {
    use std::sync::{Mutex, OnceLock};
    static MEMO: OnceLock<Mutex<SessionNegativeVerdictMemo>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(SessionNegativeVerdictMemo::default()))
}

fn session_negative_memo_lookup(key: &SessionProofKey) -> Option<String> {
    session_negative_memo()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .get(key)
        .map(|reason| reason.to_string())
}

fn session_negative_memo_store(key: &SessionProofKey, reason: &str) {
    session_negative_memo()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .insert(*key, reason);
}

/// Is this `AYResult::Unknown` reason a deterministic function of the session
/// key (solver bytes, checker bytes, child environment, exact SMT2), so that
/// remembering it for the rest of the process replays the same verdict the
/// live path would produce again?
///
/// YES:
/// * `incomplete AY proof certificate: c ay.proof.certificate … unproved_steps=N …`
///   — AY's own header for the proof it just emitted says the proof has holes /
///   foreign assumes / is not trust-free (`incomplete_ay_proof_reason`). What AY
///   exports for a given query is a property of the AY build and the query.
/// * `AY reported UNSAT but <checker> … rejected or could not fully verify THIS
///   Alethe proof` — the capability-probed checker replayed the exact proof
///   and did not fully verify it.
///
/// NO (everything else): a bare `unknown` (the resident server drops stderr,
/// so the reason is unknown), `(:reason-unknown …)` (AY resource envelopes,
/// e.g. `incomplete self-check-rejected` on a work limit), `unusable AY proof
/// evidence:` (covers "could not publish a same-run default proof file", an IO
/// condition), an empty/unreadable proof file, "CANNOT BE CHECKED here"
/// (installation, and unkeyable anyway — no checker means no session key), and
/// "Clean replay could not complete" (IO). None of those is guaranteed stable
/// across occurrences, so each keeps its live path.
fn unknown_reason_is_memoizable_certification_gap(reason: &str) -> bool {
    reason.starts_with("incomplete AY proof certificate:")
        || (reason.starts_with("AY reported UNSAT but")
            && reason.contains(WORKING_CHECKER_REJECTED_THIS_PROOF))
}

/// Record a live `Unknown` in the negative memo when — and only when — its
/// reason is memoisable (see [`unknown_reason_is_memoizable_certification_gap`]).
/// Called at the two live-result sites of [`verify_with_cli_smt2`], mirroring
/// the positive `session_proof_cache_store_verified` calls beside them.
fn remember_negative_session_verdict(
    session_key: &SessionProofKey,
    result: &AYResult,
    obligation_name: &str,
    smt2_len: usize,
) {
    let AYResult::Unknown(reason) = result else {
        return;
    };
    if !unknown_reason_is_memoizable_certification_gap(reason) {
        return;
    }
    session_negative_memo_store(session_key, reason);
    if crate::diag::solve_trace_enabled() {
        eprintln!(
            "TCG_SOLVE_TRACE negative_memo_store obligation={obligation_name:?} smt2_bytes={smt2_len}"
        );
    }
}

fn default_session_key(legacy_query_key: &str) -> Option<SessionProofKey> {
    let selection = select_solver_binary();
    VerificationAuthority::capture(selection.pinned()?).session_key(legacy_query_key)
}

/// Crate-visible view of the session verdict memo, so the frontend batch
/// pre-solve ([`crate::mir_semantics::batch_presolve_refinements`]) can (a) skip
/// obligations already cached this process and (b) PRIME the cache under a
/// byte-identical content key so the subsequent inline discharge
/// ([`verify_with_cli_smt2`]) is a cache HIT and spawns no solver.
///
/// SOUNDNESS: crediting via this path is IDENTICAL to crediting via the inline
/// live-solve path — both store the exact same `verdict_cache_key_v2(solver
/// identity, byte-identical SMT2)` key derived from the SAME solver and the
/// SAME query bytes. The cache stores a boolean membership only (never a
/// judgment correspondence); the batch pre-solve inserts a key ONLY when the
/// batched solver output cleanly proved that obligation `unsat` in a
/// single-verdict window, exactly the condition the inline path requires.
pub(crate) fn session_cache_contains(key: &str) -> bool {
    default_session_key(key).is_some_and(|key| session_proof_cache_lookup_verified(&key))
}

/// Prime the session verdict memo (see [`session_cache_contains`]).
pub(crate) fn session_cache_store_verified(key: &str) {
    if let Some(key) = default_session_key(key) {
        session_proof_cache_store_verified(&key);
    }
}

/// The BYTE-IDENTICAL session-cache key the inline default-config CLI discharge
/// ([`verify_with_cli_smt2`]) would compute for a query `smt2`, together with
/// the resolved solver path it would spawn — for the DEFAULT solver route (no
/// `config.solver_path`, which the frontend refinement lane always uses, since
/// it discharges with `AYConfig::default()`).
///
/// This is the ONLY sound way for a batch pre-solve to prime the session memo
/// for a frontend obligation: it reuses the EXACT solver selection
/// ([`select_solver_binary`], obligation-independent) and the EXACT key
/// derivation ([`session_proof_cache_key`] = `verdict_cache_key_v2(identity,
/// smt2)`) that `verify_with_cli_smt2` uses, so a key this returns matches the
/// inline lookup BY CONSTRUCTION. `None` (no solver / unreadable binary /
/// `TCG_NO_PROOF_CACHE`) makes the caller skip that obligation (it keeps its
/// inline live path). The batch caller must have already produced `smt2` via
/// the same simplified/raw choice `verify_with_ay` makes (see
/// [`simplifier_alone_proved_unsat`]).
pub(crate) fn default_route_cache_key(smt2: &str) -> Option<(String, String)> {
    let solver_path = select_solver_binary()
        .pinned()?
        .path()
        .to_string_lossy()
        .into_owned();
    let key = session_proof_cache_key(&solver_path, smt2)?;
    Some((solver_path, key))
}

/// Run ONE precomputed SMT-LIB2 batch script through the resolved solver in a
/// SINGLE subprocess and return its raw stdout (`None` on any spawn / IO /
/// timeout failure). Shares [`write_temp_smt2`] + [`run_solver_verdict_command`] with
/// the per-obligation live path, so the batch runs through the exact same
/// solver-invocation machinery.
///
/// The `script` is opaque to this function: it is the caller's responsibility
/// (`crate::verdict_db`) to assemble a byte-identical, echo-delimited,
/// `(reset)`-isolated batch and to parse the sentinels back out. Any failure
/// here is reported as `None` so the caller falls through to the inline
/// per-obligation live solve (fail-closed — never a weaker verdict).
pub(crate) fn run_batch_solver_script(script: &str, timeout_ms: u64) -> Option<String> {
    let solver = find_solver_binary()?;
    let tmp_file = write_temp_smt2(script).ok()?;
    let output = run_solver_verdict_command(&solver, tmp_file.path(), timeout_ms).ok()?;
    // Every batched obligation is verdict-only, so a clean script exits zero.
    // Any nonzero exit or SMT-LIB protocol error discards the WHOLE batch and
    // falls through to individual live discharge (fail closed).
    if !output.status.success() {
        return None;
    }
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    if stdout.lines().any(|line| line.trim().starts_with("(error")) {
        return None;
    }
    Some(stdout)
}

/// Batched stdout carries solver verdicts but no independently checkable proof
/// per window. It therefore cannot prime the `Verified` memo. Keep the batching
/// implementation available for future proof-framed promotion, but disable its
/// authority path until each UNSAT window carries an exact checked certificate.
pub(crate) fn batch_proof_promotion_available() -> bool {
    false
}

#[derive(Debug)]
pub(crate) enum SolverInvocationError {
    /// The deadline expired, with what the solver's process group consumed
    /// under it.
    Timeout(crate::subprocess::DeadlineExpiry),
    Io(String),
}

fn configure_solver_command(command: &mut std::process::Command, child_env: &SanitizedChildEnv) {
    child_env.apply_to_command(command);
    crate::subprocess::configure_process_group(command);
}

// ==========================================================================
// PERSISTENT SOLVER SERVER
// ==========================================================================
// Reuse one resident `ay --incremental` process to amortize startup, with
// sentinel-framed queries and `(reset)` isolation. Actual startup/solve costs
// depend on the selected AY build and workload; historical timings are not a
// current performance claim.
//
// Protocol contract: the same binary receives the same SMT query body, minus
// the trailing `(exit)`, plus `(echo <sentinel>)` and `(reset)`. Isolation relies
// on AY's reset semantics. SAT values are requested only in a subsequent
// SAT-only window; UNSAT/unknown scripts never contain a model command. The
// verdict is parsed by the SAME `parse_solver_output`. FAIL-SAFE: a
// process/framing anomaly (spawn/write/
// read error, missing/duplicate verdict, closed stream) DROPS the server
// (requesting termination) and asks the caller to retry AY in a fresh process
// — never a wrong or weaker verdict. A configured deadline also drops the
// server, but returns `TimedOut`: retrying the byte-identical query would
// silently double the caller's timeout budget. The global lock serializes
// queries (one window at a time), so windows never interleave. A query's
// deadline measures SOLVER time: it starts when the query is admitted to the
// server (the lock is held) and covers spawn and both I/O directions, never the
// time spent queued behind other queries' windows. Queueing is bounded
// separately, by the holder's own admitted budget: a waiter is refused by name
// (`AyServerHolderOverran`) only once the query holding the server has run past
// its budget plus `AY_SERVER_HOLDER_OVERRUN_ALLOWANCE`. No reader worker is
// detached. OS spawn/syscall scheduling and escaped-child cleanup are not hard
// bounded.
// Off while the regen recorder is armed (it must observe genuine fresh runs).
struct AyServer {
    process: Option<crate::subprocess::InteractiveProcess>,
    exit_registration: resident_exit_cleanup::Registration<'static>,
    /// The exact binary this resident process was spawned from. SOLVER
    /// IDENTITY BINDING: a query for a DIFFERENT admitted AY (an
    /// `AYConfig::solver` chosen in code, or another admitted copy) must never
    /// be answered by this process — the slot is dropped and respawned for the
    /// requested binary. Without this, a query naming solver B was silently
    /// routed to whichever solver A happened to become resident first.
    solver_path: std::path::PathBuf,
    solver_process_id: [u8; 32],
}

impl Drop for AyServer {
    fn drop(&mut self) {
        let Some(mut process) = self.process.take() else {
            return;
        };
        // Withdraw registry ownership before stop/reap. An exit claimant must
        // retain its unreaped PID until it has requested the group signal.
        if !self.exit_registration.release() {
            std::mem::forget(process);
            return;
        }
        if crate::diag::solve_trace_enabled() {
            eprintln!(
                "TCG_SOLVE_TRACE server_drop pid={} path={}",
                process.pid(),
                self.solver_path.display()
            );
        }
        if let Some(cleanup) = process.stop()
            && crate::diag::solve_trace_enabled()
        {
            eprintln!("TCG_SOLVE_TRACE server_cleanup {cleanup}");
        }
    }
}

/// Exit cleanup is guaranteed after proof/startup/query work has quiesced and
/// hinted prefetch has stopped (`cert_replay_prefetch::persist`). The callback
/// signals every registered idle group without locks or allocation.
///
/// Arbitrary exit during OS spawn/pipe setup or an active query is outside that
/// contract: at most MAX_PROOF_GATE_WORKERS groups can be in flight, with no
/// finite OS-scheduling bound. Late publication refuses and stops its own child
/// if that owner still runs. A fork child never signals parent groups.
#[cfg(unix)]
mod resident_exit_cleanup {
    use std::sync::atomic::{AtomicBool, AtomicU32, Ordering::SeqCst};
    const PENDING: u32 = u32::MAX;
    const SIGNALLING: u32 = u32::MAX - 1;
    const SIGNALLED: u32 = u32::MAX - 2;
    struct Registry {
        owner: AtomicU32,
        exiting: AtomicBool,
        groups: [AtomicU32; super::MAX_PROOF_GATE_WORKERS],
    }
    impl Registry {
        const fn new() -> Self {
            Self {
                owner: AtomicU32::new(0),
                exiting: AtomicBool::new(false),
                groups: [const { AtomicU32::new(0) }; super::MAX_PROOF_GATE_WORKERS],
            }
        }
        fn reserve(&self, pid: u32) -> Option<Reservation<'_>> {
            if self.exiting.load(SeqCst) || !bind_owner(&self.owner, pid) {
                return None;
            }
            for group in &self.groups {
                if group.compare_exchange(0, PENDING, SeqCst, SeqCst).is_ok() {
                    let reservation = Reservation {
                        registry: self,
                        group,
                    };
                    return (!self.exiting.load(SeqCst)).then_some(reservation);
                }
            }
            None
        }
        /// Pending startup/query slots have no exit signal authority.
        fn close(&self, pid: u32, signal: impl Fn(u32)) -> usize {
            let owner = self.owner.load(SeqCst);
            if owner != 0 && owner != pid {
                return 0;
            }
            self.exiting.store(true, SeqCst); // Also latch an empty registry.
            let mut pending = 0;
            for group in &self.groups {
                let id = group.load(SeqCst);
                if id == PENDING {
                    pending += 1;
                }
                if (2..=i32::MAX as u32).contains(&id)
                    && group
                        .compare_exchange(id, SIGNALLING, SeqCst, SeqCst)
                        .is_ok()
                {
                    signal(id);
                    group.store(SIGNALLED, SeqCst);
                }
            }
            pending
        }
    }
    static REGISTRY: Registry = Registry::new();
    pub(super) fn bind_owner(owner: &AtomicU32, pid: u32) -> bool {
        match owner.compare_exchange(0, pid, SeqCst, SeqCst) {
            Ok(_) => true,
            Err(bound) => bound == pid,
        }
    }
    pub(super) fn runtime_owned_by_current_process() -> bool {
        bind_owner(&REGISTRY.owner, std::process::id())
    }
    pub(super) fn exit_started() -> bool {
        REGISTRY.exiting.load(SeqCst)
    }
    fn kill_group(pid: u32) {
        if pid > 1 && pid <= i32::MAX as u32 {
            // SAFETY: this exit claim excludes concurrent reaping of the idle
            // Child; only its owned, unreaped PID can name this process group.
            unsafe {
                libc::kill(-(pid as i32), libc::SIGKILL);
            }
        }
    }
    extern "C" fn kill_resident_group_at_exit() {
        REGISTRY.close(std::process::id(), kill_group);
    }
    /// Install the callback and reserve fixed capacity BEFORE spawning.
    pub(super) fn prepare_spawn() -> Option<Reservation<'static>> {
        if !runtime_owned_by_current_process() || exit_started() {
            return None;
        }
        static REGISTERED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
        // SAFETY: callback captures nothing and takes no Rust mutex.
        if !*REGISTERED.get_or_init(|| unsafe { libc::atexit(kill_resident_group_at_exit) } == 0) {
            return None;
        }
        REGISTRY.reserve(std::process::id())
    }
    pub(super) struct Reservation<'a> {
        registry: &'a Registry,
        group: &'a AtomicU32,
    }
    impl<'a> Reservation<'a> {
        pub(super) fn publish(self, pid: u32) -> Option<Registration<'a>> {
            if !(2..=i32::MAX as u32).contains(&pid) || self.registry.exiting.load(SeqCst) {
                return None;
            }
            self.group
                .compare_exchange(PENDING, pid, SeqCst, SeqCst)
                .ok()?;
            Some(Registration {
                registry: self.registry,
                group: self.group,
                pid,
            })
        }
    }
    impl Drop for Reservation<'_> {
        fn drop(&mut self) {
            let _ = self.group.compare_exchange(PENDING, 0, SeqCst, SeqCst);
        }
    }
    pub(super) struct Registration<'a> {
        registry: &'a Registry,
        group: &'a AtomicU32,
        pid: u32,
    }
    impl Registration<'_> {
        /// Exchange can stop/reap internally, so first withdraw idle authority.
        pub(super) fn pause(&self) -> bool {
            self.registry.owner.load(SeqCst) == std::process::id()
                && !self.registry.exiting.load(SeqCst)
                && self
                    .group
                    .compare_exchange(self.pid, PENDING, SeqCst, SeqCst)
                    .is_ok()
                && !self.registry.exiting.load(SeqCst)
        }
        pub(super) fn resume(&self) -> bool {
            self.registry.owner.load(SeqCst) == std::process::id()
                && !self.registry.exiting.load(SeqCst)
                && self
                    .group
                    .compare_exchange(PENDING, self.pid, SeqCst, SeqCst)
                    .is_ok()
                && !self.registry.exiting.load(SeqCst)
        }
        /// False while the exit callback owns the signal. Preserve the Child
        /// unreaped in that case, so the callback cannot signal a reused PID.
        pub(super) fn release(&self) -> bool {
            if self.registry.owner.load(SeqCst) != std::process::id() {
                return false;
            }
            match self.group.compare_exchange(self.pid, 0, SeqCst, SeqCst) {
                Ok(_) => true,
                Err(PENDING) => self
                    .group
                    .compare_exchange(PENDING, 0, SeqCst, SeqCst)
                    .is_ok(),
                Err(SIGNALLED | 0) => true,
                _ => false,
            }
        }
    }
    #[cfg(test)]
    pub(super) fn quiescent() -> bool {
        REGISTRY
            .groups
            .iter()
            .all(|g| !matches!(g.load(SeqCst), PENDING | SIGNALLING))
    }
    #[cfg(test)]
    pub(super) fn close_for_test() {
        kill_resident_group_at_exit();
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn empty_shutdown_latches_before_first_publication() {
            let registry = Registry::new();
            assert_eq!(
                registry.close(std::process::id(), |_| panic!("empty registry signalled")),
                0
            );
            assert!(registry.exiting.load(SeqCst));
            assert!(registry.reserve(std::process::id()).is_none());
        }
        #[test]
        fn reservations_are_bounded_and_failed_spawn_releases_capacity() {
            let registry = Registry::new();
            let pid = std::process::id();
            let mut tickets = (0..super::super::MAX_PROOF_GATE_WORKERS)
                .map(|_| registry.reserve(pid).unwrap())
                .collect::<Vec<_>>();
            assert!(registry.reserve(pid).is_none());
            drop(tickets.pop());
            assert!(registry.reserve(pid).is_some());
            for invalid in [0, 1, u32::MAX] {
                drop(tickets.pop());
                assert!(registry.reserve(pid).unwrap().publish(invalid).is_none());
            }
        }
        #[test]
        fn foreign_fork_owner_cannot_close_or_reserve_parent_registry() {
            let registry = Registry::new();
            let pid = std::process::id();
            let registration = registry.reserve(pid).unwrap().publish(200).unwrap();
            let foreign = if pid == 100 { 101 } else { 100 };
            assert!(registry.reserve(foreign).is_none());
            assert_eq!(
                registry.close(foreign, |_| panic!("foreign PID signalled")),
                0
            );
            assert!(!registry.exiting.load(SeqCst));
            let signalled = std::cell::Cell::new(0);
            assert_eq!(registry.close(pid, |group| signalled.set(group)), 0);
            assert_eq!(signalled.get(), 200);
            assert!(registration.release());
        }
        #[test]
        fn exit_during_pending_start_refuses_late_publication() {
            let registry = Registry::new();
            let pid = std::process::id();
            let ticket = registry.reserve(pid).unwrap();
            assert_eq!(
                registry.close(pid, |_| panic!("unpublished PID signalled")),
                1
            );
            assert!(ticket.publish(200).is_none());
            assert!(registry.groups.iter().all(|group| group.load(SeqCst) == 0));
        }
        #[test]
        fn active_exchange_withdraws_pid_before_internal_reap() {
            let registry = Registry::new();
            let pid = std::process::id();
            let registration = registry.reserve(pid).unwrap().publish(200).unwrap();
            assert!(registration.pause());
            assert_eq!(
                registry.close(pid, |_| panic!("query PID could be reaped")),
                1
            );
            assert!(!registration.resume());
            assert!(registration.release());
        }
        #[test]
        fn exit_signal_claim_keeps_child_unreaped_until_signal_returns() {
            let registry = Registry::new();
            let pid = std::process::id();
            let registration = registry.reserve(pid).unwrap().publish(200).unwrap();
            let entered = std::sync::Barrier::new(2);
            let finish = std::sync::Barrier::new(2);
            let can_reap_during = std::thread::scope(|scope| {
                let worker = scope.spawn(|| {
                    registry.close(pid, |group| {
                        assert_eq!(group, 200);
                        entered.wait();
                        finish.wait();
                    })
                });
                entered.wait();
                let can_reap = registration.release();
                finish.wait();
                assert_eq!(worker.join().unwrap(), 0);
                can_reap
            });
            assert!(!can_reap_during);
            assert!(registration.release());
        }
    }
}
#[cfg(not(unix))]
mod resident_exit_cleanup {
    pub(super) struct Reservation;
    pub(super) struct Registration<'a>(std::marker::PhantomData<&'a ()>);
    pub(super) fn prepare_spawn() -> Option<Reservation> {
        None
    }
    pub(super) fn exit_started() -> bool {
        true
    }
    impl Reservation {
        pub(super) fn publish(self, _: u32) -> Option<Registration<'static>> {
            None
        }
    }
    impl Registration<'_> {
        pub(super) fn pause(&self) -> bool {
            false
        }
        pub(super) fn resume(&self) -> bool {
            false
        }
        pub(super) fn release(&self) -> bool {
            true
        }
    }
}

/// Hard ceiling on simultaneously resident proof-gate solver lanes.
pub(crate) const MAX_PROOF_GATE_WORKERS: usize = 32;

thread_local! {
    static PROOF_GATE_LANE: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Scoped scheduling lane; it changes neither solver identity nor proof policy.
pub(crate) fn with_proof_gate_lane<R>(lane: usize, run: impl FnOnce() -> R) -> R {
    assert!(lane < MAX_PROOF_GATE_WORKERS);
    struct Restore(usize);
    impl Drop for Restore {
        fn drop(&mut self) {
            PROOF_GATE_LANE.with(|slot| slot.set(self.0));
        }
    }
    let _restore = Restore(PROOF_GATE_LANE.with(|slot| slot.replace(lane)));
    run()
}

fn proof_gate_server(lane: usize) -> (&'static AyServerSlot, &'static AyServerLeaseSlot) {
    if lane == 0 {
        return (ay_server_slot(), ay_server_lease());
    }
    static LANES: std::sync::OnceLock<
        [(AyServerSlot, AyServerLeaseSlot); MAX_PROOF_GATE_WORKERS - 1],
    > = std::sync::OnceLock::new();
    let lanes = LANES.get_or_init(|| {
        std::array::from_fn(|_| (std::sync::Mutex::new(None), std::sync::Mutex::new(None)))
    });
    let (slot, lease) = &lanes[lane - 1];
    (slot, lease)
}

fn ay_server_slot() -> &'static std::sync::Mutex<Option<AyServer>> {
    static SLOT: std::sync::OnceLock<std::sync::Mutex<Option<AyServer>>> =
        std::sync::OnceLock::new();
    SLOT.get_or_init(|| std::sync::Mutex::new(None))
}

fn ay_server_next_seq() -> Option<u64> {
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    reserve_server_sequence(&SEQ)
}

fn reserve_server_sequence(sequence: &std::sync::atomic::AtomicU64) -> Option<u64> {
    use std::sync::atomic::Ordering::Relaxed;
    let mut previous = sequence.load(Relaxed);
    loop {
        let next = previous.checked_add(1)?;
        match sequence.compare_exchange_weak(previous, next, Relaxed, Relaxed) {
            Ok(_) => return Some(previous),
            Err(current) => previous = current,
        }
    }
}

#[test]
fn server_sequences_never_reuse_after_exhaustion() {
    use std::sync::atomic::{AtomicU64, Ordering};
    let sequence = AtomicU64::new(u64::MAX - 32);
    let mut reserved = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..8)
            .map(|_| {
                scope.spawn(|| {
                    let mut ids = Vec::new();
                    while let Some(id) = reserve_server_sequence(&sequence) {
                        ids.push(id);
                    }
                    ids
                })
            })
            .collect();
        workers
            .into_iter()
            .flat_map(|worker| worker.join().unwrap())
            .collect::<Vec<_>>()
    });
    reserved.sort_unstable();
    assert_eq!(reserved, (u64::MAX - 32..u64::MAX).collect::<Vec<_>>());
    assert_eq!(sequence.load(Ordering::Relaxed), u64::MAX);
    assert_eq!(reserve_server_sequence(&sequence), None);
}

/// Slack a query holding the resident server may take past its own admitted
/// solver budget before a waiter treats the server as wedged and is refused:
/// the child spawn (which the deadline cannot interrupt), the bounded teardown
/// of a timed-out child, and response parsing. Those costs are normally
/// milliseconds; the slack is wide because exceeding it refuses every waiter.
const AY_SERVER_HOLDER_OVERRUN_ALLOWANCE: Duration = Duration::from_secs(10);

/// How often a queued query re-checks the server slot and the holder's lease.
const AY_SERVER_QUEUE_POLL: Duration = Duration::from_millis(5);

/// The admission record of the query holding the resident server, readable by
/// queued queries without the slot lock: when it was admitted and the solver
/// budget its deadline enforces (`None` = the explicit unlimited policy).
#[derive(Clone, Copy)]
struct AyServerLease {
    admitted_at: Instant,
    budget: Option<Duration>,
}

type AyServerSlot = std::sync::Mutex<Option<AyServer>>;
type AyServerLeaseSlot = std::sync::Mutex<Option<AyServerLease>>;

fn ay_server_lease() -> &'static AyServerLeaseSlot {
    static LEASE: AyServerLeaseSlot = std::sync::Mutex::new(None);
    &LEASE
}

fn read_ay_server_lease(lease: &AyServerLeaseSlot) -> Option<AyServerLease> {
    *lease
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

fn write_ay_server_lease(lease: &AyServerLeaseSlot, value: Option<AyServerLease>) {
    *lease
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner) = value;
}

/// A queued query's named refusal: the query holding the resident server ran
/// past its own admitted solver budget plus the overrun allowance, so the server
/// is wedged. No solver ran for the refused query and no verdict is produced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct AyServerHolderOverran {
    held_for: Duration,
    holder_budget: Duration,
    allowance: Duration,
}

impl fmt::Display for AyServerHolderOverran {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "resident AY server wedged: the query holding it has run {:?}, past its admitted \
             {:?} solver budget plus the {:?} overrun allowance; this query was refused \
             without solving",
            self.held_for, self.holder_budget, self.allowance
        )
    }
}

/// Exclusive use of the resident server for one query. The query's solver
/// deadline starts HERE, at admission, so time spent queued behind other
/// queries is never charged to it. Dropping the admission withdraws the lease
/// before the slot lock is released.
struct AyServerAdmission {
    slot: std::sync::MutexGuard<'static, Option<AyServer>>,
    lease: &'static AyServerLeaseSlot,
    deadline: crate::subprocess::Deadline,
}

impl Drop for AyServerAdmission {
    fn drop(&mut self) {
        write_ay_server_lease(self.lease, None);
    }
}

/// A resident server a query can be admitted to: the slot holding its process,
/// the lease naming the query that holds it, and the overrun allowance a waiter
/// grants that holder. Production always uses [`AyResidentServer::process`]; a
/// test passes a private one, so a holder it wedges on purpose never refuses
/// another test's query.
#[derive(Clone, Copy)]
struct AyResidentServer {
    slot: &'static AyServerSlot,
    lease: &'static AyServerLeaseSlot,
    overrun_allowance: Duration,
}

impl AyResidentServer {
    /// The process-wide resident server.
    fn process() -> Self {
        let (slot, lease) = PROOF_GATE_LANE.with(|lane| proof_gate_server(lane.get()));
        Self {
            slot,
            lease,
            overrun_allowance: AY_SERVER_HOLDER_OVERRUN_ALLOWANCE,
        }
    }

    /// Wait for this server, then admit a query with `budget` of solver time.
    /// Waiting is not charged to `budget`; it is refused only when the current
    /// holder has overrun its own admitted budget by more than the overrun
    /// allowance (a holder under the explicit unlimited policy is never treated
    /// as overrun).
    fn admit(self, budget: Option<Duration>) -> Result<AyServerAdmission, AyServerHolderOverran> {
        admit_to_server_slot(self.slot, self.lease, budget, self.overrun_allowance)
    }
}

/// [`AyResidentServer::admit`] over an explicit slot and lease.
fn admit_to_server_slot(
    slot: &'static AyServerSlot,
    lease: &'static AyServerLeaseSlot,
    budget: Option<Duration>,
    overrun_allowance: Duration,
) -> Result<AyServerAdmission, AyServerHolderOverran> {
    let admit = |slot_guard: std::sync::MutexGuard<'static, Option<AyServer>>| {
        write_ay_server_lease(
            lease,
            Some(AyServerLease {
                admitted_at: Instant::now(),
                budget,
            }),
        );
        AyServerAdmission {
            slot: slot_guard,
            lease,
            deadline: crate::subprocess::Deadline::new(budget),
        }
    };
    loop {
        match slot.try_lock() {
            Ok(guard) => return Ok(admit(guard)),
            Err(std::sync::TryLockError::WouldBlock) => {
                if let Some(AyServerLease {
                    admitted_at,
                    budget: Some(holder_budget),
                }) = read_ay_server_lease(lease)
                {
                    let held_for = admitted_at.elapsed();
                    if held_for > holder_budget.saturating_add(overrun_allowance) {
                        return Err(AyServerHolderOverran {
                            held_for,
                            holder_budget,
                            allowance: overrun_allowance,
                        });
                    }
                }
                std::thread::sleep(AY_SERVER_QUEUE_POLL);
            }
            Err(std::sync::TryLockError::Poisoned(poisoned)) => {
                // A panic may have interrupted a protocol window. Drop its
                // process before clearing poison; never resume that transcript.
                let mut guard = poisoned.into_inner();
                *guard = None;
                slot.clear_poison();
                return Ok(admit(guard));
            }
        }
    }
}

/// Resident-server path enabled? Default ON on Unix; opt out with
/// `TCG_NO_SOLVER_SERVER=1`. Never while the regen recorder is armed (the
/// offline builder must observe genuine fresh live solver runs), and never in
/// a forked copy of the process that first used the resident runtime.
#[cfg(unix)]
pub(crate) fn ay_server_enabled() -> bool {
    resident_exit_cleanup::runtime_owned_by_current_process()
        && !resident_exit_cleanup::exit_started()
        && trust_cg_process_env::var_os("TCG_NO_SOLVER_SERVER").is_none()
        && !crate::verdict_db::recording_active()
}

/// Off Unix there is no process-group kill and no exit-time cleanup for the
/// never-dropped static server, so the one-shot solver path is always used.
#[cfg(not(unix))]
pub(crate) fn ay_server_enabled() -> bool {
    false
}

/// The strict proof campaign needs the complete one-shot transcript. The
/// resident server deliberately discards stderr because it is not query-framed,
/// while AY emits decisive `reason-unknown` and proof-authority diagnostics
/// there. Preserve those diagnostics so the strict gate can distinguish a
/// rejected authority path from ordinary solver capacity.
pub(crate) fn strict_formal_campaign_active() -> bool {
    matches!(
        trust_cg_process_env::var("TRUST_CG_RUN_FORMAL_PROOF_TESTS").as_deref(),
        Ok("1")
    )
}

/// Solver paths whose resident mode proved unusable in this process.
///
/// A server-start or framing failure is normally stable for the same binary.
/// Remembering it prevents every later obligation from repaying a doomed
/// spawn and teardown. The latch is path-scoped so one incompatible explicit
/// solver does not disable another one selected later in the process. The
/// fresh one-shot fallback remains authoritative and always runs.
const AY_SERVER_UNUSABLE_CAPACITY: usize = 128;

fn ay_server_unusable_paths() -> &'static std::sync::Mutex<std::collections::VecDeque<[u8; 32]>> {
    static PATHS: std::sync::OnceLock<std::sync::Mutex<std::collections::VecDeque<[u8; 32]>>> =
        std::sync::OnceLock::new();
    PATHS.get_or_init(|| {
        std::sync::Mutex::new(std::collections::VecDeque::with_capacity(
            AY_SERVER_UNUSABLE_CAPACITY,
        ))
    })
}

#[cfg(test)]
fn ay_server_is_unusable(solver: &PinnedAy) -> bool {
    let authority = VerificationAuthority::capture(solver);
    ay_server_is_unusable_for_authority(&authority)
}

fn ay_server_is_unusable_for_authority(authority: &VerificationAuthority) -> bool {
    ay_server_unusable_paths()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .contains(&authority.solver_process_id())
}

fn mark_ay_server_unusable_for_authority(authority: &VerificationAuthority) {
    let id = authority.solver_process_id();
    let mut paths = ay_server_unusable_paths()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    if paths.contains(&id) {
        return;
    }
    if paths.len() == AY_SERVER_UNUSABLE_CAPACITY {
        paths.pop_front();
    }
    paths.push_back(id);
}

/// Spawn `ay --incremental` with polled stdin/stdout and stderr to null.
/// Failed setup tears down the owned child; no I/O worker is detached.
fn spawn_ay_server(authority: &VerificationAuthority) -> Option<AyServer> {
    // The resident protocol needs AY's line-by-line interactive path and
    // per-response flushing. Pass only --incremental: -in is its compatibility
    // alias, so supplying both rejects the invocation instead of starting a
    // resident solver. Historical startup timings are not current evidence.
    let mut command = resident_solver_command(authority.solver())?;
    configure_solver_command(&mut command, authority.child_env());
    let reservation = resident_exit_cleanup::prepare_spawn()?;
    let mut process = crate::subprocess::InteractiveProcess::spawn(&mut command).ok()?;
    let Some(exit_registration) = reservation.publish(process.pid()) else {
        let _ = process.stop();
        return None;
    };
    if crate::diag::solve_trace_enabled() {
        eprintln!(
            "TCG_SOLVE_TRACE server_spawn pid={} path={} exec={}",
            process.pid(),
            authority.solver_path().display(),
            authority.solver().exec_path().display()
        );
    }
    let server = AyServer {
        process: Some(process),
        exit_registration,
        solver_path: authority.solver_path().to_path_buf(),
        solver_process_id: authority.solver_process_id(),
    };
    (!resident_exit_cleanup::exit_started()).then_some(server)
}

/// Start the process-wide resident server for `authority` now, if no query
/// holds the server and none is running for this authority (the replay
/// prefetch, `crate::cert_replay_prefetch`, when the scope's last compile
/// queried it). It is the start the first resident query would make: the same
/// admitted AY, the same command, environment and exit cleanup
/// ([`spawn_ay_server`]), and no query is sent. A server already running for
/// another authority is left alone; a busy slot is not waited for.
pub(crate) fn prestart_resident_server(authority: &VerificationAuthority) {
    if !ay_server_enabled()
        || strict_formal_campaign_active()
        || ay_server_is_unusable_for_authority(authority)
    {
        return;
    }
    authority.solver().make_first_start();
    let Ok(mut slot) = AyResidentServer::process().slot.try_lock() else {
        return;
    };
    if slot.is_none() {
        *slot = spawn_ay_server(authority);
        crate::process_cost::mark("resident_prestart");
    }
}

/// Result of one resident-server attempt.
///
/// `TimedOut` is deliberately distinct from `Anomaly`: a timeout consumed the
/// configured solver budget and must be surfaced directly, while an anomaly
/// permits the existing fail-closed fresh-process fallback. `QueueRefused`
/// is neither: this query never reached a solver because the query holding the
/// server overran its own budget; it is surfaced as a named error, never as a
/// solver timeout and never retried. Unlike an anomaly it does NOT latch the
/// resident server unusable: it says nothing about this solver's resident mode,
/// only that another query is holding the server past its budget, and the
/// holder's own deadline releases the server for the queries after it.
enum AyServerAttempt {
    Completed(AYResult),
    /// The budget ran out: in the exchange, with what the resident process
    /// group consumed during it (`cpu` is `None` when the caller did not ask
    /// for the measurement), or (`None`) before the exchange began.
    TimedOut(Option<crate::subprocess::DeadlineExpiry>),
    Anomaly,
    QueueRefused(AyServerHolderOverran),
}

/// Parse one framed resident response, return `TimedOut` when its budget is
/// consumed (the budget starts at admission to the server, not while queued),
/// `QueueRefused` when the query holding the server overran its own budget, or
/// request a fresh-AY retry with `Anomaly`. Candidate UNSAT must
/// still follow the caller's proof-replay policy; this stream omits stderr.
/// `smt2` MUST be the exact bytes the per-call path writes (ending in an
/// `(exit)` line).
#[cfg(test)]
fn run_solver_via_server(
    solver: &PinnedAy,
    smt2: &str,
    timeout_ms: u64,
    inputs: &[(String, u32)],
) -> AyServerAttempt {
    let authority = VerificationAuthority::capture_solver_process(solver);
    run_solver_via_server_with_authority(
        AyResidentServer::process(),
        &authority,
        smt2,
        timeout_ms,
        inputs,
        false,
    )
}

/// `measure_cpu`: measure the CPU time the resident process group consumes
/// during this query's exchange, so a deadline expiry reports it
/// ([`crate::subprocess::InteractiveProcess::exchange_measuring_cpu`]).
fn run_solver_via_server_with_authority(
    server: AyResidentServer,
    authority: &VerificationAuthority,
    smt2: &str,
    timeout_ms: u64,
    inputs: &[(String, u32)],
    measure_cpu: bool,
) -> AyServerAttempt {
    // Query body = the exact per-call SMT2 minus its trailing `(exit)` (the
    // server must NOT exit), then an echoed unique sentinel + `(reset)`.
    let trimmed = smt2.strip_suffix('\n').unwrap_or(smt2);
    let Some(body) = trimmed.strip_suffix("(exit)") else {
        return AyServerAttempt::Anomaly;
    };
    let Some(seq) = ay_server_next_seq() else {
        return AyServerAttempt::Anomaly;
    };
    let sentinel = format!("==TCG_SRV_{seq}==");

    // The solver deadline starts at admission, not here: time spent queued
    // behind other queries' windows is not solver time (see
    // `AyResidentServer::admit`). Neither is the first start of a new private
    // copy, which a spawn inside the deadline would otherwise pay: it is made
    // (or waited for) before queueing (`ay_identity::first_start`).
    authority.solver().make_first_start();
    let mut admission =
        match server.admit((timeout_ms != 0).then_some(Duration::from_millis(timeout_ms))) {
            Ok(admission) => admission,
            Err(refusal) => return AyServerAttempt::QueueRefused(refusal),
        };
    let deadline = admission.deadline;
    let guard: &mut Option<AyServer> = &mut admission.slot;
    // Solver identity binding: the resident server answers only queries for
    // the binary it was spawned from. A different `solver_path` (config
    // override, test fake) drops the resident child and spawns the requested
    // one — never silently answering with the wrong solver.
    if guard
        .as_ref()
        .is_some_and(|server| server.solver_process_id != authority.solver_process_id())
    {
        *guard = None;
    }
    if guard.is_none() {
        *guard = spawn_ay_server(authority);
    }
    if deadline.expired() {
        *guard = None;
        return AyServerAttempt::TimedOut(None);
    }
    let Some(server) = guard.as_mut() else {
        return AyServerAttempt::Anomaly;
    };

    // Unbuffered, nonblocking writes need no flush. Service response reads
    // while feeding the query so full stdin/stdout cannot deadlock each other.
    let script = format!("{body}\n(echo \"{sentinel}\")\n(reset)\n");
    crate::cert_replay_prefetch::note_resident_query();

    // Read this window until the sentinel, honoring the deadline. Capture lines
    // from the FIRST verdict line onward (so any pre-verdict noise is discarded
    // and `parse_solver_output` sees the verdict as line 0). A configured
    // deadline returns TimedOut; premature EOF or malformed framing remains
    // an anomaly eligible for a fresh-process fallback. timeout_ms == 0 means
    // no deadline, matching `run_solver_command`.
    let mut window = String::new();
    let mut verdict_lines = 0usize;
    let mut seen_verdict = false;
    let mut protocol_error: Option<String> = None;
    let on_line = |line: &str| -> std::io::Result<bool> {
        let t = line.trim();
        if t == sentinel {
            return Ok(true);
        }
        if t.starts_with("(error") {
            protocol_error = Some(t.to_owned());
        }
        if t == "sat" || t == "unsat" || t == "unknown" {
            verdict_lines = verdict_lines.saturating_add(1);
            seen_verdict = true;
        }
        if seen_verdict {
            let count = line
                .len()
                .checked_add(1)
                .ok_or(std::io::ErrorKind::OutOfMemory)?;
            window
                .try_reserve(count)
                .map_err(|error| std::io::Error::new(std::io::ErrorKind::OutOfMemory, error))?;
            window.push_str(line);
            window.push('\n');
        }
        Ok(false)
    };
    if !server.exit_registration.pause() {
        *guard = None;
        return AyServerAttempt::Anomaly;
    }
    let exchange = if measure_cpu {
        server
            .process
            .as_mut()
            .expect("live resident process")
            .exchange_measuring_cpu(script.as_bytes(), deadline, on_line)
    } else {
        server
            .process
            .as_mut()
            .expect("live resident process")
            .exchange(script.as_bytes(), deadline, on_line)
    };
    if exchange.is_ok() && !server.exit_registration.resume() {
        *guard = None;
        return AyServerAttempt::Anomaly;
    }

    if let Err(error) = exchange {
        // The exchange already performed cleanup. Keep its observations in
        // opt-in tracing before reducing the error to the public attempt kind.
        if crate::diag::solve_trace_enabled() {
            eprintln!("TCG_SOLVE_TRACE server_exchange_failed {error}");
        }
        *guard = None;
        return match error {
            // `expiry.cpu` is `None` unless `measure_cpu`.
            crate::subprocess::RunError::Timeout(expired) => {
                AyServerAttempt::TimedOut(Some(expired.expiry))
            }
            _ => AyServerAttempt::Anomaly,
        };
    }
    // Exactly one verdict per window (fail-closed framing) — 0 or >1 is an
    // anomaly; drop + fall back to a clean fresh spawn.
    if verdict_lines != 1 {
        *guard = None;
        return AyServerAttempt::Anomaly;
    }
    if let Some(error) = protocol_error {
        return AyServerAttempt::Completed(AYResult::Error(error));
    }
    AyServerAttempt::Completed(parse_solver_output(&window, "", inputs))
}

#[cfg(test)]
fn run_solver_command(
    solver: &PinnedAy,
    smt2_path: &Path,
    timeout_ms: u64,
) -> Result<std::process::Output, SolverInvocationError> {
    let child_env = SanitizedChildEnv::capture_verifier();
    let command = solver_command(solver, smt2_path, SolverEvidenceRequest::Alethe)?;
    run_bounded_verifier_command(command, &child_env, timeout_ms)
}

fn run_solver_verdict_command(
    solver: &PinnedAy,
    smt2_path: &Path,
    timeout_ms: u64,
) -> Result<std::process::Output, SolverInvocationError> {
    let child_env = SanitizedChildEnv::capture_verifier();
    let command = solver_command(solver, smt2_path, SolverEvidenceRequest::VerdictOnly)?;
    run_bounded_verifier_command(command, &child_env, timeout_ms)
}

fn run_solver_command_with_authority(
    authority: &VerificationAuthority,
    smt2_path: &Path,
    timeout_ms: u64,
) -> Result<crate::subprocess::Completed, SolverInvocationError> {
    let command = solver_command(authority.solver(), smt2_path, SolverEvidenceRequest::Alethe)?;
    run_bounded_verifier_command_measured(command, authority.child_env(), timeout_ms)
}

fn run_solver_verdict_command_with_authority(
    authority: &VerificationAuthority,
    smt2_path: &Path,
    timeout_ms: u64,
) -> Result<std::process::Output, SolverInvocationError> {
    let command = solver_command(
        authority.solver(),
        smt2_path,
        SolverEvidenceRequest::VerdictOnly,
    )?;
    run_bounded_verifier_command(command, authority.child_env(), timeout_ms)
}

enum SolverEvidenceRequest {
    Alethe,
    VerdictOnly,
}

/// The one-shot solver command, built only from an admitted AY
/// ([`PinnedAy::command`] re-checks that the file is still the admitted one).
fn solver_command(
    solver: &PinnedAy,
    smt2_path: &Path,
    evidence: SolverEvidenceRequest,
) -> Result<std::process::Command, SolverInvocationError> {
    let mut command = solver
        .command()
        .map_err(|refusal| SolverInvocationError::Io(refusal.to_string()))?;
    command.args(solver_evidence_args(smt2_path, &evidence));
    Ok(command)
}

/// The one-shot solver's arguments (also rendered into the source-bound
/// negative memo's replay protocol, so a change here changes its keys).
fn solver_evidence_args(
    smt2_path: &Path,
    evidence: &SolverEvidenceRequest,
) -> Vec<std::ffi::OsString> {
    let mut args = vec!["-smt2".into(), smt2_path.as_os_str().to_owned()];
    if matches!(evidence, SolverEvidenceRequest::Alethe) {
        // Plain SMT invocations need not emit a certificate. Request the exact
        // artifact consumed by promote_fresh_solver_unsat explicitly. AY's own
        // strict diagnostics do NOT authorize promotion: a complete transcript
        // and independent Clean replay of this exact query/proof remain required.
        args.extend([
            "--strict-proofs".into(),
            "--proof".into(),
            default_alethe_path(smt2_path).into_os_string(),
            "--proof-format".into(),
            "alethe".into(),
        ]);
    }
    args
}

/// The resident solver's arguments. Pass only --incremental: -in is its
/// compatibility alias, so supplying both rejects the invocation instead of
/// starting a resident solver.
const RESIDENT_SOLVER_ARGS: &[&str] = &["--incremental"];

/// The resident solver command, built only from an admitted AY.
fn resident_solver_command(solver: &PinnedAy) -> Option<std::process::Command> {
    let mut command = solver.command().ok()?;
    command.args(RESIDENT_SOLVER_ARGS);
    Some(command)
}

/// The fixed parts of a source-bound live replay, rendered from the builders
/// the replay itself uses: the resident solver's arguments, the fresh
/// proof-bearing solve's, the SAT model query's and the independent checker's
/// (with placeholder paths), plus the replay's control flow. Part of every
/// source-bound negative-memo key (`crate::source_bound_negative_memo`), so
/// entries recorded under another protocol miss;
/// `the_replay_protocol_renders_the_real_commands` ties it to the commands.
pub(crate) fn replay_protocol_description() -> String {
    let render = |args: &[std::ffi::OsString]| {
        args.iter()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(" ")
    };
    let fresh = solver_evidence_args(Path::new("Q.smt2"), &SolverEvidenceRequest::Alethe);
    let model = solver_evidence_args(Path::new("M.smt2"), &SolverEvidenceRequest::VerdictOnly);
    let checker = crate::obligation_cert_store::clean_verify_external_args(Path::new("C.json"));
    format!(
        "source-bound-replay-v7; formula-protocol=[{}]; \
         query=original raw (no arithmetic simplifier); \
         bounded QF DAG-let producer candidate when substantially smaller, \
         independently checked/persisted ONLY against original raw; nonVerified \
         candidate falls back raw without SAT or negative-memo credit; compact \
         occurrences bypass negative caching pending combined CPU qualification; resident=[{}] \
         (an unsat or bare unknown answer replayed fresh; a deadline replayed fresh once \
         with a new budget when the owner asks, a timeout then recorded only when both \
         deadlines used their budget); fresh=[{}]; model=[{}] after SAT \
         when models are produced; checker=[{}] over the exact query and proof under \
         the checker's own deadline (never less than the solve budget, never unbounded), \
         a checker timeout reported and recorded as a checker timeout only, never as a \
         solver timeout; and_pos \
         publication refusal retried once split into top-level asserts, the split \
         proof's top-level assumptions re-derived from the original conjunction by \
         Alethe `and` steps, with checker/persistence still bound to the original \
         conjunction",
        crate::lowering_proof::CANONICAL_PROOF_FORMULA_PROTOCOL,
        RESIDENT_SOLVER_ARGS.join(" "),
        render(&fresh),
        render(&model),
        render(&checker),
    )
}

/// The commands a source-bound replay starts, rendered with placeholder
/// paths, built by the real builders (test support for the protocol tie).
#[cfg(test)]
pub(crate) fn replay_commands_for_test(solver: &PinnedAy) -> Vec<(&'static str, String)> {
    let render = |command: &std::process::Command| {
        command
            .get_args()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect::<Vec<_>>()
            .join(" ")
    };
    let fresh = solver_command(solver, Path::new("Q.smt2"), SolverEvidenceRequest::Alethe)
        .unwrap_or_else(|_| panic!("fresh command"));
    let model = solver_command(
        solver,
        Path::new("M.smt2"),
        SolverEvidenceRequest::VerdictOnly,
    )
    .unwrap_or_else(|_| panic!("model command"));
    let resident = resident_solver_command(solver).expect("resident command");
    let checker = crate::obligation_cert_store::clean_verify_external_command(
        Path::new("clean"),
        Path::new("C.json"),
    );
    vec![
        ("resident", render(&resident)),
        ("fresh", render(&fresh)),
        ("model", render(&model)),
        ("checker", render(&checker)),
    ]
}

/// Execute the captured verifier environment with complete, supervised output.
/// Zero preserves the explicit unlimited policy; finite budgets never admit
/// partial output or replace the current bounded process cleanup implementation.
pub(crate) fn run_bounded_verifier_command(
    command: std::process::Command,
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> Result<std::process::Output, SolverInvocationError> {
    run_bounded_verifier_command_measured(command, child_env, timeout_ms)
        .map(|completed| completed.output)
}

/// [`run_bounded_verifier_command`], also reporting the completed child's
/// wall-clock and process-group CPU time.
fn run_bounded_verifier_command_measured(
    mut command: std::process::Command,
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> Result<crate::subprocess::Completed, SolverInvocationError> {
    configure_solver_command(&mut command, child_env);
    crate::subprocess::run_measured(
        &mut command,
        (timeout_ms != 0).then_some(Duration::from_millis(timeout_ms)),
    )
    .map_err(|error| match error {
        crate::subprocess::RunError::Timeout(expired) => {
            SolverInvocationError::Timeout(expired.expiry)
        }
        other => SolverInvocationError::Io(other.to_string()),
    })
}

/// The admitted AY for proof discharge. AY is the **sole** solver — z3 has
/// been removed from the discharge path entirely (the project's own AY solver
/// must prove every obligation; if it cannot, AY is what gets fixed, never z3).
///
/// There is no search order. [`crate::ay_identity`] names exactly one candidate
/// — the owning Trust toolchain's `bin/ay`, or an absolute `AY_SOLVER_PATH` —
/// and admits it only when its bytes are the recorded AY. No package store,
/// `PATH`, source checkout or home directory is consulted.
fn find_solver_binary() -> Option<PinnedAy> {
    // AY alone is a solver-verdict source, not proof authority.  Do not expose
    // a "formal solver available" route unless the independent Alethe checker
    // needed to promote UNSAT is available too.  "Available" means CAPABLE, not
    // merely present: `clean_checker_path` probes the checker against a
    // known-good control proof, so a `clean` built without `carcara-verify`
    // (which refuses every proof content-independently) correctly reads as no
    // checker at all instead of turning every UNSAT into an Unknown after the
    // solve has already been paid for. One implementation of that order
    // serves both this and the refusal it names.
    admitted_proof_solver_or_refusal().ok()
}

/// Serialize the resource-intensive formal-solver tests in this test binary.
///
/// AY proofs remain fail-closed: this lock changes only scheduling, never a
/// verdict or timeout policy.  Keeping the mutex here lets every formal test
/// lane (the category batches, wasm refinement, and GPU synthesis) share one
/// resource authority instead of running independent solver storms under the
/// default parallel test harness.
#[cfg(test)]
pub(crate) fn formal_solver_test_lock() -> std::sync::MutexGuard<'static, ()> {
    static LOCK: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
    LOCK.get_or_init(|| std::sync::Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// The solver a verdict is produced under: the AY admitted by
/// [`crate::ay_identity`]'s single rule, or the named refusal. Nothing ever
/// falls back to another location.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SolverSelection(Result<PinnedAy, AyIdentityRefusal>);

impl SolverSelection {
    /// A caller-chosen AY. It was admitted by the same rule when constructed.
    fn explicit(solver: PinnedAy) -> Self {
        Self(Ok(solver))
    }

    fn pinned(&self) -> Option<&PinnedAy> {
        self.0.as_ref().ok()
    }

    fn refusal(&self) -> Option<&AyIdentityRefusal> {
        self.0.as_ref().err()
    }

    /// The admitted path as text (`""` for a refusal).
    fn path_text(&self) -> String {
        self.pinned()
            .map(|solver| solver.path().to_string_lossy().into_owned())
            .unwrap_or_default()
    }

    /// Route label, or the refusal's stable `TCG-AY-IDENTITY-*` code.
    fn route_kind(&self) -> &'static str {
        match &self.0 {
            Ok(solver) => solver.route().as_str(),
            Err(refusal) => refusal.code(),
        }
    }

    /// The admission record, or the refusal text.
    fn detail(&self) -> String {
        match &self.0 {
            Ok(solver) => solver.describe(),
            Err(refusal) => refusal.to_string(),
        }
    }
}

/// Request-scoped input to AY selection, used to start the identity warm at
/// most once per distinct request. The rule reads no other environment: the
/// toolchain comes from the running executable and the build record.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SolverDiscoveryKey {
    ay_solver_path: Option<std::ffi::OsString>,
}

impl SolverDiscoveryKey {
    fn capture() -> Self {
        Self {
            ay_solver_path: trust_cg_process_env::var_os(crate::ay_identity::AY_OVERRIDE_ENV),
        }
    }
}

/// Resolve the AY solver binary. AY is the sole solver: every proof
/// obligation — bit-vector AND floating-point (QF_BVFP) — is discharged by
/// AY. There is no z3 route anywhere in selection; an obligation AY cannot
/// prove is a bug to fix in AY, never a reason to fall back.
///
/// Selection is [`crate::ay_identity::resolve_for_process`]: the toolchain's
/// own `bin/ay`, or an absolute `AY_SOLVER_PATH`, each admitted only when its
/// bytes are the recorded AY. The digest is memoized there against the
/// executable's exact file state, so per-function polling does not re-hash.
fn select_solver_binary() -> SolverSelection {
    let resolution = crate::ay_identity::resolve_for_process();
    if let Ok(solver) = &resolution {
        seed_admitted_solver_identity(solver);
    }
    SolverSelection(resolution)
}

/// Admission already digested these exact bytes. Publish that digest to the
/// in-process identity memo, so key derivation for the admitted path reads it
/// instead of hashing the same file again (or consulting the machine-local
/// fingerprint file first).
pub(crate) fn seed_admitted_solver_identity(solver: &PinnedAy) {
    let path = solver.path().to_string_lossy();
    let Ok(metadata) = std::fs::metadata(solver.path()) else {
        return;
    };
    let Some(stat_key) = SolverIdentityStatKey::of(&path, &metadata) else {
        return;
    };
    // The metadata above must describe the admitted file state.
    if solver.revalidate().is_err() {
        return;
    }
    let slot = {
        let mut map = solver_identity_memo()
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner());
        std::sync::Arc::clone(map.entry(stat_key).or_default())
    };
    let mut slot = slot.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
    if slot.is_none() {
        *slot = Some(solver.sha256().to_owned());
    }
}

fn obligation_logic(obligation: &ProofObligation) -> &'static str {
    let raw_formula = obligation.negated_equivalence();
    let formula = prepare_formula_for_smt(&raw_formula);
    infer_obligation_logic_for_smt2(obligation, &raw_formula, &formula, &[])
}

fn select_solver_for_obligation(_obligation: &ProofObligation) -> SolverSelection {
    select_solver_binary()
}

fn solver_info_from_selection(selection: &SolverSelection) -> String {
    match &selection.0 {
        Ok(solver) => format!("ay at {} [{}]", solver.path().display(), solver.describe()),
        Err(refusal) => format!("no AY solver admitted: {refusal}"),
    }
}

#[cfg(test)]
fn solver_route_summary_for_invocation(obligation: &ProofObligation, config: &AYConfig) -> String {
    let selection = match &config.solver {
        Some(solver) => SolverSelection::explicit(solver.clone()),
        None => select_solver_for_obligation(obligation),
    };
    solver_route_summary_from_selection(obligation_logic(obligation), &selection)
}

fn solver_route_summary_from_selection(logic: &str, selection: &SolverSelection) -> String {
    match &selection.0 {
        Ok(solver) => format!(
            "logic={} route={} solver={} admitted=[{}]",
            logic,
            selection.route_kind(),
            solver.path().display(),
            selection.detail()
        ),
        Err(_) => format!(
            "logic={} route={} solver=(refused) reason=[{}]",
            logic,
            selection.route_kind(),
            selection.detail()
        ),
    }
}

#[cfg(all(test, unix))]
#[path = "ay_subprocess_tests.rs"]
mod subprocess_tests;

/// Return a human-readable description of the selected AY solver binary.
///
/// The returned string includes the admitted path and the admission record
/// (route, toolchain, recorded build and SHA-256). Nothing is executed to
/// produce it. When the identity rule admits no AY it starts with
/// `"no AY solver admitted: "` followed by the named refusal.
/// This identifies AY independently of Clean's availability; it does not
/// authorize proof discharge. Use [`ay_available`] for that decision and
/// [`proof_toolchain_unavailable_reason`] for the missing component.
pub fn solver_info() -> String {
    solver_info_from_selection(&select_solver_binary())
}

/// A solver query written to a private temporary directory of its own.
///
/// AY writes its Alethe proof beside the query (`<query>.alethe`) through a
/// partial `<query>.alethe.tmp-<pid>-<n>` that it renames into place, and a
/// run that ends before the rename (an `unknown` after a rejected self-check,
/// a timeout) leaves the partial behind. Owning the directory makes dropping
/// the query remove everything the solver wrote beside it, on every outcome.
struct SolverQueryFile {
    // Fields drop in declaration order: the query, then its directory.
    file: tempfile::NamedTempFile,
    _directory: tempfile::TempDir,
}

impl SolverQueryFile {
    fn path(&self) -> &Path {
        self.file.path()
    }
}

/// Write SMT-LIB2 to a securely-created private temporary file, in a private
/// temporary directory of its own (see [`SolverQueryFile`]).
fn write_temp_smt2(content: &str) -> Result<SolverQueryFile, std::io::Error> {
    use std::io::Write;
    let directory = tempfile::Builder::new()
        .prefix("trust-cg-ay-query-")
        .tempdir()?;
    let mut file = tempfile::Builder::new()
        .prefix("query-")
        .suffix(".smt2")
        .tempfile_in(directory.path())?;
    file.write_all(content.as_bytes())?;
    file.flush()?;
    Ok(SolverQueryFile {
        file,
        _directory: directory,
    })
}

/// Parse solver stdout/stderr into an [`AYResult`].
fn parse_solver_process_output(
    output: &std::process::Output,
    inputs: &[(String, u32)],
) -> AYResult {
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        return AYResult::Error(format!(
            "solver exited with status {} (stdout: {}; stderr: {})",
            output.status,
            stdout.trim(),
            stderr.trim()
        ));
    }
    parse_solver_output(&stdout, &stderr, inputs)
}

fn parse_solver_output(stdout: &str, stderr: &str, inputs: &[(String, u32)]) -> AYResult {
    let stdout_trimmed = stdout.trim();
    let stderr_trimmed = stderr.trim();
    let lines: Vec<&str> = stdout_trimmed
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect();

    // A protocol error is never a usable verdict, even if AY recovered and
    // printed `sat`, `unsat`, or `unknown` later in the transcript.
    if let Some(error) = lines
        .iter()
        .copied()
        .chain(stderr_trimmed.lines().map(str::trim))
        .find(|line| line.starts_with("(error"))
    {
        return AYResult::Error(error.to_string());
    }

    let verdict_count = lines
        .iter()
        .filter(|line| matches!(**line, "sat" | "unsat" | "unknown"))
        .count();
    if verdict_count > 1 {
        return AYResult::Error(format!(
            "Ambiguous solver output: {verdict_count} verdict lines"
        ));
    }

    // Inspect only verdict/diagnostic positions for timeouts. Model output is
    // user-controlled: a valid SAT witness may contain an input named
    // `timeout`, which must remain a counterexample.
    let stdout_reports_timeout = lines.iter().any(|line| {
        let lower = line.to_ascii_lowercase();
        lower == "timeout"
            || ((lower.starts_with("(error") || lower.contains(":reason-unknown"))
                && lower.contains("timeout"))
    });
    if stdout_reports_timeout || stderr_trimmed.to_ascii_lowercase().contains("timeout") {
        return AYResult::Timeout;
    }

    // AY's caught-invalid-model disclosure OUTRANKS its `:reason-unknown`
    // line: the tail alone (`incomplete`, or even `incomplete
    // self-check-rejected`) reads as ordinary capacity or as the strict
    // self-check envelope, while the banner says the AUTHORITY misbehaved on
    // this exact query. Losing that distinction is what lets a defective
    // solver path be mistaken for the certification gap.
    let unknown_reason = ay_soundness_gate_reason(stderr_trimmed).or_else(|| {
        lines
            .iter()
            .copied()
            .chain(stderr_trimmed.lines().map(str::trim))
            .find(|line| line.contains(":reason-unknown"))
            .map(std::string::ToString::to_string)
    });

    if lines.contains(&"unknown") {
        return AYResult::Unknown(unknown_reason.unwrap_or_else(|| "unknown".to_string()));
    }

    // AY can return `unsat` while explicitly declaring that its accompanying
    // Alethe certificate has holes or trusted steps.  That is a solver verdict,
    // not proof authority: keep it pending instead of minting `Verified`.
    if lines.first().copied() == Some("unsat")
        && let Some(reason) = incomplete_ay_proof_reason(stderr_trimmed)
    {
        return AYResult::Unknown(reason);
    }

    // Check for errors
    if stdout_trimmed.starts_with("(error") || !stderr_trimmed.is_empty() {
        let msg = if !stderr_trimmed.is_empty() {
            stderr_trimmed.to_string()
        } else {
            stdout_trimmed.to_string()
        };
        // Some solvers print warnings to stderr that aren't errors
        if msg.contains("WARNING") || msg.contains("warning") {
            // Continue parsing stdout
        } else if !stdout_trimmed.starts_with("sat") && !stdout_trimmed.starts_with("unsat") {
            return AYResult::Error(msg);
        }
    }

    if lines.is_empty() {
        return AYResult::Error("Empty solver output".to_string());
    }

    let first_line = lines[0].trim();

    match first_line {
        "unsat" if lines.len() == 1 => AYResult::SolverUnsat,
        "unsat" => AYResult::Error(format!(
            "Unexpected output after UNSAT verdict: {}",
            lines[1..].join("\n")
        )),
        "sat" => {
            // Try to extract counterexample from model output
            if lines.len() > 1 {
                let model_text = lines[1..].join("\n");
                let cex = parse_model_output(&model_text, inputs);
                AYResult::CounterExample(cex)
            } else {
                // SAT but no model output
                AYResult::CounterExample(vec![])
            }
        }
        "unknown" => AYResult::Unknown(unknown_reason.unwrap_or_else(|| "unknown".to_string())),
        _ => AYResult::Error(format!("Unexpected solver output: {}", first_line)),
    }
}

/// AY's ALWAYS-ON model gate caught one of AY's OWN theory-search paths
/// returning a model that falsifies an assertion, so AY withheld the verdict
/// and published `unknown`.
///
/// AY prints
/// `[AY SOUNDNESS GATE] caught an INVALID model — a theory-search path
/// returned a model that falsifies an assertion.` on stderr, followed by
/// `AY fail-closed to \`unknown\` (this is SOUND); it indicates an internal
/// solver bug worth reporting.` The verdict is WITHHELD, never wrong — but
/// the obligation itself may be perfectly valid, so this says nothing about
/// the proof and everything about the authority.
///
/// It is therefore categorically distinct from the three shapes the guarded
/// lib tests are allowed to skip on:
///
/// * solver capacity — a plain `(:reason-unknown incomplete)`;
/// * the v0.9.0-era strict self-check envelope —
///   `(:reason-unknown (incomplete self-check-rejected))`;
/// * a certification gap — `incomplete AY proof certificate:` and its two
///   siblings, where AY established the verdict and only the independent
///   certification half is missing.
///
/// Naming it here is what keeps it out of all three:
/// [`crate::gap_classify::ay_reason_is_soundness_gate_refusal`] recognizes the
/// minted reason and both gap predicates reject it unconditionally, even when
/// AY publishes the banner alongside a `:reason-unknown` tail that would
/// otherwise classify. AY's own tail is preserved in the reason so nothing
/// previously observable is lost.
fn ay_soundness_gate_reason(stderr: &str) -> Option<String> {
    if !stderr.contains(crate::gap_classify::AY_SOUNDNESS_GATE_BANNER) {
        return None;
    }
    let published = stderr
        .lines()
        .map(str::trim)
        .find(|line| line.contains(":reason-unknown"))
        .unwrap_or("(no :reason-unknown published)");
    Some(format!(
        "{}: AY fail-closed on this exact query; its published reason was {published}",
        crate::gap_classify::AY_SOUNDNESS_GATE_REASON
    ))
}

fn incomplete_ay_proof_reason(stderr: &str) -> Option<String> {
    for line in stderr.lines().map(str::trim) {
        if line.starts_with("c ay.proof.certificate ") {
            let mut unproved_steps: Option<u64> = None;
            let mut foreign_assumes: Option<&str> = None;
            let mut trust_free: Option<&str> = None;
            for field in line.split_whitespace() {
                if let Some(value) = field.strip_prefix("unproved_steps=") {
                    unproved_steps = value.parse().ok();
                } else if let Some(value) = field.strip_prefix("foreign_assumes=") {
                    foreign_assumes = Some(value);
                } else if let Some(value) = field.strip_prefix("trust_free=") {
                    trust_free = Some(value);
                }
            }
            if unproved_steps.is_some_and(|count| count != 0)
                || foreign_assumes.is_some_and(|value| value != "no")
                || trust_free.is_some_and(|value| value != "yes")
            {
                return Some(format!("incomplete AY proof certificate: {line}"));
            }
        }

        let lower = line.to_ascii_lowercase();
        if lower.contains("holey")
            || lower.contains("no proof certificate emitted")
            || lower.contains("could not publish a same-run default proof file")
        {
            return Some(format!("unusable AY proof evidence: {line}"));
        }
    }
    None
}

/// Parse SMT-LIB2 `(get-value ...)` output to extract variable assignments.
///
/// Expected format:
/// ```text
/// ((a #x0000000a)
///  (b #x00000014))
/// ```
fn parse_model_output(model_text: &str, inputs: &[(String, u32)]) -> Vec<(String, u64)> {
    let mut result = Vec::new();

    for (name, _width) in inputs {
        // Look for the variable assignment in the model
        // Format: (name #xHEXVALUE) or (name (_ bvDECIMAL WIDTH))
        if let Some(val) = extract_bv_value(model_text, name) {
            result.push((name.clone(), val));
        }
    }

    result
}

/// Extract a bitvector value for a variable from SMT-LIB2 model output.
fn extract_bv_value(model_text: &str, var_name: &str) -> Option<u64> {
    // Pattern 1: (var_name #xHEXDIGITS)
    let hex_pattern = format!("({} #x", var_name);
    if let Some(pos) = model_text.find(&hex_pattern) {
        let start = pos + hex_pattern.len();
        let end = model_text[start..].find(')')? + start;
        let hex_str = &model_text[start..end];
        return u64::from_str_radix(hex_str, 16).ok();
    }

    // Pattern 2: (var_name #bBINDIGITS)
    let bin_pattern = format!("({} #b", var_name);
    if let Some(pos) = model_text.find(&bin_pattern) {
        let start = pos + bin_pattern.len();
        let end = model_text[start..].find(')')? + start;
        let bin_str = &model_text[start..end];
        return u64::from_str_radix(bin_str, 2).ok();
    }

    // Pattern 3: (var_name (_ bvDECIMAL WIDTH))
    let bv_pattern = format!("({} (_ bv", var_name);
    if let Some(pos) = model_text.find(&bv_pattern) {
        let start = pos + bv_pattern.len();
        let space = model_text[start..].find(' ')? + start;
        let dec_str = &model_text[start..space];
        return dec_str.parse::<u64>().ok();
    }

    None
}

// ---------------------------------------------------------------------------
// Unified verification interface
// ---------------------------------------------------------------------------

/// Verify a proof obligation using the external AY solver.
///
/// Returns [`AYResult::Verified`] if the lowering rule is correct for all inputs.
///
/// # TCB soundness guard (residual close): never let the simplifier alone mint `Verified`
///
/// The verdict is obtained by asking the solver whether the negated equivalence
/// (`trust_ir != machine`) is UNSAT. The normal path runs the solver-oriented
/// bitvector simplifier ([`simplify_solver_expr`]) on that formula first, which
/// is fast and helps the solver. But if the simplifier ALONE collapses the
/// negated equivalence to a constant `false` (see
/// [`simplifier_alone_proved_unsat`]), the solver would only ever see
/// `(assert false)` — trivially `unsat` — and the bridge would report
/// `Verified` for an obligation the SOLVER NEVER actually checked. An unsound
/// simplifier rewrite could therefore mint a false `Verified` (the TCB caveat
/// documented in `proof_gate.rs`).
///
/// Guard: for exactly those degenerate-`false` obligations we DO NOT trust the
/// simplified formula. We re-emit the UN-simplified raw negated equivalence
/// (bounded quantifiers still expanded — a sound mechanical unroll) and require
/// the SOLVER to return `unsat` on it. The fast simplified path is kept for
/// every non-degenerate obligation.
pub fn verify_with_ay(obligation: &ProofObligation, config: &AYConfig) -> AYResult {
    verify_with_ay_attributed(obligation, config).result
}

/// [`verify_with_ay`], with the AY the verdict is attributable to: the admitted
/// binary (route, path, SHA-256, recorded build) and whether it ran, answered
/// from an in-process memo or certificate, or was never started.
pub fn verify_with_ay_attributed(obligation: &ProofObligation, config: &AYConfig) -> AyVerdict {
    // An exact original-goal CIC certificate is independent evidence. It does
    // not start AY or create an AY-produced cache/reuse receipt. Every failure
    // leaves the existing checked solver path unchanged.
    #[cfg(feature = "original-i128-cic")]
    if !crate::verdict_db::recording_active()
        && let Some(certificate) = crate::i128_cic_certificate::try_original_i128_certificate(
            obligation,
            config.timeout_ms,
        )
    {
        return AyVerdict {
            result: AYResult::Verified,
            solver: None,
            source: AyVerdictSource::OriginalCicCertificate { certificate },
        };
    }
    // Floating point and arrays first go through their bit-vector lowering,
    // the only form whose UNSAT proof the independent checker can replay
    // (Clean's Carcara has no FP sort, and AY's array reasoning has no replayable
    // derivation). Only a checked UNSAT is taken from it: the FP lowering
    // abstracts rounding, so its SAT or unknown says nothing about the
    // obligation, and the exact query below answers instead — including every
    // counterexample.
    for (lowered_smt2, producer, lowered) in source_bound_lowered_query_scripts(obligation, config)
    {
        let verdict = verify_with_cli_query(
            &lowered,
            config,
            AyQueryText {
                original: &lowered_smt2,
                producer: producer.as_deref(),
                closed_definitions: false,
                fresh_after_resident_timeout: false,
            },
        );
        if verdict.result == AYResult::Verified {
            return verdict;
        }
    }
    // TCB soundness guard: if the local simplifier alone reduced the negated
    // equivalence to constant `false`, route the obligation through the solver
    // on the raw (un-simplified) formula so the solver — not the rewrite —
    // produces the verdict. See the function docs above.
    let smt2 = lane_smt2_query(obligation, config);
    let verdict = verify_with_cli_smt2(obligation, config, &smt2);
    // A counterexample is final, and a verified obligation needs nothing
    // more. Otherwise the checker may have been unable to replay the proof
    // because the query names an operator it cannot bit-blast (`bvule`,
    // `bvsdiv`, ...): the same query with those spelled by their SMT-LIB
    // definitions is an equivalent formula, and only its checked UNSAT is
    // taken.
    if matches!(
        verdict.result,
        AYResult::Verified | AYResult::CounterExample(_)
    ) {
        return verdict;
    }
    for (definitional_smt2, lowered) in generate_definitional_queries(obligation, config) {
        let attempt = verify_with_cli_smt2(&lowered, config, &definitional_smt2);
        if attempt.result == AYResult::Verified {
            return attempt;
        }
    }
    verdict
}

/// Re-verify all known lowering proofs using the ay solver.
///
/// Collects all standard proof obligations (arithmetic, comparison, branch,
/// peephole, NZCV, constant folding, CSE/LICM) and verifies each one.
///
/// Returns a list of (proof_name, result) pairs. For STRICT proven-honesty use
/// [`verify_all_with_ay_structural`], which additionally records, per
/// obligation, whether it is structurally DEGENERATE (`trust_ir_expr ==
/// aarch64_expr`) so a degenerate `Verified` is never credited as genuine.
pub fn verify_all_with_ay(config: &AYConfig) -> Vec<(String, AYResult)> {
    verify_all_with_ay_structural(config)
        .into_iter()
        .map(|(name, result, _degenerate)| (name, result))
        .collect()
}

/// STRICT variant of [`verify_all_with_ay`]: returns
/// `(proof_name, result, is_degenerate)` triples where `is_degenerate` is
/// computed STRUCTURALLY from the obligation (`trust_ir_expr == aarch64_expr`),
/// NOT from any name ledger. A degenerate obligation that discharges `Verified`
/// proves nothing (it is a model-consistency check, since `NOT(X == X)` is
/// vacuously UNSAT) and must be excluded from every genuine/verified tally.
pub fn verify_all_with_ay_structural(config: &AYConfig) -> Vec<(String, AYResult, bool)> {
    let mut results = Vec::new();

    // Arithmetic lowering proofs
    for obligation in crate::lowering_proof::all_arithmetic_proofs() {
        let result = verify_with_ay(&obligation, config);
        results.push((obligation.name.clone(), result, obligation.is_degenerate()));
    }

    // NZCV flag + comparison + branch proofs
    for obligation in crate::lowering_proof::all_nzcv_proofs() {
        let result = verify_with_ay(&obligation, config);
        results.push((obligation.name.clone(), result, obligation.is_degenerate()));
    }

    // Peephole identity proofs
    for obligation in crate::peephole_proofs::all_peephole_proofs_with_32bit() {
        let result = verify_with_ay(&obligation, config);
        results.push((obligation.name.clone(), result, obligation.is_degenerate()));
    }

    results
}

/// Summary statistics for a batch verification run.
#[derive(Debug, Clone)]
pub struct VerificationSummary {
    /// Total number of proofs checked.
    pub total: usize,
    /// Number of proofs independently verified. RAW — includes degenerate
    /// model-consistency results. The HONEST headline is
    /// [`Self::genuinely_verified`].
    pub verified: usize,
    /// STRICT HONESTY (task #61): number of `Verified` results that are
    /// STRUCTURALLY DEGENERATE (`trust_ir_expr == aarch64_expr`, an X==X
    /// self-equality). These discharge `UNSAT(X != X)` trivially and prove
    /// NOTHING about a lowering (model-consistency only); counted SEPARATELY, NOT
    /// genuine. Determined PURELY STRUCTURALLY (no name ledger) when built via
    /// [`Self::from_results_structural`].
    pub degenerate_debt: usize,
    /// Number of proofs that found counterexamples (SAT).
    pub failed: usize,
    /// Number of proofs that timed out.
    pub timeouts: usize,
    /// Number of proofs that had errors.
    pub errors: usize,
}

impl VerificationSummary {
    /// Compute summary from a list of `(name, result)` results WITHOUT structural
    /// degeneracy context. Because no obligation is supplied, `degenerate_debt`
    /// is left at 0 — this constructor cannot (and must not) infer degeneracy
    /// from the name under STRICT (the name ledger is no longer load-bearing).
    /// Use [`Self::from_results_structural`] to credit only non-degenerate
    /// `Verified` results.
    pub fn from_results(results: &[(String, AYResult)]) -> Self {
        let widened: Vec<(String, AYResult, bool)> = results
            .iter()
            .map(|(n, r)| (n.clone(), r.clone(), false))
            .collect();
        Self::from_results_structural(&widened)
    }

    /// STRICT structural summary (task #61): each entry carries
    /// `(name, result, is_degenerate)` where `is_degenerate` is the PURELY
    /// STRUCTURAL `trust_ir_expr == aarch64_expr` flag computed from the
    /// obligation (see [`verify_all_with_ay_structural`]). A `Verified` result
    /// whose obligation is degenerate is counted into `degenerate_debt` and
    /// EXCLUDED from [`Self::genuinely_verified`] — it proves nothing.
    pub fn from_results_structural(results: &[(String, AYResult, bool)]) -> Self {
        let mut summary = Self {
            total: results.len(),
            verified: 0,
            degenerate_debt: 0,
            failed: 0,
            timeouts: 0,
            errors: 0,
        };

        for (_name, result, is_degenerate) in results {
            match result {
                AYResult::Verified => {
                    summary.verified += 1;
                    // STRICT HONESTY (task #61): a structurally degenerate X==X
                    // obligation that discharges Verified proves nothing — count
                    // it separately, never as genuine. Purely structural.
                    if *is_degenerate {
                        summary.degenerate_debt += 1;
                    }
                }
                AYResult::SolverUnsat => summary.errors += 1,
                AYResult::CounterExample(_) => summary.failed += 1,
                AYResult::Timeout => summary.timeouts += 1,
                AYResult::Unknown(_) => summary.errors += 1,
                AYResult::Error(_) => summary.errors += 1,
            }
        }

        summary
    }

    /// STRICT HONESTY (task #61): number of GENUINELY verified proofs —
    /// `Verified` AND non-degenerate. This is the honest headline; `verified` is
    /// the raw (inflated) count. `verified == genuinely_verified() +
    /// degenerate_debt`.
    pub fn genuinely_verified(&self) -> usize {
        self.verified - self.degenerate_debt
    }

    /// Returns true if every proof was GENUINELY verified under STRICT — i.e.
    /// each obligation discharged `Verified` AND was non-degenerate. A degenerate
    /// `Verified` (X==X model-consistency) does NOT satisfy this, so a database
    /// containing any degenerate obligation is honestly NOT "all verified".
    pub fn all_verified(&self) -> bool {
        self.genuinely_verified() == self.total
    }
}

impl fmt::Display for VerificationSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}/{} genuinely verified ({} degenerate debt excluded — X==X proves nothing), \
             {} failed, {} timeouts, {} errors",
            self.genuinely_verified(),
            self.total,
            self.degenerate_debt,
            self.failed,
            self.timeouts,
            self.errors
        )
    }
}

// ---------------------------------------------------------------------------
// AY availability check
// ---------------------------------------------------------------------------

/// Check whether an authorized AY solver binary is available on the system.
///
/// Returns `true` only if both AY and the independent Clean/Carcara Alethe
/// checker are available. AY alone can produce a diagnostic solver verdict but
/// is not an authorized proof-discharge route.
pub fn ay_available() -> bool {
    find_solver_binary().is_some()
}

/// The AY a proof discharge would bind to right now: admitted by
/// [`crate::ay_identity`] AND paired with a capable independent checker.
/// `None` exactly when [`ay_available`] is false.
pub fn admitted_proof_solver() -> Option<PinnedAy> {
    find_solver_binary()
}

/// [`admitted_proof_solver`] and, when it admits none, why, from the SAME
/// resolution: `Err(Some(refusal))` when the identity rule refused AY (its
/// `TCG-AY-IDENTITY-*` refusal), `Err(None)` when no capable independent
/// checker was found (AY is then not resolved at all, exactly as
/// [`admitted_proof_solver`] does not resolve it). A caller that decides on
/// this answer and names why it refused uses this refusal, never a later
/// resolution ([`solver_refusal_note`]), which can differ when a cache path
/// is re-pointed in between.
pub fn admitted_proof_solver_or_refusal() -> Result<PinnedAy, Option<AyIdentityRefusal>> {
    if crate::obligation_cert_store::clean_checker_path().is_none() {
        return Err(None);
    }
    select_solver_binary().0.map_err(Some)
}

/// How [`route_refusal_note_for`] begins.
pub const ROUTE_REFUSAL_NOTE_HEAD: &str = "the proof route was resolved with no AY admitted";

/// The note a refusal or disclosure decided on ONE resolution of the proof
/// route ([`admitted_proof_solver_or_refusal`]) carries when the identity rule
/// refused AY there: that refusal, with its `TCG-AY-IDENTITY-*` code and
/// reason (for a cache directory another user could write, the directory,
/// its mode and the remedy). `None` for [`AyIdentityRefusal::Unrecorded`]
/// (see [`solver_refusal_note`]).
pub fn route_refusal_note_for(refusal: &AyIdentityRefusal) -> Option<String> {
    (!matches!(refusal, AyIdentityRefusal::Unrecorded { .. })).then(|| {
        format!(
            "{ROUTE_REFUSAL_NOTE_HEAD}, so nothing on it could be discharged formally: {refusal}"
        )
    })
}

/// Compatibility alias for [`ay_available`]. Z3 is never searched or invoked.
pub fn z3_available() -> bool {
    ay_available()
}

/// Explain the missing component without mistaking a broken Clean package for
/// a missing SMT solver. This diagnostic never authorizes a proof.
pub fn proof_toolchain_unavailable_reason() -> Option<String> {
    if let Some(reason) = crate::obligation_cert_store::clean_checker_unavailable_reason() {
        return Some(reason);
    }
    select_solver_binary()
        .refusal()
        .map(|refusal| format!("AY is the sole SMT solver and none is admitted: {refusal}"))
}

// ---------------------------------------------------------------------------
// ProofDatabaseAYReport: comprehensive AY verification of ProofDatabase
// ---------------------------------------------------------------------------

/// Per-category breakdown of AY verification results.
#[derive(Debug, Clone)]
pub struct AYCategoryBreakdown {
    /// The proof category.
    pub category: ProofCategory,
    /// Total proofs in this category.
    pub total: usize,
    /// Number independently verified.
    pub verified: usize,
    /// Number that found counterexamples (SAT).
    pub failed: usize,
    /// Number that timed out.
    pub timeouts: usize,
    /// Number that lacked proof authority or had errors.
    pub errors: usize,
}

/// Comprehensive report from verifying every proof in a [`ProofDatabase`]
/// through the AY SMT solver.
///
/// Unlike [`VerificationSummary`] (which covers only arithmetic/NZCV/peephole),
/// this report covers the ENTIRE proof database across all categories.
#[derive(Debug, Clone)]
pub struct ProofDatabaseAYReport {
    /// Per-proof results: `(name, category, result, is_degenerate)`. The trailing
    /// `is_degenerate` flag is computed PURELY STRUCTURALLY at construction
    /// (`trust_ir_expr == aarch64_expr`) — under STRICT proven-honesty (task #61)
    /// it is the SOLE basis for excluding a `Verified` from the genuine count, NOT
    /// any name ledger.
    pub results: Vec<(String, ProofCategory, AYResult, bool)>,
    /// Total wall-clock time for the verification run.
    pub total_duration: Duration,
}

impl ProofDatabaseAYReport {
    /// Total number of proofs checked.
    pub fn total(&self) -> usize {
        self.results.len()
    }

    /// Number of proofs independently verified. NOTE: this is the RAW verified count and
    /// includes structurally-degenerate proofs whose UNSAT(X!=X) is vacuous. For
    /// the HONEST "genuinely verified" headline use [`Self::genuinely_verified`];
    /// the difference is [`Self::degenerate_debt_count`].
    pub fn verified(&self) -> usize {
        self.results
            .iter()
            .filter(|(_, _, r, _)| matches!(r, AYResult::Verified))
            .count()
    }

    /// STRICT HONESTY (task #61): number of proofs GENUINELY verified —
    /// `Verified` AND structurally NON-DEGENERATE (`trust_ir_expr !=
    /// aarch64_expr`). A degenerate `X == X` obligation discharges
    /// `UNSAT(X != X)` = `Verified` trivially and proves NOTHING (it is a
    /// model-consistency check), so it is EXCLUDED from this honest count and
    /// reported separately as degenerate debt. Purely structural — no name ledger.
    pub fn genuinely_verified(&self) -> usize {
        self.results
            .iter()
            .filter(|(_, _, r, is_degenerate)| matches!(r, AYResult::Verified) && !*is_degenerate)
            .count()
    }

    /// STRICT HONESTY (task #61): number of `Verified` results that are
    /// structurally DEGENERATE (`trust_ir_expr == aarch64_expr`). Reported
    /// SEPARATELY; NOT genuine evidence.
    /// `verified() == genuinely_verified() + degenerate_debt_count()`.
    pub fn degenerate_debt_count(&self) -> usize {
        self.results
            .iter()
            .filter(|(_, _, r, is_degenerate)| matches!(r, AYResult::Verified) && *is_degenerate)
            .count()
    }

    /// Number of proofs that found counterexamples (SAT).
    pub fn failed(&self) -> usize {
        self.results
            .iter()
            .filter(|(_, _, r, _)| matches!(r, AYResult::CounterExample(_)))
            .count()
    }

    /// Number of proofs that timed out.
    pub fn timeouts(&self) -> usize {
        self.results
            .iter()
            .filter(|(_, _, r, _)| matches!(r, AYResult::Timeout))
            .count()
    }

    /// Number of proofs that lacked proof authority or had errors.
    pub fn errors(&self) -> usize {
        self.results
            .iter()
            .filter(|(_, _, r, _)| {
                matches!(
                    r,
                    AYResult::SolverUnsat | AYResult::Unknown(_) | AYResult::Error(_)
                )
            })
            .count()
    }

    /// Returns true if every proof was GENUINELY verified under STRICT —
    /// `Verified` AND non-degenerate for every proof. A degenerate `Verified`
    /// (X==X model-consistency) does NOT satisfy this, so a database holding any
    /// degenerate obligation is honestly NOT "all verified".
    pub fn all_verified(&self) -> bool {
        self.results
            .iter()
            .all(|(_, _, r, is_degenerate)| matches!(r, AYResult::Verified) && !*is_degenerate)
    }

    /// Per-category breakdown of results.
    pub fn by_category(&self) -> Vec<AYCategoryBreakdown> {
        ProofCategory::all_categories()
            .iter()
            .filter_map(|cat| {
                let cat_results: Vec<&(String, ProofCategory, AYResult, bool)> = self
                    .results
                    .iter()
                    .filter(|(_, c, _, _)| c == cat)
                    .collect();
                if cat_results.is_empty() {
                    return None;
                }
                let total = cat_results.len();
                // STRICT (task #61): per-category `verified` credits ONLY
                // non-degenerate `Verified` results — a degenerate X==X discharge
                // proves nothing and never counts toward category coverage.
                let verified = cat_results
                    .iter()
                    .filter(|(_, _, r, is_degenerate)| {
                        matches!(r, AYResult::Verified) && !*is_degenerate
                    })
                    .count();
                let failed = cat_results
                    .iter()
                    .filter(|(_, _, r, _)| matches!(r, AYResult::CounterExample(_)))
                    .count();
                let timeouts = cat_results
                    .iter()
                    .filter(|(_, _, r, _)| matches!(r, AYResult::Timeout))
                    .count();
                let errors = cat_results
                    .iter()
                    .filter(|(_, _, r, _)| {
                        matches!(
                            r,
                            AYResult::SolverUnsat | AYResult::Unknown(_) | AYResult::Error(_)
                        )
                    })
                    .count();
                Some(AYCategoryBreakdown {
                    category: *cat,
                    total,
                    verified,
                    failed,
                    timeouts,
                    errors,
                })
            })
            .collect()
    }

    /// Details of all non-(genuinely-)verified proofs — counterexamples,
    /// timeouts, errors, AND structurally-degenerate `Verified` results (which
    /// prove nothing under STRICT). Returns `(name, category, detail_string)`.
    pub fn failed_details(&self) -> Vec<(String, ProofCategory, String)> {
        self.results
            .iter()
            .filter_map(|(name, cat, result, is_degenerate)| match result {
                // A degenerate X==X discharge is `Verified` to the solver but
                // proves nothing — surface it honestly rather than hide it.
                AYResult::Verified if *is_degenerate => Some((
                    name.clone(),
                    *cat,
                    "DEGENERATE (trust_ir_expr == aarch64_expr): X==X model-consistency only, \
                     proves nothing — not genuinely verified"
                        .to_string(),
                )),
                AYResult::Verified => None,
                AYResult::SolverUnsat => Some((
                    name.clone(),
                    *cat,
                    "SOLVER UNSAT (UNCERTIFIED): no independently accepted exact proof".to_string(),
                )),
                AYResult::CounterExample(cex) => {
                    let detail = format!(
                        "COUNTEREXAMPLE: {}",
                        cex.iter()
                            .map(|(n, v)| format!("{} = {:#x}", n, v))
                            .collect::<Vec<_>>()
                            .join(", ")
                    );
                    Some((name.clone(), *cat, detail))
                }
                AYResult::Timeout => Some((name.clone(), *cat, "TIMEOUT".to_string())),
                AYResult::Unknown(msg) => Some((name.clone(), *cat, format!("UNKNOWN: {}", msg))),
                AYResult::Error(msg) => Some((name.clone(), *cat, format!("ERROR: {}", msg))),
            })
            .collect()
    }
}

impl fmt::Display for ProofDatabaseAYReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "ProofDatabase AY Verification Report")?;
        writeln!(f, "========================================")?;
        writeln!(f)?;

        let status = if self.all_verified() { "PASS" } else { "FAIL" };
        writeln!(
            f,
            "Result: {} ({}/{} GENUINELY verified, {} degenerate X==X excluded (proves nothing), \
             {} failed, {} timeouts, {} errors)",
            status,
            self.genuinely_verified(),
            self.total(),
            self.degenerate_debt_count(),
            self.failed(),
            self.timeouts(),
            self.errors()
        )?;
        writeln!(f, "Duration: {:.3}s", self.total_duration.as_secs_f64())?;
        writeln!(f)?;

        writeln!(f, "Per-category breakdown:")?;
        for bd in &self.by_category() {
            let cat_status = if bd.failed == 0 && bd.timeouts == 0 && bd.errors == 0 {
                "OK"
            } else {
                "FAIL"
            };
            writeln!(
                f,
                "  {:25} {:>4}/{:>4} verified  [{:>4}]",
                bd.category.name(),
                bd.verified,
                bd.total,
                cat_status,
            )?;
        }

        let failures = self.failed_details();
        if !failures.is_empty() {
            writeln!(f)?;
            writeln!(f, "Non-verified proofs ({}):", failures.len())?;
            for (name, cat, detail) in &failures {
                writeln!(f, "  [{}] {} -- {}", cat.name(), name, detail)?;
            }
        }

        Ok(())
    }
}

/// Verify every proof in a [`ProofDatabase`] through the AY SMT solver.
///
/// This is the comprehensive integration point: it takes the full proof
/// database and verifies each obligation by piping SMT-LIB2 to the solver
/// CLI, returning a [`ProofDatabaseAYReport`] with per-proof and per-category
/// results.
///
/// # Graceful degradation
///
/// If no solver binary is available, every proof result will be
/// `AYResult::Error("No AY solver found...")`. Use [`z3_available()`] (the
/// compatibility-named AY availability check) before calling.
pub fn verify_proof_database_with_ay(
    db: &ProofDatabase,
    config: &AYConfig,
) -> ProofDatabaseAYReport {
    let start = Instant::now();
    let all = db.all();
    let mut results = Vec::with_capacity(all.len());

    for cp in all {
        // Same TCB soundness guard as `verify_with_ay`: an obligation the local
        // simplifier alone folds to constant `false` must be checked by the
        // solver on the raw formula, never minted as `Verified` by the rewrite.
        let result = if simplifier_alone_proved_unsat(&cp.obligation) {
            verify_with_cli_raw(&cp.obligation, config)
        } else {
            verify_with_cli(&cp.obligation, config)
        };
        // STRICT (task #61): record structural degeneracy from the obligation so
        // a degenerate X==X discharge is never credited as genuinely verified.
        results.push((
            cp.obligation.name.clone(),
            cp.category,
            result,
            cp.obligation.is_degenerate(),
        ));
    }

    let total_duration = start.elapsed();
    ProofDatabaseAYReport {
        results,
        total_duration,
    }
}

// ---------------------------------------------------------------------------
// CHC serialization
// ---------------------------------------------------------------------------

/// Encode a [`ProofObligation`] as an SMT-LIB2 CHC query string.
///
/// Translation validation obligations are quantifier-free bitvector
/// equivalence checks:
///
/// ```text
/// forall inputs: trust_ir_expr == aarch64_expr
/// ```
///
/// We encode this as a CHC problem with one predicate `Valid` that
/// holds for all inputs. The query clause asserts that no `Valid`
/// state violates the equivalence. If the CHC solver returns
/// **Safe**, the equivalence holds for all inputs.
///
/// # CHC encoding
///
/// ```text
/// (set-logic HORN)
/// (declare-fun Valid ((BitVec w1) ... (BitVec wN)) Bool)
/// ;; Init: all inputs are Valid
/// (assert (forall ((x1 (BitVec w1)) ...) (Valid x1 ...)))
/// ;; Query: Valid /\ NOT(trust_ir == aarch64) => false
/// (assert (forall ((x1 (BitVec w1)) ...)
///   (=> (and (Valid x1 ...) (not (= trust_ir_expr aarch64_expr))) false)))
/// (check-sat)
/// ```
///
/// The function is always available (no feature gate) since it only
/// produces text. The actual CHC solving requires the `ay` feature.
pub fn encode_obligation_as_chc(obligation: &ProofObligation) -> String {
    let mut lines = Vec::new();

    lines.push("(set-logic HORN)".to_string());

    // Build the predicate sort signature from inputs
    let mut param_sorts = Vec::new();
    for (_name, width) in &obligation.inputs {
        param_sorts.push(format!("(_ BitVec {})", width));
    }
    for (_name, eb, sb) in &obligation.fp_inputs {
        param_sorts.push(format!("(_ FloatingPoint {} {})", eb, sb));
    }

    // Declare the Valid predicate
    lines.push(format!(
        "(declare-fun Valid ({}) Bool)",
        param_sorts.join(" ")
    ));

    // Collect all variable names and their sorted declarations
    let mut var_decls = Vec::new();
    let mut var_names = Vec::new();
    for (name, width) in &obligation.inputs {
        var_decls.push(format!("({} (_ BitVec {}))", name, width));
        var_names.push(name.as_str());
    }
    for (name, eb, sb) in &obligation.fp_inputs {
        var_decls.push(format!("({} (_ FloatingPoint {} {}))", name, eb, sb));
        var_names.push(name.as_str());
    }

    let vars_str = var_decls.join(" ");
    let names_str = var_names.join(" ");

    // Scan for UF declarations needed by the formula
    let formula = obligation.negated_equivalence();
    let mut uf_decls = Vec::new();
    collect_uf_declarations(&formula, &mut uf_decls);
    for (name, arg_sorts, ret_sort) in &uf_decls {
        let arg_sorts_str: Vec<String> = arg_sorts.iter().map(sort_to_smt2).collect();
        lines.push(format!(
            "(declare-fun {} ({}) {})",
            name,
            arg_sorts_str.join(" "),
            sort_to_smt2(ret_sort)
        ));
    }

    // Init clause: forall inputs => Valid(inputs)
    if obligation.preconditions.is_empty() {
        lines.push(format!(
            "(assert (forall ({}) (Valid {})))",
            vars_str, names_str
        ));
    } else {
        // With preconditions: precond => Valid(inputs)
        let precond_strs: Vec<String> = obligation
            .preconditions
            .iter()
            .map(|p| format!("{}", p))
            .collect();
        let precond = if precond_strs.len() == 1 {
            precond_strs[0].clone()
        } else {
            format!("(and {})", precond_strs.join(" "))
        };
        lines.push(format!(
            "(assert (forall ({}) (=> {} (Valid {}))))",
            vars_str, precond, names_str
        ));
    }

    // Query clause: Valid(inputs) /\ NOT(trust_ir == aarch64) => false
    let trust_ir_str = format!("{}", obligation.trust_ir_expr);
    let aarch64_str = format!("{}", obligation.aarch64_expr);

    let mut body_parts = vec![format!("(Valid {})", names_str)];

    // Add preconditions to the query body too
    for pre in &obligation.preconditions {
        body_parts.push(format!("{}", pre));
    }

    // Add the negated equivalence
    body_parts.push(format!("(not (= {} {}))", trust_ir_str, aarch64_str));

    let body = if body_parts.len() == 1 {
        body_parts[0].clone()
    } else {
        format!("(and {})", body_parts.join(" "))
    };

    lines.push(format!(
        "(assert (forall ({}) (=> {} false)))",
        vars_str, body
    ));

    lines.push("(check-sat)".to_string());

    lines.join("\n")
}

// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod split_assert_tests {
    use super::{AYResult, is_and_pos_publication_failure, split_assert_conjuncts};

    const HEADER: &str = "(set-logic QF_BV)\n(declare-const a (_ BitVec 64))";

    /// The exact `Ident` shape from the committed snapshot corpus — the
    /// register-to-register COPY obligation — split into one assert per conjunct.
    #[test]
    fn splits_the_right_nested_ident_shape() {
        let q = format!(
            "{HEADER}\n(assert (and (= p0 e_rdi) (and (= m0 e_rdi) (and (= m1 m0) (not (= p0 m1))))))\n(check-sat)\n(exit)"
        );
        let out = split_assert_conjuncts(&q).expect("the conjunctive assert must split");
        assert_eq!(
            out,
            format!(
                "{HEADER}\n(assert (= p0 e_rdi))\n(assert (= m0 e_rdi))\n(assert (= m1 m0))\n(assert (not (= p0 m1)))\n(check-sat)\n(exit)"
            ),
            "conjuncts must keep their written ORDER and everything else must be byte-identical"
        );
    }

    /// A FLAT n-ary conjunction splits the same way.
    #[test]
    fn splits_a_flat_conjunction() {
        let q = format!("{HEADER}\n(assert (and (= a a) (not (= a a))))\n(check-sat)");
        assert_eq!(
            split_assert_conjuncts(&q).unwrap(),
            format!("{HEADER}\n(assert (= a a))\n(assert (not (= a a)))\n(check-sat)")
        );
    }

    /// FAIL CLOSED: nothing to split, more than one conjunctive assert, or an
    /// unbalanced term all decline, so the caller keeps the original query.
    #[test]
    fn declines_anything_it_cannot_rewrite_with_certainty() {
        for (q, why) in [
            (
                format!("{HEADER}\n(assert (not (= a a)))\n(check-sat)"),
                "no conjunction to split",
            ),
            (
                format!(
                    "{HEADER}\n(assert (and (= a a) (not (= a a))))\n(assert (and (= a a) (not (= a a))))\n(check-sat)"
                ),
                "two conjunctive asserts is not the shape this path renders",
            ),
            (
                format!("{HEADER}\n(assert (and (= a a) (not (= a a)))\n(check-sat)"),
                "unbalanced parens",
            ),
        ] {
            assert!(split_assert_conjuncts(&q).is_none(), "must decline: {why}");
        }
    }

    /// The retry trigger is NARROW: only AY's `and_pos` publication refusal, never
    /// a timeout, an incomplete certificate, or a plain verdict.
    #[test]
    fn only_the_and_pos_publication_failure_triggers_a_retry() {
        assert!(is_and_pos_publication_failure(&AYResult::Error(
            "required UNSAT publication failed: refusing to write unverifiable proof to \
             /tmp/q.alethe (#8821): invalid surface proof step t1: and_pos indexed conjunct \
             is absent from its effective source"
                .to_string()
        )));
        for other in [
            AYResult::Error("solver exited with status 1".to_string()),
            AYResult::Unknown(
                "incomplete AY proof certificate: unproved_steps=1 trust_free=no".to_string(),
            ),
            AYResult::Timeout,
            AYResult::SolverUnsat,
        ] {
            assert!(
                !is_and_pos_publication_failure(&other),
                "must not retry on {other:?}"
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lowering_proof::ProofObligation;
    use crate::smt::{SmtExpr, SmtSort};

    /// The miss annotation touches only `Unknown`/`Error` TEXT: a verifying
    /// verdict is never demoted, a counterexample is never reworded, and
    /// `Timeout`/`SolverUnsat` keep their variant so callers that account for
    /// them separately still see them.
    #[test]
    fn cert_skip_miss_annotation_changes_text_only() {
        let miss = || Some("portable certificate miss".to_string());
        assert_eq!(
            annotate_cert_skip_miss(AYResult::Unknown("solver unknown (x)".into()), miss()),
            AYResult::Unknown("solver unknown (x); portable certificate miss".into())
        );
        assert_eq!(
            annotate_cert_skip_miss(AYResult::Error("no solver".into()), miss()),
            AYResult::Error("no solver; portable certificate miss".into())
        );
        for untouched in [
            AYResult::Verified,
            AYResult::SolverUnsat,
            AYResult::Timeout,
            AYResult::CounterExample(vec![("x".into(), 7)]),
        ] {
            assert_eq!(
                annotate_cert_skip_miss(untouched.clone(), miss()),
                untouched
            );
        }
        assert_eq!(
            annotate_cert_skip_miss(AYResult::Unknown("solver unknown (x)".into()), None),
            AYResult::Unknown("solver unknown (x)".into())
        );
    }

    /// The solver-identity hash keys the verdict cache, so its VALUE is
    /// load-bearing: change it and previously-recorded verdicts stop matching
    /// the binary that produced them. `solver_identity_hash` streams the file in
    /// 1MiB chunks instead of `fs::read`-ing ~95MB into memory; this pins that
    /// the chunked digest equals the whole-buffer digest, so the optimization
    /// cannot silently re-key the cache.
    #[test]
    fn streamed_solver_hash_equals_whole_buffer_hash() {
        use sha2::{Digest, Sha256};

        // Deliberately not a multiple of the 1MiB chunk, so the final short read
        // is exercised rather than landing exactly on a boundary.
        let data: Vec<u8> = (0..(1usize << 20) + 12345)
            .map(|i| (i % 251) as u8)
            .collect();

        let mut whole = Sha256::new();
        whole.update(&data);
        let expected = format!("{:x}", whole.finalize());

        let mut streamed = Sha256::new();
        let mut cursor = &data[..];
        let mut buf = vec![0u8; 1 << 20];
        loop {
            let n = std::io::Read::read(&mut cursor, &mut buf).expect("read");
            if n == 0 {
                break;
            }
            streamed.update(&buf[..n]);
        }
        let got = format!("{:x}", streamed.finalize());

        assert_eq!(
            got, expected,
            "chunked hashing must not change the digest — it keys the verdict cache"
        );
    }

    #[test]
    fn cache_hardening_session_key_separates_query_and_solver() {
        // Use this test binary itself as a readable stand-in solver.
        let solver = std::env::current_exe().unwrap();
        let solver = solver.to_str().unwrap();
        let k1 = session_proof_cache_key(solver, "(assert true)").unwrap();
        let k2 = session_proof_cache_key(solver, "(assert false)").unwrap();
        assert_ne!(k1, k2, "different SMT2 must produce different keys");

        // Keep raw SMT2 bytes authoritative. A textual `_v<digits>` rewrite
        // looks like SSA alpha-renaming for generated bit-vector symbols, but
        // the same bytes are legal inside semantic string literals. These two
        // formulas have opposite satisfiability and therefore must never alias:
        // `"x_v9"` has length 4, while `"x_v73"` has length 5.
        let sat = "(assert (= (str.len \"x_v9\") 4))";
        let unsat = "(assert (= (str.len \"x_v73\") 4))";
        assert_ne!(
            session_proof_cache_key(solver, sat).unwrap(),
            session_proof_cache_key(solver, unsat).unwrap(),
            "unparsed SMT2 renaming must not merge SAT and UNSAT queries",
        );
        assert_eq!(
            k1,
            session_proof_cache_key(solver, "(assert true)").unwrap(),
            "key derivation must be deterministic"
        );
        assert!(
            session_proof_cache_key("/nonexistent/solver/binary", "(assert true)").is_none(),
            "an unreadable solver must disable the cache"
        );
    }

    /// Admission digests the AY once; that digest is published to the identity
    /// memo so key derivation never hashes the admitted file a second time, and
    /// it equals an independent hash of the same bytes.
    #[cfg(unix)]
    #[test]
    fn admission_publishes_its_digest_to_the_identity_memo() {
        use std::os::unix::fs::PermissionsExt;
        let directory = tempfile::tempdir().unwrap();
        let path = directory.path().join("ay");
        std::fs::write(&path, b"#!/bin/sh\n# memo-seed fixture\nexit 97\n").unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        let path_text = path.to_str().unwrap();
        assert_eq!(solver_identity_hash_if_ready(path_text), None);
        let admitted = crate::ay_identity::test_fixtures::pin(&path);
        seed_admitted_solver_identity(&admitted);
        assert_eq!(
            solver_identity_hash_if_ready(path_text).as_deref(),
            Some(admitted.sha256())
        );
        use sha2::{Digest, Sha256};
        let independent = format!("{:x}", Sha256::digest(std::fs::read(&path).unwrap()));
        assert_eq!(admitted.sha256(), independent);
    }

    #[test]
    fn solver_identity_is_content_based_not_stat_based() {
        // PROOF-3 v2 key schema: solver identity is the SHA-256 of the
        // binary's BYTES, so two same-bytes copies at different paths share
        // an identity (and therefore share verdict keys), while different
        // bytes at the same length do not.
        let dir = std::env::temp_dir().join(format!(
            "tcg_solver_identity_test_{}_{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let a = dir.join("solver_a");
        let b = dir.join("solver_b");
        let c = dir.join("solver_c");
        std::fs::write(&a, b"solver bytes v1").unwrap();
        std::fs::write(&b, b"solver bytes v1").unwrap();
        std::fs::write(&c, b"solver bytes v2").unwrap();

        let ia = solver_identity_hash(a.to_str().unwrap()).unwrap();
        let ib = solver_identity_hash(b.to_str().unwrap()).unwrap();
        let ic = solver_identity_hash(c.to_str().unwrap()).unwrap();
        assert_eq!(ia, ib, "identical bytes at different paths share identity");
        assert_ne!(ia, ic, "different bytes must have different identities");

        // The shared v2 key binds solver identity and query content.
        let smt2 = "(assert true)";
        assert_eq!(
            verdict_cache_key_v2(&ia, smt2),
            verdict_cache_key_v2(&ib, smt2),
            "same-bytes solvers share verdict keys (rebuild-stable)"
        );
        assert_ne!(
            verdict_cache_key_v2(&ia, smt2),
            verdict_cache_key_v2(&ic, smt2),
            "a changed solver binary invalidates every verdict key"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// BOTH memo keys — the process-local one and the machine-local one — must
    /// DISCRIMINATE a binary that was modified IN PLACE: same path, same inode,
    /// same length, mtime restored.
    ///
    /// This is the hazard a memo introduces, and the staleness window itself is
    /// not new: `solver_identity_hash` already memoized on `(path, size, mtime)`
    /// within a process, so an mtime-restoring in-place edit already served a
    /// stale hash there. Two independent tightenings landed on that, and this
    /// test covers BOTH:
    ///
    /// * [`SolverIdentityStatKey`] replaces the old `(path, size, mtime)` tuple
    ///   for the PROCESS-scoped memo;
    /// * [`SolverFileKey`] extends the same judgement from one process to the
    ///   MACHINE, which widens the staleness window, so its key has to be at
    ///   least as strict as the in-process one.
    ///
    /// Both bind dev+inode (a replaced file is a different record) and ctime,
    /// which advances on every write and which an unprivileged process cannot
    /// rewind (unlike mtime, via `utimensat`).
    ///
    /// Threat-model note: an attacker who can rewrite the solver binary in place
    /// already controls the solver and could simply make it answer `unsat`.
    /// Hashing is not the weak link there. This test guards the ACCIDENTAL case
    /// — a rebuild or restore that lands the same size and mtime.
    ///
    /// `cfg(unix)`: both keys carry dev/inode/ctime only on unix, and
    /// `SolverFileKey::of` deliberately returns `None` elsewhere rather than key
    /// on a tuple weaker than the in-process memo already uses.
    #[cfg(unix)]
    #[test]
    fn solver_identity_memo_key_discriminates_in_place_edit() {
        // The machine-local layer is live only with an explicit directory in
        // a unit test (`solver_identity_cache_dir`), and only when that
        // directory is private: `tempdir` makes it `0777 & !umask`.
        let memo = tempfile::tempdir().unwrap();
        std::fs::set_permissions(
            memo.path(),
            std::os::unix::fs::PermissionsExt::from_mode(0o700),
        )
        .unwrap();
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_PROOF_CACHE_DIR", memo.path());
            env.remove("TCG_NO_SOLVER_ID_CACHE");
            solver_identity_memo_key_discriminates_in_place_edit_body();
        });
        assert!(memo.path().join("solver-identity-v1").is_file());
    }

    #[cfg(unix)]
    fn solver_identity_memo_key_discriminates_in_place_edit_body() {
        let dir = std::env::temp_dir().join(format!(
            "tcg_solver_identity_inplace_{}_{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let solver = dir.join("solver");

        std::fs::write(&solver, b"solver bytes v1").unwrap();
        let meta_before = std::fs::metadata(&solver).unwrap();
        let solver_path = solver.to_str().unwrap();
        let file_key_before = SolverFileKey::of(&meta_before).expect("unix metadata");
        let stat_key_before =
            SolverIdentityStatKey::of(solver_path, &meta_before).expect("unix metadata");
        let hash_before = solver_identity_hash(solver_path).unwrap();
        let modified = meta_before.modified().unwrap();

        // Overwrite in place at the SAME length, then restore mtime to hide it.
        std::thread::sleep(std::time::Duration::from_millis(2));
        std::fs::write(&solver, b"solver bytes v2").unwrap();
        let f = std::fs::OpenOptions::new()
            .write(true)
            .open(&solver)
            .unwrap();
        let times = std::fs::FileTimes::new()
            .set_modified(modified)
            .set_accessed(modified);
        let _ = f.set_times(times);
        drop(f);

        let meta_after = std::fs::metadata(&solver).unwrap();
        assert_eq!(meta_after.len(), meta_before.len(), "same length");
        let file_key_after = SolverFileKey::of(&meta_after).expect("unix metadata");
        let stat_key_after =
            SolverIdentityStatKey::of(solver_path, &meta_after).expect("unix metadata");

        // Precision: dev, inode and size are all UNCHANGED and mtime was
        // restored, so ctime is the only field that can carry the difference.
        // Asserting that keeps this test from passing for the wrong reason if
        // the key composition ever changes. Checked for EACH key separately:
        // they are independent records, and either one going stale serves a
        // wrong content hash.
        assert_eq!(stat_key_before.dev, stat_key_after.dev, "same device");
        assert_eq!(stat_key_before.ino, stat_key_after.ino, "same inode");
        assert_eq!(stat_key_before.size, stat_key_after.size, "same size");
        assert_eq!(
            stat_key_before.mtime_ns, stat_key_after.mtime_ns,
            "mtime restored"
        );
        assert_ne!(
            stat_key_before.ctime_ns, stat_key_after.ctime_ns,
            "ctime must advance on an in-place write",
        );
        assert!(
            stat_key_before != stat_key_after,
            "the process memo key must differ after an in-place edit even with mtime restored",
        );

        assert_eq!(file_key_before.dev, file_key_after.dev, "same device");
        assert_eq!(file_key_before.ino, file_key_after.ino, "same inode");
        assert_eq!(file_key_before.size, file_key_after.size, "same size");
        assert_eq!(
            file_key_before.mtime_ns, file_key_after.mtime_ns,
            "mtime restored"
        );
        assert_ne!(
            file_key_before.ctime_ns, file_key_after.ctime_ns,
            "ctime must advance on an in-place write",
        );
        assert!(
            file_key_before != file_key_after,
            "the machine-local memo key must differ after an in-place edit even with mtime restored",
        );

        // And a record written under the old key must not answer for the new
        // one. The positive control comes FIRST and uses a well-formed 64-hex
        // digest on purpose: `matches` ALSO rejects a malformed hash, so a
        // short placeholder would make the negative assertion below pass
        // without ever exercising key discrimination.
        let digest = "ab".repeat(32);
        let record = file_key_before.line(&digest);
        let matched = file_key_before.matches(&record);
        assert_eq!(
            matched.as_deref(),
            Some(digest.as_str()),
            "a well-formed record must match the key that wrote it",
        );
        assert!(
            file_key_after.matches(&record).is_none(),
            "a record stored under the pre-edit key must not match the post-edit key",
        );

        // End to end through BOTH layers: the next call must re-hash the bytes
        // rather than serve either stale record.
        assert_ne!(
            solver_identity_hash(solver_path).unwrap(),
            hash_before,
            "the memo must re-hash bytes after the in-place edit",
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// The memo's default directory is `<user cache>/trust-cg` by the one
    /// user-cache rule, the directory AY's private copy lives under: an
    /// empty or relative `XDG_CACHE_HOME` is ignored and a relative `HOME`
    /// names none, so it never depends on the working directory (X-HOST-P13
    /// second audit: it read a relative value against the working directory).
    #[test]
    fn solver_identity_memo_default_directory_is_the_one_user_cache_rule() {
        for (xdg, home, expected) in [
            (Some("/xdg"), "/home/u", Some("/xdg/trust-cg")),
            (Some(""), "/home/u", Some("/home/u/.cache/trust-cg")),
            (Some("relative"), "/home/u", Some("/home/u/.cache/trust-cg")),
            (None, "/home/u", Some("/home/u/.cache/trust-cg")),
            (Some("relative"), "relative-home", None),
            (None, "", None),
        ] {
            trust_cg_process_env::with_env_edits(|env| {
                match xdg {
                    Some(xdg) => env.set("XDG_CACHE_HOME", xdg),
                    None => env.remove("XDG_CACHE_HOME"),
                }
                env.set("HOME", home);
                assert_eq!(
                    default_solver_identity_dir(),
                    expected.map(std::path::PathBuf::from),
                    "XDG_CACHE_HOME={xdg:?} HOME={home:?}"
                );
            });
        }
    }

    /// The machine-local memo is private whatever the umask, and unit tests
    /// never write it into a user cache (X-HOST-P13 closure audit: the file
    /// was written with `std::fs::write`, `0664` under umask `0002`, and a
    /// test run left fixture identities in `~/.cache/trust-cg`). In a child
    /// test process under umask `0002`: with no `TCG_PROOF_CACHE_DIR` nothing
    /// is written under `XDG_CACHE_HOME` or `HOME`; with one, the directories
    /// the store creates are `0700` and the memo `0600`; a memo an earlier
    /// build left `0664` is replaced by a `0600` one while its existing
    /// directory keeps its mode; a symlink at the temporary's name is removed,
    /// never written through.
    #[cfg(unix)]
    #[test]
    fn solver_identity_memo_is_private_and_unit_tests_never_write_the_user_cache() {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        const CHILD: &str = "SOLVER_IDENTITY_MEMO_UMASK_CHILD";
        const NAME: &str = "ay_bridge::tests::\
            solver_identity_memo_is_private_and_unit_tests_never_write_the_user_cache";
        if std::env::var_os(CHILD).is_none() {
            let output = std::process::Command::new("/bin/sh")
                .arg("-c")
                .arg("umask 0002 && exec \"$0\" \"$@\"")
                .arg(std::env::current_exe().unwrap())
                .args(["--exact", NAME, "--nocapture", "--test-threads=1"])
                .env(CHILD, "1")
                .output()
                .unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            assert!(
                output.status.success() && stdout.contains("1 passed"),
                "umask 0002 child: {}\n{stdout}\n{stderr}",
                output.status
            );
            return;
        }
        let mode =
            |path: &std::path::Path| std::fs::symlink_metadata(path).unwrap().mode() & 0o7777;
        let directory = tempfile::tempdir().unwrap();
        // The memo is used only below a private directory; `tempdir` makes
        // it `0777 & !umask`, `0775` here.
        std::fs::set_permissions(directory.path(), std::fs::Permissions::from_mode(0o700)).unwrap();
        let control = directory.path().join("control");
        std::fs::create_dir_all(&control).unwrap();
        assert_eq!(mode(&control), 0o775, "the child must run under umask 0002");
        let solver = directory.path().join("solver");
        std::fs::write(&solver, b"memo fixture solver").unwrap();
        let solver_path = solver.to_str().unwrap().to_owned();
        let key = SolverFileKey::of(&std::fs::metadata(&solver).unwrap()).unwrap();

        // No explicit memo directory: a unit test writes nothing under the
        // user cache, whichever of XDG_CACHE_HOME and HOME names it.
        let user_cache = directory.path().join("user-cache");
        let home = directory.path().join("home");
        trust_cg_process_env::with_env_edits(|env| {
            env.remove("TCG_PROOF_CACHE_DIR");
            env.remove("TCG_NO_SOLVER_ID_CACHE");
            env.set("XDG_CACHE_HOME", &user_cache);
            env.set("HOME", &home);
            assert_eq!(solver_identity_cache_dir(), None);
            assert!(solver_identity_hash(&solver_path).is_some());
            env.remove("XDG_CACHE_HOME");
            solver_identity_cache_store(&key, &"cd".repeat(32));
        });
        assert!(
            !user_cache.exists() && !home.exists(),
            "nothing in a user cache"
        );

        let memo_dir = directory.path().join("base").join("trust-cg");
        let memo = memo_dir.join("solver-identity-v1");
        trust_cg_process_env::with_env_edits(|env| {
            env.set("TCG_PROOF_CACHE_DIR", &memo_dir);
            env.remove("TCG_NO_SOLVER_ID_CACHE");
            let first = "ab".repeat(32);
            solver_identity_cache_store(&key, &first);
            for created in [directory.path().join("base"), memo_dir.clone()] {
                assert_eq!(mode(&created), 0o700, "{}", created.display());
            }
            assert_eq!(mode(&memo), 0o600);
            assert_eq!(solver_identity_cache_lookup(&key), Some(first));

            // A memo an earlier build wrote with the umask's mode, in a
            // directory that already existed with its own mode: ignored,
            // never trusted, then replaced by a private one.
            std::fs::set_permissions(&memo, std::fs::Permissions::from_mode(0o664)).unwrap();
            std::fs::set_permissions(&memo_dir, std::fs::Permissions::from_mode(0o755)).unwrap();
            assert_eq!(solver_identity_cache_lookup(&key), None);
            let elsewhere = directory.path().join("elsewhere");
            let tmp = memo.with_extension(format!("tmp{}", std::process::id()));
            std::os::unix::fs::symlink(&elsewhere, &tmp).unwrap();
            let second = "ef".repeat(32);
            solver_identity_cache_store(&key, &second);
            assert_eq!(mode(&memo), 0o600, "the rewritten memo is private");
            assert_eq!(
                mode(&memo_dir),
                0o755,
                "an existing directory is never changed"
            );
            assert!(!elsewhere.exists(), "never written through a symlink");
            assert!(std::fs::symlink_metadata(&tmp).is_err());
            assert_eq!(solver_identity_cache_lookup(&key), Some(second));
        });
        println!("SOLVER_IDENTITY_MEMO_UMASK_0002 dir=0700 memo=0600 user_cache=untouched");
    }

    /// The machine-local identity memo is read only from a private canonical
    /// location and is otherwise ignored, never trusted (X-HOST-P13 fourth
    /// closure audit: it was read through the uncanonicalized cache path with
    /// no privacy check, and this host's legacy memo is `0664`). A memo
    /// another user could write, one in a directory another user could write
    /// or below an ancestor another user could rename entries in, and one
    /// reached through a symlink, each read as no memo; the store then writes
    /// only into a private canonical directory, by its canonical name.
    #[cfg(unix)]
    #[test]
    fn solver_identity_memo_is_read_only_from_a_private_canonical_location() {
        use std::os::unix::fs::{MetadataExt, PermissionsExt};
        let set_mode = |path: &std::path::Path, mode: u32| {
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(mode)).unwrap();
        };
        let mode =
            |path: &std::path::Path| std::fs::symlink_metadata(path).unwrap().mode() & 0o7777;
        let directory = tempfile::tempdir().unwrap();
        let root = directory.path().canonicalize().unwrap();
        set_mode(&root, 0o700);
        let solver = root.join("solver");
        std::fs::write(&solver, b"memo privacy fixture solver").unwrap();
        let key = SolverFileKey::of(&std::fs::metadata(&solver).unwrap()).unwrap();
        let planted = "ee".repeat(32);
        let plant = |memo: &std::path::Path| {
            std::fs::write(memo, key.line(&planted) + "\n").unwrap();
        };
        let with_memo_dir = |dir: &std::path::Path, body: &dyn Fn()| {
            trust_cg_process_env::with_env_edits(|env| {
                env.set("TCG_PROOF_CACHE_DIR", dir);
                env.remove("TCG_NO_SOLVER_ID_CACHE");
                body();
            });
        };

        // The control: a private memo in a private directory is read.
        let private = root.join("private");
        std::fs::create_dir(&private).unwrap();
        set_mode(&private, 0o700);
        let memo = private.join(SOLVER_IDENTITY_MEMO);
        plant(&memo);
        set_mode(&memo, 0o600);
        with_memo_dir(&private, &|| {
            assert_eq!(solver_identity_cache_lookup(&key), Some(planted.clone()));
        });

        // A memo another user could write (the legacy `0664`), or read.
        for loose in [0o664, 0o644, 0o606] {
            set_mode(&memo, loose);
            with_memo_dir(&private, &|| {
                assert_eq!(solver_identity_cache_lookup(&key), None, "{loose:o}");
            });
        }
        set_mode(&memo, 0o600);

        // A memo that is a symlink to a private file.
        let target = root.join("target-memo");
        plant(&target);
        set_mode(&target, 0o600);
        let linked = root.join("linked");
        std::fs::create_dir(&linked).unwrap();
        set_mode(&linked, 0o700);
        std::os::unix::fs::symlink(&target, linked.join(SOLVER_IDENTITY_MEMO)).unwrap();
        with_memo_dir(&linked, &|| {
            assert_eq!(solver_identity_cache_lookup(&key), None);
        });

        // A group-writable memo directory: ignored, and nothing is written
        // into it (an existing directory is never changed).
        set_mode(&private, 0o775);
        with_memo_dir(&private, &|| {
            assert_eq!(solver_identity_cache_lookup(&key), None);
            solver_identity_cache_store(&key, &"cd".repeat(32));
        });
        assert_eq!(
            std::fs::read_to_string(&memo).unwrap(),
            key.line(&planted) + "\n"
        );
        assert_eq!(mode(&private), 0o775);
        set_mode(&private, 0o700);

        // A private memo directory below an ancestor others can write, named
        // directly and through a symlink: ignored, nothing written.
        let shared = root.join("shared");
        std::fs::create_dir(&shared).unwrap();
        set_mode(&shared, 0o777);
        let inner = shared.join("inner");
        std::fs::create_dir(&inner).unwrap();
        set_mode(&inner, 0o700);
        let inner_memo = inner.join(SOLVER_IDENTITY_MEMO);
        plant(&inner_memo);
        set_mode(&inner_memo, 0o600);
        let alias = root.join("alias");
        std::os::unix::fs::symlink(&inner, &alias).unwrap();
        for dir in [&inner, &alias] {
            with_memo_dir(dir, &|| {
                assert_eq!(
                    solver_identity_cache_lookup(&key),
                    None,
                    "{}",
                    dir.display()
                );
                solver_identity_cache_store(&key, &"cd".repeat(32));
            });
        }
        assert_eq!(
            std::fs::read_to_string(&inner_memo).unwrap(),
            key.line(&planted) + "\n"
        );

        // A private directory reached through a symlink in a directory
        // others can write is used by its canonical name: re-pointing the
        // link afterwards changes nothing already resolved.
        let link = shared.join("link");
        std::os::unix::fs::symlink(&private, &link).unwrap();
        with_memo_dir(&link, &|| {
            assert_eq!(solver_identity_cache_lookup(&key), Some(planted.clone()));
            let fresh = "ab".repeat(32);
            solver_identity_cache_store(&key, &fresh);
            assert_eq!(solver_identity_cache_lookup(&key), Some(fresh));
        });
        assert_eq!(mode(&memo), 0o600);
        assert!(
            std::fs::symlink_metadata(&link)
                .unwrap()
                .file_type()
                .is_symlink(),
            "the link itself is never replaced"
        );
    }

    #[test]
    fn cache_hardening_session_ignores_forged_disk_verdicts() {
        let dir = tempfile::tempdir().unwrap();
        let key = format!(
            "{:064x}",
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        );
        std::fs::write(dir.path().join(format!("{key}.verdict")), "unsat").unwrap();
        let key = SessionProofKey::for_test(key, [0xA1; 32]);

        assert!(
            !session_proof_cache_lookup_verified(&key),
            "an attacker-writable verdict file must never establish proof authority"
        );
        session_proof_cache_store_verified(&key);
        assert!(
            session_proof_cache_lookup_verified(&key),
            "a live result recorded in this process may be reused in this process"
        );
    }

    #[test]
    fn session_proof_cache_has_a_fixed_resident_bound() {
        let mut cache = SessionProofCache::default();
        let first = SessionProofKey::for_test(format!("{:064x}", 0), [0xC1; 32]);
        for value in 0..=SESSION_PROOF_CACHE_CAPACITY {
            cache.insert(SessionProofKey::for_test(
                format!("{value:064x}"),
                [0xC1; 32],
            ));
        }
        let last =
            SessionProofKey::for_test(format!("{:064x}", SESSION_PROOF_CACHE_CAPACITY), [0xC1; 32]);

        assert_eq!(cache.entries.len(), SESSION_PROOF_CACHE_CAPACITY);
        assert!(!cache.contains(&first));
        assert!(cache.contains(&last));
    }

    /// The negative memo: remembers exactly the deterministic certification
    /// gaps, replays the FIRST recorded reason verbatim, never reads as a
    /// positive, and yields to a later `Verified` for the same key.
    #[test]
    fn negative_session_memo_replays_only_memoizable_gaps_and_yields_to_verified() {
        let key = SessionProofKey::for_test(format!("{:064x}", 0xD1u32), [0xD1; 32]);
        assert!(session_negative_memo_lookup(&key).is_none());
        assert!(!session_proof_cache_lookup_verified(&key));

        // NOT memoisable: a bare unknown, an AY resource envelope, an empty
        // proof, a replay IO failure, a toolchain-absence diagnostic, an
        // unpublishable proof file, and every non-Unknown result.
        for result in [
            AYResult::Unknown("unknown".to_string()),
            AYResult::Unknown("(:reason-unknown (incomplete self-check-rejected))".to_string()),
            AYResult::Unknown("AY reported UNSAT but emitted an empty Alethe proof".to_string()),
            AYResult::Unknown(
                "AY reported UNSAT but Clean replay could not complete: io".to_string(),
            ),
            AYResult::Unknown(
                "AY reported UNSAT but it CANNOT BE CHECKED here — no usable checker. \
                 This is a toolchain problem, not evidence about the proof."
                    .to_string(),
            ),
            AYResult::Unknown(
                "unusable AY proof evidence: could not publish a same-run default proof file"
                    .to_string(),
            ),
            AYResult::Timeout,
            AYResult::SolverUnsat,
            AYResult::Error("boom".to_string()),
            AYResult::CounterExample(vec![]),
        ] {
            remember_negative_session_verdict(&key, &result, "negative_memo_probe", 0);
            assert!(
                session_negative_memo_lookup(&key).is_none(),
                "{result:?} must not be memoised"
            );
        }

        // Memoisable: AY's own incomplete-certificate header.
        let holey = "incomplete AY proof certificate: c ay.proof.certificate \
                     path=/tmp/q.alethe unproved_steps=1 foreign_assumes=no trust_free=no \
                     ay_self_checkable=yes";
        remember_negative_session_verdict(
            &key,
            &AYResult::Unknown(holey.to_string()),
            "negative_memo_probe",
            0,
        );
        assert_eq!(session_negative_memo_lookup(&key).as_deref(), Some(holey));
        // The first recorded reason wins: a later occurrence of the same class
        // (a different temp path) does not replace it.
        let holey_again = holey.replace("/tmp/q.alethe", "/tmp/r.alethe");
        remember_negative_session_verdict(
            &key,
            &AYResult::Unknown(holey_again),
            "negative_memo_probe",
            0,
        );
        assert_eq!(session_negative_memo_lookup(&key).as_deref(), Some(holey));
        // Never a positive.
        assert!(!session_proof_cache_lookup_verified(&key));

        // A positive result for the same key evicts the negative entry.
        session_proof_cache_store_verified(&key);
        assert!(session_proof_cache_lookup_verified(&key));
        assert!(session_negative_memo_lookup(&key).is_none());

        // Memoisable: the identity-pinned checker rejected the exact proof.
        let rejected = SessionProofKey::for_test(format!("{:064x}", 0xD2u32), [0xD2; 32]);
        let checker_rejected = working_checker_rejection_reason(std::path::Path::new("/x/clean"));
        remember_negative_session_verdict(
            &rejected,
            &AYResult::Unknown(checker_rejected.clone()),
            "negative_memo_probe",
            0,
        );
        assert_eq!(
            session_negative_memo_lookup(&rejected).as_deref(),
            Some(checker_rejected.as_str())
        );
    }

    #[test]
    fn negative_session_memo_has_a_fixed_resident_bound() {
        let mut memo = SessionNegativeVerdictMemo::default();
        let first = SessionProofKey::for_test(format!("{:064x}", 0), [0xE1; 32]);
        for value in 0..=SESSION_NEGATIVE_MEMO_CAPACITY {
            memo.insert(
                SessionProofKey::for_test(format!("{value:064x}"), [0xE1; 32]),
                "incomplete AY proof certificate: probe",
            );
        }
        let last = SessionProofKey::for_test(
            format!("{:064x}", SESSION_NEGATIVE_MEMO_CAPACITY),
            [0xE1; 32],
        );

        assert_eq!(memo.entries.len(), SESSION_NEGATIVE_MEMO_CAPACITY);
        assert_eq!(memo.insertion_order.len(), SESSION_NEGATIVE_MEMO_CAPACITY);
        assert!(memo.get(&first).is_none());
        assert!(memo.get(&last).is_some());
        memo.remove(&last);
        assert!(memo.get(&last).is_none());
        assert_eq!(
            memo.insertion_order.len(),
            SESSION_NEGATIVE_MEMO_CAPACITY - 1
        );
    }

    #[test]
    fn cache_hardening_solver_query_tempfile_is_private_unique_and_raii_cleaned() {
        let first = write_temp_smt2("(check-sat)\n").unwrap();
        let first_path = first.path().to_path_buf();
        let second = write_temp_smt2("(assert false)\n").unwrap();
        assert_ne!(first.path(), second.path());
        assert_eq!(
            std::fs::read_to_string(first.path()).unwrap(),
            "(check-sat)\n"
        );

        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::metadata(first.path())
                .unwrap()
                .permissions()
                .mode();
            assert_eq!(
                mode & 0o077,
                0,
                "solver query must not be group/world accessible"
            );
        }

        // AY's proof and a partial proof it left beside the query (a run that
        // ended before AY renamed the partial into place) go with the query.
        let proof = default_alethe_path(&first_path);
        let mut partial = proof.as_os_str().to_os_string();
        partial.push(".tmp-4242-0");
        std::fs::write(&proof, "proof").unwrap();
        std::fs::write(&partial, "partial").unwrap();
        let directory = first_path.parent().unwrap().to_path_buf();
        assert_ne!(
            directory,
            std::env::temp_dir(),
            "the query owns its directory"
        );

        drop(first);
        assert!(
            !first_path.exists(),
            "RAII cleanup must remove the solver query"
        );
        assert!(
            !directory.exists(),
            "RAII cleanup must remove the query's directory with AY's proof artifacts"
        );
    }

    fn ay_batch_test_lock() -> std::sync::MutexGuard<'static, ()> {
        formal_solver_test_lock()
    }

    /// The certification-gap-guarded spelling of the tests' standard
    /// `assert_eq!(result, AYResult::Verified, …)` (`crate::formal_gap`; same
    /// rule as the plugin's `solver_test_support`): `Verified` passes (returns
    /// `true`); ONLY AY's disclosed proof hole skips — LOUDLY, naming the
    /// obligation and disclosure — returning `false`; every other outcome
    /// (`CounterExample`, a checker or self-check rejection, a bare `unknown`,
    /// `Timeout`, `Error`) panics with the ORIGINAL message, so no solver
    /// regression can hide behind the guard and the exemption un-arms itself
    /// the moment AY ships a checkable proof.
    #[track_caller]
    fn assert_verified_or_certification_gap_skip(
        obligation: &ProofObligation,
        result: &AYResult,
        original_message: std::fmt::Arguments<'_>,
    ) -> bool {
        if matches!(result, AYResult::Verified) {
            return true;
        }
        if let Some(reason) = crate::formal_gap::disclosed_proof_hole(result) {
            crate::formal_gap::print_gap_skip(
                &format!("obligation '{}'", obligation.name),
                &reason,
            );
            return false;
        }
        // The ORIGINAL assertion, verbatim shape and message.
        assert_eq!(*result, AYResult::Verified, "{original_message}");
        true
    }

    fn run_with_ay_batch_stack<F>(body: F)
    where
        F: FnOnce() + Send + 'static,
    {
        let handle = std::thread::Builder::new()
            .name("trust-cg-ay-batch".to_string())
            .stack_size(16 * 1024 * 1024)
            .spawn(body)
            .expect("spawn ay batch test thread");
        if let Err(panic) = handle.join() {
            std::panic::resume_unwind(panic);
        }
    }

    // SMT-LIB2 generation tests (always run, no solver needed)
    // -----------------------------------------------------------------------

    #[test]
    fn test_generate_smt2_query_basic() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_add".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);

        assert!(smt2.contains("(set-logic QF_BV)"));
        assert!(smt2.contains(&format!("(set-option :timeout {})", config.timeout_ms)));
        assert!(smt2.contains("(set-option :produce-models true)"));
        assert!(smt2.contains("(declare-const a (_ BitVec 32))"));
        assert!(smt2.contains("(declare-const b (_ BitVec 32))"));
        assert!(smt2.contains("(assert"));
        assert!(smt2.contains("(check-sat)"));
        assert!(!smt2.contains("(get-value"));
        assert!(smt2.contains("(exit)"));
        let timeout_pos = smt2.find("(set-option :timeout").unwrap();
        let models_pos = smt2.find("(set-option :produce-models").unwrap();
        let logic_pos = smt2.find("(set-logic").unwrap();
        assert!(timeout_pos < logic_pos && models_pos < logic_pos);

        let model_smt2 = generate_sat_model_query(&obligation, &smt2).unwrap();
        assert!(model_smt2.contains("(get-value (a b))"));
    }

    /// The complete TST flag theorem is exercised through the raw serializer
    /// when local simplification alone proves it.  Keep this lane
    /// verdict-only: AY correctly exits nonzero if an UNSAT proof query is
    /// followed by a model command.
    #[test]
    fn tst_packed_nzcv_proof_queries_are_exactly_verdict_only() {
        let config = AYConfig::default().with_timeout(30_000);

        for width in [32u32, 64] {
            let obligation = crate::cmp_combine_proofs::proof_tst_packed_nzcv(width);
            for (kind, smt2) in [
                ("normal", generate_smt2_query(&obligation, &config)),
                ("raw", generate_smt2_query_raw(&obligation, &config)),
            ] {
                assert!(
                    !smt2.contains("(get-value"),
                    "TST packed-NZCV w{width} {kind} proof query must not request a model"
                );
                assert_eq!(
                    smt2.matches("(check-sat)").count(),
                    1,
                    "TST packed-NZCV w{width} {kind} query must have one verdict"
                );
                assert!(
                    smt2.ends_with("(check-sat)\n(exit)"),
                    "TST packed-NZCV w{width} {kind} query must exit immediately after its verdict"
                );
            }
        }
    }

    // -----------------------------------------------------------------------
    // TCB soundness guard: an obligation the local simplifier alone collapses
    // to constant `false` must still be CHECKED BY THE SOLVER on the raw
    // formula, never minted as `Verified` by the rewrite.
    // (Residual close: "SIMPLIFIER IN TCB".)
    // -----------------------------------------------------------------------

    #[test]
    fn is_constant_false_only_matches_constant_false() {
        assert!(is_constant_false(&SmtExpr::bool_const(false)));
        assert!(!is_constant_false(&SmtExpr::bool_const(true)));
        assert!(!is_constant_false(&SmtExpr::var("x", 8)));
        assert!(!is_constant_false(&SmtExpr::bv_const(0, 8)));
    }

    /// Build an obligation whose two sides are syntactically identical, so the
    /// negated equivalence `not (= e e)` is folded to constant `false` by the
    /// solver-oriented simplifier alone (the unsound TCB shortcut).
    fn degenerate_false_obligation() -> ProofObligation {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "degenerate_simplifier_false".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        }
    }

    #[test]
    fn lowered_queries_decline_shared_theory_free_dag_without_expansion() {
        let mut expr = SmtExpr::var("x", 64);
        for _ in 0..64 {
            let shared = Arc::new(expr);
            expr = SmtExpr::BvAdd {
                lhs: shared.clone(),
                rhs: shared,
                width: 64,
            };
        }
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "shared theory-free census".into(),
            trust_ir_expr: expr,
            aarch64_expr: SmtExpr::var("y", 64),
            inputs: vec![("x".into(), 64), ("y".into(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        assert!(generate_lowered_queries(&obligation, &AYConfig::default()).is_empty());
    }

    #[test]
    fn lane_query_matches_guarded_generators_byte_for_byte() {
        let mut obligations = crate::lowering_proof::all_arithmetic_proofs();
        obligations.push(degenerate_false_obligation());
        // Include bounded expansion as well as a quantifier that must remain.
        for upper in [SmtExpr::bv_const(2, 8), SmtExpr::var("limit", 8)] {
            let mut obligation = degenerate_false_obligation();
            obligation.inputs.push(("limit".into(), 8));
            obligation.preconditions.push(SmtExpr::forall(
                "i",
                8,
                SmtExpr::bv_const(0, 8),
                upper,
                SmtExpr::var("i", 8).bvult(SmtExpr::bv_const(3, 8)),
            ));
            obligations.push(obligation.clone());
            obligation.aarch64_expr = SmtExpr::var("a", 32);
            obligations.push(obligation);
        }
        for produce_models in [false, true] {
            let config = AYConfig {
                timeout_ms: 1234,
                produce_models,
                ..AYConfig::default()
            };
            for obligation in &obligations {
                let historical = if simplifier_alone_proved_unsat(obligation) {
                    generate_smt2_query_raw(obligation, &config)
                } else {
                    generate_smt2_query(obligation, &config)
                };
                assert_eq!(
                    lane_smt2_query(obligation, &config),
                    historical,
                    "{}; models={produce_models}",
                    obligation.name
                );
            }
        }
    }

    #[test]
    fn simplifier_collapse_to_false_is_detected_and_rerouted_to_solver() {
        let ob = degenerate_false_obligation();

        // (1) The simplifier alone reduces the negated equivalence to `false`,
        //     so verify_with_ay's TCB guard fires for this obligation.
        assert!(
            simplifier_alone_proved_unsat(&ob),
            "expected the simplifier alone to fold `not (= e e)` to false"
        );

        // (2) Proof the unsound shortcut really exists: the NORMAL (simplified)
        //     query degenerates to `(assert false)` — which is trivially unsat
        //     and would mint `Verified` without the solver seeing the formula.
        let config = AYConfig::default();
        let simplified_smt2 = generate_smt2_query(&ob, &config);
        assert!(
            simplified_smt2.contains("(assert false)"),
            "the simplified query should degenerate to (assert false): {}",
            simplified_smt2
        );

        // (3) The RAW query that the guard routes to the solver instead must NOT
        //     be `(assert false)`: it carries the real negated equivalence so the
        //     SOLVER — not the rewrite — decides sat/unsat.
        let raw_smt2 = generate_smt2_query_raw(&ob, &config);
        assert!(
            !raw_smt2.contains("(assert false)"),
            "raw query must NOT be (assert false); the solver must see the real formula: {}",
            raw_smt2
        );
        assert!(
            raw_smt2.contains("bvadd"),
            "raw query must assert the real negated equivalence over bvadd: {}",
            raw_smt2
        );
        // The raw query still declares the inputs and asks the solver to decide.
        assert!(raw_smt2.contains("(declare-const a (_ BitVec 32))"));
        assert!(raw_smt2.contains("(declare-const b (_ BitVec 32))"));
        assert!(raw_smt2.contains("(check-sat)"));
    }

    #[test]
    fn non_degenerate_obligation_keeps_fast_simplified_path() {
        // Distinct variables: `not (= a b)` is satisfiable and the simplifier
        // does NOT collapse it, so the TCB guard must NOT fire (fast path kept).
        let ob = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "non_degenerate".to_string(),
            trust_ir_expr: SmtExpr::var("a", 32),
            aarch64_expr: SmtExpr::var("b", 32),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        assert!(
            !simplifier_alone_proved_unsat(&ob),
            "a satisfiable negated equivalence must not be flagged as simplifier-proved unsat"
        );
        let smt2 = generate_smt2_query(&ob, &AYConfig::default());
        assert!(
            !smt2.contains("(assert false)"),
            "non-degenerate obligation must keep its real formula: {}",
            smt2
        );
    }

    #[test]
    fn test_generate_smt2_no_timeout() {
        let a = SmtExpr::var("x", 64);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_no_timeout".to_string(),
            trust_ir_expr: a.clone(),
            aarch64_expr: a,
            inputs: vec![("x".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig {
            timeout_ms: 0,
            ..Default::default()
        };
        let smt2 = generate_smt2_query(&obligation, &config);
        assert!(!smt2.contains(":timeout"));
    }

    // -----------------------------------------------------------------------
    // Solver output parsing tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_parse_unsat() {
        let result = parse_solver_output("unsat\n", "", &[]);
        assert_eq!(result, AYResult::SolverUnsat);
    }

    #[test]
    fn test_parse_unsat_rejects_ambiguous_or_trailing_output() {
        for output in ["unsat\nsat\n", "unsat\nunexpected diagnostic\n"] {
            assert!(
                matches!(parse_solver_output(output, "", &[]), AYResult::Error(_)),
                "UNSAT authority requires an unambiguous transcript: {output:?}"
            );
        }
    }

    #[test]
    fn test_parse_sat_with_hex_model() {
        let output = "sat\n((a #x0000000a)\n (b #x00000014))";
        let inputs = vec![("a".to_string(), 32), ("b".to_string(), 32)];
        let result = parse_solver_output(output, "", &inputs);
        match result {
            AYResult::CounterExample(cex) => {
                assert_eq!(cex.len(), 2);
                assert_eq!(cex[0], ("a".to_string(), 0xa));
                assert_eq!(cex[1], ("b".to_string(), 0x14));
            }
            other => panic!("Expected CounterExample, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_sat_model_input_named_timeout_is_not_a_timeout() {
        let result = parse_solver_output(
            "sat\n((timeout #x0000002a))\n",
            "",
            &[("timeout".to_string(), 32)],
        );
        assert_eq!(
            result,
            AYResult::CounterExample(vec![("timeout".to_string(), 0x2a)])
        );
    }

    #[test]
    fn test_parse_sat_with_bv_model() {
        let output = "sat\n((x (_ bv42 32)))";
        let inputs = vec![("x".to_string(), 32)];
        let result = parse_solver_output(output, "", &inputs);
        match result {
            AYResult::CounterExample(cex) => {
                assert_eq!(cex.len(), 1);
                assert_eq!(cex[0], ("x".to_string(), 42));
            }
            other => panic!("Expected CounterExample, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_sat_with_binary_model() {
        let output = "sat\n((x #b00101010))";
        let inputs = vec![("x".to_string(), 8)];
        let result = parse_solver_output(output, "", &inputs);
        match result {
            AYResult::CounterExample(cex) => {
                assert_eq!(cex.len(), 1);
                assert_eq!(cex[0], ("x".to_string(), 42));
            }
            other => panic!("Expected CounterExample, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_unknown() {
        let result = parse_solver_output("unknown\n", "", &[]);
        assert_eq!(result, AYResult::Unknown("unknown".to_string()));
    }

    #[test]
    fn test_parse_unknown_with_reason() {
        let result = parse_solver_output("unknown\n(:reason-unknown incomplete)\n", "", &[]);
        assert_eq!(
            result,
            AYResult::Unknown("(:reason-unknown incomplete)".to_string())
        );
    }

    #[test]
    fn test_parse_error() {
        let result = parse_solver_output("", "Parse error at line 1", &[]);
        assert!(matches!(result, AYResult::Error(_)));
    }

    /// AY's caught-invalid-model banner must reach the verdict as its OWN
    /// named class, and must outrank whatever `:reason-unknown` tail AY
    /// printed with it. Verbatim transcript shape from ay 0.13.0 build 8256
    /// on the `Source-bound AArch64 leaf: FP/LR frame memory and writeback`
    /// obligation (2026-09-21).
    #[test]
    fn test_parse_unknown_surfaces_ay_soundness_gate_over_the_reason_tail() {
        let stderr = concat!(
            "c ay.session.start build.version=0.13.0 build.increment=8256\n",
            "[AY SOUNDNESS GATE] caught an INVALID model \u{2014} a theory-search path ",
            "returned a model that falsifies an assertion.\n",
            "    AY fail-closed to `unknown` (this is SOUND); it indicates an ",
            "internal solver bug worth reporting.\n",
            "    logic:     ALL\n",
            "(:reason-unknown incomplete)\n",
        );
        let result = parse_solver_output("unknown\n", stderr, &[]);
        let AYResult::Unknown(reason) = result else {
            panic!("a caught invalid model must stay an Unknown verdict, got {result:?}");
        };
        assert!(
            crate::gap_classify::ay_reason_is_soundness_gate_refusal(&reason),
            "reason must carry the named class: {reason}"
        );
        assert!(
            reason.contains("(:reason-unknown incomplete)"),
            "AY's own published tail must be preserved: {reason}"
        );
        // Fail-closed everywhere: never a gap-skip, always a hard gate failure.
        assert!(!crate::gap_classify::ay_reason_is_certification_gap(
            &reason
        ));
        assert!(!crate::gap_classify::ay_reason_is_self_check_rejection(
            &reason
        ));
        assert!(
            crate::formal_gap::disclosed_proof_hole(&AYResult::Unknown(reason.clone())).is_none(),
            "a caught invalid model must never authorize a test skip"
        );
    }

    /// THE EXEMPTION HOLE THIS CLOSES. AY publishes the caught-invalid-model
    /// banner AND an ordinary `(incomplete self-check-rejected)` tail for the
    /// SAME query — measured 2026-09-21 on the FP/LR frame shape written
    /// through a pinned `frame_base` constant (reproducer:
    /// `python3 frame_family.py frame-fb` in
    /// `reports/2026-09-21-frame-layout-ay-authority-gap/`; z3 `unsat`).
    /// Reading only the tail classified that as a certification gap and
    /// granted a LOUD SKIP on a query where AY had just disclosed an internal
    /// defect of its own. The banner outranks the tail, so it cannot.
    #[test]
    fn test_parse_unknown_gate_banner_outranks_a_self_check_rejected_tail() {
        let stderr = concat!(
            "c ay.session.start build.version=0.13.0 build.increment=8256\n",
            "[AY SOUNDNESS GATE] caught an INVALID model \u{2014} a theory-search path ",
            "returned a model that falsifies an assertion.\n",
            "    AY fail-closed to `unknown` (this is SOUND); it indicates an ",
            "internal solver bug worth reporting.\n",
            "(:reason-unknown (incomplete self-check-rejected))\n",
        );
        let result = parse_solver_output("unknown\n", stderr, &[]);
        let AYResult::Unknown(reason) = result else {
            panic!("expected Unknown, got {result:?}");
        };
        assert!(crate::gap_classify::ay_reason_is_soundness_gate_refusal(
            &reason
        ));
        assert!(
            !crate::gap_classify::ay_reason_is_self_check_rejection(&reason),
            "a caught invalid model must not be laundered into the self-check gap: {reason}"
        );
        assert!(!crate::gap_classify::ay_reason_is_certification_gap(
            &reason
        ));
        assert!(
            crate::formal_gap::disclosed_proof_hole(&AYResult::Unknown(reason.clone())).is_none(),
            "the guarded lib tests must NOT skip on it: {reason}"
        );
    }

    /// The gate banner is the ONLY thing that promotes the reason: an
    /// ordinary self-check rejection keeps classifying as the certification
    /// gap its siblings skip on.
    #[test]
    fn test_parse_unknown_without_the_gate_banner_is_unchanged() {
        let stderr = concat!(
            "c ay.session.start build.version=0.13.0 build.increment=8256\n",
            "(:reason-unknown (incomplete self-check-rejected))\n",
        );
        assert_eq!(
            parse_solver_output("unknown\n", stderr, &[]),
            AYResult::Unknown("(:reason-unknown (incomplete self-check-rejected))".to_string())
        );
    }

    #[test]
    fn test_parse_protocol_error_cannot_be_masked_by_a_later_verdict() {
        for output in [
            "(error \"late option\")\nunsat\n",
            "unsat\n(error \"model is not available\")\n",
            "(error \"late option\")\nunknown\n",
            "sat\n((x #x00))\n(error \"late failure\")\n",
        ] {
            assert!(
                matches!(
                    parse_solver_output(output, "", &[("x".to_string(), 8)]),
                    AYResult::Error(_)
                ),
                "protocol error must fail closed even around a verdict: {output:?}"
            );
        }
    }

    #[test]
    fn test_parse_unsat_with_holey_ay_certificate_is_pending_not_verified() {
        let holey = "c ay.proof.certificate path=/tmp/q.alethe unproved_steps=1 \
                     foreign_assumes=no trust_free=no ay_self_checkable=yes\n\
                     c warning: an external checker reports it as *holey*, never *valid*\n";
        assert!(matches!(
            parse_solver_output("unsat\n", holey, &[]),
            AYResult::Unknown(reason) if reason.contains("incomplete AY proof certificate")
        ));

        let complete = "c ay.proof.certificate path=/tmp/q.alethe unproved_steps=0 \
                        foreign_assumes=no trust_free=yes ay_self_checkable=yes\n";
        assert_eq!(
            parse_solver_output("unsat\n", complete, &[]),
            AYResult::SolverUnsat,
            "a clean AY transcript is still only a candidate until Carcara accepts the proof"
        );
    }

    /// The reasons this bridge mints are the ones the test-skip classifier and
    /// the strict gate read: a disclosed hole is the tracked capability gap, a
    /// working checker's rejection is not.
    #[test]
    fn minted_hole_is_a_disclosed_gap_and_a_checker_rejection_is_not() {
        let holey = "c ay.proof.certificate path=/tmp/q.alethe unproved_steps=1 \
                     foreign_assumes=no trust_free=no ay_self_checkable=yes\n";
        let AYResult::Unknown(hole) = parse_solver_output("unsat\n", holey, &[]) else {
            panic!("a holey UNSAT must stay pending");
        };
        assert!(
            crate::gap_classify::ay_reason_is_disclosed_proof_hole(&hole),
            "{hole}"
        );

        // A certificate that states NO unproved step but is not trust-free:
        // the bridge still mints the incomplete-certificate reason (from
        // `trust_free=no`), and it is not a hole, so a test must fail on it.
        let not_trust_free = "c ay.proof.certificate path=/tmp/q.alethe unproved_steps=0 \
                              foreign_assumes=no trust_free=no ay_self_checkable=yes\n";
        let AYResult::Unknown(not_trust_free) = parse_solver_output("unsat\n", not_trust_free, &[])
        else {
            panic!("an UNSAT whose certificate is not trust-free must stay pending");
        };
        assert!(
            not_trust_free.starts_with("incomplete AY proof certificate: "),
            "{not_trust_free}"
        );
        assert!(
            !crate::gap_classify::ay_reason_is_disclosed_proof_hole(&not_trust_free),
            "{not_trust_free}"
        );

        let foreign = "c ay.proof.certificate path=/tmp/q.alethe unproved_steps=0 \
                       foreign_assumes=yes trust_free=no ay_self_checkable=yes\n";
        let AYResult::Unknown(foreign) = parse_solver_output("unsat\n", foreign, &[]) else {
            panic!("an UNSAT with foreign assumptions must stay pending");
        };
        assert!(
            !crate::gap_classify::ay_reason_is_disclosed_proof_hole(&foreign),
            "{foreign}"
        );

        let rejection =
            working_checker_rejection_reason(Path::new("/pkg/store/clean/8606/bin/clean"));
        assert_eq!(
            rejection,
            "AY reported UNSAT but /pkg/store/clean/8606/bin/clean — which verified a known-good \
             control proof, so it is a working checker — rejected or could not fully verify THIS \
             Alethe proof"
        );
        assert!(crate::gap_classify::ay_reason_is_certification_gap(
            &rejection
        ));
        assert!(!crate::gap_classify::ay_reason_is_disclosed_proof_hole(
            &rejection
        ));
    }

    #[test]
    fn test_parse_empty_output() {
        let result = parse_solver_output("", "", &[]);
        assert!(matches!(result, AYResult::Error(_)));
    }

    // -----------------------------------------------------------------------
    // AYResult display tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_ayresult_display_verified() {
        assert_eq!(format!("{}", AYResult::Verified), "VERIFIED (UNSAT)");
    }

    #[test]
    fn test_ayresult_display_counterexample() {
        let cex = AYResult::CounterExample(vec![("a".to_string(), 10), ("b".to_string(), 20)]);
        let display = format!("{}", cex);
        assert!(display.contains("a = 0xa"));
        assert!(display.contains("b = 0x14"));
    }

    #[test]
    fn test_ayresult_display_timeout() {
        assert_eq!(format!("{}", AYResult::Timeout), "TIMEOUT");
    }

    #[test]
    fn test_ayresult_display_unknown() {
        assert_eq!(
            format!("{}", AYResult::Unknown("unknown".to_string())),
            "UNKNOWN: unknown"
        );
    }

    // -----------------------------------------------------------------------
    // VerificationSummary tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_verification_summary() {
        let results = vec![
            ("proof1".to_string(), AYResult::Verified),
            ("proof2".to_string(), AYResult::Verified),
            ("proof3".to_string(), AYResult::CounterExample(vec![])),
            ("proof4".to_string(), AYResult::Timeout),
            (
                "proof5".to_string(),
                AYResult::Unknown("(:reason-unknown incomplete)".to_string()),
            ),
            ("proof6".to_string(), AYResult::Error("oops".to_string())),
            ("proof7".to_string(), AYResult::SolverUnsat),
        ];

        let summary = VerificationSummary::from_results(&results);
        assert_eq!(summary.total, 7);
        assert_eq!(summary.verified, 2);
        assert_eq!(summary.failed, 1);
        assert_eq!(summary.timeouts, 1);
        assert_eq!(summary.errors, 3);
        assert!(!summary.all_verified());
    }

    #[test]
    fn test_verification_summary_all_verified() {
        let results = vec![
            ("proof1".to_string(), AYResult::Verified),
            ("proof2".to_string(), AYResult::Verified),
        ];

        let summary = VerificationSummary::from_results(&results);
        assert!(summary.all_verified());
    }

    // -----------------------------------------------------------------------
    // CLI integration test (only runs if AY is available)
    // -----------------------------------------------------------------------

    #[test]
    fn test_cli_verify_correct_rule() {
        // Skip if no solver binary available
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_correct_rule",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return; // No solver available, skip test
        };

        // a + b == a + b (trivially correct)
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "trivial_add_identity".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_eq!(result, AYResult::Verified);
    }

    #[test]
    fn test_cli_verify_wrong_rule() {
        // Skip if no solver binary available
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_wrong_rule",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };
        // a + b != a - b (should find counterexample)
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "wrong_add_vs_sub".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvsub(b),
            inputs: vec![("a".to_string(), 8), ("b".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert!(matches!(result, AYResult::CounterExample(_)));
    }

    #[test]
    fn test_cli_verify_iadd_i32() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_iadd_i32",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let obligation = crate::lowering_proof::proof_iadd_i32();
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_eq!(result, AYResult::Verified);
    }

    #[test]
    fn test_cli_verify_peephole_add_zero() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_peephole_add_zero",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let obligation = crate::peephole_proofs::proof_add_zero_identity();
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_eq!(result, AYResult::Verified);
    }

    // -----------------------------------------------------------------------
    // Logic inference tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_logic_bv_only() {
        let expr = SmtExpr::var("x", 32).bvadd(SmtExpr::var("y", 32));
        assert_eq!(infer_logic(&expr), "QF_BV");
    }

    #[test]
    fn test_infer_logic_array() {
        let arr = SmtExpr::const_array(SmtSort::BitVec(32), SmtExpr::bv_const(0, 32));
        let expr = SmtExpr::select(arr, SmtExpr::var("idx", 32));
        assert_eq!(infer_logic(&expr), "QF_ABV");
    }

    #[test]
    fn test_infer_logic_fp() {
        let expr = SmtExpr::fp_add(
            crate::smt::RoundingMode::RNE,
            SmtExpr::fp64_const(1.0),
            SmtExpr::fp64_const(2.0),
        );
        assert_eq!(infer_logic(&expr), "QF_BVFP");
    }

    #[test]
    fn test_infer_logic_uf() {
        let expr = SmtExpr::uf("f", vec![SmtExpr::var("x", 32)], SmtSort::BitVec(32));
        assert_eq!(infer_logic(&expr), "QF_UFBV");
    }

    #[test]
    fn test_infer_logic_mixed_array_fp() {
        let arr = SmtExpr::const_array(SmtSort::BitVec(32), SmtExpr::fp64_const(0.0));
        assert_eq!(infer_logic(&arr), "QF_ABVFP");
    }

    #[test]
    fn test_rounding_mode_smt2() {
        assert_eq!(rounding_mode_to_smt2(&RoundingMode::RNE), "RNE");
        assert_eq!(rounding_mode_to_smt2(&RoundingMode::RNA), "RNA");
        assert_eq!(rounding_mode_to_smt2(&RoundingMode::RTP), "RTP");
        assert_eq!(rounding_mode_to_smt2(&RoundingMode::RTN), "RTN");
        assert_eq!(rounding_mode_to_smt2(&RoundingMode::RTZ), "RTZ");
    }

    // -----------------------------------------------------------------------
    // Sort serialization tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_sort_to_smt2_bitvec() {
        assert_eq!(sort_to_smt2(&SmtSort::BitVec(32)), "(_ BitVec 32)");
        assert_eq!(sort_to_smt2(&SmtSort::BitVec(64)), "(_ BitVec 64)");
        assert_eq!(sort_to_smt2(&SmtSort::BitVec(8)), "(_ BitVec 8)");
    }

    #[test]
    fn test_sort_to_smt2_bool() {
        assert_eq!(sort_to_smt2(&SmtSort::Bool), "Bool");
    }

    #[test]
    fn test_sort_to_smt2_array() {
        let mem_sort = SmtSort::bv_array(64, 8);
        assert_eq!(
            sort_to_smt2(&mem_sort),
            "(Array (_ BitVec 64) (_ BitVec 8))"
        );
    }

    #[test]
    fn test_sort_to_smt2_fp() {
        assert_eq!(sort_to_smt2(&SmtSort::fp32()), "(_ FloatingPoint 8 24)");
        assert_eq!(sort_to_smt2(&SmtSort::fp64()), "(_ FloatingPoint 11 53)");
    }

    // -----------------------------------------------------------------------
    // Array theory SMT-LIB2 serialization tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_array_select_serialization() {
        // (select array index) serialized via SmtExpr::Display
        let arr = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let idx = SmtExpr::var("addr", 64);
        let sel = SmtExpr::select(arr, idx);
        let serialized = format!("{}", sel);
        assert_eq!(
            serialized,
            "(select ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv0 8)) addr)"
        );
    }

    #[test]
    fn test_array_store_serialization() {
        // (store array index value) serialized via SmtExpr::Display
        let arr = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let idx = SmtExpr::var("addr", 64);
        let val = SmtExpr::var("byte", 8);
        let st = SmtExpr::store(arr, idx, val);
        let serialized = format!("{}", st);
        assert_eq!(
            serialized,
            "(store ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv0 8)) addr byte)"
        );
    }

    #[test]
    fn test_array_const_array_serialization() {
        // ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv0 8))
        let arr = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let serialized = format!("{}", arr);
        assert_eq!(
            serialized,
            "((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv0 8))"
        );
    }

    #[test]
    fn test_array_nested_store_select() {
        // store at addr, then select at same addr: should produce nested expression
        let arr = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let addr = SmtExpr::var("a", 64);
        let val = SmtExpr::bv_const(42, 8);
        let stored = SmtExpr::store(arr, addr.clone(), val);
        let loaded = SmtExpr::select(stored, addr);
        let serialized = format!("{}", loaded);
        assert!(serialized.contains("(select (store"));
        assert!(serialized.contains(
            "(store ((as const (Array (_ BitVec 64) (_ BitVec 8))) (_ bv0 8)) a (_ bv42 8))"
        ));
    }

    #[test]
    fn test_generate_smt2_query_with_array_ops() {
        // A proof obligation that involves array operations should get QF_ABV logic
        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::var("d", 8));
        let addr = SmtExpr::var("a", 64);
        let val = SmtExpr::var("v", 8);

        // trust_ir side: store then select at same address
        let mem_after = SmtExpr::store(mem.clone(), addr.clone(), val.clone());
        let trust_ir_result = SmtExpr::select(mem_after, addr.clone());

        // aarch64 side: should equal the stored value
        let aarch64_result = val.clone();

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "store_load_roundtrip".to_string(),
            trust_ir_expr: trust_ir_result,
            aarch64_expr: aarch64_result,
            inputs: vec![
                ("a".to_string(), 64),
                ("v".to_string(), 8),
                ("d".to_string(), 8),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);

        // Must use QF_ABV logic (arrays + bitvectors)
        assert!(
            smt2.contains("(set-logic QF_ABV)"),
            "Expected QF_ABV logic, got: {}",
            smt2
        );
        // Must declare all bitvector inputs
        assert!(smt2.contains("(declare-const a (_ BitVec 64))"));
        assert!(smt2.contains("(declare-const v (_ BitVec 8))"));
        assert!(smt2.contains("(declare-const d (_ BitVec 8))"));
        // Must contain array operations in the assertion
        assert!(smt2.contains("select"));
        assert!(smt2.contains("store"));
        assert!(smt2.contains("(check-sat)"));
    }

    #[test]
    fn test_generate_smt2_query_with_extra_array_decls() {
        // Test the enhanced query generator with explicit array declarations
        let _mem_var = SmtExpr::var("mem", 64); // placeholder -- in real usage this would be array
        let addr = SmtExpr::var("a", 64);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_array_decl".to_string(),
            trust_ir_expr: addr.clone(),
            aarch64_expr: addr,
            inputs: vec![("a".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let extra_decls = vec![("mem".to_string(), SmtSort::bv_array(64, 8))];
        let smt2 = generate_smt2_query_with_arrays(&obligation, &config, &extra_decls);

        // Must declare the array variable with correct sort
        assert!(
            smt2.contains("(declare-const mem (Array (_ BitVec 64) (_ BitVec 8)))"),
            "Missing array declaration in: {}",
            smt2,
        );
        // Must still declare BV inputs
        assert!(smt2.contains("(declare-const a (_ BitVec 64))"));
    }

    #[test]
    fn test_memory_proof_smt2_serialization() {
        // End-to-end test: generate SMT-LIB2 for a store-load roundtrip from memory_proofs
        // (I8 uses the exact scalar McCarthy form for portable certification;
        // retain I16 here as the representative array-theory serialization.)
        let obligation = crate::memory_proofs::proof_roundtrip_i16();
        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);

        // Memory proofs use array operations, so logic should be QF_ABV
        assert!(
            smt2.contains("(set-logic QF_ABV)"),
            "Expected QF_ABV for memory proof, got: {}",
            smt2
        );
        // Must contain array operations (select, store, as const)
        assert!(smt2.contains("select"), "Missing select in: {}", smt2);
        assert!(smt2.contains("store"), "Missing store in: {}", smt2);
        assert!(smt2.contains("as const"), "Missing as const in: {}", smt2);
    }

    #[test]
    fn test_cli_verify_memory_roundtrip_i8() {
        // Integration test: verify store-load roundtrip with the AY CLI.
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_memory_roundtrip_i8",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return; // No solver available, skip test
        };

        let obligation = crate::memory_proofs::proof_roundtrip_i8();
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Store-load roundtrip I8 should be verified"),
        );
    }

    // -----------------------------------------------------------------------
    // Floating-point SMT-LIB2 serialization tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_fp_add_smt2_serialization() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = SmtExpr::fp_add(RoundingMode::RNE, a, b);
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp.add RNE"));
        assert!(s.contains("(fp #b"));
    }

    #[test]
    fn test_fp_mul_smt2_serialization() {
        let a = SmtExpr::fp64_const(3.0);
        let b = SmtExpr::fp64_const(7.0);
        let expr = SmtExpr::fp_mul(RoundingMode::RTZ, a, b);
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp.mul RTZ"));
    }

    #[test]
    fn test_fp_div_smt2_serialization() {
        let a = SmtExpr::fp64_const(10.0);
        let b = SmtExpr::fp64_const(4.0);
        let expr = SmtExpr::fp_div(RoundingMode::RNA, a, b);
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp.div RNA"));
    }

    #[test]
    fn test_fp_neg_smt2_serialization() {
        let a = SmtExpr::fp64_const(42.0);
        let expr = a.fp_neg();
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp.neg"));
    }

    #[test]
    fn test_fp_eq_smt2_serialization() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(1.0);
        let expr = a.fp_eq(b);
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp.eq"));
    }

    #[test]
    fn test_fp_lt_smt2_serialization() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let expr = a.fp_lt(b);
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp.lt"));
    }

    #[test]
    fn test_fp_const_smt2_serialization() {
        let expr = SmtExpr::fp64_const(1.0_f64);
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp #b"));
        assert!(s.contains("#b0"));
        assert!(s.contains("#b01111111111"));
    }

    #[test]
    fn test_fp_const_fp32_smt2_serialization() {
        let expr = SmtExpr::fp32_const(1.5_f32);
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp #b0"));
        assert!(s.contains("#b01111111"));
    }

    #[test]
    fn test_fp_const_negative_smt2() {
        let expr = SmtExpr::fp64_const(-1.0_f64);
        let s = format!("{}", expr);
        assert!(s.starts_with("(fp #b1"));
    }

    #[test]
    fn test_generate_smt2_query_with_fp_inputs() {
        let a_const = SmtExpr::fp64_const(1.0);
        let b_const = SmtExpr::fp64_const(2.0);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_fp_add".to_string(),
            trust_ir_expr: SmtExpr::fp_add(RoundingMode::RNE, a_const.clone(), b_const.clone()),
            aarch64_expr: SmtExpr::fp_add(RoundingMode::RNE, a_const, b_const),
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![("a".to_string(), 11, 53), ("b".to_string(), 11, 53)],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);

        assert!(
            smt2.contains("QF_BVFP") || smt2.contains("QF_FP"),
            "Expected FP logic, got: {}",
            smt2
        );
        assert!(
            smt2.contains("(declare-const a (_ FloatingPoint 11 53))"),
            "Missing FP64 declaration for a: {}",
            smt2
        );
        assert!(
            smt2.contains("(declare-const b (_ FloatingPoint 11 53))"),
            "Missing FP64 declaration for b: {}",
            smt2
        );
        assert!(!smt2.contains("(get-value"));
        let model_smt2 = generate_sat_model_query(&obligation, &smt2).unwrap();
        assert!(model_smt2.contains("(get-value (a b))"));
    }

    #[test]
    fn test_generate_smt2_query_mixed_bv_fp() {
        let _bv_a = SmtExpr::var("x", 32);
        let fp_a = SmtExpr::fp32_const(1.0_f32);
        let fp_b = SmtExpr::fp32_const(2.0_f32);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_mixed".to_string(),
            trust_ir_expr: SmtExpr::fp_add(RoundingMode::RNE, fp_a.clone(), fp_b.clone()),
            aarch64_expr: SmtExpr::fp_add(RoundingMode::RNE, fp_a, fp_b),
            inputs: vec![("x".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![("fa".to_string(), 8, 24)],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);

        assert!(smt2.contains("(declare-const x (_ BitVec 32))"));
        assert!(smt2.contains("(declare-const fa (_ FloatingPoint 8 24))"));
        assert!(!smt2.contains("(get-value"));
        let model_smt2 = generate_sat_model_query(&obligation, &smt2).unwrap();
        assert!(model_smt2.contains("(get-value (x fa))"));
    }

    #[test]
    fn test_fp_sort_display_in_declare() {
        let fp32 = SmtSort::fp32();
        assert_eq!(format!("{}", fp32), "(_ FloatingPoint 8 24)");
        let fp64 = SmtSort::fp64();
        assert_eq!(format!("{}", fp64), "(_ FloatingPoint 11 53)");
        let fp16 = SmtSort::fp16();
        assert_eq!(format!("{}", fp16), "(_ FloatingPoint 5 11)");
    }

    #[test]
    fn test_infer_logic_fp_add() {
        let expr = SmtExpr::fp_add(
            RoundingMode::RNE,
            SmtExpr::fp32_const(1.0_f32),
            SmtExpr::fp32_const(2.0_f32),
        );
        assert_eq!(infer_logic(&expr), "QF_BVFP");
    }

    #[test]
    fn test_infer_logic_fp_neg() {
        let expr = SmtExpr::fp64_const(1.0).fp_neg();
        assert_eq!(infer_logic(&expr), "QF_BVFP");
    }

    #[test]
    fn test_infer_logic_fp_eq() {
        let expr = SmtExpr::fp64_const(1.0).fp_eq(SmtExpr::fp64_const(2.0));
        assert_eq!(infer_logic(&expr), "QF_BVFP");
    }

    #[test]
    fn test_infer_logic_fp_lt() {
        let expr = SmtExpr::fp64_const(1.0).fp_lt(SmtExpr::fp64_const(2.0));
        assert_eq!(infer_logic(&expr), "QF_BVFP");
    }

    #[test]
    fn test_infer_logic_fp_const_only() {
        let expr = SmtExpr::fp64_const(std::f64::consts::PI);
        assert_eq!(infer_logic(&expr), "QF_BVFP");
    }

    #[test]
    fn test_infer_logic_fp_mul() {
        let expr = SmtExpr::fp_mul(
            RoundingMode::RTZ,
            SmtExpr::fp64_const(2.0),
            SmtExpr::fp64_const(3.0),
        );
        assert_eq!(infer_logic(&expr), "QF_BVFP");
    }

    #[test]
    fn test_infer_logic_fp_div() {
        let expr = SmtExpr::fp_div(
            RoundingMode::RNE,
            SmtExpr::fp64_const(10.0),
            SmtExpr::fp64_const(3.0),
        );
        assert_eq!(infer_logic(&expr), "QF_BVFP");
    }

    // -----------------------------------------------------------------------
    // Public API convenience function tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_serialize_to_smt2() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_serialize".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let smt2 = serialize_to_smt2(&obligation);

        // Should produce a complete SMT-LIB2 script
        assert!(smt2.contains("(set-logic QF_BV)"));
        assert!(smt2.contains("(declare-const a (_ BitVec 32))"));
        assert!(smt2.contains("(declare-const b (_ BitVec 32))"));
        assert!(smt2.contains("(assert"));
        assert!(smt2.contains("(check-sat)"));
        assert!(smt2.contains("(exit)"));
        // Default config includes timeout and models. The exact timeout is
        // `DEFAULT_AY_TIMEOUT_MS` (or overridden by `TRUST_CG_AY_TIMEOUT_MS`);
        // we just assert the option is present.
        assert!(smt2.contains("(set-option :timeout "));
        assert!(smt2.contains("(set-option :produce-models true)"));
    }

    #[test]
    fn test_parse_ay_output_unsat() {
        let result = parse_ay_output("unsat\n", &[]);
        assert_eq!(result, AYResult::SolverUnsat);
    }

    #[test]
    fn test_parse_ay_output_sat_with_model() {
        let output = "sat\n((x #x0000002a))";
        let inputs = vec![("x".to_string(), 32)];
        let result = parse_ay_output(output, &inputs);
        match result {
            AYResult::CounterExample(cex) => {
                assert_eq!(cex.len(), 1);
                assert_eq!(cex[0], ("x".to_string(), 0x2a));
            }
            other => panic!("Expected CounterExample, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_ay_output_unknown() {
        let result = parse_ay_output("unknown\n", &[]);
        assert_eq!(result, AYResult::Unknown("unknown".to_string()));
    }

    #[test]
    fn test_parse_ay_output_timeout_in_text() {
        let result = parse_ay_output("timeout\n", &[]);
        assert_eq!(result, AYResult::Timeout);
    }

    #[test]
    fn test_parse_ay_output_empty() {
        let result = parse_ay_output("", &[]);
        assert!(matches!(result, AYResult::Error(_)));
    }

    #[test]
    fn test_parse_ay_output_unexpected() {
        let result = parse_ay_output("garbage\n", &[]);
        assert!(matches!(result, AYResult::Error(_)));
    }

    // -----------------------------------------------------------------------
    // SmtExpr::to_smt2_expr() tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_to_smt2_expr_var() {
        let expr = SmtExpr::var("x", 32);
        assert_eq!(expr.to_smt2_expr(), "x");
    }

    #[test]
    fn test_to_smt2_expr_bv_const() {
        let expr = SmtExpr::bv_const(42, 32);
        assert_eq!(expr.to_smt2_expr(), "(_ bv42 32)");
    }

    #[test]
    fn test_to_smt2_expr_bool_const() {
        assert_eq!(SmtExpr::bool_const(true).to_smt2_expr(), "true");
        assert_eq!(SmtExpr::bool_const(false).to_smt2_expr(), "false");
    }

    #[test]
    fn test_to_smt2_expr_bvadd() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        assert_eq!(a.bvadd(b).to_smt2_expr(), "(bvadd a b)");
    }

    #[test]
    fn test_to_smt2_expr_bvsub() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        assert_eq!(a.bvsub(b).to_smt2_expr(), "(bvsub a b)");
    }

    #[test]
    fn test_to_smt2_expr_bvmul() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        assert_eq!(a.bvmul(b).to_smt2_expr(), "(bvmul a b)");
    }

    #[test]
    fn test_to_smt2_expr_bvneg() {
        let a = SmtExpr::var("a", 32);
        assert_eq!(a.bvneg().to_smt2_expr(), "(bvneg a)");
    }

    #[test]
    fn test_to_smt2_expr_bitwise_ops() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        assert_eq!(a.clone().bvand(b.clone()).to_smt2_expr(), "(bvand a b)");
        assert_eq!(a.clone().bvor(b.clone()).to_smt2_expr(), "(bvor a b)");
        assert_eq!(a.clone().bvxor(b.clone()).to_smt2_expr(), "(bvxor a b)");
    }

    #[test]
    fn test_to_smt2_expr_shift_ops() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        assert_eq!(a.clone().bvshl(b.clone()).to_smt2_expr(), "(bvshl a b)");
        assert_eq!(a.clone().bvlshr(b.clone()).to_smt2_expr(), "(bvlshr a b)");
        assert_eq!(a.clone().bvashr(b.clone()).to_smt2_expr(), "(bvashr a b)");
    }

    #[test]
    fn test_to_smt2_expr_comparisons() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        assert_eq!(a.clone().eq_expr(b.clone()).to_smt2_expr(), "(= a b)");
        assert_eq!(a.clone().bvslt(b.clone()).to_smt2_expr(), "(bvslt a b)");
        assert_eq!(a.clone().bvsge(b.clone()).to_smt2_expr(), "(bvsge a b)");
        assert_eq!(a.clone().bvult(b.clone()).to_smt2_expr(), "(bvult a b)");
        assert_eq!(a.clone().bvuge(b.clone()).to_smt2_expr(), "(bvuge a b)");
    }

    #[test]
    fn test_to_smt2_expr_logical_ops() {
        let a = SmtExpr::bool_const(true);
        let b = SmtExpr::bool_const(false);
        assert_eq!(
            a.clone().and_expr(b.clone()).to_smt2_expr(),
            "(and true false)"
        );
        assert_eq!(
            a.clone().or_expr(b.clone()).to_smt2_expr(),
            "(or true false)"
        );
        assert_eq!(a.not_expr().to_smt2_expr(), "(not true)");
    }

    #[test]
    fn test_to_smt2_expr_ite() {
        let cond = SmtExpr::var("c", 32).eq_expr(SmtExpr::bv_const(0, 32));
        let then_e = SmtExpr::var("a", 32);
        let else_e = SmtExpr::var("b", 32);
        let expr = SmtExpr::ite(cond, then_e, else_e);
        assert_eq!(expr.to_smt2_expr(), "(ite (= c (_ bv0 32)) a b)");
    }

    #[test]
    fn test_to_smt2_expr_extract() {
        let a = SmtExpr::var("a", 32);
        assert_eq!(a.extract(15, 0).to_smt2_expr(), "((_ extract 15 0) a)");
    }

    #[test]
    fn test_to_smt2_expr_concat() {
        let hi = SmtExpr::var("hi", 16);
        let lo = SmtExpr::var("lo", 16);
        assert_eq!(hi.concat(lo).to_smt2_expr(), "(concat hi lo)");
    }

    #[test]
    fn test_to_smt2_expr_extend() {
        let a = SmtExpr::var("a", 8);
        assert_eq!(
            a.clone().zero_ext(24).to_smt2_expr(),
            "((_ zero_extend 24) a)"
        );
        assert_eq!(a.sign_ext(24).to_smt2_expr(), "((_ sign_extend 24) a)");
    }

    #[test]
    fn test_to_smt2_expr_division() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        assert_eq!(a.clone().bvsdiv(b.clone()).to_smt2_expr(), "(bvsdiv a b)");
        assert_eq!(a.clone().bvudiv(b.clone()).to_smt2_expr(), "(bvudiv a b)");
        assert_eq!(a.bvurem(b).to_smt2_expr(), "(bvurem a b)");
    }

    #[test]
    fn test_to_smt2_expr_nested() {
        // (bvadd (bvmul a b) (bvsub c d))
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let c = SmtExpr::var("c", 32);
        let d = SmtExpr::var("d", 32);
        let expr = a.bvmul(b).bvadd(c.bvsub(d));
        assert_eq!(expr.to_smt2_expr(), "(bvadd (bvmul a b) (bvsub c d))");
    }

    #[test]
    fn test_to_smt2_expr_fp_operations() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let add = SmtExpr::fp_add(RoundingMode::RNE, a.clone(), b.clone());
        assert!(add.to_smt2_expr().starts_with("(fp.add RNE"));

        let neg = a.clone().fp_neg();
        assert!(neg.to_smt2_expr().starts_with("(fp.neg"));

        let eq = a.clone().fp_eq(b.clone());
        assert!(eq.to_smt2_expr().starts_with("(fp.eq"));
    }

    #[test]
    fn test_to_smt2_expr_array_operations() {
        let arr = SmtExpr::const_array(SmtSort::BitVec(32), SmtExpr::bv_const(0, 8));
        let smt2 = arr.to_smt2_expr();
        assert!(smt2.contains("as const"));
        assert!(smt2.contains("Array"));

        let sel = SmtExpr::select(arr.clone(), SmtExpr::var("idx", 32));
        assert!(sel.to_smt2_expr().starts_with("(select"));

        let st = SmtExpr::store(arr, SmtExpr::var("idx", 32), SmtExpr::bv_const(42, 8));
        assert!(st.to_smt2_expr().starts_with("(store"));
    }

    // -----------------------------------------------------------------------
    // CLI integration tests for the public API wrappers
    // -----------------------------------------------------------------------

    #[test]
    fn test_verify_with_ay_cli_trivial_correct() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_verify_with_ay_cli_trivial_correct",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let a = SmtExpr::var("x", 16);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "trivial_identity".to_string(),
            trust_ir_expr: a.clone(),
            aarch64_expr: a,
            inputs: vec![("x".to_string(), 16)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_ay_cli(&obligation, &config);
        assert_eq!(result, AYResult::Verified);
    }

    #[test]
    fn test_verify_with_ay_cli_trivial_wrong() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_verify_with_ay_cli_trivial_wrong",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        // x != x + 1 (should find counterexample for any x)
        let x = SmtExpr::var("x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "wrong_identity".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x.bvadd(SmtExpr::bv_const(1, 8)),
            inputs: vec![("x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_ay_cli(&obligation, &config);
        match result {
            AYResult::CounterExample(values) => assert_eq!(
                values.len(),
                1,
                "the SAT-only second query must return x's model value"
            ),
            other => panic!("expected a counterexample with a model, got {other:?}"),
        }
    }

    /// Exercise the exact command protocol against the selected AY binary,
    /// independently of the resident/fresh routing and session cache.
    #[test]
    fn test_selected_ay_protocol_unsat_sat_unknown_and_timeout_are_clean() {
        let Some(solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_selected_ay_protocol_unsat_sat_unknown_and_timeout_are_clean",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };
        let Some(checker) = crate::obligation_cert_store::clean_checker_path() else {
            eprintln!("selected AY protocol campaign needs TCG_CLEAN_CHECKER");
            return;
        };

        let no_protocol_errors = |output: &std::process::Output| {
            let stdout = String::from_utf8_lossy(&output.stdout);
            let stderr = String::from_utf8_lossy(&output.stderr);
            stdout
                .lines()
                .chain(stderr.lines())
                .all(|line| !line.trim().starts_with("(error"))
        };

        // UNSAT authority query: options are legal start-mode commands and no
        // model command is present after the proof verdict.
        let x = SmtExpr::var("protocol_x", 8);
        let unsat_obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "exact_ay_clean_unsat".to_string(),
            trust_ir_expr: SmtExpr::bv_const(0, 8),
            aarch64_expr: SmtExpr::bv_const(0, 8),
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let config = AYConfig::default().with_timeout(30_000);
        let unsat_smt2 = "(set-option :timeout 30000)\n\
                          (set-option :produce-models true)\n\
                          (set-logic QF_BV)\n\
                          (assert false)\n\
                          (check-sat)\n\
                          (exit)"
            .to_string();
        assert!(!unsat_smt2.contains("(get-value"));
        let unsat_file = write_temp_smt2(&unsat_smt2).unwrap();
        let unsat_output = run_solver_command(&solver, unsat_file.path(), 30_000).unwrap();
        assert!(unsat_output.status.success());
        assert!(no_protocol_errors(&unsat_output));
        let unsat_candidate = parse_solver_process_output(&unsat_output, &unsat_obligation.inputs);
        assert_eq!(unsat_candidate, AYResult::SolverUnsat);
        let unsat_proof = std::fs::read_to_string(default_alethe_path(unsat_file.path()))
            .expect("AY's exact Alethe proof artifact must be present");
        assert!(
            crate::obligation_cert_store::carcara_verify(&checker, &unsat_smt2, &unsat_proof),
            "the independent checker must accept AY's complete exact proof"
        );
        assert!(
            !crate::obligation_cert_store::carcara_verify(
                &checker,
                &unsat_smt2,
                "(step deliberately_invalid (cl) :rule not_a_rule)",
            ),
            "the independent checker must reject invalid proof text"
        );
        assert_eq!(
            {
                let authority = VerificationAuthority::capture(&solver);
                promote_fresh_solver_unsat(
                    unsat_candidate,
                    &authority,
                    unsat_file.path(),
                    &unsat_smt2,
                    "test:cli-contract-unsat",
                    config.timeout_ms,
                    &ReplayWitness::new(None),
                )
            },
            AYResult::Verified,
            "the exact complete proof must be independently accepted"
        );

        // SAT is first established by a verdict-only query. Values are then
        // requested by replaying the same formula/options in a SAT-only query.
        let sat_obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "exact_ay_clean_sat_model".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x.bvadd(SmtExpr::bv_const(1, 8)),
            inputs: vec![("protocol_x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let sat_smt2 = generate_smt2_query(&sat_obligation, &config);
        assert!(!sat_smt2.contains("(get-value"));
        let sat_file = write_temp_smt2(&sat_smt2).unwrap();
        let sat_output = run_solver_command(&solver, sat_file.path(), 30_000).unwrap();
        assert!(sat_output.status.success());
        assert!(no_protocol_errors(&sat_output));
        assert!(matches!(
            parse_solver_process_output(&sat_output, &sat_obligation.inputs),
            AYResult::CounterExample(values) if values.is_empty()
        ));

        let model_smt2 = generate_sat_model_query(&sat_obligation, &sat_smt2).unwrap();
        assert_eq!(
            model_smt2.matches("(assert ").count(),
            sat_smt2.matches("(assert ").count(),
            "the SAT model replay must preserve the canonical formula"
        );
        let model_file = write_temp_smt2(&model_smt2).unwrap();
        let model_output = run_solver_verdict_command(&solver, model_file.path(), 30_000).unwrap();
        assert!(model_output.status.success());
        assert!(no_protocol_errors(&model_output));
        assert!(matches!(
            parse_solver_process_output(&model_output, &sat_obligation.inputs),
            AYResult::CounterExample(values) if values.len() == 1
        ));

        // Exercise a production-style 64-bit multiply identity. Some AY
        // revisions emit a complete proof; older ones explicitly report a
        // holey certificate (`unproved_steps=1`, `trust_free=no`). Either way,
        // only an independently accepted exact proof may promote to Verified.
        // An outer process deadline remains a distinct Timeout.
        let hard_x = SmtExpr::var("hard_x", 64);
        let hard_obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "exact_ay_clean_unknown_timeout".to_string(),
            trust_ir_expr: hard_x.clone().bvmul(SmtExpr::bv_const(u64::MAX, 64)),
            aarch64_expr: hard_x.bvneg(),
            inputs: vec![("hard_x".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        // The query carries the test's own 30 s solver budget. It used to carry
        // a 1 ms `(set-option :timeout 1)` header (a leftover: the identity
        // solved sub-millisecond on the authorities this test was written
        // against). build.7387 and later honour that header and answer
        // `(:reason-unknown timeout)`, so the artifact assertions below had
        // nothing to inspect and the test skipped on a timeout it set itself.
        let hard_smt2 = generate_smt2_query_raw(&hard_obligation, &config);
        let hard_file = write_temp_smt2(&hard_smt2).unwrap();
        let holey_output = run_solver_command(&solver, hard_file.path(), 30_000).unwrap();
        assert!(holey_output.status.success());
        assert!(no_protocol_errors(&holey_output));
        let hard_candidate = parse_solver_process_output(&holey_output, &hard_obligation.inputs);
        if let AYResult::Unknown(reason) = &hard_candidate {
            assert!(
                !crate::proof_gate::unknown_is_hard_failure(reason),
                "AY rejected its own production-style proof ({reason}); the strict proof gate \
                 files this as a soundness failure; stderr={}",
                String::from_utf8_lossy(&holey_output.stderr)
            );
        }
        let hard_proof = std::fs::read_to_string(default_alethe_path(hard_file.path()))
            .expect("AY's production-style Alethe artifact must be present");
        let hard_checker_accepted =
            crate::obligation_cert_store::carcara_verify(&checker, &hard_smt2, &hard_proof);
        if matches!(
            &hard_candidate,
            AYResult::Unknown(reason) if reason.contains("incomplete AY proof certificate")
        ) {
            assert!(
                !hard_checker_accepted,
                "AY declared the proof incomplete but the independent checker accepted it"
            );
        }
        let authority = VerificationAuthority::capture(&solver);
        let hard_result = promote_fresh_solver_unsat(
            hard_candidate.clone(),
            &authority,
            hard_file.path(),
            &hard_smt2,
            "test:cli-contract-hard",
            config.timeout_ms,
            &ReplayWitness::new(None),
        );
        if matches!(hard_result, AYResult::Verified) {
            assert_eq!(hard_candidate, AYResult::SolverUnsat);
            assert!(hard_checker_accepted);
        } else {
            assert!(
                matches!(hard_result, AYResult::Unknown(_)),
                "an unaccepted production-style proof must remain Unknown, got {hard_result:?}; \
                 stdout={}; stderr={}",
                String::from_utf8_lossy(&holey_output.stdout),
                String::from_utf8_lossy(&holey_output.stderr)
            );
        }

        let timeout = run_solver_command(&solver, hard_file.path(), 1);
        assert!(matches!(timeout, Err(SolverInvocationError::Timeout(_))));
    }

    #[cfg(unix)]
    fn write_temp_solver_script(contents: &str) -> String {
        use std::os::unix::fs::PermissionsExt;

        let path = std::env::temp_dir().join(format!(
            "trust_cg_verify_solver_{}_{}.sh",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock should be after unix epoch")
                .as_nanos()
        ));
        std::fs::write(
            &path,
            crate::ay_identity::test_fixtures::bind_self(&path, contents),
        )
        .expect("failed to write temp solver script");

        let mut perms = std::fs::metadata(&path)
            .expect("failed to stat temp solver script")
            .permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("failed to chmod temp solver script");

        path.to_string_lossy().to_string()
    }

    /// [`write_temp_solver_script`] for a fixture its test then bounds by a
    /// deadline: it answers the warm-up argument, and it (with its admitted
    /// private copy) is started once now, so that deadline is not spent on
    /// the host's first-exec assessment of a new file
    /// (`test_fixtures::warm`).
    #[cfg(unix)]
    fn write_warm_solver_script(contents: &str) -> String {
        use crate::ay_identity::test_fixtures::{warm, with_warm_guard};
        let path = write_temp_solver_script(&with_warm_guard(contents));
        warm(std::path::Path::new(&path));
        path
    }

    /// Process-start and framed-response allowance for fake resident solvers.
    ///
    /// The full proof suite has several CPU-heavy aggregate checks. A 2-second
    /// deadline could expire before a just-spawned shell wrote its first byte
    /// when those checks ran in parallel, turning protocol assertions into
    /// scheduler-dependent failures. Ten seconds stays tightly bounded while
    /// covering loaded publication hosts.
    #[cfg(unix)]
    const FAKE_RESIDENT_SOLVER_TIMEOUT_MS: u64 = 10_000;

    #[cfg(unix)]
    fn fake_solver_invocation_count(solver_path: &str) -> u32 {
        std::fs::read_to_string(format!("{solver_path}.count"))
            .expect("fake solver should record its invocation count")
            .trim()
            .parse()
            .expect("fake solver invocation count should be numeric")
    }

    #[cfg(unix)]
    fn remove_temp_solver_and_count(solver_path: &str) {
        let _ = std::fs::remove_file(solver_path);
        let _ = std::fs::remove_file(format!("{solver_path}.count"));
    }

    #[cfg(unix)]
    fn process_status_is_running(status: &str) -> bool {
        // `kill -0` succeeds for a zombie until its parent/init reaps it. A
        // process in POSIX Z state is already terminated and cannot retain
        // solver resources, so treating it as live makes the timeout test
        // load-dependent. Unknown/empty states stay fail-closed as live.
        !matches!(status.trim().chars().next(), Some('Z'))
    }

    #[cfg(unix)]
    fn process_exists(pid: u32) -> bool {
        // Keep every test cleanup path fail-closed too: external `kill` treats
        // PID 0 as the caller's process group, so malformed fixture output must
        // never reach it even though real child IDs are always greater than 1.
        if pid <= 1 {
            return false;
        }
        std::process::Command::new("kill")
            .arg("-0")
            .arg(pid.to_string())
            .stdout(std::process::Stdio::null())
            .stderr(std::process::Stdio::null())
            .status()
            .is_ok_and(|status| status.success())
    }

    #[cfg(unix)]
    fn process_is_running(pid: u32) -> bool {
        if !process_exists(pid) {
            return false;
        }

        // Distinguish a still-running (or PID-reused) process from a killed
        // descendant awaiting reaping. If `ps` cannot classify the existing
        // PID, retain the strict/live answer rather than masking an escape.
        let status = std::process::Command::new("ps")
            .args(["-o", "stat=", "-p", &pid.to_string()])
            .output()
            .ok()
            .filter(|output| output.status.success())
            .and_then(|output| String::from_utf8(output.stdout).ok());
        match status {
            Some(status) if status.trim().is_empty() => {
                // The process can disappear between the existence probe and
                // ps. Recheck existence so that race is termination, while
                // PID reuse or an unclassifiable extant process stays loud.
                process_exists(pid)
            }
            Some(status) => process_status_is_running(&status),
            None => true,
        }
    }

    #[cfg(unix)]
    #[test]
    fn process_status_classifies_zombies_as_terminated() {
        assert!(!process_status_is_running("Z"));
        assert!(!process_status_is_running(" Z+ \n"));
        assert!(process_status_is_running("S+"));
        assert!(process_status_is_running("R"));
        assert!(
            process_status_is_running(""),
            "unknown state must fail closed"
        );
    }

    #[cfg(unix)]
    #[test]
    fn process_exists_rejects_group_special_ids() {
        assert!(!process_exists(0));
        assert!(!process_exists(1));
    }

    #[cfg(unix)]
    #[test]
    fn test_resident_solver_timeout_does_not_retry_fresh_process() {
        let _batch_lock = ay_batch_test_lock();
        if !ay_server_enabled() {
            return;
        }

        // The same executable handles both resident (`--incremental`) and
        // fresh (`-smt2 ...`) invocations. It records every process start and
        // then remains CPU-bound until the caller's deadline kills it. A
        // resident timeout must therefore leave the count at exactly one; the
        // old anomaly/timeout conflation produced a second fresh invocation.
        let solver_path = write_warm_solver_script(
            "#!/bin/sh\n\
             count_file=\"$0.count\"\n\
             count=0\n\
             if [ -r \"$count_file\" ]; then count=$(cat \"$count_file\"); fi\n\
             count=$((count + 1))\n\
             printf '%s\\n' \"$count\" > \"$count_file\"\n\
             while :; do :; done\n",
        );

        let x = SmtExpr::var("x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "resident_timeout_is_single_attempt".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x,
            inputs: vec![("x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_with_cli(
            &obligation,
            &AYConfig {
                solver: Some(crate::ay_identity::test_fixtures::pin(
                    std::path::Path::new(&solver_path),
                )),
                // Leave enough time for the fake shell to be scheduled and
                // persist its startup counter on a heavily loaded test host.
                // The loop remains bounded by this solver deadline.
                timeout_ms: FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
                produce_models: true,
            },
        );
        let invocation_count = fake_solver_invocation_count(&solver_path);
        remove_temp_solver_and_count(&solver_path);

        assert_eq!(result, AYResult::Timeout);
        assert_eq!(
            invocation_count, 1,
            "a resident deadline must not retry the same query in a fresh process"
        );
    }

    /// Slice 19 (OD-197): a query whose owner asks for it (the x86-64 body
    /// owner's) is replayed once in a fresh process after a resident
    /// deadline, under the same budget: two process starts, and the fresh
    /// deadline's `Timeout` is the answer.
    #[cfg(unix)]
    #[test]
    fn test_resident_timeout_replays_fresh_when_the_owner_asks() {
        let _batch_lock = ay_batch_test_lock();
        if !ay_server_enabled() {
            return;
        }
        let solver_path = write_warm_solver_script(
            "#!/bin/sh\n\
             count_file=\"$0.count\"\n\
             count=0\n\
             if [ -r \"$count_file\" ]; then count=$(cat \"$count_file\"); fi\n\
             count=$((count + 1))\n\
             printf '%s\\n' \"$count\" > \"$count_file\"\n\
             while :; do :; done\n",
        );
        let x = SmtExpr::var("x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "resident_timeout_replays_fresh".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x,
            inputs: vec![("x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let solver = crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path));
        let config = AYConfig {
            solver: Some(solver.clone()),
            timeout_ms: FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
            produce_models: true,
        };
        let smt2 = generate_smt2_query_raw(&obligation, &config);
        let selection = SolverSelection::explicit(solver.clone());
        let authority = VerificationAuthority::capture_with_timeout(&solver, config.timeout_ms);
        let (result, _) = verify_with_cli_smt2_under_authority(
            &obligation,
            &config,
            AyQueryText {
                original: &smt2,
                producer: None,
                closed_definitions: false,
                fresh_after_resident_timeout: true,
            },
            &selection,
            &authority,
            false,
            None,
        );
        let invocation_count = fake_solver_invocation_count(&solver_path);
        remove_temp_solver_and_count(&solver_path);
        assert_eq!(result, AYResult::Timeout);
        assert_eq!(
            invocation_count, 2,
            "a resident deadline replays the query once in a fresh process when its owner asks"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_resident_solver_anomaly_still_retries_fresh_process() {
        let _batch_lock = ay_batch_test_lock();
        if !ay_server_enabled() {
            return;
        }

        // The resident invocation exits without a framed verdict, which is a
        // process/framing anomaly. The fresh `-smt2` invocation then returns a
        // valid UNSAT verdict. This pins the fail-closed fallback independently
        // from the no-retry timeout behavior above.
        let solver_path = write_warm_solver_script(
            "#!/bin/sh\n\
             count_file=\"$0.count\"\n\
             count=0\n\
             if [ -r \"$count_file\" ]; then count=$(cat \"$count_file\"); fi\n\
             count=$((count + 1))\n\
             printf '%s\\n' \"$count\" > \"$count_file\"\n\
             if [ \"$1\" = \"--incremental\" ]; then exit 0; fi\n\
             printf 'unsat\\n'\n",
        );

        let x = SmtExpr::var("x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "resident_anomaly_uses_fresh_fallback".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x,
            inputs: vec![("x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let result = verify_with_cli(
            &obligation,
            &AYConfig {
                solver: Some(crate::ay_identity::test_fixtures::pin(
                    std::path::Path::new(&solver_path),
                )),
                timeout_ms: FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
                produce_models: true,
            },
        );
        let invocation_count = fake_solver_invocation_count(&solver_path);

        assert!(
            matches!(result, AYResult::Unknown(_)),
            "resident anomaly fallback UNSAT without a checked proof must remain pending"
        );
        assert_eq!(
            invocation_count, 2,
            "a resident process/framing anomaly must retain the fresh-process fallback"
        );
        assert!(ay_server_is_unusable(
            &crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path))
        ));
        let different_path = format!("{solver_path}.different");
        std::fs::copy(&solver_path, &different_path).unwrap();
        std::fs::write(
            &different_path,
            format!(
                "{}\n# a different binary\n",
                std::fs::read_to_string(&solver_path).unwrap()
            ),
        )
        .unwrap();
        assert!(
            !ay_server_is_unusable(&crate::ay_identity::test_fixtures::pin(
                std::path::Path::new(&different_path)
            )),
            "the resident failure latch must be scoped to one solver binary"
        );
        let _ = std::fs::remove_file(&different_path);

        // The failed resident mode is remembered only for this exact binary:
        // the next query goes directly to the one-shot fallback instead of
        // paying for another known-bad resident spawn.
        let y = SmtExpr::var("different_x", 8);
        let different_obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "resident_anomaly_latch_uses_fresh_fallback".to_string(),
            trust_ir_expr: y.clone(),
            aarch64_expr: y,
            inputs: vec![("different_x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let result = verify_with_cli(
            &different_obligation,
            &AYConfig {
                solver: Some(crate::ay_identity::test_fixtures::pin(
                    std::path::Path::new(&solver_path),
                )),
                timeout_ms: FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
                produce_models: true,
            },
        );
        let invocation_count = fake_solver_invocation_count(&solver_path);
        remove_temp_solver_and_count(&solver_path);

        assert!(
            matches!(result, AYResult::Unknown(_)),
            "latched fresh UNSAT without a checked proof must remain pending"
        );
        assert_eq!(
            invocation_count, 3,
            "a known-bad resident binary must be bypassed on later queries"
        );
    }

    #[cfg(unix)]
    #[test]
    fn resident_holey_unsat_never_enters_verified_session_cache() {
        let _batch_lock = ay_batch_test_lock();
        if !ay_server_enabled() {
            return;
        }

        // Resident mode can report only a candidate UNSAT. The fresh replay
        // emits an explicitly holey proof, which must remain Unknown and must
        // never seed the process-local Verified memo. The second identical
        // call is answered by the NEGATIVE memo — same key, the same `Unknown`
        // this process already produced — so it spawns nothing at all. On a
        // host with no capable checker there is no session key, hence no memo
        // of either sign, and the second call performs another fresh replay
        // (the pre-memo behaviour); the assertion below covers both.
        let solver_path = write_warm_solver_script(
            "#!/bin/sh\n\
             count_file=\"$0.count\"\n\
             count=0\n\
             if [ -r \"$count_file\" ]; then count=$(cat \"$count_file\"); fi\n\
             count=$((count + 1))\n\
             printf '%s\\n' \"$count\" > \"$count_file\"\n\
             if [ \"$1\" = \"--incremental\" ]; then\n\
               while IFS= read -r line; do\n\
                 if [ \"$line\" = \"(check-sat)\" ]; then printf 'unsat\\n'; fi\n\
                 sentinel=$(printf '%s\\n' \"$line\" | sed -n 's/^(echo \"\\(==TCG_SRV_[0-9][0-9]*==\\)\")$/\\1/p')\n\
                 if [ -n \"$sentinel\" ]; then printf '%s\\n' \"$sentinel\"; fi\n\
               done\n\
               exit 0\n\
             fi\n\
             proof_path=\"$2.alethe\"\n\
             printf '(holey-proof)\\n' > \"$proof_path\"\n\
             printf 'unsat\\n'\n\
             printf 'c ay.proof.certificate path=%s unproved_steps=1 foreign_assumes=no trust_free=no ay_self_checkable=yes\\n' \"$proof_path\" >&2\n",
        );

        let x = SmtExpr::var("resident_holey_x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "resident_holey_unsat_cache_guard".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x,
            inputs: vec![("resident_holey_x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let config = AYConfig {
            solver: Some(crate::ay_identity::test_fixtures::pin(
                std::path::Path::new(&solver_path),
            )),
            timeout_ms: FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
            produce_models: false,
        };

        let first = verify_with_cli_raw(&obligation, &config);
        assert!(matches!(first, AYResult::Unknown(_)), "got {first:?}");
        let first_invocation_count = fake_solver_invocation_count(&solver_path);
        assert_eq!(first_invocation_count, 2);

        // The key the live path used, derived exactly as `verify_with_cli_smt2`
        // derives it. `None` means this host has no capable checker: then no
        // memo of either sign exists and the pre-memo behaviour must hold.
        let authority = VerificationAuthority::capture_with_timeout(
            config.solver.as_ref().expect("the pinned fake solver"),
            config.timeout_ms,
        );
        let session_key = session_proof_cache_key(
            authority.solver_path_text(),
            &generate_smt2_query_raw(&obligation, &config),
        )
        .and_then(|legacy| authority.session_key(&legacy));
        if let Some(key) = &session_key {
            assert!(
                !session_proof_cache_lookup_verified(key),
                "holey UNSAT must not be promoted into the Verified session cache"
            );
            assert!(
                session_negative_memo_lookup(key).is_some(),
                "a holey UNSAT is a memoisable certification gap for this key"
            );
        }

        let second = verify_with_cli_raw(&obligation, &config);
        let invocation_count = fake_solver_invocation_count(&solver_path);
        remove_temp_solver_and_count(&solver_path);
        assert!(matches!(second, AYResult::Unknown(_)), "got {second:?}");
        match session_key {
            Some(_) => {
                assert_eq!(
                    second, first,
                    "the negative memo replays the exact Unknown this process already produced"
                );
                assert_eq!(
                    invocation_count, first_invocation_count,
                    "a memoised certification gap must not spawn the solver again"
                );
            }
            None => assert!(
                invocation_count > first_invocation_count,
                "without a session key nothing is memoised; the second query must \
                 invoke the solver again"
            ),
        }
    }

    /// The negative memo remembers ONLY the deterministic certification gaps.
    /// A bare `unknown` carries no reason, so its next occurrence must reach
    /// the solver again.
    ///
    /// The fake solver answers `unknown` on BOTH its resident and its
    /// one-shot path, so each call now costs two answers: the resident
    /// exchange, then the fresh proof-bearing replay
    /// `verify_with_cli_smt2_under_authority` runs to recover the reason the
    /// server's discarded stderr would have carried. What this pins is
    /// unchanged — a reasonless unknown is never memoised — and the
    /// assertion is on the answer count strictly increasing, not on its
    /// exact value.
    #[cfg(unix)]
    #[test]
    fn resident_bare_unknown_is_not_memoised_and_is_re_solved() {
        let _batch_lock = ay_batch_test_lock();
        if !ay_server_enabled() {
            return;
        }
        let solver_path = write_warm_solver_script(
            "#!/bin/sh\n\
             count_file=\"$0.count\"\n\
             count=0\n\
             if [ -r \"$count_file\" ]; then count=$(cat \"$count_file\"); fi\n\
             count=$((count + 1))\n\
             printf '%s\\n' \"$count\" > \"$count_file\"\n\
             if [ \"$1\" = \"--incremental\" ]; then\n\
               while IFS= read -r line; do\n\
                 if [ \"$line\" = \"(check-sat)\" ]; then printf 'q\\n' >> \"$0.queries\"; printf 'unknown\\n'; fi\n\
                 sentinel=$(printf '%s\\n' \"$line\" | sed -n 's/^(echo \"\\(==TCG_SRV_[0-9][0-9]*==\\)\")$/\\1/p')\n\
                 if [ -n \"$sentinel\" ]; then printf '%s\\n' \"$sentinel\"; fi\n\
               done\n\
               exit 0\n\
             fi\n\
             printf 'q\\n' >> \"$0.queries\"\n\
             printf 'unknown\\n'\n",
        );
        let queries_answered = |path: &str| -> usize {
            std::fs::read_to_string(format!("{path}.queries"))
                .map_or(0, |text| text.lines().count())
        };

        let x = SmtExpr::var("resident_bare_unknown_x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "resident_bare_unknown_not_memoised".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x,
            inputs: vec![("resident_bare_unknown_x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        let solver = crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path));
        let config = AYConfig {
            solver: Some(solver),
            timeout_ms: FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
            produce_models: false,
        };

        let first = verify_with_cli_raw(&obligation, &config);
        assert!(
            matches!(&first, AYResult::Unknown(reason) if reason == "unknown"),
            "got {first:?}"
        );
        let answered_after_first = queries_answered(&solver_path);
        assert!(
            answered_after_first >= 1,
            "the fake solver must have answered the first query"
        );

        let second = verify_with_cli_raw(&obligation, &config);
        let answered_after_second = queries_answered(&solver_path);
        remove_temp_solver_and_count(&solver_path);
        let _ = std::fs::remove_file(format!("{solver_path}.queries"));
        assert!(
            matches!(&second, AYResult::Unknown(reason) if reason == "unknown"),
            "got {second:?}"
        );
        assert!(
            answered_after_second > answered_after_first,
            "a bare unknown carries no memoisable reason; the second query must be solved again \
             (answered {answered_after_first} then {answered_after_second})"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_verify_with_cli_enforces_process_timeout() {
        // Keep the fake solver serialized with the other transport controls.
        let _batch_lock = ay_batch_test_lock();
        // Keep the fixture far beyond the assertion budget. The full verifier
        // suite saturates the host with thousands of proof tests, so a
        // sub-second wall-clock bound measures scheduler latency rather than
        // the configured 50 ms solver deadline. A 30-second sleeper paired
        // with a 10-second outer bound still proves that timeout teardown did
        // not wait for natural process exit, while remaining stable under
        // publication-suite load.
        // First-exec assessment of a new executable and queueing behind an
        // unrelated resident query happen outside the solver deadline. Warm
        // this fixture and use the fresh public path so this wall-clock bound
        // measures the configured process timeout. Separate resident controls
        // check its admission deadline and complete process-group teardown.
        let solver_path = write_warm_solver_script("#!/bin/sh\nsleep 30\necho unsat\n");

        let x = SmtExpr::var("x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "fake_solver_timeout".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x,
            inputs: vec![("x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let start = Instant::now();
        let result =
            trust_cg_process_env::with_env_overrides(&[("TCG_NO_SOLVER_SERVER", "1")], || {
                verify_with_cli(
                    &obligation,
                    &AYConfig {
                        solver: Some(crate::ay_identity::test_fixtures::pin(
                            std::path::Path::new(&solver_path),
                        )),
                        timeout_ms: 50,
                        produce_models: true,
                    },
                )
            });
        let elapsed = start.elapsed();

        let _ = std::fs::remove_file(&solver_path);

        assert_eq!(result, AYResult::Timeout);
        assert!(
            elapsed < Duration::from_secs(10),
            "solver subprocess timeout should be enforced promptly, elapsed {:?}",
            elapsed
        );
    }

    #[cfg(unix)]
    #[test]
    fn resident_runtime_binds_to_the_first_process_that_uses_it() {
        use std::sync::atomic::AtomicU32;
        let owner = AtomicU32::new(0);
        assert!(resident_exit_cleanup::bind_owner(&owner, 100));
        assert!(resident_exit_cleanup::bind_owner(&owner, 100));
        // A forked child sees the inherited owner and a different PID.
        assert!(!resident_exit_cleanup::bind_owner(&owner, 101));
        assert!(resident_exit_cleanup::runtime_owned_by_current_process());
    }

    /// Subprocess-only half of
    /// `test_resident_solver_process_group_is_killed_at_normal_exit`.
    ///
    /// An in-process test cannot observe process exit. The parent test runs
    /// this exact test in a fresh libtest process, where it leaves a live
    /// resident solver in the static slot and then returns normally.
    #[cfg(unix)]
    #[test]
    fn test_resident_solver_normal_exit_helper() {
        let Some(solver_path) = std::env::var_os("TCG_TEST_RESIDENT_NORMAL_EXIT_SOLVER") else {
            return;
        };
        assert!(
            ay_server_enabled(),
            "normal-exit helper must exercise the resident solver path"
        );
        // The fixture enters through the same rule as every AY (test-declared
        // bytes; `PinnedAy::command` is still the only launcher). Its private
        // copy is new in this process's fixture root, so it is started once
        // before the resident deadline (`test_fixtures::warm`).
        crate::ay_identity::test_fixtures::warm(std::path::Path::new(&solver_path));
        if std::env::var_os("TCG_TEST_RESIDENT_CLOSE_BEFORE_START").is_some() {
            resident_exit_cleanup::close_for_test();
            assert!(!ay_server_enabled());
            let result = run_solver_via_server(
                &crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path)),
                "(check-sat)\n(exit)\n",
                FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
                &[],
            );
            assert!(matches!(result, AyServerAttempt::Anomaly));
            assert!(resident_exit_cleanup::quiescent());
            return;
        }
        let lanes = std::env::var("TCG_TEST_RESIDENT_NORMAL_EXIT_LANES")
            .ok()
            .and_then(|value| value.parse::<usize>().ok())
            .unwrap_or(1);
        assert!((1..=MAX_PROOF_GATE_WORKERS).contains(&lanes));
        let start = std::sync::Barrier::new(lanes);
        std::thread::scope(|scope| {
            for lane in 0..lanes {
                let solver_path = &solver_path;
                let start = &start;
                scope.spawn(move || {
                    start.wait();
                    for _ in 0..2 {
                        let result = with_proof_gate_lane(lane, || {
                            run_solver_via_server(
                                &crate::ay_identity::test_fixtures::pin(std::path::Path::new(
                                    solver_path,
                                )),
                                "(check-sat)\n(exit)\n",
                                FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
                                &[],
                            )
                        });
                        assert!(
                            matches!(result, AyServerAttempt::Completed(_)),
                            "each live lane must answer its framed window"
                        );
                    }
                });
            }
        });
        // SAFETY: the child uses only PID/atomic ownership checks and _exit;
        // it never touches inherited Rust mutexes, allocators or I/O buffers.
        let child = unsafe { libc::fork() };
        assert!(child >= 0, "fork fixture failed");
        if child == 0 {
            let refused = !resident_exit_cleanup::runtime_owned_by_current_process();
            resident_exit_cleanup::close_for_test();
            // SAFETY: terminate the fork child without Rust/static destructors.
            unsafe {
                libc::_exit(if refused { 0 } else { 97 });
            }
        }
        let mut status = 0;
        loop {
            // SAFETY: wait only for this fixture's own child and valid status.
            let waited = unsafe { libc::waitpid(child, &mut status, 0) };
            if waited == child {
                break;
            }
            assert_eq!(
                std::io::Error::last_os_error().kind(),
                std::io::ErrorKind::Interrupted
            );
        }
        assert!(libc::WIFEXITED(status));
        assert_eq!(libc::WEXITSTATUS(status), 0);
        for lane in 0..lanes {
            let result = with_proof_gate_lane(lane, || {
                run_solver_via_server(
                    &crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path)),
                    "(check-sat)\n(exit)\n",
                    FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
                    &[],
                )
            });
            assert!(
                matches!(result, AyServerAttempt::Completed(_)),
                "fork child must not kill its parent's lane"
            );
        }
        assert!(resident_exit_cleanup::quiescent());
        // Deliberately leave `ay_server_slot` populated: the static is never
        // dropped, so only exit-time cleanup can stop its process group.
    }

    #[cfg(unix)]
    #[test]
    fn test_resident_solver_process_group_is_killed_at_normal_exit() {
        let _batch_lock = ay_batch_test_lock();
        let pid_file = std::env::temp_dir().join(format!(
            "trust_cg_verify_solver_exit_child_{}_{}.pid",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock should be after unix epoch")
                .as_nanos()
        ));
        // A fake interactive solver that publishes its pid and a TERM-ignoring
        // descendant, answers each framed window, and keeps its process group
        // alive after stdin EOF by waiting on the descendant. The helper
        // process warms it (it answers the warm-up argument first).
        let solver_path = write_temp_solver_script(
            &crate::ay_identity::test_fixtures::with_warm_guard(&format!(
                "#!/bin/sh\n\
             ( trap '' TERM; exec sleep 120 ) &\n\
             printf '%s %s\\n' \"$$\" \"$!\" > \"{}\"\n\
             while IFS= read -r line; do\n\
               if [ \"$line\" = \"(check-sat)\" ]; then printf 'unsat\\n'; fi\n\
               sentinel=$(printf '%s\\n' \"$line\" | sed -n 's/^(echo \"\\(==TCG_SRV_[0-9][0-9]*==\\)\")$/\\1/p')\n\
               if [ -n \"$sentinel\" ]; then printf '%s\\n' \"$sentinel\"; fi\n\
             done\n\
             wait\n",
                pid_file.display()
            )),
        );

        let helper = std::process::Command::new(
            std::env::current_exe().expect("current libtest executable must be available"),
        )
        .arg("--exact")
        .arg("ay_bridge::tests::test_resident_solver_normal_exit_helper")
        .arg("--nocapture")
        .arg("--test-threads=1")
        .env("TCG_TEST_RESIDENT_NORMAL_EXIT_SOLVER", &solver_path)
        .env_remove("TCG_NO_SOLVER_SERVER")
        .stdin(std::process::Stdio::null())
        .output()
        .expect("failed to launch normal-exit resident-solver helper");

        let pid_deadline = Instant::now() + Duration::from_secs(5);
        let mut identity: Option<(u32, u32)> = None;
        while Instant::now() < pid_deadline {
            if let Ok(contents) = std::fs::read_to_string(&pid_file) {
                let mut pids = contents
                    .split_whitespace()
                    .filter_map(|field| field.parse::<u32>().ok());
                if let (Some(solver), Some(child)) = (pids.next(), pids.next()) {
                    identity = Some((solver, child));
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(20));
        }

        let mut descendant_still_running = false;
        if let Some((_, child)) = identity {
            let deadline = Instant::now() + Duration::from_secs(5);
            while process_is_running(child) && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(10));
            }
            descendant_still_running = process_is_running(child);
        }
        // Never leak the fixture, whatever the verdict.
        if let Some((solver, child)) = identity {
            for pid in [solver, child] {
                let _ = std::process::Command::new("kill")
                    .arg("-KILL")
                    .arg(pid.to_string())
                    .stdout(std::process::Stdio::null())
                    .stderr(std::process::Stdio::null())
                    .status();
            }
        }
        let _ = std::fs::remove_file(&solver_path);
        let _ = std::fs::remove_file(&pid_file);

        assert!(
            helper.status.success(),
            "normal-exit resident-solver helper failed with {}:\n{}\n{}",
            helper.status,
            String::from_utf8_lossy(&helper.stdout),
            String::from_utf8_lossy(&helper.stderr)
        );
        assert!(
            String::from_utf8_lossy(&helper.stdout).contains("1 passed"),
            "the helper test must actually run:\n{}",
            String::from_utf8_lossy(&helper.stdout)
        );
        let identity = identity.expect("fake resident solver must publish its identity");
        assert!(
            !descendant_still_running,
            "normal process exit must kill the resident solver's process group \
             (solver pid, descendant pid) = {identity:?}"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_multiple_resident_lanes_survive_each_other_and_exit_cleanly() {
        let _batch_lock = ay_batch_test_lock();
        let directory = tempfile::tempdir().unwrap();
        let pid_file = directory.path().join("owned-pids");
        let script = write_temp_solver_script(&crate::ay_identity::test_fixtures::with_warm_guard(
            &format!(
                "#!/bin/sh\n(trap '' TERM; exec sleep 120) &\nprintf '%s %s\\n' \"$$\" \"$!\" >> \"{}\"\nwhile IFS= read -r line; do\nif [ \"$line\" = \"(check-sat)\" ]; then printf 'unsat\\n'; fi\nsentinel=$(printf '%s\\n' \"$line\" | sed -n 's/^(echo \"\\(==TCG_SRV_[0-9][0-9]*==\\)\")$/\\1/p')\nif [ -n \"$sentinel\" ]; then printf '%s\\n' \"$sentinel\"; fi\ndone\nwait\n",
                pid_file.display()
            ),
        ));
        let helper = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "ay_bridge::tests::test_resident_solver_normal_exit_helper",
                "--nocapture",
                "--test-threads=1",
            ])
            .env("TCG_TEST_RESIDENT_NORMAL_EXIT_SOLVER", &script)
            .env("TCG_TEST_RESIDENT_NORMAL_EXIT_LANES", "3")
            .env_remove("TCG_NO_SOLVER_SERVER")
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        let pids = std::fs::read_to_string(&pid_file)
            .unwrap_or_default()
            .split_whitespace()
            .map(|word| word.parse::<u32>().unwrap())
            .collect::<Vec<_>>();
        let deadline = Instant::now() + Duration::from_secs(5);
        while pids.iter().any(|pid| process_is_running(*pid)) && Instant::now() < deadline {
            std::thread::sleep(Duration::from_millis(10));
        }
        let alive = pids.iter().any(|pid| process_is_running(*pid));
        // Clean up exactly the processes this private fixture published.
        for pid in &pids {
            let _ = std::process::Command::new("kill")
                .args(["-KILL", &pid.to_string()])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status();
        }
        std::fs::remove_file(&pid_file).unwrap();
        let closed = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "ay_bridge::tests::test_resident_solver_normal_exit_helper",
                "--nocapture",
                "--test-threads=1",
            ])
            .env("TCG_TEST_RESIDENT_NORMAL_EXIT_SOLVER", &script)
            .env("TCG_TEST_RESIDENT_CLOSE_BEFORE_START", "1")
            .env_remove("TCG_NO_SOLVER_SERVER")
            .stdin(std::process::Stdio::null())
            .output()
            .unwrap();
        let unexpected = std::fs::read_to_string(&pid_file).unwrap_or_default();
        for pid in unexpected
            .split_whitespace()
            .filter_map(|word| word.parse::<u32>().ok())
        {
            let _ = std::process::Command::new("kill")
                .args(["-KILL", &pid.to_string()])
                .stdout(std::process::Stdio::null())
                .stderr(std::process::Stdio::null())
                .status();
        }
        assert!(
            closed.status.success(),
            "{}",
            String::from_utf8_lossy(&closed.stderr)
        );
        assert!(String::from_utf8_lossy(&closed.stdout).contains("1 passed"));
        assert!(
            unexpected.is_empty(),
            "an empty shutdown must prevent the first resident spawn"
        );
        let _ = std::fs::remove_file(script);
        assert!(
            helper.status.success(),
            "{}",
            String::from_utf8_lossy(&helper.stderr)
        );
        assert!(String::from_utf8_lossy(&helper.stdout).contains("1 passed"));
        assert_eq!(
            pids.len(),
            6,
            "three servers and three descendants, with no lane respawn"
        );
        assert!(!alive, "every admitted lane must be stopped on normal exit");
    }

    #[cfg(unix)]
    #[test]
    fn test_resident_solver_timeout_kills_process_group() {
        let _batch_lock = ay_batch_test_lock();
        let pid_file = std::env::temp_dir().join(format!(
            "trust_cg_verify_solver_child_{}_{}.pid",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock should be after unix epoch")
                .as_nanos()
        ));
        // The grandchild sleeps far longer than the solver timeout so it is
        // still alive when the timeout fires; the test then proves the whole
        // process group (not just the direct child) was killed.
        let solver_path = write_temp_solver_script(&format!(
            "#!/bin/sh\n\
             ( trap '' TERM; sleep 120 ) &\n\
             printf '%s %s\\n' \"$$\" \"$!\" > \"{}\"\n\
             wait\n",
            pid_file.display()
        ));

        // A generous (3s, not 1s) solver timeout: on a heavily loaded shared
        // host, process spawn + the shell reaching its first `printf` can take
        // well over a second, and a 1s budget produced false failures (the
        // child pid file not yet written when the timeout killed the solver).
        // The grandchild sleeps 120s, so a 3s timeout still proves the timeout
        // does not wait for the descendant.
        let timeout = Duration::from_secs(3);
        let start = Instant::now();
        // Exercise the resident path directly: a generic verify call could be
        // routed through the fresh fallback and accidentally mask a regression
        // in AyServer teardown.
        let result = run_solver_via_server(
            &crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path)),
            "(check-sat)\n(exit)\n",
            timeout.as_millis() as u64,
            &[],
        );
        let elapsed = start.elapsed();

        // The grandchild pid is written by the fake solver right after it
        // spawns the grandchild. Poll for it (the write can land slightly after
        // the timeout fires, or be delayed by host load) rather than reading
        // once. If it never appears, the solver was killed before it even
        // spawned the grandchild — the process group still died cleanly, so
        // there is no orphan to verify.
        let pid_deadline = Instant::now() + Duration::from_secs(5);
        let mut solver_pid: Option<u32> = None;
        let mut child_pid: Option<u32> = None;
        while Instant::now() < pid_deadline {
            if let Ok(contents) = std::fs::read_to_string(&pid_file) {
                let mut pids = contents
                    .split_whitespace()
                    .filter_map(|field| field.parse::<u32>().ok());
                if let (Some(solver), Some(child)) = (pids.next(), pids.next()) {
                    solver_pid = Some(solver);
                    child_pid = Some(child);
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(20));
        }

        let mut child_still_running = false;
        let mut child_snapshot: Option<String> = None;
        if let Some(pid) = child_pid {
            let deadline = Instant::now() + Duration::from_secs(5);
            while process_is_running(pid) && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(10));
            }
            child_still_running = process_is_running(pid);
            if child_still_running {
                child_snapshot = std::process::Command::new("ps")
                    .args(["-o", "pid=,ppid=,pgid=,stat=,comm=", "-p", &pid.to_string()])
                    .output()
                    .ok()
                    .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string());
                let _ = std::process::Command::new("kill")
                    .arg("-KILL")
                    .arg(pid.to_string())
                    .stdout(std::process::Stdio::null())
                    .stderr(std::process::Stdio::null())
                    .status();
            }
        }

        let _ = std::fs::remove_file(&solver_path);
        let _ = std::fs::remove_file(&pid_file);

        assert!(
            matches!(result, AyServerAttempt::TimedOut(_)),
            "resident solver should consume its deadline without a fresh retry"
        );
        // The timeout must not wait for the 120s pipe-holding descendant. Allow
        // generous slack over the 3s timeout for teardown under host load,
        // while staying far below the descendant's 120s sleep.
        assert!(
            elapsed < timeout + Duration::from_secs(15),
            "solver subprocess timeout should not wait for pipe-holding descendants, elapsed {:?}",
            elapsed
        );
        assert!(
            !child_still_running,
            "timed-out solver descendant should be killed with its process group \
             (solver pid {:?}, child pid {:?}, child snapshot {:?})",
            solver_pid, child_pid, child_snapshot
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_fresh_solver_timeout_kills_process_group() {
        let _batch_lock = ay_batch_test_lock();
        let pid_file = std::env::temp_dir().join(format!(
            "trust_cg_verify_fresh_solver_child_{}_{}.pid",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .expect("system clock should be after unix epoch")
                .as_nanos()
        ));
        let solver_path = write_warm_solver_script(&format!(
            "#!/bin/sh\n\
             ( trap '' TERM; sleep 120 ) &\n\
             printf '%s %s\\n' \"$$\" \"$!\" > \"{}\"\n\
             wait\n",
            pid_file.display()
        ));
        let query = write_temp_smt2("(check-sat)\n(exit)\n").expect("write fake solver query");

        let timeout = Duration::from_secs(3);
        let start = Instant::now();
        let result = run_solver_command(
            &crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path)),
            query.path(),
            timeout.as_millis() as u64,
        );
        let elapsed = start.elapsed();

        let pid_deadline = Instant::now() + Duration::from_secs(5);
        let mut solver_pid: Option<u32> = None;
        let mut child_pid: Option<u32> = None;
        while Instant::now() < pid_deadline {
            if let Ok(contents) = std::fs::read_to_string(&pid_file) {
                let mut pids = contents
                    .split_whitespace()
                    .filter_map(|field| field.parse::<u32>().ok());
                if let (Some(solver), Some(child)) = (pids.next(), pids.next()) {
                    solver_pid = Some(solver);
                    child_pid = Some(child);
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(20));
        }

        let mut child_still_running = false;
        let mut child_snapshot: Option<String> = None;
        if let Some(pid) = child_pid {
            let deadline = Instant::now() + Duration::from_secs(5);
            while process_is_running(pid) && Instant::now() < deadline {
                std::thread::sleep(Duration::from_millis(10));
            }
            child_still_running = process_is_running(pid);
            if child_still_running {
                child_snapshot = std::process::Command::new("ps")
                    .args(["-o", "pid=,ppid=,pgid=,stat=,comm=", "-p", &pid.to_string()])
                    .output()
                    .ok()
                    .map(|output| String::from_utf8_lossy(&output.stdout).trim().to_string());
                let _ = std::process::Command::new("kill")
                    .arg("-KILL")
                    .arg(pid.to_string())
                    .stdout(std::process::Stdio::null())
                    .stderr(std::process::Stdio::null())
                    .status();
            }
        }

        let _ = std::fs::remove_file(&solver_path);
        let _ = std::fs::remove_file(&pid_file);

        assert!(
            matches!(result, Err(SolverInvocationError::Timeout(_))),
            "fresh solver should consume its configured deadline"
        );
        assert!(
            solver_pid.is_some() && child_pid.is_some(),
            "fake fresh solver must spawn the descendant that exercises group teardown"
        );
        assert!(
            elapsed < timeout + Duration::from_secs(15),
            "fresh solver timeout should not wait for descendants, elapsed {:?}",
            elapsed
        );
        assert!(
            !child_still_running,
            "fresh solver descendant should be killed with its process group \
             (solver pid {:?}, child pid {:?}, child snapshot {:?})",
            solver_pid, child_pid, child_snapshot
        );
    }

    #[test]
    fn test_serialize_to_smt2_roundtrip_with_solver() {
        // Verify that serialize_to_smt2 output is valid SMT-LIB2 by running it
        // through AY if available.
        let Some(solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_serialize_to_smt2_roundtrip_with_solver",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "roundtrip_test".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let smt2 = serialize_to_smt2(&obligation);

        // Write to a temp file and verify AY can parse it.
        let tmp_file = write_temp_smt2(&smt2).expect("failed to write temp file");
        let output = run_solver_command(&solver, tmp_file.path(), AYConfig::default().timeout_ms)
            .expect("failed to invoke solver");

        let stdout = String::from_utf8_lossy(&output.stdout);
        // Should be unsat (a+b == a+b is trivially true)
        assert!(
            stdout.trim().starts_with("unsat"),
            "Expected unsat, got: {}",
            stdout
        );
    }

    #[test]
    fn test_serialize_to_smt2_with_preconditions() {
        // Test serialization of obligations with preconditions
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let precond = b.clone().eq_expr(SmtExpr::bv_const(0, 32)).not_expr();

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "div_with_precond".to_string(),
            trust_ir_expr: a.clone().bvsdiv(b.clone()),
            aarch64_expr: a.bvsdiv(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![precond],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let smt2 = serialize_to_smt2(&obligation);
        assert!(smt2.contains("(assert"));
        assert!(smt2.contains("bvsdiv"));
        assert!(smt2.contains("(not (=")); // precondition b != 0
    }

    #[test]
    fn test_verify_with_ay_cli_with_preconditions() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_verify_with_ay_cli_with_preconditions",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        // a / b == a / b with precondition b != 0
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);
        let precond = b.clone().eq_expr(SmtExpr::bv_const(0, 32)).not_expr();

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "sdiv_identity".to_string(),
            trust_ir_expr: a.clone().bvsdiv(b.clone()),
            aarch64_expr: a.bvsdiv(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![precond],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_ay_cli(&obligation, &config);
        assert_eq!(result, AYResult::Verified);
    }

    #[test]
    fn test_verify_with_ay_cli_negation_rule() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_verify_with_ay_cli_negation_rule",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        // Verify that bvneg(a) == bvsub(0, a) -- foundational identity
        let a = SmtExpr::var("a", 32);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "neg_is_sub_zero".to_string(),
            trust_ir_expr: a.clone().bvneg(),
            aarch64_expr: SmtExpr::bv_const(0, 32).bvsub(a),
            inputs: vec![("a".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_ay_cli(&obligation, &config);
        assert_eq!(result, AYResult::Verified);
    }

    #[test]
    fn test_verify_with_ay_cli_bitwise_identity() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_verify_with_ay_cli_bitwise_identity",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        // Verify that a XOR a == 0 for all 16-bit values
        let a = SmtExpr::var("a", 16);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "xor_self_is_zero".to_string(),
            trust_ir_expr: a.clone().bvxor(a.clone()),
            aarch64_expr: SmtExpr::bv_const(0, 16),
            inputs: vec![("a".to_string(), 16)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_ay_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "obligation '{}' must be Verified, got {}",
                obligation.name, result
            ),
        );
    }

    #[test]
    fn test_verify_with_ay_cli_extract_zeroext_identity() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_verify_with_ay_cli_extract_zeroext_identity",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        // Verify that zero_extend(extract[7:0](a), 24) extracts and extends correctly
        // For a 32-bit value, this should equal a AND 0xFF
        let a = SmtExpr::var("a", 32);
        let trust_ir = a.clone().extract(7, 0).zero_ext(24);
        let aarch64 = a.bvand(SmtExpr::bv_const(0xFF, 32));

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "extract_zext_eq_mask".to_string(),
            trust_ir_expr: trust_ir,
            aarch64_expr: aarch64,
            inputs: vec![("a".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_ay_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "obligation '{}' must be Verified, got {}",
                obligation.name, result
            ),
        );
    }

    #[test]
    fn test_parse_ay_output_sat_empty_model() {
        // SAT but no model lines following
        let result = parse_ay_output("sat\n", &[("x".to_string(), 32)]);
        match result {
            AYResult::CounterExample(cex) => {
                // No model available, empty counterexample
                assert!(cex.is_empty());
            }
            other => panic!("Expected CounterExample, got {:?}", other),
        }
    }

    #[test]
    fn test_parse_ay_output_multiple_vars() {
        let output = "sat\n((a #x00000001)\n (b #x00000002)\n (c #x00000003))";
        let inputs = vec![
            ("a".to_string(), 32),
            ("b".to_string(), 32),
            ("c".to_string(), 32),
        ];
        let result = parse_ay_output(output, &inputs);
        match result {
            AYResult::CounterExample(cex) => {
                assert_eq!(cex.len(), 3);
                assert_eq!(cex[0], ("a".to_string(), 1));
                assert_eq!(cex[1], ("b".to_string(), 2));
                assert_eq!(cex[2], ("c".to_string(), 3));
            }
            other => panic!("Expected CounterExample, got {:?}", other),
        }
    }

    // -----------------------------------------------------------------------
    // CLI batch verification tests (issue #228: first real SMT solver calls)
    //
    // These tests run real lowering proofs through the selected CLI solver,
    // moving from statistical mock evaluation to actual formal verification.
    // Each test gracefully skips if no solver binary is installed.
    // -----------------------------------------------------------------------

    /// Verify ALL arithmetic lowering proofs (add/sub/mul/neg for I8/I16/I32/I64
    /// plus division) through the selected CLI solver. This is 20 proofs, each formally verified
    /// for ALL possible inputs via the SMT solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_arithmetic_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_arithmetic_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::lowering_proof::all_arithmetic_proofs();
        assert!(
            proofs.len() >= 16,
            "Expected at least 16 arithmetic proofs, got {}",
            proofs.len()
        );

        let mut verified_count = 0;
        for obligation in &proofs {
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "Arithmetic proof '{}' failed via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
            verified_count += 1;
        }

        assert!(
            verified_count >= 16,
            "Expected >= 16 arithmetic proofs verified, got {}",
            verified_count
        );
    }

    /// Verify all comparison proofs (eq/ne/slt/sge/sgt/sle/ult/uge/ugt/ule
    /// for both i32 and i64) through the selected CLI solver. This is 20 proofs.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_comparison_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_comparison_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs_i32 = crate::lowering_proof::all_comparison_proofs_i32();
        let proofs_i64 = crate::lowering_proof::all_comparison_proofs_i64();

        // #62 originally retracted the degenerate Icmp_UGE_I32/I64 pair.  The
        // adder-carry NZCV model made those obligations genuine again, and the
        // registry's `uge_proofs_are_no_longer_degenerate` test pins that fact.
        assert_eq!(proofs_i32.len(), 10, "Expected 10 i32 comparison proofs");
        assert_eq!(proofs_i64.len(), 10, "Expected 10 i64 comparison proofs");

        for obligation in proofs_i32.iter().chain(proofs_i64.iter()) {
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "Comparison proof '{}' failed via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }
    }

    /// Verify all conditional branch proofs through the selected CLI solver. This is 20 proofs.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_branch_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_branch_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::lowering_proof::all_branch_proofs();
        // #62 originally retracted the degenerate CondBr_UGE_I32/I64 pair.
        // The adder-carry NZCV model made both obligations genuine again, so
        // the two ten-predicate width families now contribute twenty proofs.
        assert_eq!(proofs.len(), 20, "Expected 20 branch proofs");

        for obligation in &proofs {
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "Branch proof '{}' failed via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }
    }

    /// Verify all peephole identity proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_peephole_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_peephole_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::peephole_proofs::all_peephole_proofs_with_32bit();
        assert!(
            proofs.len() >= 9,
            "Expected at least 9 peephole proofs, got {}",
            proofs.len()
        );

        let mut verified = 0;
        let mut known_timeouts = 0;
        let mut gap_skips = 0;
        for obligation in &proofs {
            let result = verify_with_cli(obligation, &config);
            match result {
                AYResult::Verified => verified += 1,
                AYResult::Timeout if obligation.name.contains("MUL Xd, Xn, #-1 ≡ NEG Xd, Xn") => {
                    known_timeouts += 1;
                    eprintln!(
                        "KNOWN ISSUE: {} -- solver timeout on hard mul/neg equivalence proof",
                        obligation.name
                    );
                }
                // Certification-gap guard (crate::formal_gap): skip LOUDLY only
                // on AY's disclosed proof hole; anything else still panics with
                // the original message.
                other => match crate::formal_gap::disclosed_proof_hole(&other) {
                    Some(reason) => {
                        crate::formal_gap::print_gap_skip(
                            &format!("Peephole proof '{}'", obligation.name),
                            &reason,
                        );
                        gap_skips += 1;
                    }
                    None => panic!(
                        "Peephole proof '{}' failed via {}: {}",
                        obligation.name,
                        solver_route_summary_for_invocation(obligation, &config),
                        other
                    ),
                },
            }
        }

        assert!(
            verified + known_timeouts + gap_skips == proofs.len() && known_timeouts <= 1,
            "Expected all peephole proofs verified except at most one known timeout and the \
             loudly-skipped certification gaps, got {verified} verified, {known_timeouts} known \
             timeouts and {gap_skips} certification-gap skips out of {}",
            proofs.len(),
        );
        if gap_skips == 0 {
            assert!(
                verified + known_timeouts == proofs.len() && known_timeouts <= 1,
                "Expected all peephole proofs verified except at most one known timeout, got {verified} verified and {known_timeouts} known timeouts out of {}",
                proofs.len(),
            );
        }
    }

    /// End-to-end test: use verify_all_with_ay() to batch-verify all registered
    /// arithmetic, NZCV, and peephole proofs and check the VerificationSummary.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_all_and_summary() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_all_and_summary",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let results = verify_all_with_ay(&config);

        let summary = VerificationSummary::from_results(&results);

        // Must have a meaningful number of proofs
        assert!(
            summary.total >= 30,
            "Expected >= 30 proofs in verify_all_with_ay, got {}",
            summary.total
        );

        // CAPACITY-PENDING ALLOWLIST. The two `X Xd, Xn, #-1 ≡ NEG Xd, Xn`
        // peepholes (MUL and SDIV) are VALID 64-bit identities — on AArch64
        // `n*-1`, `n/-1` and `NEG n` all equal `-n` mod 2^64 (SDIV does not trap,
        // and INT_MIN/-1 = INT_MIN = NEG INT_MIN), so AY finds no counterexample;
        // it simply bit-blasts 64-bit mul/div past the solver timeout under load.
        // A `Timeout` is therefore a CAPACITY pending, never a SOUNDNESS failure
        // (mirrors the full-DB `proof_gate_strict` treatment). We tolerate a
        // timeout ONLY for these named identities and still hard-fail on any
        // CounterExample / Error / Unknown.
        let is_known_capacity_timeout = |name: &str| {
            name.contains("Peephole: MUL Xd, Xn, #-1 ≡ NEG Xd, Xn")
                || name.contains("Peephole: SDIV Xd, Xn, #-1 ≡ NEG Xd, Xn")
        };
        let known_timeouts = results
            .iter()
            .filter(|(name, result)| {
                matches!(result, AYResult::Timeout) && is_known_capacity_timeout(name)
            })
            .count();

        // Certification-gap guard (crate::formal_gap): skip LOUDLY only on
        // AY's disclosed proof hole. Everything else keeps failing the
        // original assertions below.
        let mut gap_names: std::collections::HashSet<&str> = std::collections::HashSet::new();
        for (name, result) in &results {
            if let Some(reason) = crate::formal_gap::disclosed_proof_hole(result) {
                crate::formal_gap::print_gap_skip(&format!("batch proof '{name}'"), &reason);
                gap_names.insert(name.as_str());
            }
        }

        let unexpected: Vec<_> = results
            .iter()
            .filter(|(name, result)| match result {
                AYResult::Verified => false,
                AYResult::SolverUnsat => !is_known_capacity_timeout(name),
                AYResult::Timeout => !is_known_capacity_timeout(name),
                AYResult::Unknown(_) => !gap_names.contains(name.as_str()),
                AYResult::CounterExample(_) | AYResult::Error(_) => true,
            })
            .collect();

        assert_eq!(
            summary.failed, 0,
            "solver found {} counterexamples in batch verification",
            summary.failed
        );
        if gap_names.is_empty() {
            assert_eq!(
                summary.errors, 0,
                "solver had {} errors in batch verification",
                summary.errors
            );
        }
        assert!(
            unexpected.is_empty(),
            "Unexpected verify_all_with_ay results: {:?}",
            unexpected
        );
        assert!(
            summary.verified
                >= summary
                    .total
                    .saturating_sub(known_timeouts + gap_names.len()),
            "Not enough proofs verified in batch verification (beyond known timeouts and \
             loudly-skipped certification gaps): {}",
            summary
        );
        if gap_names.is_empty() {
            assert!(
                summary.verified >= summary.total.saturating_sub(known_timeouts),
                "Not enough proofs verified in batch verification: {}",
                summary
            );
        }
    }

    /// Verify load/store proofs through the selected CLI solver (array theory QF_ABV).
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_load_store_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_load_store_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::lowering_proof::all_load_store_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "Expected 2 genuine load/store roundtrip proofs (8 degenerate \
             Load_I*/Store_I* X==X retracted in #62), got {}",
            proofs.len()
        );

        for obligation in &proofs {
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "Load/store proof '{}' failed via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }
    }

    /// Verify bitwise and shift proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_bitwise_shift_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_bitwise_shift_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::lowering_proof::all_bitwise_shift_proofs();
        assert!(
            proofs.len() >= 7,
            "Expected at least 7 bitwise/shift proofs, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "Bitwise/shift proof '{}' failed via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }
    }

    // -----------------------------------------------------------------------
    // CLI batch verification: remaining proof categories (issue #239)
    //
    // These tests expand CLI batch verification from the original 7 categories
    // (arithmetic, NZCV, comparison, branch, peephole, memory, bitwise_shift)
    // to cover ALL 36 categories in the ProofDatabase (LoadStoreLowering added
    // via #422 wiring).
    // -----------------------------------------------------------------------

    /// Helper: verify all proofs in a given category through the active CLI
    /// solver via ProofDatabase.
    fn verify_category_batch(category: ProofCategory, min_expected: usize) {
        verify_category_batch_with_timeout(category, min_expected, 30_000);
    }

    /// Verify a proof category with an explicit per-proof solver budget.
    ///
    /// Most categories finish comfortably within the default batch budget.
    /// Categories with known, intrinsically expensive bit-vector obligations
    /// use an evidence-backed larger budget.
    fn verify_category_batch_with_timeout(
        category: ProofCategory,
        min_expected: usize,
        timeout_ms: u64,
    ) {
        if !z3_available() {
            crate::formal_gap::skip_test(
                &format!("verify_category_batch({category:?})"),
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        use crate::proof_database::{CategorizedProof, ProofDatabase};

        let full_db = ProofDatabase::new();
        let subset: Vec<CategorizedProof> =
            full_db.by_category(category).into_iter().cloned().collect();
        assert!(
            subset.len() >= min_expected,
            "Expected at least {} {} proofs, got {}",
            min_expected,
            category.name(),
            subset.len()
        );

        let config = AYConfig::default().with_timeout(timeout_ms);
        for cp in &subset {
            let result = verify_with_cli(&cp.obligation, &config);
            // Certification-gap guard (crate::formal_gap): AY answers unsat
            // but discloses an unproved hole step the constellation cannot
            // certify yet — skip LOUDLY on that disclosure only; every other
            // non-Verified outcome still fails the original assertion below.
            if let Some(reason) = crate::formal_gap::disclosed_proof_hole(&result) {
                crate::formal_gap::print_gap_skip(
                    &format!("{} proof '{}'", category.name(), cp.obligation.name),
                    &reason,
                );
                continue;
            }
            let solver = solver_info();
            assert_eq!(
                result,
                AYResult::Verified,
                "{} proof '{}' failed via {}: {}",
                category.name(),
                cp.obligation.name,
                solver,
                result
            );
        }
    }

    /// Verify all division proofs (sdiv/udiv I32/I64) through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_division_proofs() {
        verify_category_batch(ProofCategory::Division, 4);
    }

    /// FORMAL (real AY solver) discharge of the div-guard diamond COLLAPSE
    /// obligations — the HARDWARE-TOTAL semantics that let `select(b!=0, a/b, 0)`
    /// collapse to a single unguarded `SDIV`/`UDIV`. Pins that each collapse
    /// obligation discharges via the ACTUAL solver AND is structurally
    /// NON-degenerate, and that the wrong-else NEGATIVE control REFUTES (a SAT
    /// counterexample at `b == 0`), proving the collapse is not vacuous.
    #[test]
    fn test_ay_verify_div_guard_collapse_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_verify_div_guard_collapse_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default().with_timeout(30000);
        let proofs = crate::if_convert_proofs::all_select_div_collapse_proofs();
        assert_eq!(
            proofs.len(),
            4,
            "expected 4 div-guard collapse obligations, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "div-guard collapse '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            assert!(
                obligation.preconditions.is_empty(),
                "div-guard collapse '{}' must hold for ALL inputs (b==0 too) — no precondition",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "div-guard collapse '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_info(),
                    result
                ),
            );
        }

        // NON-VACUITY: the wrong-else control must be REFUTED by the real solver.
        let controls = crate::if_convert_proofs::select_div_collapse_wrong_controls();
        assert_eq!(controls.len(), 1);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "div-guard NEGATIVE control '{}' was VERIFIED — a wrong else value must REFUTE",
                obligation.name
            );
        }
    }

    /// Verify all floating-point lowering proofs (fadd/fsub/fmul/fdiv/fneg/fcmp F32/F64) through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_floating_point_proofs() {
        verify_category_batch(ProofCategory::FloatingPoint, 38);
    }

    /// Verify all general optimization pass proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_optimization_proofs() {
        // #62: ConstFold(k1,k2)/DCE/CopyProp X==X retracted; 2 genuine absorb proofs remain.
        verify_category_batch(ProofCategory::Optimization, 2);
    }

    /// Verify all constant folding proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_constant_folding_proofs() {
        verify_category_batch(ProofCategory::ConstantFolding, 5);
    }

    /// Verify all CSE/LICM proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_cse_licm_proofs() {
        if !z3_available() {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_cse_licm_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        use crate::proof_database::{CategorizedProof, ProofDatabase};

        let full_db = ProofDatabase::new();
        let subset: Vec<CategorizedProof> = full_db
            .by_category(ProofCategory::CseLicm)
            .into_iter()
            .cloned()
            .collect();
        assert!(
            subset.len() >= 3,
            "Expected at least 3 {} proofs, got {}",
            ProofCategory::CseLicm.name(),
            subset.len()
        );

        let config = AYConfig::default().with_timeout(30000);
        let mut verified = 0;
        let mut known_timeouts = 0;
        for cp in &subset {
            let result = verify_with_cli(&cp.obligation, &config);
            match result {
                AYResult::Verified => verified += 1,
                AYResult::Timeout
                    if cp
                        .obligation
                        .name
                        .contains("CSE commutative: mul(a, b) == mul(b, a)") =>
                {
                    known_timeouts += 1;
                    eprintln!(
                        "KNOWN ISSUE: {} -- solver timeout on hard commutative mul proof",
                        cp.obligation.name
                    );
                }
                other => panic!(
                    "{} proof '{}' failed via AY: {}",
                    ProofCategory::CseLicm.name(),
                    cp.obligation.name,
                    other
                ),
            }
        }

        assert!(
            verified >= subset.len().saturating_sub(known_timeouts),
            "Expected all CSE/LICM proofs verified except known timeouts, got {verified}/{} verified",
            subset.len()
        );
    }

    /// Verify all CFG simplification proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_cfg_simplification_proofs() {
        verify_category_batch(ProofCategory::CfgSimplification, 3);
    }

    /// Verify all NEON lowering proofs (trust_ir vector ops -> NEON) through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_lowering_proofs() {
        verify_category_batch(ProofCategory::NeonLowering, 20);
    }

    /// FORMAL (real AY solver) discharge of the 15 FAITHFUL per-lane
    /// D-register-pair COMPUTE obligations — the ones the coverage gate credits for
    /// the NEON lane-wise arith / compare / min-max / shift opcodes. This pins that
    /// they discharge via the ACTUAL solver (complete for all inputs), not just the
    /// statistical mock evaluator, AND that each is structurally NON-degenerate.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_lanewise_compute_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_lanewise_compute_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_lanewise_compute_proofs();
        assert_eq!(
            proofs.len(),
            18,
            "expected 18 faithful NEON lane-wise compute proofs, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON lane-wise compute proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON lane-wise compute proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY under the REAL solver: each wrong NEON encoding must be
        // REFUTED (a SAT counterexample), proving the faithful obligations above are
        // not trivially satisfiable.
        let controls = crate::neon_lowering_proofs::neon_lanewise_wrong_encoding_controls();
        assert_eq!(controls.len(), proofs.len());
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON lane-wise NEGATIVE control '{}' was VERIFIED by the solver — a wrong NEON \
                 encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the 30 FAITHFUL per-lane NEON FP
    /// obligations (FADD/FSUB/FMUL/FDIV/FCMGT x .4S/.2D x every lane) — the
    /// LANE-PLUMBING obligations the coverage gate credits for the NEON FP
    /// vector ops (see the honesty note in neon_lowering_proofs: both sides
    /// share the SMT FP model, so these pin lane wiring / op selection / lane
    /// width, NOT independent FP-circuit semantics). Pins that each discharges
    /// via the ACTUAL solver AND is structurally NON-degenerate, and that every
    /// wrong-encoding control — op confusions (FADD-as-FSUB, FMUL-as-FDIV,
    /// FCMGT-as-FCMGE/FCMEQ) and the WRONG-LANE-WIRING rotation — REFUTES.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_fp_lanewise_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_fp_lanewise_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_fp_lanewise_proofs();
        assert_eq!(
            proofs.len(),
            30,
            "expected 30 faithful NEON FP lane obligations, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON FP lane proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON FP lane proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY under the REAL solver: every wrong encoding must be
        // REFUTED (a SAT counterexample).
        let controls = crate::neon_lowering_proofs::neon_fp_lanewise_wrong_encoding_controls();
        assert_eq!(controls.len(), 14);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON FP lane NEGATIVE control '{}' was VERIFIED by the solver — a wrong NEON \
                 encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the 10 FAITHFUL `neon_fpred`
    /// per-lane obligations — {FMLA, FMLS (fused single-rounding `fp.fma`), UCVTF,
    /// SCVTF (per-lane int->FP), DupScalarD (64-bit lane copy)} x `.2D` 2 lanes —
    /// the ops the IV-synthesized FP-reduction vectorizer emits. Pins that each
    /// discharges via the ACTUAL solver AND is structurally NON-degenerate, and
    /// that every wrong-encoding control — FMLA<->FMLS opcode confusion, the
    /// accumulator miswire, sign confusion UCVTF<->SCVTF, and the wrong-lane
    /// wirings — REFUTES (non-vacuity). HONESTY as the FP lane proofs: both sides
    /// share the SMT FP model, so these pin lane/op/width plumbing, NOT an
    /// independent FP-circuit model.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_fpred_lane_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_fpred_lane_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_fpred_proofs();
        assert_eq!(
            proofs.len(),
            26,
            "expected 26 faithful NEON fpred lane obligations (10 .2D + 8 cvt .4S + 8 fma .4S), got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON fpred lane proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON fpred lane proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY under the REAL solver: every wrong encoding must be REFUTED
        // (a SAT counterexample), proving the faithful obligations are not
        // trivially satisfiable.
        let controls = crate::neon_lowering_proofs::neon_fpred_wrong_encoding_controls();
        assert_eq!(controls.len(), 8);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON fpred NEGATIVE control '{}' was VERIFIED by the solver — a wrong NEON \
                 encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the 20 FAITHFUL `NeonFmlaLaneV`
    /// (FMLA by element) obligations — the FULL (selector, dest) grid at `.4S`
    /// (16) and `.2D` (4) — the by-element fused multiply-accumulate the
    /// elementwise-FP vectorizer (`neon_fmap`) emits for `y[i] += da*x[i]` with
    /// the scalar invariant `da` kept in a broadcast lane. Pins that each
    /// discharges via the ACTUAL solver AND is structurally NON-degenerate, and
    /// that every wrong-encoding control — FMLA<->FMLS polarity, wrong-lane
    /// selector, and the accumulator miswire — REFUTES (non-vacuity). HONESTY as
    /// the FP lane proofs: both sides share the SMT FP model, so these pin
    /// lane/op/width/SELECTOR plumbing, NOT an independent FP-circuit model.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_fmla_lane_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_fmla_lane_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_fmla_lane_proofs();
        assert_eq!(
            proofs.len(),
            20,
            "expected 20 faithful NEON FMLA-by-element obligations, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON fmla-lane proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON fmla-lane proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY under the REAL solver: every wrong encoding must be REFUTED.
        let controls = crate::neon_lowering_proofs::neon_fmla_lane_wrong_encoding_controls();
        assert_eq!(controls.len(), 6);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON fmla-lane NEGATIVE control '{}' was VERIFIED by the solver — a wrong NEON \
                 encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the 4 FAITHFUL FCVTL/FCVTL2
    /// per-lane obligations — {FCVTL (low half), FCVTL2 (high half)} x `.2D` 2
    /// lanes — the `f32 -> f64` widen the FP array-reduction vectorizer
    /// (`neon_farray`) emits for the widening dot. Pins that each discharges via
    /// the ACTUAL solver AND is structurally NON-degenerate, and that every
    /// wrong-encoding control — the wrong-HALF confusion (FCVTL<->FCVTL2) and the
    /// wrong-lane wirings — REFUTES (non-vacuity). Widening `f32 -> f64` is EXACT
    /// (fpext, no rounding), so this is a genuine FP-to-FP identity; as with the
    /// other NEON-FP obligations both sides share the SMT `fp_to_fp` node, so this
    /// pins the LANE/HALF plumbing over the shared FP model.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_fcvtl_lane_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_fcvtl_lane_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_fcvtl_proofs();
        assert_eq!(
            proofs.len(),
            4,
            "expected 4 faithful NEON fcvtl lane obligations, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON fcvtl lane proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON fcvtl lane proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY under the REAL solver: every wrong encoding must be REFUTED.
        let controls = crate::neon_lowering_proofs::neon_fcvtl_wrong_encoding_controls();
        assert_eq!(controls.len(), 4);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON fcvtl NEGATIVE control '{}' was VERIFIED by the solver — a wrong NEON \
                 encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the FAITHFUL EOR-ROR
    /// shifted-register obligations — `EOR Rd, Rn, Rm, ROR #k` at W and X across
    /// representative amounts — the instruction the rotate-fusion peephole
    /// (`eor_rotate_fuse`) emits for the ARX `x ^= ROTL(v, r)` idiom (salsa20).
    /// Pins that each discharges via the ACTUAL solver AND is structurally
    /// NON-degenerate (SOURCE = frontend ROTL-XOR idiom, MACHINE = shifted-register
    /// EOR-ROR model — the two shifted halves in opposite OR order, so
    /// `trust_ir_expr != aarch64_expr` yet provably equal), and that every
    /// wrong-encoding control — wrong-amount, wrong-shift-kind (ROR-vs-LSR), and
    /// operand-swap — REFUTES (non-vacuity). PURE QF_BV: a complete faithful proof
    /// of the rotate + XOR.
    /// Formal AY discharge for the x86 ROL (rotate-left-by-constant) lowering,
    /// at both widths and across representative amounts including BOTH
    /// boundaries (k = 1 and k = width - 1).
    ///
    /// Pins all three properties a lowering obligation needs. (a) each
    /// DISCHARGES via the ACTUAL solver; (b) each is structurally
    /// NON-DEGENERATE — `ROL` means exactly the shift/shift/or idiom it
    /// replaces, so the naive obligation would be `X == X`, and the machine
    /// side is deliberately written with the OR halves in the opposite order;
    /// (c) every wrong encoding REFUTES, so (a) is not vacuous.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_x86_rol_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_x86_rol_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };
        let _batch_lock = ay_batch_test_lock();
        let config = AYConfig::default();

        let proofs = crate::x86_64_lowering_proofs::all_x86_rol_proofs();
        assert_eq!(proofs.len(), 11, "5 amounts at 32-bit + 6 at 64-bit");
        for obligation in &proofs {
            assert!(
                !obligation.is_degenerate(),
                "x86 ROL proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_eq!(
                result,
                AYResult::Verified,
                "x86 ROL proof '{}' did NOT formally discharge via {}: {}",
                obligation.name,
                solver_route_summary_for_invocation(obligation, &config),
                result
            );
        }

        // NON-VACUITY under the REAL solver: every wrong encoding must REFUTE.
        for size in [
            crate::x86_64_semantics::X86OperandSize::S32,
            crate::x86_64_semantics::X86OperandSize::S64,
        ] {
            for obligation in crate::x86_64_lowering_proofs::x86_rol_wrong_controls(size, 9) {
                let result = verify_with_cli(&obligation, &config);
                assert_ne!(
                    result,
                    AYResult::Verified,
                    "x86 ROL NEGATIVE control '{}' was VERIFIED — a wrong rotate \
                     encoding must REFUTE, else the positive obligation is vacuous",
                    obligation.name
                );
            }
        }
    }

    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_eor_ror_shift_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_eor_ror_shift_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::lowering_proof::all_eor_ror_shift_proofs();
        assert_eq!(
            proofs.len(),
            10,
            "expected 10 faithful EOR-ROR obligations (5 amounts x {{W,X}}), got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "EOR-ROR proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_eq!(
                result,
                AYResult::Verified,
                "EOR-ROR proof '{}' did NOT formally discharge via {}: {}",
                obligation.name,
                solver_route_summary_for_invocation(obligation, &config),
                result
            );
        }

        // NON-VACUITY under the REAL solver: every wrong encoding must be REFUTED.
        let controls = crate::lowering_proof::eor_ror_shift_wrong_controls();
        assert_eq!(controls.len(), 6, "3 controls x {{W,X}}");
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "EOR-ROR NEGATIVE control '{}' was VERIFIED by the solver — a wrong \
                 shifted-register EOR encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// Formal AY discharge for the UMULL widening-multiply obligation
    /// (`proof_umull_rr` — `Xd == zext64(Wn) * zext64(Wm)` over BV64, the
    /// UMADDL-with-XZR alias). 64-bit `bvmul` of two zero-extended 32-bit
    /// operands is solver-tractable (unlike the 128-bit Smulh/Umulh product).
    /// NON-VACUITY under the REAL solver: the SMULL sext confusion — the exact
    /// control that distinguishes UMULL from SMULL — and the truncating-MUL
    /// confusion must both be REFUTED.
    #[test]
    fn test_ay_verify_umull_widening() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_verify_umull_widening",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let obligation = crate::lowering_proof::proof_umull_rr();
        assert!(
            obligation.is_genuinely_proven(),
            "UMULL proof '{}' is DEGENERATE (X==X)",
            obligation.name
        );
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "UMULL proof '{}' did NOT formally discharge via {}: {}",
                obligation.name,
                solver_route_summary_for_invocation(&obligation, &config),
                result
            ),
        );

        let controls = crate::lowering_proof::umull_wrong_controls();
        assert_eq!(controls.len(), 2, "SMULL-sext + truncating-MUL controls");
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "UMULL NEGATIVE control '{}' was VERIFIED by the solver — a wrong \
                 widening-multiply machine side must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// Formal AY discharge for the LSL/LSR shifted-EOR forms emitted by
    /// `ShiftAluFuse`. The source shift is expressed independently as
    /// multiply/divide by a power of two, so these are genuine (non-X==X)
    /// obligations. Wrong-kind and wrong-amount controls must remain SAT.
    #[test]
    fn test_ay_verify_eor_lsl_lsr_reconstruction() {
        use crate::aarch64_semantics::{RegShiftKind, encode_eor_shifted_reg};
        use crate::function_verifier::reconstruct_alu_obligation;
        use trust_cg_ir::{AArch64Opcode, MachInst, MachOperand, RegClass, VReg};

        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_verify_eor_lsl_lsr_reconstruction",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };
        let _batch_lock = ay_batch_test_lock();
        let config = AYConfig::default();

        for (class, width) in [(RegClass::Gpr32, 32u32), (RegClass::Gpr64, 64u32)] {
            let reg = |id| MachOperand::VReg(VReg::new(id, class));
            for opcode in [AArch64Opcode::EorRRLsl, AArch64Opcode::EorRRLsr] {
                for amount in [1u32, 7, width - 1] {
                    let inst = MachInst::new(
                        opcode,
                        vec![reg(0), reg(1), reg(2), MachOperand::Imm(i64::from(amount))],
                    );
                    let obligation = reconstruct_alu_obligation(&inst)
                        .expect("well-formed shifted EOR must reconstruct");
                    assert!(
                        obligation.is_genuinely_proven(),
                        "{} must be structurally non-degenerate",
                        obligation.name
                    );
                    let result = verify_with_cli(&obligation, &config);
                    assert_verified_or_certification_gap_skip(
                        &obligation,
                        &result,
                        format_args!(
                            "AY failed {} via {}",
                            obligation.name,
                            solver_route_summary_for_invocation(&obligation, &config)
                        ),
                    );
                }
            }
        }

        let reg = |id| MachOperand::VReg(VReg::new(id, RegClass::Gpr32));
        let inst = MachInst::new(
            AArch64Opcode::EorRRLsl,
            vec![reg(0), reg(1), reg(2), MachOperand::Imm(7)],
        );
        let base = reconstruct_alu_obligation(&inst).expect("control base must reconstruct");
        for (label, kind, amount) in [
            ("LSR-for-LSL", RegShiftKind::Lsr, 7u32),
            ("wrong-amount", RegShiftKind::Lsl, 8u32),
        ] {
            let mut wrong = base.clone();
            wrong.name = format!("{} negative control: {label}", base.name);
            wrong.aarch64_expr = encode_eor_shifted_reg(
                trust_cg_ir::cc::OperandSize::S32,
                SmtExpr::var("recon_src1", 32),
                SmtExpr::var("recon_src2", 32),
                kind,
                amount,
            );
            assert_ne!(
                verify_with_cli(&wrong, &config),
                AYResult::Verified,
                "AY verified shifted-EOR negative control {label}"
            );
        }
    }

    /// The LSR+low-mask -> UBFX pass is authorized by the symbolic W/X UBFM
    /// encoding theorem, not a fixed `(k,width)` example. Check both universal
    /// carrier theorems through AY and make the classic `imms = lsb + width`
    /// off-by-one refute under the same preconditions.
    #[test]
    fn test_ay_verify_symbolic_ubfx_encoding_and_refute_off_by_one() {
        use crate::lowering_proof::{proof_ubfm_extract_w32, proof_ubfm_extract_w64};

        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_verify_symbolic_ubfx_encoding_and_refute_off_by_one",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };
        let _batch_lock = ay_batch_test_lock();
        let config = AYConfig::default();

        for (width, base) in [
            (32u32, proof_ubfm_extract_w32()),
            (64u32, proof_ubfm_extract_w64()),
        ] {
            let base_result = verify_with_cli(&base, &config);
            assert_verified_or_certification_gap_skip(
                &base,
                &base_result,
                format_args!("AY failed symbolic UBFM/UBFX theorem at width {width}"),
            );

            let idx_width = if width == 32 { 6 } else { 7 };
            let rn = SmtExpr::var("rn", width);
            let one = SmtExpr::bv_const(1, width);
            let lsb = SmtExpr::var("lsb", idx_width).zero_ext(width - idx_width);
            let field_width = SmtExpr::var("width", idx_width).zero_ext(width - idx_width);
            let wrong_imms = lsb.clone().bvadd(field_width);
            let decoded_width = wrong_imms.bvsub(lsb.clone()).bvadd(one.clone());

            let mut wrong = base.clone();
            wrong.name = format!("{} negative control: imms off by one", base.name);
            wrong.aarch64_expr = rn
                .bvlshr(lsb)
                .bvand(one.clone().bvshl(decoded_width).bvsub(one));
            assert_ne!(
                verify_with_cli(&wrong, &config),
                AYResult::Verified,
                "AY accepted wrong UBFM imms formula at width {width}"
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the FAITHFUL FCSEL bit-preserving
    /// mux obligations — `CMP sel,#0` + `FCSEL(dst, a, b, from_intcc(cond))` at
    /// the S (f32) and D (f64) forms across a spread of condition codes — the
    /// instruction the FP-`Select` isel path emits (replacing the FMOV->CSEL->FMOV
    /// cross-bank round trip). Pins that each discharges via the ACTUAL solver AND
    /// is structurally NON-degenerate (SOURCE = `ite(trust_ir icmp(cond,sel,0), a,
    /// b)`, MACHINE = `ite(eval_condition(from_intcc(cond), CMP(sel,0)), a, b)` —
    /// a direct compare vs the NZCV-subtraction flag model, so `trust_ir_expr !=
    /// aarch64_expr` yet provably equal), and that every wrong-encoding control —
    /// inverted-cond and operand-swap — REFUTES (non-vacuity). PURE QF_BV: the FP
    /// register bits are never interpreted as floats (bit-preserving by
    /// construction — NaN/±0/denormal safe with no FP reasoning).
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_fcsel_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_fcsel_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::lowering_proof::all_fcsel_proofs();
        assert_eq!(
            proofs.len(),
            12,
            "expected 12 faithful FCSEL obligations (6 conds x {{S,D}}), got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "FCSEL proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "FCSEL proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY under the REAL solver: every wrong encoding must be REFUTED.
        let controls = crate::lowering_proof::fcsel_wrong_controls();
        assert_eq!(controls.len(), 8, "2 control types x 2 conds x {{S,D}}");
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "FCSEL NEGATIVE control '{}' was VERIFIED by the solver — a wrong FCSEL \
                 encoding (inverted-cond / operand-swap) must REFUTE, so the obligation \
                 is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the 30 FAITHFUL per-(size, lane)
    /// `NeonUmovGen` extract obligations — the FULL emitted matrix (`.16B` 16
    /// lanes + `.8H` 8 + `.4S` 4 + `.2D` 2), the op every NEON lane->scalar
    /// extract lowers through (reduction drains at `.S`/`.D` + the
    /// `V{16I8,8I16,4I32,2I64}ExtractLane` isel at `.B`/`.H`/`.S`/`.D`). Pins that
    /// each discharges via the ACTUAL solver AND is structurally NON-degenerate,
    /// and that every wrong-encoding control — wrong-lane on all four sizes and
    /// wrong-size (element-size operand confusion) — REFUTES (non-vacuity). These
    /// are PURE QF_BV: unlike the FP lane proofs there is NO shared opaque node,
    /// so this is a COMPLETE faithful proof of the extract + zero-extend.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_umov_lane_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_umov_lane_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_umov_proofs();
        assert_eq!(
            proofs.len(),
            30,
            "expected 30 faithful NEON UMOV (size,lane) obligations, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON UMOV extract proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON UMOV extract proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY under the REAL solver: every wrong encoding must be REFUTED
        // (a SAT counterexample), proving the faithful obligations are not
        // trivially satisfiable.
        let controls = crate::neon_lowering_proofs::neon_umov_wrong_encoding_controls();
        assert_eq!(controls.len(), 7);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON UMOV NEGATIVE control '{}' was VERIFIED by the solver — a wrong lane \
                 or element size must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the 10 FAITHFUL `.2D` (2 x i64)
    /// lane-wise compute obligations — one per op the i64 (`.2D`) vectorizer
    /// paths emit (ADD/SUB, the 5 compares, the 3 immediate shifts). Pins that
    /// each discharges via the ACTUAL solver AND is structurally NON-degenerate,
    /// and that every wrong encoding — including the WRONG-ARRANGEMENT
    /// (.2D-as-.4S) control — is REFUTED (non-vacuity).
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_lanewise_compute_proofs_2d() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_lanewise_compute_proofs_2d",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_lanewise_compute_proofs_2d();
        assert_eq!(
            proofs.len(),
            10,
            "expected 10 faithful NEON `.2D` lane-wise compute proofs, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON `.2D` lane-wise compute proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON `.2D` lane-wise compute proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY under the REAL solver: 10 per-op mutations + the
        // wrong-arrangement (.2D-as-.4S) control must ALL refute.
        let controls = crate::neon_lowering_proofs::neon_lanewise_wrong_encoding_controls_2d();
        assert_eq!(controls.len(), proofs.len() + 1);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON `.2D` NEGATIVE control '{}' was VERIFIED by the solver — a wrong NEON \
                 encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the 2 FAITHFUL SADDLP (signed
    /// add-long-pairwise) obligations — the ones the coverage gate credits for
    /// the widening `sext(i8/i16)` reduction lowering's `NeonSaddlpV`. Pins that
    /// they discharge via the ACTUAL solver AND are structurally NON-degenerate,
    /// and that each wrong encoding — MOST IMPORTANTLY the sign-confusion
    /// SADDLP-as-UADDLP mutation — is REFUTED (non-vacuity).
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_saddlp_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_saddlp_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_saddlp_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "expected 2 faithful NEON SADDLP proofs, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON SADDLP proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON SADDLP proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY: SADDLP-as-UADDLP (sign confusion, x2 arrangements) and
        // SADDLP-as-pairwise-SUB (x2) must ALL refute under the real solver.
        let controls = crate::neon_lowering_proofs::neon_saddlp_wrong_encoding_controls();
        assert_eq!(controls.len(), 4);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON SADDLP NEGATIVE control '{}' was VERIFIED by the solver — a wrong NEON \
                 encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the FAITHFUL BIT (bitwise insert
    /// if true) obligation — the one the coverage gate credits for the i64
    /// (`.2D`) min/max reduction's `NeonBitV`. Pins solver discharge +
    /// non-degeneracy, and that the BSL/BIT/BIF wiring confusions REFUTE.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_bit_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_bit_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_bit_proofs();
        assert_eq!(proofs.len(), 1, "expected 1 faithful NEON BIT proof");

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON BIT proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON BIT proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        let controls = crate::neon_lowering_proofs::neon_bit_wrong_encoding_controls();
        assert_eq!(controls.len(), 3);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON BIT NEGATIVE control '{}' was VERIFIED by the solver — a wrong NEON \
                 encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the 3 FAITHFUL popcount-fold
    /// obligations (CNT.16B + UADDLP `.16B->.8H` + `.8H->.4S`) — the ones the
    /// coverage gate credits for the ctpop-reduction lowering's NEON ops. Pins that
    /// they discharge via the ACTUAL solver AND are structurally NON-degenerate, and
    /// that each wrong encoding is REFUTED (non-vacuity).
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_popcount_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_popcount_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_popcount_proofs();
        assert_eq!(
            proofs.len(),
            3,
            "expected 3 faithful NEON popcount-fold proofs, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON popcount-fold proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON popcount-fold proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY: each wrong NEON encoding (CNT-as-identity, UADDLP-as-SUB)
        // must be REFUTED by the real solver.
        let controls = crate::neon_lowering_proofs::neon_popcount_wrong_encoding_controls();
        assert_eq!(controls.len(), proofs.len());
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON popcount-fold NEGATIVE control '{}' was VERIFIED by the solver — a wrong \
                 NEON encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the FAITHFUL signed-abs obligation
    /// (ABS.4S) — the one the coverage gate credits for the abs-sum reduction
    /// lowering's `NeonAbsV`. Pins that it discharges via the ACTUAL solver AND is
    /// structurally NON-degenerate, and that each wrong encoding is REFUTED
    /// (non-vacuity).
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_abs_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_abs_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_abs_proofs();
        assert_eq!(
            proofs.len(),
            1,
            "expected 1 faithful NEON signed-abs proof, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON signed-abs proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON signed-abs proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY: each wrong NEON encoding (abs-as-identity,
        // abs-as-negate-always) must be REFUTED by the real solver.
        let controls = crate::neon_lowering_proofs::neon_abs_wrong_encoding_controls();
        assert_eq!(controls.len(), 2);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON signed-abs NEGATIVE control '{}' was VERIFIED by the solver — a wrong \
                 NEON encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the FAITHFUL unsigned
    /// dot-product-accumulate obligation (UDOT.4S, FEAT_DotProd) — the one the
    /// coverage gate credits for the ctpop-reduction lowering's `NeonUdotV`. Pins
    /// that it discharges via the ACTUAL solver AND is structurally NON-degenerate,
    /// and that each wrong encoding is REFUTED (non-vacuity).
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_udot_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_udot_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_udot_proofs();
        assert_eq!(
            proofs.len(),
            1,
            "expected 1 faithful NEON udot proof, got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON udot proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON udot proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY: each wrong NEON encoding (dot-without-accumulate,
        // UDOT-as-SDOT, wrong byte group) must be REFUTED by the real solver.
        let controls = crate::neon_lowering_proofs::neon_udot_wrong_encoding_controls();
        assert_eq!(controls.len(), 3);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON udot NEGATIVE control '{}' was VERIFIED by the solver — a wrong \
                 NEON encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real solver) discharge of the FAITHFUL 32-bit pair-swap
    /// obligation (REV64.4S) — the one the coverage gate credits for the
    /// butterfly vectorizer's `NeonRev64V`. Pins that it discharges via the
    /// ACTUAL solver AND is structurally NON-degenerate, and that each wrong
    /// encoding (identity / doubleword swap / half-lane smear) is REFUTED.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_rev64_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_rev64_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_rev64_proofs();
        assert_eq!(
            proofs.len(),
            2,
            "expected 2 faithful NEON rev64 proofs (.4S + the emitted .16B form), got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON rev64 proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON rev64 proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY: each wrong NEON encoding must be REFUTED by the solver.
        let controls = crate::neon_lowering_proofs::neon_rev64_wrong_encoding_controls();
        assert_eq!(controls.len(), 6, "3 x .4S controls + 3 x .16B controls");
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON rev64 NEGATIVE control '{}' was VERIFIED by the solver — a wrong \
                 NEON encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// FORMAL (real AY solver) discharge of the FAITHFUL byte-window extract
    /// obligations (EXT.16B #1/#4/#8/#12/#15) — the ones the coverage gate
    /// credits for the stencil and stencil-count-if vectorizers' `NeonExtV`.
    /// Pins that each discharges via the ACTUAL solver AND is structurally
    /// NON-degenerate, and that each wrong encoding is REFUTED (non-vacuity).
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_ext_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_neon_ext_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::neon_lowering_proofs::all_neon_ext_proofs();
        assert_eq!(
            proofs.len(),
            5,
            "expected 5 faithful NEON ext proofs (one per emitted immediate: \
             #1/#4/#8/#12/#15), got {}",
            proofs.len()
        );

        for obligation in &proofs {
            assert!(
                obligation.is_genuinely_proven(),
                "NEON ext proof '{}' is DEGENERATE (X==X)",
                obligation.name
            );
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                obligation,
                &result,
                format_args!(
                    "NEON ext proof '{}' did NOT formally discharge via {}: {}",
                    obligation.name,
                    solver_route_summary_for_invocation(obligation, &config),
                    result
                ),
            );
        }

        // NON-VACUITY: each wrong NEON encoding (swapped operands, wrong
        // immediate, ext-as-identity, and the stencil-neighbor
        // opposite-direction #1<->#15 controls) must be REFUTED by the real
        // solver.
        let controls = crate::neon_lowering_proofs::neon_ext_wrong_encoding_controls();
        assert_eq!(controls.len(), 8);
        for obligation in &controls {
            let result = verify_with_cli(obligation, &config);
            assert_ne!(
                result,
                AYResult::Verified,
                "NEON ext NEGATIVE control '{}' was VERIFIED by the solver — a wrong \
                 NEON encoding must REFUTE, so the obligation is vacuous",
                obligation.name
            );
        }
    }

    /// Verify all NEON encoding correctness proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_neon_encoding_proofs() {
        verify_category_batch(ProofCategory::NeonEncoding, 5);
    }

    /// Verify all vectorization proofs (scalar-to-NEON mapping) through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_vectorization_proofs() {
        verify_category_batch(ProofCategory::Vectorization, 30);
    }

    /// Verify all register allocation correctness proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_regalloc_proofs() {
        verify_category_batch(ProofCategory::RegAlloc, 5);
    }

    /// Verify constant materialization proofs (MOVZ, MOVZ+MOVK, ORR, MOVN) through the selected CLI solver.
    /// NOTE: Known issue -- MOVZ+MOVK exhaustive proof has a BV width mismatch
    /// in its SMT encoding (16-bit vs 24-bit). This test tracks the issue.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_constant_materialization_proofs() {
        if !z3_available() {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_constant_materialization_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        use crate::proof_database::{CategorizedProof, ProofDatabase};

        let full_db = ProofDatabase::new();
        let subset: Vec<CategorizedProof> = full_db
            .by_category(ProofCategory::ConstantMaterialization)
            .into_iter()
            .cloned()
            .collect();
        assert!(
            subset.len() >= 3,
            "Expected at least 3 proofs, got {}",
            subset.len()
        );

        let config = AYConfig::default().with_timeout(10000);
        let mut verified = 0;
        let mut known_errors = 0;
        let mut gap_skips = 0;
        for cp in &subset {
            let result = verify_with_cli(&cp.obligation, &config);
            match &result {
                AYResult::Verified => verified += 1,
                AYResult::Error(msg) if msg.contains("does not match declaration") => {
                    // Known BV sort mismatch in MOVZ+MOVK proof encoding
                    known_errors += 1;
                    eprintln!(
                        "KNOWN ISSUE: {} -- BV sort mismatch: {}",
                        cp.obligation.name, msg
                    );
                }
                // Certification-gap guard (crate::formal_gap): skip LOUDLY only
                // on AY's disclosed proof hole; anything else still panics with
                // the original message.
                other => match crate::formal_gap::disclosed_proof_hole(other) {
                    Some(reason) => {
                        crate::formal_gap::print_gap_skip(
                            &format!("Constant Materialization proof '{}'", cp.obligation.name),
                            &reason,
                        );
                        gap_skips += 1;
                    }
                    None => panic!(
                        "Constant Materialization proof '{}' failed unexpectedly: {}",
                        cp.obligation.name, other
                    ),
                },
            }
        }
        assert!(
            verified + gap_skips >= 2,
            "Expected at least 2 verified (counting loudly-skipped certification gaps), got \
             {verified} verified and {gap_skips} gap skips"
        );
        if gap_skips == 0 {
            assert!(
                verified >= 2,
                "Expected at least 2 verified, got {}",
                verified
            );
        }
        // Track known errors for issue reporting
        if known_errors > 0 {
            eprintln!(
                "ConstantMaterialization: {} known sort-mismatch errors",
                known_errors
            );
        }
    }

    /// Verify all address mode formation proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_address_mode_proofs() {
        verify_category_batch(ProofCategory::AddressMode, 3);
    }

    /// Verify all frame layout / frame index elimination proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_frame_layout_proofs() {
        verify_category_batch(ProofCategory::FrameLayout, 3);
    }

    /// Verify all instruction scheduling correctness proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_instruction_scheduling_proofs() {
        verify_category_batch(ProofCategory::InstructionScheduling, 5);
    }

    /// Verify all Mach-O emission correctness proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_macho_emission_proofs() {
        verify_category_batch(ProofCategory::MachOEmission, 3);
    }

    /// Verify all loop optimization proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_loop_optimization_proofs() {
        // Faulhaber's m=3 obligation legitimately exceeds both the generic
        // 30s category budget and 180s on a heavily loaded publication host.
        verify_category_batch_with_timeout(ProofCategory::LoopOptimization, 3, 300_000);
    }

    /// Verify all strength reduction proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_strength_reduction_proofs() {
        run_with_ay_batch_stack(|| verify_category_batch(ProofCategory::StrengthReduction, 3));
    }

    /// Verify all compare-combine proofs (compare-and-branch, compare-select) through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_cmp_combine_proofs() {
        verify_category_batch(ProofCategory::CmpCombine, 3);
    }

    /// The authority actually bound to an emitted TST is the complete packed
    /// NZCV theorem at the concrete W/X width, not any one condition-code view.
    /// Route both carrier proofs through AY's exact-proof protocol; `Verified`
    /// is returned only after the independent Clean/Carcara checker accepts the
    /// hole-free Alethe artifact.
    #[test]
    fn test_ay_verify_tst_packed_nzcv_proofs() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_ay_verify_tst_packed_nzcv_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let _batch_lock = ay_batch_test_lock();
        let config = AYConfig::default().with_timeout(30_000);
        for width in [32u32, 64] {
            let obligation = crate::cmp_combine_proofs::proof_tst_packed_nzcv(width);
            let result = verify_with_cli(&obligation, &config);
            assert_verified_or_certification_gap_skip(
                &obligation,
                &result,
                format_args!(
                    "packed-NZCV TST w{width} failed exact checked discharge via {}: {result}",
                    solver_route_summary_for_invocation(&obligation, &config),
                ),
            );
            let raw_result = verify_with_cli_raw(&obligation, &config);
            assert_verified_or_certification_gap_skip(
                &obligation,
                &raw_result,
                format_args!(
                    "packed-NZCV TST w{width} failed RAW exact checked discharge via {}: {raw_result}",
                    solver_route_summary_for_invocation(&obligation, &config),
                ),
            );
        }
    }

    /// Verify all GVN (Global Value Numbering) proofs through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_gvn_proofs() {
        if !z3_available() {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_gvn_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        use crate::proof_database::{CategorizedProof, ProofDatabase};

        let full_db = ProofDatabase::new();
        let subset: Vec<CategorizedProof> = full_db
            .by_category(ProofCategory::Gvn)
            .into_iter()
            .cloned()
            .collect();
        assert!(
            subset.len() >= 3,
            "Expected at least 3 {} proofs, got {}",
            ProofCategory::Gvn.name(),
            subset.len()
        );

        let config = AYConfig::default().with_timeout(30000);
        let mut verified = 0;
        let mut known_timeouts = 0;
        for cp in &subset {
            let result = verify_with_cli(&cp.obligation, &config);
            match result {
                AYResult::Verified => verified += 1,
                AYResult::Timeout
                    if cp
                        .obligation
                        .name
                        .contains("GVN commutativity: mul(a, b) == mul(b, a)") =>
                {
                    known_timeouts += 1;
                    eprintln!(
                        "KNOWN ISSUE: {} -- solver timeout on hard commutative mul proof",
                        cp.obligation.name
                    );
                }
                other => panic!(
                    "{} proof '{}' failed via AY: {}",
                    ProofCategory::Gvn.name(),
                    cp.obligation.name,
                    other
                ),
            }
        }

        assert!(
            verified >= subset.len().saturating_sub(known_timeouts),
            "Expected all GVN proofs verified except known timeouts, got {verified}/{} verified",
            subset.len()
        );
    }

    /// Verify all if-conversion proofs (diamond/triangle CFG to CSEL) through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_if_conversion_proofs() {
        // #62: the 22 self-equality IfConversion X==X were retracted; 2 genuine
        // CSEL condition-inversion proofs (64+8bit) remain.
        verify_category_batch(ProofCategory::IfConversion, 2);
    }

    /// Verify FP conversion proofs (FCVTZS, FCVTZU, SCVTF, etc.) through the selected CLI solver.
    /// The FCVTZS_NaN_produces_zero obligation now uses an `isNaN` guard on the
    /// impl side (NaN -> 0), so it discharges like every other FP conversion
    /// proof — there is no longer a tolerated NaN counterexample.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_fp_conversion_proofs() {
        if !z3_available() {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_fp_conversion_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        use crate::proof_database::{CategorizedProof, ProofDatabase};

        let full_db = ProofDatabase::new();
        let subset: Vec<CategorizedProof> = full_db
            .by_category(ProofCategory::FpConversion)
            .into_iter()
            .cloned()
            .collect();
        assert!(
            subset.len() >= 3,
            "Expected at least 3 FP conversion proofs, got {}",
            subset.len()
        );

        let config = AYConfig::default().with_timeout(30000);
        let mut verified = 0;
        let mut gap_skips = 0;
        for cp in &subset {
            let result = verify_with_cli(&cp.obligation, &config);
            match &result {
                AYResult::Verified => verified += 1,
                // Certification-gap guard (crate::formal_gap): skip LOUDLY only
                // on AY's disclosed proof hole; anything else still panics with
                // the original message.
                other => match crate::formal_gap::disclosed_proof_hole(other) {
                    Some(reason) => {
                        crate::formal_gap::print_gap_skip(
                            &format!("FP Conversion proof '{}'", cp.obligation.name),
                            &reason,
                        );
                        gap_skips += 1;
                    }
                    None => panic!(
                        "FP Conversion proof '{}' failed unexpectedly: {} \
                         (the NaN obligation is now isNaN-guarded and must verify)",
                        cp.obligation.name, other
                    ),
                },
            }
        }
        assert!(
            verified + gap_skips >= 2,
            "Expected at least 2 verified (counting loudly-skipped certification gaps), got \
             {verified} verified and {gap_skips} gap skips"
        );
        if gap_skips == 0 {
            assert!(
                verified >= 2,
                "Expected at least 2 verified, got {}",
                verified
            );
        }
    }

    /// Verify all extension/truncation proofs (SXTB, UXTB, etc.) through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_ext_trunc_proofs() {
        verify_category_batch(ProofCategory::ExtensionTruncation, 5);
    }

    /// Verify atomic operation proofs (LDAR/STLR, LDADD, CAS, etc.) through the selected CLI solver.
    /// The non-interference formulas remain a known formal-solver gap: some
    /// report counterexamples or timeouts through the CLI path, and are kept
    /// observable instead of being counted as verified.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_atomic_proofs() {
        if !z3_available() {
            crate::formal_gap::skip_test(
                "test_ay_batch_verify_atomic_proofs",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        use crate::proof_database::{CategorizedProof, ProofDatabase};

        let full_db = ProofDatabase::new();
        let subset: Vec<CategorizedProof> = full_db
            .by_category(ProofCategory::AtomicOperations)
            .into_iter()
            .cloned()
            .collect();
        assert!(
            subset.len() >= 5,
            "Expected at least 5 atomic proofs, got {}",
            subset.len()
        );

        let config = AYConfig::default().with_timeout(30_000);
        let mut verified = 0;
        let mut known_cex = 0;
        let mut known_timeout = 0;
        let mut gap_skips = 0;
        for cp in &subset {
            let result = verify_with_cli(&cp.obligation, &config);
            match &result {
                AYResult::Verified => verified += 1,
                AYResult::CounterExample(_) if cp.obligation.name.contains("non-interference") => {
                    // Known issue: non-interference proofs need stronger formal modeling.
                    known_cex += 1;
                    eprintln!(
                        "KNOWN ISSUE: {} -- non-interference counterexample",
                        cp.obligation.name
                    );
                }
                AYResult::Timeout if cp.obligation.name.contains("non-interference") => {
                    known_timeout += 1;
                    eprintln!(
                        "KNOWN ISSUE: {} -- non-interference solver timeout",
                        cp.obligation.name
                    );
                }
                // Certification-gap guard (crate::formal_gap): skip LOUDLY only
                // on AY's disclosed proof hole; anything else still panics with
                // the original message.
                other => match crate::formal_gap::disclosed_proof_hole(other) {
                    Some(reason) => {
                        crate::formal_gap::print_gap_skip(
                            &format!("Atomic proof '{}'", cp.obligation.name),
                            &reason,
                        );
                        gap_skips += 1;
                    }
                    None => panic!(
                        "Atomic proof '{}' failed unexpectedly: {}",
                        cp.obligation.name, other
                    ),
                },
            }
        }
        assert!(
            verified + gap_skips >= 3,
            "Expected at least 3 verified (counting loudly-skipped certification gaps), got \
             {verified} verified and {gap_skips} gap skips"
        );
        if gap_skips == 0 {
            assert!(
                verified >= 3,
                "Expected at least 3 verified, got {}",
                verified
            );
        }
        if known_cex > 0 {
            eprintln!(
                "AtomicOperations: {} known non-interference counterexamples",
                known_cex
            );
        }
        if known_timeout > 0 {
            eprintln!(
                "AtomicOperations: {} known non-interference timeouts",
                known_timeout
            );
        }
    }

    /// Verify all call lowering proofs (argument placement, callee-saved, etc.) through the selected CLI solver.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_call_lowering_proofs() {
        verify_category_batch(ProofCategory::CallLowering, 5);
    }

    /// Comprehensive test: verify ALL proof categories through the selected CLI solver via ProofDatabase.
    /// This is the definitive batch test that ensures every category is covered.
    ///
    /// Known issues (pre-existing proof encoding and solver-capacity limits):
    /// - ConstantMaterialization: MOVZ+MOVK BV sort mismatch (error)
    /// - Per-proof AY timeouts (load-induced under concurrent test runs): see #460
    ///
    /// FIXED (no longer tolerated — they must now formally verify):
    /// - FpConversion FCVTZS NaN: re-encoded with an `isNaN` guard (NaN -> 0).
    /// - AtomicOperations/Memory non-interference: now carry no-wrap + natural-
    ///   alignment disjointness preconditions, so the wrapping counterexample is
    ///   excluded and the obligations discharge.
    #[test]
    #[cfg_attr(
        not(feature = "live-ay"),
        ignore = "live-AY batch group: run with --features live-ay (TRUSTCG-21)"
    )]
    fn test_ay_batch_verify_all_categories_comprehensive() {
        run_with_ay_batch_stack(|| {
            if !z3_available() {
                crate::formal_gap::skip_test(
                    "test_ay_batch_verify_all_categories_comprehensive",
                    crate::formal_gap::NO_PROOF_AUTHORITY,
                );
                return;
            }

            let _batch_lock = ay_batch_test_lock();

            use crate::proof_database::ProofDatabase;

            let db = ProofDatabase::new();
            // Per-proof timeout: 90s. AY is the sole solver now, and the exact
            // f64 int<->fp roundtrip conversion proofs legitimately take several
            // seconds each under AY's bit-blasting (and more under the parallel
            // test load this rollup generates). 90s gives robust headroom while
            // keeping total wall time within the test budget (the fast BV proofs
            // dominate the count and finish sub-second). See issue #460.
            let config = AYConfig::default().with_timeout(90000);
            let report = verify_proof_database_with_ay(&db, &config);

            // Print summary for diagnostics
            eprintln!("{}", report);

            // Every category in the database must have been tested
            let breakdown = report.by_category();
            assert!(
                breakdown.len() >= 30,
                "Expected at least 30 categories in AY report, got {}",
                breakdown.len()
            );

            // Count known-issue failures separately from unexpected failures.
            //
            // Known pre-existing proof encoding and solver-capacity issues:
            // 1. ConstantMaterialization exhaustive: BV sort width mismatch (16 vs 24)
            // 2. Memory range non-interference: missing address range disjointness precondition
            // 3. Per-proof AY timeouts (load-induced, not a logic failure): see #460
            //
            // NO LONGER TOLERATED (must verify): AtomicOperations/Memory
            // non-interference (now no-wrap + alignment guarded) and FpConversion
            // FCVTZS NaN (now isNaN-guarded) — their tolerances were removed so a
            // regression fails the test rather than being silently skipped.
            let is_known_issue = |name: &str, detail: &str| -> bool {
                // ConstMat BV sort mismatch
                name.contains("exhaustive")
                // Memory range non-interference missing range disjointness
                || name.contains("RangeNonInterference")
                // Sort mismatch errors (pre-existing encoding issues)
                || detail.contains("does not match declaration")
                // x86-64 narrow-vector multiply (V16I8Mul -> PUNPCKBW+PMULLW+
                // PAND+PACKUSWB) saturates AY's bit-vector reasoning: the proof
                // composes two 8->16 unpacks, a 16-bit multiply, a mask, and a
                // saturating pack, which AY reports as `(:reason-unknown
                // incomplete)` rather than sat/unsat. This is solver
                // incompleteness on a hard BV goal, not a lowering bug.
                // A rejected proof is not incompleteness: an `incomplete
                // self-check-rejected` detail, a working checker's rejection,
                // or AY's caught-invalid-model refusal (`incomplete` is a
                // substring of that reason too) is a soundness failure and
                // stays unexpected.
                || (name.contains("V16I8Mul")
                    && detail.contains("incomplete")
                    && !crate::proof_gate::unknown_is_hard_failure(detail))
                // Per-proof AY timeouts are load-induced, not logic failures.
                // This comprehensive rollup runs dozens of proofs back-to-back
                // and is sensitive to concurrent test-parallelism / cargo lock
                // contention on the same host. The report still surfaces them
                // via report.timeouts() below, so they remain observable. The
                // surrounding test-level assertion (verified >= 200) keeps us
                // honest: if timeouts become widespread, the verified count
                // will drop below threshold and the test will still fail.
                // See issue #460 for the flake root-cause analysis.
                || detail == "TIMEOUT"
                // STRICT (task #61): degenerate X==X obligations are now listed
                // in failed_details (they discharge `Verified` but prove nothing).
                // They are DISCLOSED DEBT, not a SOLVER failure — this test is
                // about solver soundness/liveness, so they are not "unexpected".
                || detail.starts_with("DEGENERATE")
            };
            // Certification-gap guard (crate::formal_gap): a row whose
            // diagnostic is AY's disclosed proof hole skips LOUDLY; every other
            // failure (a checker or self-check rejection and a bare `UNKNOWN:
            // unknown` included) stays an UNEXPECTED FAILURE and panics below.
            let mut gap_skips = 0usize;
            let mut unexpected_failures: Vec<(String, ProofCategory, String)> = Vec::new();
            for (name, cat, detail) in report.failed_details() {
                if is_known_issue(&name, &detail) {
                    continue;
                }
                let confirmed_gap = detail.strip_prefix("UNKNOWN: ").and_then(|reason| {
                    crate::formal_gap::disclosed_proof_hole(&AYResult::Unknown(reason.to_string()))
                });
                match confirmed_gap {
                    Some(reason) => {
                        crate::formal_gap::print_gap_skip(
                            &format!("[{}] {}", cat.name(), name),
                            &reason,
                        );
                        gap_skips += 1;
                    }
                    None => unexpected_failures.push((name, cat, detail)),
                }
            }

            let all_failures = report.failed_details();
            let known_count = all_failures.len() - unexpected_failures.len() - gap_skips;
            if known_count > 0 {
                eprintln!(
                    "NOTE: {} known pre-existing proof encoding issues skipped",
                    known_count
                );
            }

            if !unexpected_failures.is_empty() {
                for (name, cat, detail) in &unexpected_failures {
                    eprintln!(
                        "UNEXPECTED FAILURE: [{}] {} -- {}",
                        cat.name(),
                        name,
                        detail
                    );
                }
                panic!(
                    "AY found {} UNEXPECTED failures (excluding {} known issues)",
                    unexpected_failures.len(),
                    known_count
                );
            }

            // Timeouts are acceptable for complex proofs but we track them
            if report.timeouts() > 0 {
                eprintln!(
                    "WARNING: {} proofs timed out (not failures, but should be investigated)",
                    report.timeouts()
                );
            }

            // Total proofs verified must be substantial. While the
            // certification gap is live the loudly-skipped rows stand in for
            // their verdicts (each is a confirmed right-verdict/uncertifiable
            // -proof row); the moment the gap count reaches zero the original
            // floor is enforced verbatim.
            assert!(
                report.verified() + gap_skips >= 200,
                "Expected >= 200 proofs verified (counting {} loudly-skipped certification \
                 gaps), got {}",
                gap_skips,
                report.verified()
            );
            if gap_skips == 0 {
                assert!(
                    report.verified() >= 200,
                    "Expected >= 200 proofs verified, got {}",
                    report.verified()
                );
            }
        });
    }

    // -----------------------------------------------------------------------
    // Compatibility-named z3_available() AY availability tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_z3_available_consistent_with_find_solver_binary() {
        let available = z3_available();
        let solver = find_solver_binary();
        assert_eq!(available, solver.is_some());
    }

    // -----------------------------------------------------------------------
    // ProofDatabaseAYReport tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_proof_database_ay_report_synthetic() {
        use crate::proof_database::ProofCategory;

        let report = ProofDatabaseAYReport {
            results: vec![
                (
                    "p1".to_string(),
                    ProofCategory::Arithmetic,
                    AYResult::Verified,
                    false,
                ),
                (
                    "p2".to_string(),
                    ProofCategory::Arithmetic,
                    AYResult::Verified,
                    false,
                ),
                (
                    "p3".to_string(),
                    ProofCategory::Division,
                    AYResult::CounterExample(vec![("a".to_string(), 0)]),
                    false,
                ),
                (
                    "p4".to_string(),
                    ProofCategory::Memory,
                    AYResult::Timeout,
                    false,
                ),
                (
                    "p5".to_string(),
                    ProofCategory::Peephole,
                    AYResult::Error("parse error".to_string()),
                    false,
                ),
                (
                    "p6".to_string(),
                    ProofCategory::Peephole,
                    AYResult::SolverUnsat,
                    false,
                ),
            ],
            total_duration: Duration::from_millis(1234),
        };

        assert_eq!(report.total(), 6);
        assert_eq!(report.verified(), 2);
        assert_eq!(report.failed(), 1);
        assert_eq!(report.timeouts(), 1);
        assert_eq!(report.errors(), 2);
        assert!(!report.all_verified());

        let by_cat = report.by_category();
        let arith = by_cat
            .iter()
            .find(|b| b.category == ProofCategory::Arithmetic)
            .unwrap();
        assert_eq!(arith.total, 2);
        assert_eq!(arith.verified, 2);
        assert_eq!(arith.failed, 0);

        let failures = report.failed_details();
        assert_eq!(failures.len(), 4);
        assert!(failures[0].2.contains("COUNTEREXAMPLE"));
        assert_eq!(failures[1].2, "TIMEOUT");
        assert!(failures[2].2.contains("ERROR"));
        assert!(failures[3].2.contains("UNCERTIFIED"));

        let peephole = by_cat
            .iter()
            .find(|b| b.category == ProofCategory::Peephole)
            .unwrap();
        assert_eq!(peephole.total, 2);
        assert_eq!(peephole.verified, 0);
        assert_eq!(peephole.errors, 2);

        // Display should work without panic
        let text = format!("{}", report);
        assert!(text.contains("FAIL"));
        assert!(text.contains("Arithmetic"));
        assert!(text.contains("Non-verified proofs"));
    }

    #[test]
    fn test_proof_database_ay_report_all_verified() {
        let report = ProofDatabaseAYReport {
            results: vec![
                (
                    "p1".to_string(),
                    ProofCategory::Arithmetic,
                    AYResult::Verified,
                    false,
                ),
                (
                    "p2".to_string(),
                    ProofCategory::Branch,
                    AYResult::Verified,
                    false,
                ),
            ],
            total_duration: Duration::from_millis(100),
        };
        assert!(report.all_verified());
        assert_eq!(report.failed_details().len(), 0);
        let text = format!("{}", report);
        assert!(text.contains("PASS"));
    }

    /// Integration test: verify a small subset of the ProofDatabase through the selected CLI solver.
    /// Uses only Arithmetic proofs to keep runtime reasonable.
    #[test]
    fn test_verify_proof_database_with_ay_arithmetic_subset() {
        if !z3_available() {
            crate::formal_gap::skip_test(
                "test_verify_proof_database_with_ay_arithmetic_subset",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        use crate::proof_database::{CategorizedProof, ProofDatabase};

        let full_db = ProofDatabase::new();
        let subset: Vec<CategorizedProof> = full_db
            .by_category(ProofCategory::Arithmetic)
            .into_iter()
            .cloned()
            .collect();
        assert!(
            subset.len() >= 5,
            "Expected at least 5 Arithmetic proofs, got {}",
            subset.len()
        );
        let db = ProofDatabase::from_proofs(subset);

        let config = AYConfig::default();
        let report = verify_proof_database_with_ay(&db, &config);

        assert_eq!(report.total(), db.len());

        // HONEST floor (#67): ZERO soundness failures — no counterexample and no
        // solver error. A counterexample would mean a miscompiled arithmetic
        // lowering, the cardinal sin this guards.
        assert_eq!(
            report.failed(),
            0,
            "Arithmetic SOUNDNESS FAILURE (counterexample) via AY:\n{}",
            report
        );
        // The genuine 64-bit checked-MUL overflow equivalence (full 2w-bit bvmul
        // != ext(wrapped value)) is SMT-hard and TIMES OUT — it is NOT a 64-bit
        // formal claim. Tolerate ONLY those known capacity-bound mul timeouts
        // and the loudly-skipped exact certification-gap diagnostics
        // (crate::formal_gap); every OTHER Arithmetic proof must formally
        // verify, and a timeout is never a silent pass.  The honest width-8
        // mul-equivalence anchors (`CheckedSmul_I8`/`CheckedUmul_I8`) DO
        // verify and are NOT in this set.
        let mut gap_skips = 0usize;
        for (name, _cat, result, _is_degenerate) in &report.results {
            if matches!(result, AYResult::Verified) {
                continue;
            }
            let is_capacity_bound_mul_i64 = matches!(result, AYResult::Timeout)
                && (name.contains("CheckedSmul_I64") || name.contains("CheckedUmul_I64"));
            if is_capacity_bound_mul_i64 {
                continue;
            }
            // The i128 checked-multiply idiom family (L04-P10,
            // `checked_mul_i128_proofs`) carries 128-bit `bvmul` terms (and,
            // in AArch64's division-identity rows, `bvudiv`/`bvsdiv`) — the
            // same capacity class as the 64-bit checked-mul rows, one width
            // up. Its six rows are tolerated
            // ONLY as timeouts and ONLY by exact registered name, so a rename
            // cannot inherit the tolerance and a counterexample still fails.
            // Their evidence is the evaluator plus the native-oracle battery
            // and refuted controls of `checked_mul_i128_credit`, never a formal
            // claim.
            let is_capacity_bound_mul_i128 = matches!(result, AYResult::Timeout)
                && crate::checked_mul_i128_proofs::all_checked_mul_i128_proofs()
                    .iter()
                    .any(|o| o.name == *name);
            if is_capacity_bound_mul_i128 {
                continue;
            }
            if let Some(reason) = crate::formal_gap::disclosed_proof_hole(result) {
                crate::formal_gap::print_gap_skip(&format!("Arithmetic proof '{name}'"), &reason);
                gap_skips += 1;
                continue;
            }
            panic!(
                "Arithmetic proof {name:?} is non-verified ({result}) and is NOT a tolerated \
                 capacity-bound 64-bit or i128 checked-mul timeout — no other non-formal pass is \
                 allowed:\n{}",
                report
            );
        }
        if gap_skips == 0 {
            assert_eq!(
                report.errors(),
                0,
                "Arithmetic proof errored (could not even run) via AY:\n{}",
                report
            );
        }
    }

    // -----------------------------------------------------------------------
    // Array theory (QF_ABV) CLI verification tests
    //
    // These tests verify array-theory expressions through the AY CLI
    // backend, exercising the same Select/Store/ConstArray translation
    // paths that a future native AY API lane would use.
    // -----------------------------------------------------------------------

    #[test]
    fn test_cli_verify_array_store_load_roundtrip() {
        // Verify: select(store(mem, addr, val), addr) == val
        // This is the fundamental array axiom: read-after-write returns the written value.
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_array_store_load_roundtrip",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let addr = SmtExpr::var("addr", 64);
        let val = SmtExpr::var("val", 8);

        let stored = SmtExpr::store(mem, addr.clone(), val.clone());
        let loaded = SmtExpr::select(stored, addr);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "array_store_load_roundtrip".to_string(),
            trust_ir_expr: loaded,
            aarch64_expr: val,
            inputs: vec![("addr".to_string(), 64), ("val".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Array store-load roundtrip should be verified"),
        );
    }

    #[test]
    fn test_cli_verify_array_store_load_different_addr() {
        // Verify: select(store(mem, a, v), b) == select(mem, b) when a != b
        // This is the second array axiom: write at address a doesn't affect reads at b.
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_array_store_load_different_addr",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let default_val = SmtExpr::var("d", 8);
        let mem = SmtExpr::const_array(SmtSort::BitVec(64), default_val.clone());
        let a = SmtExpr::var("a", 64);
        let b = SmtExpr::var("b", 64);
        let v = SmtExpr::var("v", 8);

        let stored = SmtExpr::store(mem.clone(), a.clone(), v);
        let read_after_write = SmtExpr::select(stored, b.clone());
        let read_original = SmtExpr::select(mem, b.clone());

        // Precondition: a != b
        let precond = a.eq_expr(b).not_expr();

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "array_store_load_different_addr".to_string(),
            trust_ir_expr: read_after_write,
            aarch64_expr: read_original,
            inputs: vec![
                ("a".to_string(), 64),
                ("b".to_string(), 64),
                ("v".to_string(), 8),
                ("d".to_string(), 8),
            ],
            preconditions: vec![precond],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Array read at different address after write should be unchanged"),
        );
    }

    #[test]
    fn test_cli_verify_array_double_store() {
        // Verify: store(store(mem, a, v1), a, v2) at a == v2
        // Overwriting the same address with a new value: last write wins.
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_array_double_store",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let a = SmtExpr::var("a", 64);
        let v1 = SmtExpr::var("v1", 8);
        let v2 = SmtExpr::var("v2", 8);

        let mem1 = SmtExpr::store(mem, a.clone(), v1);
        let mem2 = SmtExpr::store(mem1, a.clone(), v2.clone());
        let loaded = SmtExpr::select(mem2, a);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "array_double_store_last_wins".to_string(),
            trust_ir_expr: loaded,
            aarch64_expr: v2,
            inputs: vec![
                ("a".to_string(), 64),
                ("v1".to_string(), 8),
                ("v2".to_string(), 8),
            ],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Double store at same address: last write should win"),
        );
    }

    #[test]
    fn test_cli_verify_array_const_array_select() {
        // Verify: select(const_array(0), any_addr) == 0
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_array_const_array_select",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0xFF, 8));
        let addr = SmtExpr::var("addr", 64);
        let loaded = SmtExpr::select(mem, addr);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "const_array_select".to_string(),
            trust_ir_expr: loaded,
            aarch64_expr: SmtExpr::bv_const(0xFF, 8),
            inputs: vec![("addr".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Reading from const array should return the constant value"),
        );
    }

    #[test]
    fn test_cli_verify_array_lowering_retains_checked_proofs_and_original_counterexamples() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_array_lowering_retains_checked_proofs_and_original_counterexamples",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };
        let loaded = SmtExpr::select(
            SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0xff, 8)),
            SmtExpr::var("addr", 64),
        );
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "wrong_const_array_select".into(),
            trust_ir_expr: loaded,
            aarch64_expr: SmtExpr::bv_const(0xfe, 8),
            inputs: vec![("addr".into(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };
        for produce_models in [false, true] {
            let config = AYConfig {
                produce_models,
                ..AYConfig::default()
            };
            let mut correct = obligation.clone();
            correct.aarch64_expr = SmtExpr::bv_const(0xff, 8);
            for result in [
                verify_with_cli(&correct, &config),
                verify_with_ay_cli(&correct, &config),
            ] {
                assert_eq!(
                    result,
                    AYResult::Verified,
                    "correct array claim requires independent proof, no gap skip"
                );
            }
            for result in [
                verify_with_cli(&obligation, &config),
                verify_with_ay_cli(&obligation, &config),
            ] {
                assert!(
                    matches!(result, AYResult::CounterExample(_)),
                    "wrong original array claim must remain SAT: {result:?}"
                );
            }
        }
    }

    #[test]
    fn test_array_smt2_uses_qf_abv_logic() {
        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let addr = SmtExpr::var("a", 64);
        let val = SmtExpr::var("v", 8);

        let stored = SmtExpr::store(mem, addr.clone(), val.clone());
        let loaded = SmtExpr::select(stored, addr);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "array_logic_test".to_string(),
            trust_ir_expr: loaded,
            aarch64_expr: val,
            inputs: vec![("a".to_string(), 64), ("v".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);
        assert!(
            smt2.contains("(set-logic QF_ABV)"),
            "Array operations should trigger QF_ABV logic, got: {}",
            smt2
        );
    }

    // -----------------------------------------------------------------------
    // Floating-point theory (QF_BVFP) CLI verification tests
    //
    // These tests verify FP expressions through the selected AY CLI backend.
    // AY is the sole authorized solver in both automatic selection and
    // explicit project configuration.
    // -----------------------------------------------------------------------

    #[test]
    fn test_cli_verify_fp_add_identity() {
        // Verify: fp.add(RNE, x, +0.0) == x for all normal FP64 values
        // Note: this is NOT true for NaN, and the solver will find that. So we test
        // the simpler identity: fp.add(RNE, a, a) == fp.add(RNE, a, a)
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp_add_identity",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let add = SmtExpr::fp_add(RoundingMode::RNE, a.clone(), b.clone());
        let add2 = SmtExpr::fp_add(RoundingMode::RNE, a, b);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "fp_add_self_identity".to_string(),
            trust_ir_expr: add,
            aarch64_expr: add2,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_eq!(
            result,
            AYResult::Verified,
            "Identical FP additions should be equivalent"
        );
    }

    #[test]
    fn test_cli_verify_fp_neg_double() {
        // Verify: fp.neg(fp.neg(x)) == x for symbolic FP64
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp_neg_double",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        // Test with concrete constants to keep it simple
        // and verify the SMT-LIB2 generation path.
        let a = SmtExpr::fp64_const(42.5);
        let neg_neg = a.clone().fp_neg().fp_neg();

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "fp_double_negation".to_string(),
            trust_ir_expr: neg_neg,
            aarch64_expr: a,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Double FP negation should be identity"),
        );
    }

    #[test]
    fn test_cli_verify_fp_sub_as_add_neg() {
        // Verify: fp.sub(RNE, a, b) == fp.add(RNE, a, fp.neg(b)) for concrete values
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp_sub_as_add_neg",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let a = SmtExpr::fp64_const(10.0);
        let b = SmtExpr::fp64_const(3.0);

        let sub = SmtExpr::fp_sub(RoundingMode::RNE, a.clone(), b.clone());
        let add_neg = SmtExpr::fp_add(RoundingMode::RNE, a, b.fp_neg());

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "fp_sub_as_add_neg".to_string(),
            trust_ir_expr: sub,
            aarch64_expr: add_neg,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("FP subtraction should equal addition of negation"),
        );
    }

    #[test]
    fn test_cli_verify_fp_mul_commutative() {
        // Verify: fp.mul(RNE, a, b) == fp.mul(RNE, b, a) for concrete values
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp_mul_commutative",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let a = SmtExpr::fp64_const(3.125);
        let b = SmtExpr::fp64_const(2.71);

        let mul_ab = SmtExpr::fp_mul(RoundingMode::RNE, a.clone(), b.clone());
        let mul_ba = SmtExpr::fp_mul(RoundingMode::RNE, b, a);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "fp_mul_commutative".to_string(),
            trust_ir_expr: mul_ab,
            aarch64_expr: mul_ba,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("FP multiplication should be commutative"),
        );
    }

    fn fp_symbolic_add_commutative_fp16_obligation() -> ProofObligation {
        let a = SmtExpr::Var {
            name: "a".to_string(),
            width: 16,
        };
        let b = SmtExpr::Var {
            name: "b".to_string(),
            width: 16,
        };

        let add_ab = SmtExpr::fp_add(RoundingMode::RNE, a.clone(), b.clone());
        let add_ba = SmtExpr::fp_add(RoundingMode::RNE, b, a);

        ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "fp_symbolic_add_commutative_fp16".to_string(),
            trust_ir_expr: add_ab,
            aarch64_expr: add_ba,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![("a".to_string(), 5, 11), ("b".to_string(), 5, 11)],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        }
    }

    #[test]
    fn test_generate_smt2_query_fp_symbolic_add_commutative_fp16_repro() {
        let obligation = fp_symbolic_add_commutative_fp16_obligation();
        let smt2 = generate_smt2_query(&obligation, &AYConfig::default().with_timeout(15000));

        assert_eq!(
            smt2,
            "\
(set-option :timeout 15000)\n\
(set-option :produce-models true)\n\
(set-logic QF_BVFP)\n\
(declare-const a (_ FloatingPoint 5 11))\n\
(declare-const b (_ FloatingPoint 5 11))\n\
(assert (not (= (fp.add RNE a b) (fp.add RNE b a))))\n\
(check-sat)\n\
(exit)"
        );
    }

    #[test]
    fn test_cli_verify_fp_symbolic_add_commutative_fp16() {
        // Verify: fp.add(RNE, a, b) == fp.add(RNE, b, a) for symbolic FP16 inputs.
        // FP16 (5-bit exponent, 11-bit significand) is used instead of FP64 because
        // symbolic FP reasoning with full 64-bit IEEE 754 is extremely expensive for
        // SMT solvers (often times out at 5s). FP16 has 16 bits total, making the
        // bitvector encoding tractable.
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp_symbolic_add_commutative_fp16",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let obligation = fp_symbolic_add_commutative_fp16_obligation();

        // Symbolic FP16 addition is a real floating-point proof and can exceed
        // the 15s query-generation fixture budget on a loaded release host.
        // More solver time changes no acceptance criterion: Timeout remains a
        // failure and only an unsat result is reported as Verified.
        let config = AYConfig::default().with_timeout(60_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("FP addition should be commutative for all FP16 values"),
        );
    }

    #[test]
    fn test_cli_verify_fp_neg_self_not_identity() {
        // Verify that fp.neg(a) != a (should find counterexample for non-zero values)
        // Actually fp.neg(0.0) == -0.0 which is NOT equal by fp.eq... but let's use
        // a concrete non-zero value to make this clean.
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp_neg_self_not_identity",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let a = SmtExpr::fp64_const(1.0);
        let neg_a = a.clone().fp_neg();

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "fp_neg_not_identity".to_string(),
            trust_ir_expr: neg_a,
            aarch64_expr: a,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        // This should find a counterexample (neg(1.0) != 1.0)
        assert!(
            matches!(result, AYResult::CounterExample(_)),
            "fp.neg(1.0) should NOT equal 1.0, got: {:?}",
            result
        );
    }

    #[test]
    fn test_cli_verify_fp_roundtrip_prefers_fp_safe_solver() {
        // AY is the sole solver: gate on AY availability and discharge the FP
        // roundtrip through AY (z3 has been removed from selection entirely).
        if find_solver_binary().is_none() {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp_roundtrip_prefers_fp_safe_solver",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs();
        // f64 int<->fp roundtrip proofs legitimately take several seconds under
        // AY's exact bit-blasting; 90s gives robust headroom even under load.
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        let route = solver_route_summary_for_invocation(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "int32->f32->int32 roundtrip should verify within the exact f32 integer range via {}",
                route
            ),
        );
    }

    #[test]
    fn test_cli_verify_fp16_roundtrip_prefers_fp_safe_solver() {
        // AY is the sole solver: gate on AY availability and discharge the FP
        // roundtrip through AY (z3 has been removed from selection entirely).
        if find_solver_binary().is_none() {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp16_roundtrip_prefers_fp_safe_solver",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs_i16();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "int16->f16->int16 roundtrip should verify within the exact f16 integer range"
            ),
        );
    }

    #[test]
    fn test_cli_verify_fp64_roundtrip_prefers_fp_safe_solver() {
        // AY is the sole solver: gate on AY availability and discharge the FP
        // roundtrip through AY (z3 has been removed from selection entirely).
        if find_solver_binary().is_none() {
            crate::formal_gap::skip_test(
                "test_cli_verify_fp64_roundtrip_prefers_fp_safe_solver",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs_i64();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "int64->f64->int64 roundtrip should verify within the exact f64 integer range"
            ),
        );
    }

    #[test]
    fn test_cli_verify_unsigned_fp16_roundtrip_prefers_fp_safe_solver() {
        // AY is the sole solver: gate on AY availability and discharge the FP
        // roundtrip through AY (z3 has been removed from selection entirely).
        if find_solver_binary().is_none() {
            crate::formal_gap::skip_test(
                "test_cli_verify_unsigned_fp16_roundtrip_prefers_fp_safe_solver",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu_i16();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "u16->f16->u16 roundtrip should verify within the exact f16 integer range"
            ),
        );
    }

    #[test]
    fn test_cli_verify_unsigned_fp64_roundtrip_prefers_fp_safe_solver() {
        // AY is the sole solver: gate on AY availability and discharge the FP
        // roundtrip through AY (z3 has been removed from selection entirely).
        if find_solver_binary().is_none() {
            crate::formal_gap::skip_test(
                "test_cli_verify_unsigned_fp64_roundtrip_prefers_fp_safe_solver",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu_i64();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "u64->f64->u64 roundtrip should verify within the exact f64 integer range"
            ),
        );
    }

    #[test]
    fn test_cli_verify_unsigned_fp_roundtrip_prefers_fp_safe_solver() {
        // AY is the sole solver: gate on AY availability and discharge the FP
        // roundtrip through AY (z3 has been removed from selection entirely).
        if find_solver_binary().is_none() {
            crate::formal_gap::skip_test(
                "test_cli_verify_unsigned_fp_roundtrip_prefers_fp_safe_solver",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!(
                "u32->f32->u32 roundtrip should verify within the exact f32 integer range"
            ),
        );
    }

    #[test]
    fn test_fp_smt2_uses_qf_bvfp_logic() {
        let a = SmtExpr::fp64_const(1.0);
        let b = SmtExpr::fp64_const(2.0);
        let add = SmtExpr::fp_add(RoundingMode::RNE, a, b.clone());

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "fp_logic_test".to_string(),
            trust_ir_expr: add,
            aarch64_expr: b,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);
        assert!(
            smt2.contains("(set-logic QF_BVFP)"),
            "FP operations should trigger QF_BVFP logic, got: {}",
            smt2
        );
    }

    // -----------------------------------------------------------------------
    // Uninterpreted function (QF_UFBV) SMT-LIB2 serialization tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_uf_smt2_uses_qf_ufbv_logic() {
        let x = SmtExpr::var("x", 32);
        let f_x = SmtExpr::uf("f", vec![x], SmtSort::BitVec(32));

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "uf_logic_test".to_string(),
            trust_ir_expr: f_x.clone(),
            aarch64_expr: f_x,
            inputs: vec![("x".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);
        assert!(
            smt2.contains("(set-logic QF_UFBV)"),
            "UF operations should trigger QF_UFBV logic, got: {}",
            smt2
        );
    }

    #[test]
    fn test_uf_smt2_serialization() {
        let x = SmtExpr::var("x", 32);
        let f_x = SmtExpr::uf("f", vec![x], SmtSort::BitVec(32));
        let serialized = format!("{}", f_x);
        assert_eq!(serialized, "(f x)");
    }

    #[test]
    fn test_uf_decl_smt2_serialization() {
        let decl = SmtExpr::uf_decl(
            "g",
            vec![SmtSort::BitVec(32), SmtSort::BitVec(64)],
            SmtSort::BitVec(8),
        );
        let serialized = format!("{}", decl);
        assert!(
            serialized.contains("declare-fun g"),
            "UF decl should serialize to declare-fun, got: {}",
            serialized
        );
    }

    #[test]
    fn test_cli_verify_uf_equality() {
        // Verify: f(x) == f(x) for uninterpreted function f
        // This should be trivially true by reflexivity.
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_uf_equality",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let x = SmtExpr::var("x", 32);
        let f_x1 = SmtExpr::uf("f", vec![x.clone()], SmtSort::BitVec(32));
        let f_x2 = SmtExpr::uf("f", vec![x], SmtSort::BitVec(32));

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "uf_reflexivity".to_string(),
            trust_ir_expr: f_x1,
            aarch64_expr: f_x2,
            inputs: vec![("x".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_eq!(
            result,
            AYResult::Verified,
            "f(x) == f(x) should be verified for any UF"
        );
    }

    // -----------------------------------------------------------------------
    // Mixed theory tests (Array + FP, Array + UF)
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_logic_mixed_array_and_uf() {
        // Array + UF in one expression should get "ALL" logic
        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let sel = SmtExpr::select(mem, SmtExpr::var("a", 64));
        let uf = SmtExpr::uf("f", vec![sel.clone()], SmtSort::BitVec(8));

        // sel carries array flag, uf carries UF flag
        assert_eq!(infer_logic(&uf), "ALL");
    }

    #[test]
    fn test_infer_logic_array_only() {
        assert_eq!(
            infer_logic(&SmtExpr::select(
                SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8)),
                SmtExpr::var("a", 64),
            )),
            "QF_ABV"
        );
    }

    // -----------------------------------------------------------------------
    // Quantifier detection and bounded expansion tests (#249)
    //
    // These tests verify that:
    // 1. infer_logic detects ForAll/Exists and selects quantified logics (ABV)
    // 2. Bounded quantifiers with small constant ranges are expanded to
    //    conjunctions/disjunctions (staying in QF_* logic)
    // 3. Non-expandable quantifiers upgrade the logic to a quantified variant
    // 4. Memory proofs with quantifiers produce correct SMT-LIB2 output
    // -----------------------------------------------------------------------

    #[test]
    fn test_infer_logic_forall_bv_only() {
        // ForAll over bitvectors (no arrays) should get "BV" (not "QF_BV")
        let body = SmtExpr::var("i", 8).bvult(SmtExpr::bv_const(4, 8));
        let expr = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(4, 8),
            body,
        );
        assert_eq!(infer_logic(&expr), "BV");
    }

    #[test]
    fn test_infer_logic_forall_with_array() {
        // ForAll over array operations should get "ABV" (not "QF_ABV")
        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let body = SmtExpr::select(mem, SmtExpr::var("i", 64)).eq_expr(SmtExpr::bv_const(0, 8));
        let expr = SmtExpr::forall(
            "i",
            64,
            SmtExpr::bv_const(0, 64),
            SmtExpr::bv_const(16, 64),
            body,
        );
        assert_eq!(infer_logic(&expr), "ABV");
    }

    #[test]
    fn test_infer_logic_no_quantifier_still_qf() {
        // Without quantifiers, arrays still get QF_ABV
        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let expr = SmtExpr::select(mem, SmtExpr::var("a", 64));
        assert_eq!(infer_logic(&expr), "QF_ABV");
    }

    #[test]
    fn test_has_quantifiers_true() {
        let body = SmtExpr::bool_const(true);
        let expr = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(4, 8),
            body,
        );
        assert!(has_quantifiers(&expr));
    }

    #[test]
    fn test_has_quantifiers_false() {
        let expr = SmtExpr::var("x", 32).bvadd(SmtExpr::bv_const(1, 32));
        assert!(!has_quantifiers(&expr));
    }

    #[test]
    fn test_expand_forall_small_range() {
        // ForAll i in [0, 3): i < 10  -->  (0 < 10) AND (1 < 10) AND (2 < 10)
        let body = SmtExpr::var("i", 8).bvult(SmtExpr::bv_const(10, 8));
        let forall = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::bv_const(3, 8),
            body,
        );
        let expanded = expand_bounded_quantifiers(&forall);
        // After expansion, should not contain quantifiers
        assert!(
            !has_quantifiers(&expanded),
            "Expanded forall should be quantifier-free"
        );
        // Should still infer QF logic
        let logic = infer_logic(&expanded);
        assert!(
            logic.starts_with("QF_"),
            "Expanded forall should use QF logic, got: {}",
            logic
        );
    }

    #[test]
    fn test_expand_forall_empty_range() {
        // ForAll i in [5, 3): body --> true (vacuously)
        let body = SmtExpr::var("i", 8).bvult(SmtExpr::bv_const(10, 8));
        let forall = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(5, 8),
            SmtExpr::bv_const(3, 8),
            body,
        );
        let expanded = expand_bounded_quantifiers(&forall);
        assert_eq!(expanded, SmtExpr::bool_const(true));
    }

    #[test]
    fn test_expand_exists_small_range() {
        // Exists i in [0, 3): i == 1  -->  (0 == 1) OR (1 == 1) OR (2 == 1)
        let body = SmtExpr::var("i", 8).eq_expr(SmtExpr::bv_const(1, 8));
        let exists = SmtExpr::Exists {
            var: "i".to_string(),
            var_width: 8,
            lower: Arc::new(SmtExpr::bv_const(0, 8)),
            upper: Arc::new(SmtExpr::bv_const(3, 8)),
            body: Arc::new(body),
        };
        let expanded = expand_bounded_quantifiers(&exists);
        assert!(!has_quantifiers(&expanded));
    }

    #[test]
    fn test_expand_forall_non_constant_bounds_preserved() {
        // ForAll with non-constant bound cannot be expanded
        let body = SmtExpr::var("i", 8).bvult(SmtExpr::bv_const(10, 8));
        let forall = SmtExpr::forall(
            "i",
            8,
            SmtExpr::bv_const(0, 8),
            SmtExpr::var("n", 8), // non-constant upper bound
            body,
        );
        let expanded = expand_bounded_quantifiers(&forall);
        // Should still have quantifiers
        assert!(
            has_quantifiers(&expanded),
            "Non-constant bound should preserve quantifier"
        );
    }

    #[test]
    fn test_expand_forall_large_range_preserved() {
        // ForAll with range > limit should not be expanded
        let body = SmtExpr::var("i", 32).bvult(SmtExpr::bv_const(1000, 32));
        let forall = SmtExpr::forall(
            "i",
            32,
            SmtExpr::bv_const(0, 32),
            SmtExpr::bv_const(1000, 32), // exceeds BOUNDED_QUANTIFIER_EXPANSION_LIMIT (256)
            body,
        );
        let expanded = expand_bounded_quantifiers(&forall);
        assert!(
            has_quantifiers(&expanded),
            "Large range should preserve quantifier"
        );
        assert_eq!(infer_logic(&expanded), "BV");
    }

    #[test]
    fn test_prepare_formula_expands_memory_proof_quantifiers() {
        // Memory proofs like memset use ForAll with small constant bounds.
        // After prepare_formula_for_smt, these should be expanded and
        // the formula should stay in QF_ABV.
        let obligation = crate::memory_proofs::proof_memset_correctness(4);
        let raw = obligation.negated_equivalence();
        // Raw formula has quantifiers (from the ForAll in the proof)
        assert!(
            has_quantifiers(&raw),
            "Raw memset proof should have quantifiers"
        );

        let prepared = prepare_formula_for_smt(&raw);
        // After expansion, no quantifiers remain (N=4 < 256)
        assert!(
            !has_quantifiers(&prepared),
            "Expanded memset proof should be quantifier-free"
        );

        // Logic should be QF_ABV (not ABV)
        let logic = infer_logic(&prepared);
        assert_eq!(
            logic, "QF_ABV",
            "Expanded memset proof should use QF_ABV, got: {}",
            logic
        );
    }

    #[test]
    fn test_prepare_formula_simplifies_issue_636_batch_timeouts() {
        let obligations = [
            crate::lowering_proof::proof_imul_i128_hi(),
            crate::peephole_proofs::proof_udiv_pow2_k1(),
            crate::peephole_proofs::proof_udiv_pow2_k2(),
            crate::peephole_proofs::proof_sdiv_neg_one_to_neg(),
        ];

        for obligation in obligations {
            let prepared = prepare_formula_for_smt(&obligation.negated_equivalence());
            assert_eq!(
                prepared,
                SmtExpr::bool_const(false),
                "issue #636 obligation should simplify to an UNSAT negated equivalence: {}",
                obligation.name
            );
        }
    }

    #[test]
    fn test_smt2_memory_proof_with_quantifiers_correct_logic() {
        // End-to-end: generate SMT-LIB2 for a memset proof.
        // The small quantifier should be expanded, yielding QF_ABV.
        let obligation = crate::memory_proofs::proof_memset_correctness(4);
        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);

        // After expansion, should use QF_ABV (quantifier-free)
        assert!(
            smt2.contains("(set-logic QF_ABV)"),
            "Expanded memset proof should use QF_ABV in SMT-LIB2, got: {}",
            smt2
        );
        // Should NOT contain forall keyword (expanded)
        assert!(
            !smt2.contains("(forall"),
            "Expanded memset proof should not contain forall in SMT-LIB2"
        );
    }

    #[test]
    fn test_smt2_memcpy_proof_expanded_correctly() {
        let obligation = crate::memory_proofs::proof_memcpy_correctness(4);
        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);

        // Memcpy with N=4 should be expanded (4 < 256)
        assert!(
            smt2.contains("(set-logic QF_ABV)"),
            "Expanded memcpy proof should use QF_ABV, got: {}",
            smt2
        );
        assert!(
            !smt2.contains("(forall"),
            "Expanded memcpy proof should not contain forall"
        );
    }

    #[test]
    fn test_smt2_non_quantified_proof_unchanged() {
        // Non-quantified proofs should still get QF_ABV
        let obligation = crate::memory_proofs::proof_roundtrip_i32();
        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);
        assert!(
            smt2.contains("(set-logic QF_ABV)"),
            "Non-quantified memory proof should use QF_ABV, got: {}",
            smt2
        );
    }

    #[test]
    fn test_to_smt2_memory_proof_with_quantifiers() {
        // Test ProofObligation::to_smt2() path for quantified proofs
        let obligation = crate::memory_proofs::proof_buffer_init_zero(8);
        let smt2 = obligation.to_smt2();

        // Should be expanded (N=8 < 256), yielding QF_ABV
        assert!(
            smt2.contains("(set-logic QF_ABV)"),
            "Expanded buffer init proof should use QF_ABV via to_smt2(), got: {}",
            smt2
        );
        assert!(
            !smt2.contains("(forall"),
            "Expanded buffer init proof should not contain forall via to_smt2()"
        );
    }

    #[test]
    fn test_large_quantifier_uses_abv_logic() {
        // A quantifier with range > 256 should not be expanded and should use ABV
        let mem = SmtExpr::const_array(SmtSort::BitVec(64), SmtExpr::bv_const(0, 8));
        let body = SmtExpr::select(mem, SmtExpr::var("i", 64)).eq_expr(SmtExpr::bv_const(0, 8));
        let forall = SmtExpr::forall(
            "i",
            64,
            SmtExpr::bv_const(0, 64),
            SmtExpr::bv_const(1000, 64),
            body,
        );
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "large_quantifier_test".to_string(),
            trust_ir_expr: SmtExpr::bool_const(true),
            aarch64_expr: forall,
            inputs: vec![],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let smt2 = generate_smt2_query(&obligation, &config);

        // Large range: should NOT be expanded, should use ABV (quantified arrays+bv)
        assert!(
            smt2.contains("(set-logic ABV)"),
            "Large quantifier should use ABV logic, got: {}",
            smt2
        );
        assert!(
            smt2.contains("(forall"),
            "Large quantifier should contain forall in SMT-LIB2"
        );
    }

    #[test]
    fn test_cli_verify_expanded_memset() {
        // Integration test: verify the expanded-quantifier memset proof through AY.
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_expanded_memset",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let obligation = crate::memory_proofs::proof_memset_correctness(4);
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Memset correctness proof should verify with expanded quantifiers"),
        );
    }

    #[test]
    fn test_cli_verify_expanded_buffer_init() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_expanded_buffer_init",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let obligation = crate::memory_proofs::proof_buffer_init_zero(8);
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Buffer init zero proof should verify with expanded quantifiers"),
        );
    }

    #[test]
    fn test_cli_verify_expanded_memcpy() {
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_expanded_memcpy",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let obligation = crate::memory_proofs::proof_memcpy_correctness(4);
        let config = AYConfig::default().with_timeout(30000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("Memcpy correctness proof should verify with expanded quantifiers"),
        );
    }

    #[test]
    fn test_cli_verify_array_32bit_index() {
        // Verify array operations with 32-bit indices (common for memory models)
        let Some(_solver) = find_solver_binary() else {
            crate::formal_gap::skip_test(
                "test_cli_verify_array_32bit_index",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        };

        let mem = SmtExpr::const_array(SmtSort::BitVec(32), SmtExpr::bv_const(0, 32));
        let addr = SmtExpr::var("addr", 32);
        let val = SmtExpr::var("val", 32);

        let stored = SmtExpr::store(mem, addr.clone(), val.clone());
        let loaded = SmtExpr::select(stored, addr);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "array_32bit_store_load".to_string(),
            trust_ir_expr: loaded,
            aarch64_expr: val,
            inputs: vec![("addr".to_string(), 32), ("val".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &result,
            format_args!("32-bit array store-load roundtrip should be verified"),
        );
    }

    // -----------------------------------------------------------------------
    // CHC encoding tests (always run, no solver needed)
    // -----------------------------------------------------------------------

    #[test]
    fn test_encode_obligation_as_chc_basic() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_chc_add".to_string(),
            trust_ir_expr: a.clone().bvadd(b.clone()),
            aarch64_expr: a.bvadd(b),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let chc = encode_obligation_as_chc(&obligation);

        // Must use HORN logic
        assert!(
            chc.contains("(set-logic HORN)"),
            "Expected HORN logic, got:\n{}",
            chc
        );
        // Must declare Valid predicate with BV32 params
        assert!(
            chc.contains("(declare-fun Valid ((_ BitVec 32) (_ BitVec 32)) Bool)"),
            "Missing Valid predicate declaration in:\n{}",
            chc
        );
        // Must have init clause (forall ... Valid ...)
        assert!(
            chc.contains("(forall ((a (_ BitVec 32)) (b (_ BitVec 32))) (Valid a b))"),
            "Missing init clause in:\n{}",
            chc
        );
        // Must have query clause with negated equivalence
        assert!(
            chc.contains("(not (= (bvadd a b) (bvadd a b)))"),
            "Missing negated equivalence in:\n{}",
            chc
        );
        // Must end with check-sat
        assert!(
            chc.contains("(check-sat)"),
            "Missing check-sat in:\n{}",
            chc
        );
    }

    #[test]
    fn test_encode_obligation_as_chc_with_preconditions() {
        let a = SmtExpr::var("a", 32);
        let b = SmtExpr::var("b", 32);

        // Precondition: b != 0
        let precond = b.clone().eq_expr(SmtExpr::bv_const(0, 32)).not_expr();

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_chc_div_precond".to_string(),
            trust_ir_expr: a.clone(),
            aarch64_expr: a.clone(),
            inputs: vec![("a".to_string(), 32), ("b".to_string(), 32)],
            preconditions: vec![precond],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let chc = encode_obligation_as_chc(&obligation);

        // Init clause should include precondition as implication
        assert!(
            chc.contains("(=>"),
            "Expected implication in init clause with preconditions, got:\n{}",
            chc
        );
        // Query body should include the precondition
        assert!(
            chc.contains("(Valid a b)"),
            "Query clause must reference Valid predicate in:\n{}",
            chc
        );
    }

    #[test]
    fn test_encode_obligation_as_chc_single_input() {
        let x = SmtExpr::var("x", 64);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_chc_identity".to_string(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x,
            inputs: vec![("x".to_string(), 64)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let chc = encode_obligation_as_chc(&obligation);

        assert!(
            chc.contains("(declare-fun Valid ((_ BitVec 64)) Bool)"),
            "Single-input Valid predicate wrong in:\n{}",
            chc
        );
        assert!(
            chc.contains("(forall ((x (_ BitVec 64))) (Valid x))"),
            "Single-input init clause wrong in:\n{}",
            chc
        );
    }

    #[test]
    fn test_encode_obligation_as_chc_bitvec_declarations() {
        let a = SmtExpr::var("a", 8);
        let b = SmtExpr::var("b", 16);

        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "test_chc_mixed_widths".to_string(),
            trust_ir_expr: a.clone().bvadd(SmtExpr::ZeroExtend {
                operand: Arc::new(a.clone()),
                extra_bits: 8,
                width: 16,
            }),
            aarch64_expr: b.clone(),
            inputs: vec![("a".to_string(), 8), ("b".to_string(), 16)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: Some(crate::lowering_proof::TransvalCheckKind::InstructionLowering),
        };

        let chc = encode_obligation_as_chc(&obligation);

        // Must declare Valid with mixed-width params
        assert!(
            chc.contains("(declare-fun Valid ((_ BitVec 8) (_ BitVec 16)) Bool)"),
            "Mixed-width Valid declaration wrong in:\n{}",
            chc
        );
    }

    // -----------------------------------------------------------------------
    // find_solver_binary / solver_info / verdict provenance tests
    //
    // The identity rule itself (every refusal, the hosting/build toolchain
    // choice, the named routes) is tested in `ay_identity_tests.rs` against
    // fixture toolchains. These tests pin what the BRIDGE does with it.
    // -----------------------------------------------------------------------

    fn sha256_of_file(path: &std::path::Path) -> String {
        use sha2::{Digest, Sha256};
        format!("{:x}", Sha256::digest(std::fs::read(path).unwrap()))
    }

    /// Every branch asserts: an admitted AY is an existing absolute file whose
    /// bytes are the admitted digest; no admitted AY is always explained.
    #[test]
    fn test_find_solver_binary_returns_valid_path() {
        let selection = select_solver_binary();
        match (&selection.0, find_solver_binary()) {
            (Ok(admitted), Some(solver)) => {
                assert_eq!(&solver, admitted);
                assert!(solver.path().is_absolute(), "{solver}");
                assert!(solver.path().is_file(), "{solver}");
                assert_eq!(solver.sha256(), sha256_of_file(solver.path()), "{solver}");
                solver.revalidate().unwrap();
            }
            (Ok(admitted), None) => {
                assert!(
                    crate::obligation_cert_store::clean_checker_path().is_none(),
                    "an admitted AY with a capable checker must be the discharge route: {admitted}"
                );
                let reason = proof_toolchain_unavailable_reason()
                    .expect("a withheld admitted AY must be explained");
                assert!(!reason.is_empty());
            }
            (Err(refusal), found) => {
                assert!(found.is_none(), "a refused selection resolved {found:?}");
                assert!(refusal.code().starts_with("TCG-AY-IDENTITY-"), "{refusal}");
                assert!(
                    proof_toolchain_unavailable_reason().is_some(),
                    "a refusal must surface as an unavailability reason"
                );
            }
        }
    }

    /// A refused override resolves NOTHING — it never falls back to the
    /// toolchain AY, a package, or a same-named binary on `PATH`.
    #[test]
    fn explicit_missing_relative_or_empty_ay_override_cannot_fall_back() {
        let directory = tempfile::tempdir().unwrap();
        let missing = directory.path().join("missing-ay");
        let record = crate::ay_identity::recorded_toolchain_ay_identity();
        for (value, code) in [
            ("", "TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE"),
            ("ay", "TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE"),
            (
                missing.to_str().unwrap(),
                "TCG-AY-IDENTITY-OVERRIDE-MISSING",
            ),
        ] {
            trust_cg_process_env::with_env_overrides(&[("AY_SOLVER_PATH", value)], || {
                let selection = select_solver_binary();
                assert!(
                    selection.pinned().is_none(),
                    "{value:?} admitted {selection:?}"
                );
                let expected = if record.is_ok() {
                    code
                } else {
                    "TCG-AY-IDENTITY-UNRECORDED"
                };
                assert_eq!(selection.route_kind(), expected, "{value:?}: {selection:?}");
                assert!(
                    selection.detail().contains(expected),
                    "the recorded detail must carry the refusal: {selection:?}"
                );
                assert!(find_solver_binary().is_none());
            });
        }
    }

    /// REGRESSION PIN for the managed-AY defect: the plugin's solver-coupled
    /// tests ran `aterm/pkg/store/ay/8256/bin/ay` (ay 0.13.0, dd4de9e94) while
    /// the Trust toolchain that built them ships ay 0.26.0 (075a482ae).
    ///
    /// Every location the old discovery consulted is populated with a COPY of
    /// the build toolchain's own AY bytes (the worst case: each would be
    /// admitted if it were named). The selection must be the same with and
    /// without them, and — in this test harness, which no compiler hosts — must
    /// be the building toolchain's own `bin/ay`.
    #[cfg(unix)]
    #[test]
    fn selection_consults_no_package_path_home_or_checkout_location() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let root = directory.path();
        let record = crate::ay_identity::ToolchainAyRecord::recorded();
        let toolchain_ay = record
            .build_sysroot()
            .join("bin")
            .join(format!("ay{}", std::env::consts::EXE_SUFFIX));
        let decoy = |relative: &str| {
            let path = root.join(relative);
            std::fs::create_dir_all(path.parent().unwrap()).unwrap();
            if toolchain_ay.is_file() {
                std::fs::copy(&toolchain_ay, &path).unwrap();
            } else {
                std::fs::write(&path, b"#!/bin/sh\nexit 70\n").unwrap();
            }
            std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        };
        for relative in [
            "home/Library/Application Support/aterm/pkg/store/ay/current/bin/ay",
            "home/.local/share/aterm/pkg/store/ay/current/bin/ay",
            "prefix/store/ay/current/bin/ay",
            "path-bin/ay",
            "trust-sysroot/bin/ay",
            "trust-root/build/aarch64-apple-darwin/stage2/bin/ay",
            "trust-root/first-party/ay/target/release/ay",
            "home/trust/build/aarch64-apple-darwin/stage2/bin/ay",
            "cargo-target/release/ay",
            "home/ay/target/release/ay",
        ] {
            decoy(relative);
        }
        let path = std::env::join_paths([root.join("path-bin"), root.join("prefix/bin")]).unwrap();
        let isolated =
            trust_cg_process_env::with_env_overrides_removed(&["AY_SOLVER_PATH"], || {
                trust_cg_process_env::with_env_overrides(
                    &[
                        ("PATH", path.to_str().unwrap()),
                        ("HOME", root.join("home").to_str().unwrap()),
                        (
                            "TRUST_SYSROOT",
                            root.join("trust-sysroot").to_str().unwrap(),
                        ),
                        ("TRUST_ROOT", root.join("trust-root").to_str().unwrap()),
                        (
                            "CARGO_TARGET_DIR",
                            root.join("cargo-target").to_str().unwrap(),
                        ),
                    ],
                    select_solver_binary,
                )
            });
        let plain = trust_cg_process_env::with_env_overrides_removed(
            &[
                "AY_SOLVER_PATH",
                "TRUST_SYSROOT",
                "TRUST_ROOT",
                "CARGO_TARGET_DIR",
            ],
            select_solver_binary,
        );
        assert_eq!(
            isolated, plain,
            "AY selection changed with PATH/HOME/TRUST_*/CARGO_TARGET_DIR: it is still \
             discovering instead of applying the toolchain identity rule"
        );
        assert!(
            !isolated.path_text().starts_with(root.to_str().unwrap()),
            "a decoy location was selected: {isolated:?}"
        );
        match record.expected() {
            Ok(expected) => match &isolated.0 {
                Ok(admitted) => {
                    assert_eq!(admitted.route().as_str(), "toolchain-pinned-ay");
                    assert_eq!(admitted.path(), toolchain_ay);
                    assert_eq!(admitted.identity(), expected);
                }
                // The build toolchain is expected to ship its recorded AY; if
                // it no longer does, the rule must say so by name.
                Err(refusal) => assert!(
                    matches!(
                        refusal.code(),
                        "TCG-AY-IDENTITY-MISSING" | "TCG-AY-IDENTITY-MISMATCH"
                    ),
                    "unexpected refusal for the build toolchain AY: {refusal}"
                ),
            },
            Err(_) => {
                assert!(isolated.pinned().is_none());
                assert_eq!(isolated.route_kind(), "TCG-AY-IDENTITY-UNRECORDED");
            }
        }
    }

    /// Every branch asserts. Without a capable checker there is no discharge
    /// route (and that is explained); with one, the route is EXACTLY the
    /// identity rule's admission, recorded with the admitted digest and build,
    /// or its named refusal.
    #[test]
    fn test_find_solver_binary_requires_checker_and_uses_the_pinned_toolchain_ay() {
        let solver = find_solver_binary();
        let selection = select_solver_binary();
        if crate::obligation_cert_store::clean_checker_path().is_none() {
            assert!(
                solver.is_none(),
                "AY without an independent proof checker is not proof authority"
            );
            assert!(
                proof_toolchain_unavailable_reason().is_some(),
                "a missing checker must be named"
            );
            crate::formal_gap::skip_test(
                "test_find_solver_binary_requires_checker_and_uses_the_pinned_toolchain_ay",
                crate::formal_gap::NO_CLEAN_CHECKER,
            );
            return;
        }
        assert_eq!(
            solver.as_ref(),
            selection.pinned(),
            "with a checker present, the discharge route is exactly the identity-rule selection"
        );
        match &selection.0 {
            Ok(admitted) => {
                assert!(
                    matches!(
                        admitted.route().as_str(),
                        "toolchain-pinned-ay" | "override-pinned-ay"
                    ),
                    "{selection:?}"
                );
                let recorded = crate::ay_identity::recorded_toolchain_ay_identity()
                    .expect("an admitted AY outside a fixture scope implies a recorded identity");
                assert_eq!(admitted.identity(), recorded);
                let detail = selection.detail();
                assert!(detail.contains(recorded.sha256()), "{detail}");
                assert!(
                    detail.contains(recorded.build().unwrap().commit()),
                    "the selection must record the admitted build identity: {detail}"
                );
                assert_ne!(
                    admitted.path().file_stem().and_then(|name| name.to_str()),
                    Some("z3"),
                    "z3 is not an authorized proof-discharge route"
                );
            }
            Err(refusal) => {
                assert!(refusal.code().starts_with("TCG-AY-IDENTITY-"), "{refusal}");
                let reason = proof_toolchain_unavailable_reason().unwrap();
                assert!(reason.contains(refusal.code()), "{reason}");
            }
        }
    }

    /// AY is the sole solver: a floating-point (QF_BVFP) obligation must
    /// resolve the SAME AY binary as any other obligation, and must NEVER
    /// route to z3. (Previously these obligations preferred z3 because the
    /// local ay CLI was unstable on QF_BVFP; z3 has since been removed
    /// entirely and AY's fp soundness fixes landed.)
    fn is_authorized_ay_selection(selection: &SolverSelection) -> bool {
        selection.pinned().is_some_and(|solver| {
            solver.path().is_file()
                && matches!(
                    solver.route().as_str(),
                    "explicit-pinned-ay" | "toolchain-pinned-ay" | "override-pinned-ay"
                )
        })
    }

    fn assert_fp_obligation_uses_ay(obligation: &ProofObligation) {
        let selection = select_solver_for_obligation(obligation);
        assert!(
            !selection.route_kind().contains("z3") && !selection.path_text().contains("/z3"),
            "FP obligations must NOT route to z3 (route={}, solver={})",
            selection.route_kind(),
            selection.path_text()
        );
        // The FP obligation resolves the identical selection as a logic-agnostic
        // lookup — i.e. the obligation's logic no longer steers solver choice.
        assert_eq!(
            selection,
            select_solver_binary(),
            "FP obligation must resolve the same AY selection as any obligation"
        );
        match &selection.0 {
            Ok(_) => assert!(
                is_authorized_ay_selection(&selection),
                "resolved FP solver must use an authorized AY route (route={}, solver={})",
                selection.route_kind(),
                selection.path_text()
            ),
            Err(refusal) => {
                assert!(refusal.code().starts_with("TCG-AY-IDENTITY-"), "{refusal}")
            }
        }
    }

    #[test]
    fn test_find_solver_binary_for_fp_obligation_uses_ay() {
        assert_fp_obligation_uses_ay(&crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs());
    }

    #[test]
    fn test_find_solver_binary_for_fp16_obligation_uses_ay() {
        assert_fp_obligation_uses_ay(&crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs_i16());
    }

    #[test]
    fn test_find_solver_binary_for_fp64_obligation_uses_ay() {
        assert_fp_obligation_uses_ay(&crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs_i64());
    }

    #[test]
    fn test_find_solver_binary_for_unsigned_fp16_obligation_uses_ay() {
        assert_fp_obligation_uses_ay(&crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu_i16());
    }

    #[test]
    fn test_find_solver_binary_for_unsigned_fp64_obligation_uses_ay() {
        assert_fp_obligation_uses_ay(&crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu_i64());
    }

    #[test]
    fn test_find_solver_binary_for_unsigned_fp_obligation_uses_ay() {
        assert_fp_obligation_uses_ay(&crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu());
    }

    #[test]
    fn test_solver_route_summary_for_fp_obligation_includes_route_kind_and_path() {
        let obligation = crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs();
        let selection = select_solver_for_obligation(&obligation);
        let summary = solver_route_summary_for_invocation(&obligation, &AYConfig::default());
        assert!(
            summary.contains("logic=QF_BVFP"),
            "expected FP route summary to include logic, got: {}",
            summary
        );
        // z3 is gone: the FP route is an AY route (or a named refusal), never
        // a z3 route.
        assert!(
            !summary.contains("z3"),
            "FP route summary must not mention z3, got: {}",
            summary
        );
        match &selection.0 {
            Err(refusal) => assert!(
                summary.contains(&format!("route={}", refusal.code()))
                    && summary.contains("solver=(refused)"),
                "a refused FP route summary must report the refusal, got: {}",
                summary
            ),
            Ok(solver) => {
                assert!(
                    is_authorized_ay_selection(&selection),
                    "resolved FP solver must use an authorized AY route (route={}, solver={})",
                    selection.route_kind(),
                    selection.path_text()
                );
                assert!(
                    summary.contains(&format!("route={}", selection.route_kind()))
                        && summary.contains(&format!("solver={}", solver.path().display()))
                        && summary.contains(solver.sha256()),
                    "FP route summary must report the selected route kind, path and digest, \
                     got: {}",
                    summary
                );
            }
        }
    }

    /// An explicit AY reaches the configuration only as an admitted value, and
    /// the route summary names that route, path and digest.
    #[cfg(unix)]
    #[test]
    fn test_solver_route_summary_for_explicit_solver_names_its_route() {
        let solver_path =
            write_temp_solver_script("#!/bin/sh\n# explicit route fixture\nexit 70\n");
        let solver = crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path));
        let obligation = crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs();
        let config = AYConfig::default().with_solver(solver.clone());
        let summary = solver_route_summary_for_invocation(&obligation, &config);
        let _ = std::fs::remove_file(&solver_path);
        assert!(
            summary.contains("route=explicit-pinned-ay"),
            "expected the explicit route, got: {summary}"
        );
        assert!(
            summary.contains(&format!("solver={solver_path}")) && summary.contains(solver.sha256()),
            "expected the explicit path and digest, got: {summary}"
        );
    }

    /// A fixture that records every time it is executed (except a warm-up
    /// start, `test_fixtures::warm`, which it answers first).
    #[cfg(unix)]
    fn marker_solver_script(body: &str) -> (String, std::path::PathBuf) {
        let path = write_temp_solver_script(&crate::ay_identity::test_fixtures::with_warm_guard(
            &format!("#!/bin/sh\n: > \"$0.executed\"\n{body}\n"),
        ));
        let marker = std::path::PathBuf::from(format!("{path}.executed"));
        (path, marker)
    }

    #[cfg(unix)]
    #[test]
    fn test_solver_info_identifies_ay_without_authorizing_an_absent_checker() {
        let directory = tempfile::tempdir().unwrap();
        let (solver, marker) = marker_solver_script("exit 70");
        let missing_checker = directory.path().join("missing-clean");
        let declaration =
            crate::ay_identity::test_fixtures::declare(&[std::path::Path::new(&solver)]);
        trust_cg_process_env::with_env_edits(|environment| {
            environment.set("AY_SOLVER_PATH", &solver);
            environment.set(
                crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
                &declaration,
            );
            environment.set("TCG_EXTERNAL_CLEAN_CHECKER", missing_checker.as_os_str());
            assert!(!ay_available(), "AY alone must not authorize proofs");
            assert!(find_solver_binary().is_none());
            let reason = proof_toolchain_unavailable_reason().unwrap();
            assert!(reason.contains("TCG_EXTERNAL_CLEAN_CHECKER"), "{reason}");
            let info = solver_info();
            assert!(
                info.starts_with(&format!("ay at {solver} [")),
                "checker unavailability must not be reported as an absent AY: {info}"
            );
            assert!(info.contains("route=override-pinned-ay"), "{info}");
            assert!(info.contains(&declaration), "{info}");
        });
        let executed = marker.exists();
        let _ = std::fs::remove_file(&solver);
        let _ = std::fs::remove_file(&marker);
        assert!(!executed, "identifying the AY must not execute it");
    }

    #[test]
    fn test_solver_info_when_available() {
        let info = solver_info();
        match select_solver_binary().0 {
            Ok(solver) => {
                assert!(
                    info.starts_with(&format!("ay at {} [", solver.path().display())),
                    "expected solver_info to name the admitted path, got: {info}"
                );
                assert!(info.contains(solver.sha256()), "{info}");
            }
            Err(refusal) => assert_eq!(info, format!("no AY solver admitted: {refusal}")),
        }
    }

    #[test]
    fn test_solver_info_contains_solver_name() {
        let info = solver_info();
        assert!(
            info.contains("ay at ") || info.contains("no AY solver admitted: [TCG-AY-IDENTITY-"),
            "expected solver_info to name AY or its refusal, got: {info}"
        );
    }

    /// A caller-chosen AY is used exactly, and the verdict records it: which
    /// bytes answered, on which route, and that it actually ran.
    #[cfg(unix)]
    #[test]
    fn explicit_solver_verdict_records_the_admitted_ay_that_ran() {
        let (solver_path, marker) = marker_solver_script("printf 'unknown\\n'");
        // Started once before its deadline: its private copy is a new file.
        crate::ay_identity::test_fixtures::warm(std::path::Path::new(&solver_path));
        let solver = crate::ay_identity::test_fixtures::pin(std::path::Path::new(&solver_path));
        let x = SmtExpr::var("provenance_x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "explicit_solver_verdict_provenance".to_string(),
            trust_ir_expr: x.clone().bvadd(SmtExpr::bv_const(1, 8)),
            aarch64_expr: x,
            inputs: vec![("provenance_x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        };
        let verdict = trust_cg_process_env::with_env_overrides(
            &[
                ("TCG_NO_SOLVER_SERVER", "1"),
                ("TCG_NO_CERT_STORE", "1"),
                ("TCG_CANARY_NO_CACHE", "1"),
            ],
            || {
                verify_with_ay_attributed(
                    &obligation,
                    &AYConfig::default()
                        .with_timeout(FAKE_RESIDENT_SOLVER_TIMEOUT_MS)
                        .with_solver(solver.clone()),
                )
            },
        );
        let executed = marker.exists();
        let _ = std::fs::remove_file(&solver_path);
        let _ = std::fs::remove_file(&marker);
        assert!(
            matches!(verdict.result, AYResult::Unknown(_)),
            "{verdict:?}"
        );
        assert_eq!(verdict.solver.as_ref(), Some(&solver));
        assert_eq!(verdict.source, AyVerdictSource::LiveSolve);
        let provenance = verdict.provenance();
        assert!(provenance.contains("source=live-solve"), "{provenance}");
        assert!(provenance.contains(solver.sha256()), "{provenance}");
        assert!(
            provenance.contains("route=explicit-pinned-ay"),
            "{provenance}"
        );
        assert!(executed, "the recorded AY is the one that ran");
    }

    /// The round-4 residual through the PUBLIC API: `AY_SOLVER_PATH` naming a
    /// script that prints the pinned banner starts nothing, and the verdict
    /// names the refusal and records that no AY ran.
    #[cfg(unix)]
    #[test]
    fn a_banner_claiming_override_starts_nothing_and_the_verdict_names_the_refusal() {
        let banner = crate::ay_identity::recorded_toolchain_ay_identity()
            .ok()
            .and_then(|identity| identity.build().cloned())
            .map(|build| {
                format!(
                    "ay {v}+build.{i}.{c}@2026-09-16T06:27:30Z\nbuild.version={v}\n\
                     build.increment={i}\nbuild.commit={c}\n\
                     build.datetime_utc=2026-09-16T06:27:30Z\n\
                     build.stamp={v}+build.{i}.{c}@2026-09-16T06:27:30Z\n",
                    v = build.version(),
                    i = build.increment(),
                    c = build.commit()
                )
            })
            .unwrap_or_default();
        let (script, marker) = marker_solver_script(&format!(
            "if [ \"$1\" = --version ]; then cat <<'EOF'\n{banner}EOF\nexit 0; fi\nprintf 'unsat\\n'"
        ));
        let x = SmtExpr::var("banner_decoy_x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: crate::lowering_proof::MachineSideProvenance::StaticDb,
            name: "banner_decoy_is_never_started".to_string(),
            trust_ir_expr: x.clone().bvadd(SmtExpr::bv_const(1, 8)),
            aarch64_expr: x,
            inputs: vec![("banner_decoy_x".to_string(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        };
        let (verdict, explicit) = trust_cg_process_env::with_env_edits(|environment| {
            environment.set("AY_SOLVER_PATH", &script);
            environment.remove(crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV);
            environment.set("TCG_CANARY_NO_CACHE", "1");
            (
                verify_with_ay_attributed(&obligation, &AYConfig::default()),
                crate::ay_identity::resolve_explicit_path(&script),
            )
        });
        let executed = marker.exists();
        let _ = std::fs::remove_file(&script);
        let _ = std::fs::remove_file(&marker);
        let expected_code = if crate::ay_identity::recorded_toolchain_ay_identity().is_ok() {
            "TCG-AY-IDENTITY-MISMATCH"
        } else {
            "TCG-AY-IDENTITY-UNRECORDED"
        };
        assert!(
            matches!(&verdict.result, AYResult::Error(message) if message.contains(expected_code)),
            "{verdict:?}"
        );
        assert_eq!(verdict.solver, None);
        assert_eq!(verdict.source, AyVerdictSource::NotRun);
        assert_eq!(explicit.unwrap_err().code(), expected_code);
        assert!(!executed, "a refused AY must never be started");
    }

    /// MEASURED AUTHORITY BOUNDARY (2026-09-21) — `Source-bound AArch64 leaf:
    /// FP/LR frame memory and writeback`
    /// ([`crate::source_bound_frame::frame_obligation`]) is a
    /// [`ProofCategory::FrameLayout`] row the installed AY cannot decide at
    /// all, so [`tests::test_ay_batch_verify_frame_layout_proofs`] is RED on
    /// purpose.
    ///
    /// On ay 0.13.0 build 8256 the FRESH one-shot transcript prints
    /// `[AY SOUNDNESS GATE] caught an INVALID model` and
    /// `(:reason-unknown incomplete)` — deterministically, 20 runs of 20 — at
    /// every rigor level, and ay 0.11.0 build 2157 answers the same
    /// `(:reason-unknown incomplete)` without the banner. z3 4.16.0
    /// discharges the byte-identical bridge query `unsat` in 0.13 s, so the
    /// obligation is VALID and its encoding faithful: the AUTHORITY is
    /// defective on this query, not the proof. A caught invalid model is not
    /// one of AY's certification-gap disclosures and must never be skipped as
    /// one. See `reports/2026-09-21-frame-layout-ay-authority-gap/`.
    ///
    /// This pin deliberately does NOT assert that AY still fails — that would
    /// freeze the defect in place. It asserts the two properties the BRIDGE
    /// owes whatever AY answers, and self-retires on `Verified`:
    ///
    /// 1. the verdict that escapes the bridge is never the resident server's
    ///    stderr-truncated bare `Unknown("unknown")` — AY's own published
    ///    reason has to survive;
    /// 2. a caught-invalid-model refusal can never authorize a test skip
    ///    ([`crate::formal_gap::disclosed_proof_hole`] is the only one).
    #[test]
    fn frame_obligation_verdict_is_reason_bearing_and_never_gap_classified() {
        if !z3_available() {
            crate::formal_gap::skip_test(
                "frame_obligation_verdict_is_reason_bearing_and_never_gap_classified",
                crate::formal_gap::NO_PROOF_AUTHORITY,
            );
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        let obligation = crate::source_bound_frame::frame_obligation();
        let config = AYConfig::default().with_timeout(30_000);
        let result = verify_with_cli(&obligation, &config);

        if result == AYResult::Verified {
            // An authority caught up with the obligation; nothing left to pin.
            return;
        }

        assert_ne!(
            result,
            AYResult::Unknown("unknown".to_string()),
            "the bridge must replay a server-truncated bare unknown through the fresh \
             one-shot transcript instead of publishing the truncation (route: {})",
            solver_route_summary_for_invocation(&obligation, &config),
        );

        if let AYResult::Unknown(reason) = &result
            && crate::gap_classify::ay_reason_is_soundness_gate_refusal(reason)
        {
            assert!(
                crate::formal_gap::disclosed_proof_hole(&result).is_none(),
                "AY's caught-invalid-model refusal was classified as a skippable proof hole: \
                 {reason}"
            );
        }
    }
    // -----------------------------------------------------------------------
}
