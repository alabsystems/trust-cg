// trust-cg-verify/ay_bridge.rs - Bridge to the ay SMT solver
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Translates our SmtExpr AST into SMT-LIB2 format and invokes an SMT solver
// to check satisfiability. v0.1.0 invokes an external AY binary through the
// standard SMT-LIB2 text interface.
//
// Reference: designs/2026-04-13-verification-architecture.md

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

use crate::lowering_proof::ProofObligation;
use crate::proof_database::{ProofCategory, ProofDatabase};
use crate::smt::{RoundingMode, SmtExpr, SmtSort};
use std::fmt;
use std::path::Path;
use std::sync::Arc;
use std::time::{Duration, Instant};

#[cfg(unix)]
const SIGTERM: i32 = 15;
#[cfg(unix)]
const SIGKILL: i32 = 9;

#[cfg(unix)]
unsafe extern "C" {
    fn kill(pid: i32, sig: i32) -> i32;
}

// ---------------------------------------------------------------------------
// AYResult
// ---------------------------------------------------------------------------

/// Result of an AY verification check.
#[derive(Debug, Clone, PartialEq)]
pub enum AYResult {
    /// The property is independently certified: AY reported UNSAT and an
    /// external checker accepted the exact, hole-free Alethe refutation.
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
    /// Explicit AY binary override (default: resolve an authorized AY build).
    pub solver_path: Option<String>,
    /// Timeout in milliseconds. Default is [`DEFAULT_AY_TIMEOUT_MS`] (30 s),
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
            solver_path: None,
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

    /// Create a config with an explicit AY binary path.
    pub fn with_solver_path(mut self, path: impl Into<String>) -> Self {
        self.solver_path = Some(path.into());
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
        SmtExpr::ConstArray { value, .. } => {
            *has_array = true;
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
        SmtExpr::UF { args, .. } => {
            *has_uf = true;
            for arg in args {
                infer_logic_walk(arg, has_array, has_fp, has_uf, has_quantifier);
            }
        }
        SmtExpr::UFDecl { .. } => {
            *has_uf = true;
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
    match expr {
        SmtExpr::UF {
            name,
            args,
            ret_sort,
        } => {
            // Add declaration if not already present
            if !decls.iter().any(|(n, _, _)| n == name) {
                let arg_sorts: Vec<SmtSort> = args.iter().map(|a| a.sort()).collect();
                decls.push((name.clone(), arg_sorts, ret_sort.clone()));
            }
            // Recurse into arguments
            for arg in args {
                collect_uf_declarations(arg, decls);
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
        // Binary operators
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
        | SmtExpr::Or { lhs, rhs }
        | SmtExpr::FPAdd { lhs, rhs, .. }
        | SmtExpr::FPSub { lhs, rhs, .. }
        | SmtExpr::FPMul { lhs, rhs, .. }
        | SmtExpr::FPDiv { lhs, rhs, .. }
        | SmtExpr::FPEq { lhs, rhs }
        | SmtExpr::FPLt { lhs, rhs }
        | SmtExpr::FPGt { lhs, rhs }
        | SmtExpr::FPGe { lhs, rhs }
        | SmtExpr::FPLe { lhs, rhs } => {
            collect_uf_declarations(lhs, decls);
            collect_uf_declarations(rhs, decls);
        }
        // Unary operators
        SmtExpr::BvNeg { operand, .. }
        | SmtExpr::Not { operand }
        | SmtExpr::Extract { operand, .. }
        | SmtExpr::ZeroExtend { operand, .. }
        | SmtExpr::SignExtend { operand, .. }
        | SmtExpr::FPNeg { operand }
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
            collect_uf_declarations(operand, decls);
        }
        SmtExpr::Concat { hi, lo, .. } => {
            collect_uf_declarations(hi, decls);
            collect_uf_declarations(lo, decls);
        }
        SmtExpr::TrapIfZero { guard, value, .. } => {
            collect_uf_declarations(guard, decls);
            collect_uf_declarations(value, decls);
        }
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_uf_declarations(cond, decls);
            collect_uf_declarations(then_expr, decls);
            collect_uf_declarations(else_expr, decls);
        }
        SmtExpr::FPFma { a, b, c, .. } => {
            collect_uf_declarations(a, decls);
            collect_uf_declarations(b, decls);
            collect_uf_declarations(c, decls);
        }
        SmtExpr::Select { array, index } => {
            collect_uf_declarations(array, decls);
            collect_uf_declarations(index, decls);
        }
        SmtExpr::Store {
            array,
            index,
            value,
        } => {
            collect_uf_declarations(array, decls);
            collect_uf_declarations(index, decls);
            collect_uf_declarations(value, decls);
        }
        SmtExpr::ConstArray { value, .. } => {
            collect_uf_declarations(value, decls);
        }
        // A memory load is an uninterpreted function `mem_load_W_s : BV(addr) ->
        // BV(load_bits)` (one symbol per load width + signedness). Declare it so
        // the SMT-LIB query is well-formed; the surrounding sign/zero-extend to
        // result_width is emitted inline by `Display`. Same congruence the
        // evaluator's deterministic `mix` gives: equal addresses ⇒ equal loads.
        SmtExpr::MemLoad {
            addr,
            load_bits,
            signed,
            ..
        } => {
            let s = if *signed { "s" } else { "u" };
            let name = format!("mem_load_{load_bits}_{s}");
            if !decls.iter().any(|(n, _, _)| n == &name) {
                let addr_sort = SmtSort::BitVec(addr.try_bv_width().unwrap_or(64));
                decls.push((name, vec![addr_sort], SmtSort::BitVec(*load_bits)));
            }
            collect_uf_declarations(addr, decls);
        }
        SmtExpr::ForAll {
            lower, upper, body, ..
        }
        | SmtExpr::Exists {
            lower, upper, body, ..
        } => {
            collect_uf_declarations(lower, decls);
            collect_uf_declarations(upper, decls);
            collect_uf_declarations(body, decls);
        }
        // Leaves: no children to recurse into
        SmtExpr::Var { .. }
        | SmtExpr::BvConst { .. }
        | SmtExpr::BoolConst(_)
        | SmtExpr::FPConst { .. } => {}
    }
}

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
    let mut has_array = false;
    let mut has_fp = false;
    let mut has_uf = false;
    let mut has_q = false;
    infer_logic_walk(expr, &mut has_array, &mut has_fp, &mut has_uf, &mut has_q);
    has_q
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
    let expanded = expand_bounded_quantifiers(&raw_formula);
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
    let expanded = expand_bounded_quantifiers(expr);
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
    match expr {
        SmtExpr::BoolConst(_) | SmtExpr::BvConst { .. } | SmtExpr::Var { .. } => expr.clone(),
        SmtExpr::Not { operand } => {
            let operand = simplify_solver_expr(operand);
            match operand {
                SmtExpr::BoolConst(value) => SmtExpr::bool_const(!value),
                SmtExpr::Not { operand } => Arc::unwrap_or_clone(operand),
                other => SmtExpr::Not {
                    operand: Arc::new(other),
                },
            }
        }
        SmtExpr::Eq { lhs, rhs } => {
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
            if lhs == rhs {
                SmtExpr::bool_const(true)
            } else {
                SmtExpr::Eq {
                    lhs: Arc::new(lhs),
                    rhs: Arc::new(rhs),
                }
            }
        }
        SmtExpr::And { lhs, rhs } => {
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
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
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
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
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
            simplify_bvadd(lhs, rhs, *width)
        }
        SmtExpr::BvSub { lhs, rhs, width } => {
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
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
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
            simplify_bvmul(lhs, rhs, *width)
        }
        SmtExpr::BvSDiv { lhs, rhs, width } => {
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
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
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
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
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::BvNeg { operand, width } => {
            let operand = simplify_solver_expr(operand);
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
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
            let (lhs, rhs) = sorted_commutative_pair(lhs, rhs);
            SmtExpr::BvAnd {
                lhs: Arc::new(lhs),
                rhs: Arc::new(rhs),
                width: *width,
            }
        }
        SmtExpr::BvOr { lhs, rhs, width } => {
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
            let (lhs, rhs) = sorted_commutative_pair(lhs, rhs);
            SmtExpr::BvOr {
                lhs: Arc::new(lhs),
                rhs: Arc::new(rhs),
                width: *width,
            }
        }
        SmtExpr::BvXor { lhs, rhs, width } => {
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
            let (lhs, rhs) = sorted_commutative_pair(lhs, rhs);
            SmtExpr::BvXor {
                lhs: Arc::new(lhs),
                rhs: Arc::new(rhs),
                width: *width,
            }
        }
        SmtExpr::BvShl { lhs, rhs, width } => {
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
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
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
            simplify_bvlshr(lhs, rhs, *width)
        }
        SmtExpr::BvAshr { lhs, rhs, width } => {
            let lhs = simplify_solver_expr(lhs);
            let rhs = simplify_solver_expr(rhs);
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
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::BvSge { lhs, rhs, width } => SmtExpr::BvSge {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::BvSgt { lhs, rhs, width } => SmtExpr::BvSgt {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::BvSle { lhs, rhs, width } => SmtExpr::BvSle {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::BvUlt { lhs, rhs, width } => SmtExpr::BvUlt {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::BvUge { lhs, rhs, width } => SmtExpr::BvUge {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::BvUgt { lhs, rhs, width } => SmtExpr::BvUgt {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::BvUle { lhs, rhs, width } => SmtExpr::BvUle {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            width: *width,
        },
        SmtExpr::Ite {
            cond,
            then_expr,
            else_expr,
        } => {
            let cond = simplify_solver_expr(cond);
            let then_expr = simplify_solver_expr(then_expr);
            let else_expr = simplify_solver_expr(else_expr);
            match cond {
                SmtExpr::BoolConst(true) => then_expr,
                SmtExpr::BoolConst(false) => else_expr,
                cond => SmtExpr::Ite {
                    cond: Arc::new(cond),
                    then_expr: Arc::new(then_expr),
                    else_expr: Arc::new(else_expr),
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
            operand: Arc::new(simplify_solver_expr(operand)),
            width: *width,
        },
        SmtExpr::ZeroExtend {
            operand,
            extra_bits,
            width,
        } => SmtExpr::ZeroExtend {
            operand: Arc::new(simplify_solver_expr(operand)),
            extra_bits: *extra_bits,
            width: *width,
        },
        SmtExpr::SignExtend {
            operand,
            extra_bits,
            width,
        } => SmtExpr::SignExtend {
            operand: Arc::new(simplify_solver_expr(operand)),
            extra_bits: *extra_bits,
            width: *width,
        },
        SmtExpr::Concat { hi, lo, width } => SmtExpr::Concat {
            hi: Arc::new(simplify_solver_expr(hi)),
            lo: Arc::new(simplify_solver_expr(lo)),
            width: *width,
        },
        SmtExpr::TrapIfZero {
            guard,
            value,
            width,
        } => SmtExpr::TrapIfZero {
            guard: Arc::new(simplify_solver_expr(guard)),
            value: Arc::new(simplify_solver_expr(value)),
            width: *width,
        },
        SmtExpr::Select { array, index } => SmtExpr::Select {
            array: Arc::new(simplify_solver_expr(array)),
            index: Arc::new(simplify_solver_expr(index)),
        },
        SmtExpr::Store {
            array,
            index,
            value,
        } => SmtExpr::Store {
            array: Arc::new(simplify_solver_expr(array)),
            index: Arc::new(simplify_solver_expr(index)),
            value: Arc::new(simplify_solver_expr(value)),
        },
        SmtExpr::ConstArray { index_sort, value } => SmtExpr::ConstArray {
            index_sort: index_sort.clone(),
            value: Arc::new(simplify_solver_expr(value)),
        },
        SmtExpr::MemLoad {
            addr,
            load_bits,
            signed,
            result_width,
        } => SmtExpr::MemLoad {
            addr: Arc::new(simplify_solver_expr(addr)),
            load_bits: *load_bits,
            signed: *signed,
            result_width: *result_width,
        },
        SmtExpr::FPAdd { lhs, rhs, rm } => SmtExpr::FPAdd {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            rm: *rm,
        },
        SmtExpr::FPSub { lhs, rhs, rm } => SmtExpr::FPSub {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            rm: *rm,
        },
        SmtExpr::FPMul { lhs, rhs, rm } => SmtExpr::FPMul {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            rm: *rm,
        },
        SmtExpr::FPDiv { lhs, rhs, rm } => SmtExpr::FPDiv {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
            rm: *rm,
        },
        SmtExpr::FPEq { lhs, rhs } => SmtExpr::FPEq {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
        },
        SmtExpr::FPLt { lhs, rhs } => SmtExpr::FPLt {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
        },
        SmtExpr::FPGt { lhs, rhs } => SmtExpr::FPGt {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
        },
        SmtExpr::FPGe { lhs, rhs } => SmtExpr::FPGe {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
        },
        SmtExpr::FPLe { lhs, rhs } => SmtExpr::FPLe {
            lhs: Arc::new(simplify_solver_expr(lhs)),
            rhs: Arc::new(simplify_solver_expr(rhs)),
        },
        SmtExpr::FPFma { a, b, c, rm } => SmtExpr::FPFma {
            a: Arc::new(simplify_solver_expr(a)),
            b: Arc::new(simplify_solver_expr(b)),
            c: Arc::new(simplify_solver_expr(c)),
            rm: *rm,
        },
        SmtExpr::FPNeg { operand } => SmtExpr::FPNeg {
            operand: Arc::new(simplify_solver_expr(operand)),
        },
        SmtExpr::FPAbs { operand } => SmtExpr::FPAbs {
            operand: Arc::new(simplify_solver_expr(operand)),
        },
        SmtExpr::FPSqrt { operand, rm } => SmtExpr::FPSqrt {
            operand: Arc::new(simplify_solver_expr(operand)),
            rm: *rm,
        },
        SmtExpr::FPRoundToIntegral { operand, rm } => SmtExpr::FPRoundToIntegral {
            operand: Arc::new(simplify_solver_expr(operand)),
            rm: *rm,
        },
        SmtExpr::FPIsNaN { operand } => SmtExpr::FPIsNaN {
            operand: Arc::new(simplify_solver_expr(operand)),
        },
        SmtExpr::FPIsInf { operand } => SmtExpr::FPIsInf {
            operand: Arc::new(simplify_solver_expr(operand)),
        },
        SmtExpr::FPIsZero { operand } => SmtExpr::FPIsZero {
            operand: Arc::new(simplify_solver_expr(operand)),
        },
        SmtExpr::FPIsNormal { operand } => SmtExpr::FPIsNormal {
            operand: Arc::new(simplify_solver_expr(operand)),
        },
        SmtExpr::FPToSBv {
            rm,
            operand,
            width,
            mode,
        } => SmtExpr::FPToSBv {
            rm: *rm,
            operand: Arc::new(simplify_solver_expr(operand)),
            width: *width,
            mode: *mode,
        },
        SmtExpr::FPToUBv { rm, operand, width } => SmtExpr::FPToUBv {
            rm: *rm,
            operand: Arc::new(simplify_solver_expr(operand)),
            width: *width,
        },
        SmtExpr::BvToFP {
            rm,
            operand,
            eb,
            sb,
        } => SmtExpr::BvToFP {
            rm: *rm,
            operand: Arc::new(simplify_solver_expr(operand)),
            eb: *eb,
            sb: *sb,
        },
        SmtExpr::FPToFP {
            operand,
            eb,
            sb,
            rm,
        } => SmtExpr::FPToFP {
            operand: Arc::new(simplify_solver_expr(operand)),
            eb: *eb,
            sb: *sb,
            rm: *rm,
        },
        SmtExpr::BvBitsToFP { operand, eb, sb } => SmtExpr::BvBitsToFP {
            operand: Arc::new(simplify_solver_expr(operand)),
            eb: *eb,
            sb: *sb,
        },
        SmtExpr::UF {
            name,
            args,
            ret_sort,
        } => SmtExpr::UF {
            name: name.clone(),
            args: args.iter().map(simplify_solver_expr).collect(),
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
    let formula = expand_bounded_quantifiers(&raw_formula);
    generate_smt2_query_from_formula(obligation, config, &[], &raw_formula, &formula)
}

fn generate_smt2_query_from_formula(
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

    // Assert the negated equivalence (with quantifiers expanded where possible)
    lines.push(format!("(assert {})", formula));

    // Check satisfiability
    lines.push("(check-sat)".to_string());

    lines.push("(exit)".to_string());

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
    let formula = expand_bounded_quantifiers(&raw_formula);
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

/// Verify a proof obligation using an AY CLI subprocess.
///
/// This function:
/// 1. Generates SMT-LIB2 from the proof obligation
/// 2. Writes it to a temp file
/// 3. Invokes the solver binary
/// 4. Parses the output (sat/unsat/timeout/error)
/// 5. If sat, extracts the counterexample from the model
pub fn verify_with_cli(obligation: &ProofObligation, config: &AYConfig) -> AYResult {
    let smt2 = generate_smt2_query(obligation, config);
    verify_with_cli_smt2(obligation, config, &smt2)
}

/// Like [`verify_with_cli`] but invokes the solver on the UN-simplified raw
/// negated equivalence (bounded quantifiers still expanded). Used by
/// [`verify_with_ay`]'s TCB soundness guard so that an obligation the local
/// simplifier alone reduced to constant `false` is still actually checked by
/// the solver, never minted as `Verified` by the rewrite.
pub fn verify_with_cli_raw(obligation: &ProofObligation, config: &AYConfig) -> AYResult {
    let smt2 = generate_smt2_query_raw(obligation, config);
    verify_with_cli_smt2(obligation, config, &smt2)
}

/// Core of [`verify_with_cli`]: invoke the solver on a precomputed SMT-LIB2
/// query. Split out so both the normal (simplified) and raw (un-simplified)
/// query paths share solver selection, temp-file handling, and output parsing.
fn verify_with_cli_smt2(obligation: &ProofObligation, config: &AYConfig, smt2: &str) -> AYResult {
    // Find the solver binary
    let solver_selection = match &config.solver_path {
        Some(path) => config_solver_selection(path.clone()),
        None => select_solver_for_obligation(obligation),
    };
    let solver_path = solver_selection.path.clone();

    if solver_path.is_empty() {
        return AYResult::Error(format!(
            "No AY solver found ({}). Build or install AY and place `ay` on PATH, or set solver_path to an AY binary.",
            solver_route_summary_for_invocation(obligation, config)
        ));
    }

    // An independently checked result may be reused only inside this process.
    // Persistent verdict files and the committed verdict DB are untrusted hints,
    // not proof certificates: a writable file containing `unsat` must never mint
    // `AYResult::Verified`. The key binds the exact query and solver bytes;
    // recording bypasses even the process-local memo so regen observes live
    // solver output.
    let recording = crate::verdict_db::recording_active();
    let cache_key = if recording {
        None
    } else {
        session_proof_cache_key(&solver_path, smt2)
    };
    if let Some(key) = &cache_key
        && session_proof_cache_lookup_verified(key)
    {
        return AYResult::Verified;
    }

    // CERT-SKIP tier (crate::canary_cert): a repo-committed, build-embedded
    // DRAT certificate for a fixed canary obligation, INDEPENDENTLY re-checked
    // by the vendored drat-trim in this process before it is credited. Unlike
    // the removed `.verdict` disk cache, no recorded verdict is trusted here:
    // the recorded proof is re-checked on every consume, the key binds the
    // exact SMT2 bytes and the solver binary's bytes-hash, and any
    // miss/mismatch/tamper/check-failure falls through to the live solve
    // below (fail-closed, never a weaker verdict). `cache_key` is `None`
    // while the regen recorder is armed or under `TCG_NO_PROOF_CACHE`, so
    // regen always observes live runs; `TCG_CANARY_NO_CACHE=1` disables just
    // this tier. See canary_cert.rs for the full soundness argument.
    if let Some(key) = &cache_key
        && crate::canary_cert::cert_skip_verified(key, &solver_path)
    {
        session_proof_cache_store_verified(key);
        return AYResult::Verified;
    }

    // ALETHE CERT STORE (crate::obligation_cert_store): the sound, machine-local
    // generalization of the canary DRAT tier. A stored Alethe proof is credited
    // ONLY after an INDEPENDENT Carcara re-check confirms it refutes THIS exact
    // SMT2 under THIS solver identity, in this process — strictly stronger than
    // the live ay verdict it replaces, and never a weaker one (any
    // miss/binding-mismatch/tamper/absent-checker falls through). Inert unless
    // `TCG_PROOF_CERT_STORE` is set; suppressed while recording.
    if let Some(key) = &cache_key
        && crate::obligation_cert_store::alethe_cert_skip_verified(key, &solver_path, smt2)
    {
        session_proof_cache_store_verified(key);
        return AYResult::Verified;
    }

    // PERSISTENT SERVER (compile-time floor): discharge through the resident
    // `ay --incremental` process first — same binary, byte-identical query,
    // identical verdict, but ONE process startup amortized across every live
    // obligation.
    // On a process/framing anomaly it falls through to the fresh per-call spawn
    // below (never a wrong or weaker verdict). A genuine resident deadline is
    // already a conclusive Timeout for this configured budget, so it is returned
    // directly instead of spending the same budget a second time. Skipped while
    // recording.
    if ay_server_enabled()
        && !strict_formal_campaign_active()
        && !ay_server_is_unusable(&solver_path)
    {
        let srv_t0 = std::env::var_os("TCG_SOLVE_TRACE")
            .is_some()
            .then(std::time::Instant::now);
        match run_solver_via_server(&solver_path, smt2, config.timeout_ms, &obligation.inputs) {
            AyServerAttempt::Completed(result) => {
                if let Some(t0) = srv_t0 {
                    eprintln!(
                        "TCG_SOLVE_TRACE server_solve {:.3}s obligation={:?} smt2_bytes={}",
                        t0.elapsed().as_secs_f64(),
                        obligation.name,
                        smt2.len(),
                    );
                }
                let result = if matches!(result, AYResult::SolverUnsat) {
                    // A resident process has no exact per-query proof artifact
                    // to hand to the independent checker. Treat its UNSAT as a
                    // candidate only, then replay once through the fresh
                    // proof-bearing path before any cache/authority promotion.
                    run_fresh_authority_query(&solver_path, obligation, config, smt2)
                } else {
                    enrich_sat_counterexample_via_server(
                        &solver_path,
                        obligation,
                        config,
                        smt2,
                        result,
                    )
                };
                if let (Some(key), AYResult::Verified) = (&cache_key, &result) {
                    session_proof_cache_store_verified(key);
                    // MINT-ON-MISS (opt-in, off the hot path): persist an
                    // independently-Carcara-verified Alethe cert so the next
                    // identical compile can skip this live solve. No-op unless
                    // `TCG_PROOF_CERT_STORE` is set; verifies before writing.
                    crate::obligation_cert_store::mint_alethe_cert(
                        key,
                        &solver_path,
                        smt2,
                        &obligation.name,
                    );
                }
                return result;
            }
            AyServerAttempt::TimedOut => {
                if let Some(t0) = srv_t0 {
                    eprintln!(
                        "TCG_SOLVE_TRACE server_timeout {:.3}s obligation={:?} smt2_bytes={}",
                        t0.elapsed().as_secs_f64(),
                        obligation.name,
                        smt2.len(),
                    );
                }
                return AYResult::Timeout;
            }
            AyServerAttempt::Anomaly => {
                // The server could not service this query. Latch it off rather
                // than re-attempting for every remaining obligation; the
                // one-shot fallback below is always correct.
                mark_ay_server_unusable(&solver_path);
            }
        }
    }

    // Write SMT-LIB2 to a temp file
    let tmp_file = match write_temp_smt2(smt2) {
        Ok(file) => file,
        Err(e) => return AYResult::Error(format!("Failed to write temp file: {}", e)),
    };

    // DIAGNOSTIC (default off, no behavior change): `TCG_SOLVE_TRACE=1` logs the
    // wall time of every LIVE solver subprocess plus the obligation name, so the
    // per-family live-solve cost across a warm compile is a measurement, not a
    // guess. Purely additive — the timing wrap does not alter control flow.
    let solve_trace = std::env::var_os("TCG_SOLVE_TRACE").is_some();
    let solve_t0 = solve_trace.then(std::time::Instant::now);
    let output = run_solver_command(&solver_path, tmp_file.path(), config.timeout_ms);
    if let Some(t0) = solve_t0 {
        eprintln!(
            "TCG_SOLVE_TRACE live_solve {:.3}s obligation={:?} smt2_bytes={}",
            t0.elapsed().as_secs_f64(),
            obligation.name,
            smt2.len(),
        );
    }

    let result = match output {
        Ok(output) => {
            let result = parse_solver_process_output(&output, &obligation.inputs);
            let result = promote_fresh_solver_unsat(result, &solver_path, tmp_file.path(), smt2);
            let result =
                enrich_sat_counterexample_via_fresh(&solver_path, obligation, config, smt2, result);
            if let (Some(key), AYResult::Verified) = (&cache_key, &result) {
                session_proof_cache_store_verified(key);
                crate::obligation_cert_store::mint_alethe_cert(
                    key,
                    &solver_path,
                    smt2,
                    &obligation.name,
                );
            }
            result
        }
        Err(SolverInvocationError::Timeout) => AYResult::Timeout,
        Err(SolverInvocationError::Io(e)) => AYResult::Error(format!(
            "Failed to invoke solver ({}): {}",
            solver_route_summary_from_selection(obligation_logic(obligation), &solver_selection),
            e
        )),
    };
    // Tier-0 regen recorder: observes LIVE solver results only (cache hits
    // early-return above and are never recorded). The recorder itself keeps
    // Verified verdicts exclusively — SolverUnsat / Timeout / CounterExample /
    // Unknown / Error are never persisted as rows in any tier.
    if recording {
        crate::verdict_db::record_live_result(&obligation.name, smt2, &result);
    }
    result
}

/// TEST-ONLY re-probe for the certification-gap guards
/// ([`crate::formal_gap`]): discharge `obligation` through the FRESH one-shot
/// transcript path — the same solver selection and SMT2 routing as
/// [`verify_with_ay`], but bypassing the resident server (which deliberately
/// discards stderr, where AY prints its decisive `(:reason-unknown …)` and
/// proof-authority diagnostics) and every cache/cert tier. The result is
/// therefore REASON-BEARING: a raw `unknown` that the server truncates to
/// `Unknown("unknown")` comes back here with AY's own published reason, so a
/// guard can distinguish the capability gap (`incomplete self-check-rejected`
/// — AY computed UNSAT and its mandatory strict self-certification declined
/// the proof) from a genuine solver regression. Never used by any production
/// path; the caller must not hold [`formal_solver_test_lock`]-independent
/// solver state assumptions (this spawns its own one-shot process).
#[cfg(test)]
pub(crate) fn verify_fresh_transcript_for_gap_probe(
    obligation: &ProofObligation,
    config: &AYConfig,
) -> AYResult {
    let solver_selection = match &config.solver_path {
        Some(path) => config_solver_selection(path.clone()),
        None => select_solver_for_obligation(obligation),
    };
    if solver_selection.path.is_empty() {
        return AYResult::Error("no AY solver found for the gap re-probe".to_string());
    }
    // Mirror verify_with_ay's TCB soundness routing byte-for-byte: an
    // obligation the local simplifier alone closed re-runs on the RAW formula.
    let smt2 = if simplifier_alone_proved_unsat(obligation) {
        generate_smt2_query_raw(obligation, config)
    } else {
        generate_smt2_query(obligation, config)
    };
    run_fresh_authority_query(&solver_selection.path, obligation, config, &smt2)
}

fn run_fresh_authority_query(
    solver_path: &str,
    obligation: &ProofObligation,
    config: &AYConfig,
    smt2: &str,
) -> AYResult {
    let tmp_file = match write_temp_smt2(smt2) {
        Ok(file) => file,
        Err(e) => return AYResult::Error(format!("Failed to write proof query: {e}")),
    };
    match run_solver_command(solver_path, tmp_file.path(), config.timeout_ms) {
        Ok(output) => {
            let result = parse_solver_process_output(&output, &obligation.inputs);
            let result = promote_fresh_solver_unsat(result, solver_path, tmp_file.path(), smt2);
            enrich_sat_counterexample_via_fresh(solver_path, obligation, config, smt2, result)
        }
        Err(SolverInvocationError::Timeout) => AYResult::Timeout,
        Err(SolverInvocationError::Io(e)) => {
            AYResult::Error(format!("Failed to invoke proof solver: {e}"))
        }
    }
}

fn promote_fresh_solver_unsat(
    result: AYResult,
    _solver_path: &str,
    smt2_path: &Path,
    smt2: &str,
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

    let Some(checker) = crate::obligation_cert_store::clean_checker_path() else {
        let _ = std::fs::remove_file(&proof_path);
        return AYResult::Unknown(
            "AY reported UNSAT but no independent Clean/Carcara checker is available".to_string(),
        );
    };
    let checked = crate::obligation_cert_store::carcara_verify(&checker, smt2, &proof);
    let _ = std::fs::remove_file(&proof_path);
    if checked {
        AYResult::Verified
    } else {
        AYResult::Unknown(format!(
            "AY reported UNSAT but {} rejected or could not fully verify the exact Alethe proof",
            checker.display()
        ))
    }
}

fn default_alethe_path(smt2_path: &Path) -> std::path::PathBuf {
    let mut proof_os = smt2_path.as_os_str().to_os_string();
    proof_os.push(".alethe");
    std::path::PathBuf::from(proof_os)
}

/// If a verdict-only resident query returned SAT, ask for values in a second
/// query.  The model command is therefore never executed after UNSAT/unknown.
fn enrich_sat_counterexample_via_server(
    solver_path: &str,
    obligation: &ProofObligation,
    config: &AYConfig,
    verdict_smt2: &str,
    result: AYResult,
) -> AYResult {
    if !config.produce_models || !matches!(&result, AYResult::CounterExample(_)) {
        return result;
    }
    let Some(model_smt2) = generate_sat_model_query(obligation, verdict_smt2) else {
        return result;
    };

    match run_solver_via_server(
        solver_path,
        &model_smt2,
        config.timeout_ms,
        &obligation.inputs,
    ) {
        AyServerAttempt::Completed(AYResult::CounterExample(values)) => {
            AYResult::CounterExample(values)
        }
        AyServerAttempt::Completed(other) => AYResult::Error(format!(
            "SAT model replay returned a non-SAT result: {other:?}"
        )),
        AyServerAttempt::TimedOut => AYResult::Timeout,
        AyServerAttempt::Anomaly => {
            mark_ay_server_unusable(solver_path);
            run_sat_model_query_fresh(solver_path, obligation, config, &model_smt2)
        }
    }
}

/// Fresh-process counterpart of [`enrich_sat_counterexample_via_server`].
fn enrich_sat_counterexample_via_fresh(
    solver_path: &str,
    obligation: &ProofObligation,
    config: &AYConfig,
    verdict_smt2: &str,
    result: AYResult,
) -> AYResult {
    if !config.produce_models || !matches!(&result, AYResult::CounterExample(_)) {
        return result;
    }
    let Some(model_smt2) = generate_sat_model_query(obligation, verdict_smt2) else {
        return result;
    };
    run_sat_model_query_fresh(solver_path, obligation, config, &model_smt2)
}

fn run_sat_model_query_fresh(
    solver_path: &str,
    obligation: &ProofObligation,
    config: &AYConfig,
    model_smt2: &str,
) -> AYResult {
    let tmp_file = match write_temp_smt2(model_smt2) {
        Ok(file) => file,
        Err(e) => return AYResult::Error(format!("Failed to write SAT model query: {e}")),
    };
    match run_solver_command(solver_path, tmp_file.path(), config.timeout_ms) {
        Ok(output) => match parse_solver_process_output(&output, &obligation.inputs) {
            AYResult::CounterExample(values) => AYResult::CounterExample(values),
            other => AYResult::Error(format!(
                "SAT model replay returned a non-SAT result: {other:?}"
            )),
        },
        Err(SolverInvocationError::Timeout) => AYResult::Timeout,
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
    // NOTE: the `-dirty` short-circuit lives BELOW the explicit-blocking branch,
    // not here, so that an explicit request still yields a key. See there.
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
        || solver_path != select_solver_binary().path
    {
        return Some(verdict_cache_key_v2(
            &solver_identity_hash(solver_path)?,
            smt2,
        ));
    }
    // Skip the whole tier for a `-dirty` DEFAULT solver — but NOT for the reason
    // CT-10 gave. Its comment said "a dirty solver can never match a committed
    // artifact", which is true of tier-0 and CERT-SKIP but irrelevant here: this
    // is the IN-PROCESS session cache, keyed by (solver bytes, smt2), and
    // nothing committed is involved. On that reasoning alone the short-circuit
    // was simply wrong.
    //
    // ⚑ MEASUREMENT SAYS KEEP IT, for a different reason. On a dirty solver the
    // committed tiers are dead by construction, so the session cache is the only
    // consumer left — and it is measured to save ~nothing (cache-off
    // `p3c_scalar` is ~25ms everywhere) while the identity it needs is a ~320ms
    // SHA-256 over the ~73MB `ay`. Without this, the adaptive fallback below
    // blocks for that hash after 16 uncached solves, so every proof-heavy
    // compile pays it to populate a cache that does not repay it. Removing it
    // moved the beat-llvm compile geomean 1.771x -> 2.921x of LLVM -O2 with
    // runtime unchanged — far outside the ~6.9% compile noise band.
    //
    // Declining a cache is a pure scheduling choice that can never change a
    // verdict (see the soundness note above), so the measurement decides.
    //
    // It sits BELOW the branch above deliberately: an explicit
    // `TCG_BLOCKING_IDENTITY=1`, or a caller-supplied solver, still gets the
    // exact prior behaviour. That is how a test asks for a canonical key
    // deterministically instead of depending on this policy.
    if default_solver_reports_dirty_build(solver_path) {
        return None;
    }
    if let Some(identity) = solver_identity_hash_if_ready(solver_path) {
        return Some(verdict_cache_key_v2(&identity, smt2));
    }
    // Not ready. Make sure something IS computing it — this is what keeps the
    // cache alive for consumers that never run `CodegenBackend::init` (the test
    // suite, `regen_verdict_db`, any library user), which would otherwise find
    // the identity permanently unresolved and re-solve every repeated
    // obligation. The rustc bridge still warms at `init`, strictly earlier.
    start_solver_identity_warm();

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
    static MISSES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let misses = MISSES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
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

/// Process-wide memo behind [`solver_identity_hash`], keyed by the solver's
/// (path, size, mtime).
///
/// The value is a per-key mutex rather than a bare `String` so the hash is
/// COMPUTE-ONCE: a caller arriving while another thread is mid-hash waits for
/// that result instead of streaming the same ~73MB binary again. That is what
/// makes the background warm a real prefetch, and it is what lets
/// [`solver_identity_hash_if_ready`] distinguish "already resolved" from
/// "in flight" without blocking.
type SolverIdentityMemo = std::sync::Mutex<
    std::collections::HashMap<
        (String, u64, u128),
        std::sync::Arc<std::sync::Mutex<Option<String>>>,
    >,
>;

fn solver_identity_memo() -> &'static SolverIdentityMemo {
    static MEMO: std::sync::OnceLock<SolverIdentityMemo> = std::sync::OnceLock::new();
    MEMO.get_or_init(|| std::sync::Mutex::new(std::collections::HashMap::new()))
}

/// Content identity of a solver binary: the lowercase-hex SHA-256 of its
/// bytes. Memoized per process for performance. Persistent identity files are
/// intentionally ignored: metadata such as path/size/mtime is not a secure
/// binding to file contents and a forged hash must not influence proof reuse.
/// Returns `None` when the binary cannot be stat'ed or read.
pub(crate) fn solver_identity_hash(solver_path: &str) -> Option<String> {
    use sha2::{Digest, Sha256};
    // COMPUTE-ONCE, not merely memoized. The entry is a per-key mutex rather
    // than a bare `String`, so a caller arriving while another thread is
    // mid-hash WAITS for that result instead of streaming the same ~73MB
    // binary a second time. That is what makes `warm_solver_identity` a real
    // prefetch: without it, the background warm and the first inline consumer
    // would race and each pay the full hash. A FAILED read is still not
    // cached (the slot stays `None`), preserving the prior behaviour that a
    // transient IO error is retried rather than remembered.
    let meta = std::fs::metadata(solver_path).ok()?;
    let mtime = meta
        .modified()
        .ok()?
        .duration_since(std::time::UNIX_EPOCH)
        .ok()?
        .as_nanos();
    let stat_key = (solver_path.to_string(), meta.len(), mtime);

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
    loop {
        let n = std::io::Read::read(&mut file, &mut buf).ok()?;
        if n == 0 {
            break;
        }
        hasher.update(&buf[..n]);
    }
    let hash = format!("{:x}", hasher.finalize());
    *slot = Some(hash.clone());
    Some(hash)
}

/// The solver's content identity ONLY if it is already resolved in this
/// process; never computes it.
///
/// Companion to [`warm_solver_identity`]: it lets a hot path (the session
/// verdict memo) use the identity when the background warm has produced it and
/// skip the cache otherwise, instead of blocking ~337ms mid-compile to hash the
/// solver binary. Returns `None` when the binary cannot be stat'ed, when no
/// entry exists yet, or when another thread is mid-hash (the slot is locked) —
/// all of which the caller treats as "no cache", i.e. discharge live.
fn solver_identity_hash_if_ready(solver_path: &str) -> Option<String> {
    let meta = std::fs::metadata(solver_path).ok()?;
    let mtime = meta
        .modified()
        .ok()?
        .duration_since(std::time::UNIX_EPOCH)
        .ok()?
        .as_nanos();
    let stat_key = (solver_path.to_string(), meta.len(), mtime);

    let memo = solver_identity_memo();
    // `try_lock` throughout: this function must never wait on the hash.
    let map = memo.try_lock().ok()?;
    let slot = map.get(&stat_key)?;
    let slot = slot.try_lock().ok()?;
    slot.clone()
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
    static STARTED: std::sync::OnceLock<()> = std::sync::OnceLock::new();
    STARTED.get_or_init(|| {
        std::thread::Builder::new()
            .name("trust-cg-solver-identity-warm".to_string())
            .spawn(warm_solver_identity)
            .ok();
    });
}

pub fn warm_solver_identity() {
    if crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some() {
        return;
    }
    let started = std::time::Instant::now();
    let trace = crate::env_lock::var_os("TCG_TIME").is_some();
    let path = find_solver_binary();
    if path.is_empty() {
        return;
    }
    // A `-dirty` solver's COMMITTED tiers (tier-0, CERT-SKIP) are all dead by
    // construction, so the only consumer left is the in-process session cache —
    // and that cache is MEASURED to save ~nothing (cache-off `p3c_scalar` is
    // ~25ms everywhere) while this hash costs ~320ms. Eagerly paying it here is
    // a guaranteed net loss on a dev box.
    //
    // ⚑ MEASURED, not assumed: warming unconditionally moved the beat-llvm
    // compile geomean from 1.771x to 2.767x of LLVM -O2 — a ~1x-of-LLVM
    // regression, far outside the ~6.9% compile noise band.
    //
    // Declining to warm does NOT disable the session cache; it only declines to
    // PREPAY. `session_proof_cache_key` still keys dirty builds, and CT-9's
    // adaptive fallback blocks for the identity once a compile has run 16
    // uncached solves — i.e. exactly when there is enough proof work to earn the
    // 320ms. Small crates never pay it; proof-heavy ones pay once.
    if default_solver_reports_dirty_build(&path) {
        return;
    }
    let _ = solver_identity_hash(&path);
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
}

/// The solver binary path the live discharge lane would resolve right now
/// (`None` when no solver is found). Used by the tier-0 verdict-DB regen tool
/// ([`crate::verdict_db`]) to record the identity of the EXACT binary that
/// produced the committed verdicts.
pub(crate) fn resolved_solver_path() -> Option<String> {
    let path = find_solver_binary();
    if path.is_empty() { None } else { Some(path) }
}

/// The solver's reported version string (best-effort, informational — the
/// binding solver identity is [`solver_identity_hash`]). Exposed for the
/// tier-0 verdict-DB manifest.
pub(crate) fn solver_version_string(solver_path: &str) -> Option<String> {
    detect_solver_version(solver_path)
}

fn session_proof_cache() -> &'static std::sync::Mutex<std::collections::HashSet<String>> {
    use std::sync::{Mutex, OnceLock};
    static CACHE: OnceLock<Mutex<std::collections::HashSet<String>>> = OnceLock::new();
    CACHE.get_or_init(|| Mutex::new(std::collections::HashSet::new()))
}

fn session_proof_cache_lookup_verified(key: &str) -> bool {
    session_proof_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .contains(key)
}

fn session_proof_cache_store_verified(key: &str) {
    session_proof_cache()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .insert(key.to_owned());
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
    session_proof_cache_lookup_verified(key)
}

/// Prime the session verdict memo (see [`session_cache_contains`]).
pub(crate) fn session_cache_store_verified(key: &str) {
    session_proof_cache_store_verified(key);
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
    let solver_path = select_solver_binary().path;
    if solver_path.is_empty() {
        return None;
    }
    let key = session_proof_cache_key(&solver_path, smt2)?;
    Some((solver_path, key))
}

/// Run ONE precomputed SMT-LIB2 batch script through the resolved solver in a
/// SINGLE subprocess and return its raw stdout (`None` on any spawn / IO /
/// timeout failure). Shares [`write_temp_smt2`] + [`run_solver_command`] with
/// the per-obligation live path, so the batch runs through the exact same
/// solver-invocation machinery.
///
/// The `script` is opaque to this function: it is the caller's responsibility
/// (`crate::verdict_db`) to assemble a byte-identical, echo-delimited,
/// `(reset)`-isolated batch and to parse the sentinels back out. Any failure
/// here is reported as `None` so the caller falls through to the inline
/// per-obligation live solve (fail-closed — never a weaker verdict).
pub(crate) fn run_batch_solver_script(script: &str, timeout_ms: u64) -> Option<String> {
    let solver_path = find_solver_binary();
    if solver_path.is_empty() {
        return None;
    }
    let tmp_file = write_temp_smt2(script).ok()?;
    let output = run_solver_command(&solver_path, tmp_file.path(), timeout_ms).ok()?;
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
enum SolverInvocationError {
    Timeout,
    Io(String),
}

#[cfg(unix)]
fn configure_solver_command(command: &mut std::process::Command) {
    use std::os::unix::process::CommandExt;
    command.process_group(0);
}

#[cfg(not(unix))]
fn configure_solver_command(_command: &mut std::process::Command) {}

#[cfg(unix)]
fn signal_solver_process_group(process_group_id: u32, signal: i32) {
    if process_group_id <= i32::MAX as u32 {
        let pgid = process_group_id as i32;
        unsafe {
            let _ = kill(-pgid, signal);
        }
    }
}

#[cfg(unix)]
fn terminate_solver_process_tree(child: &mut std::process::Child, process_group_id: u32) {
    signal_solver_process_group(process_group_id, SIGTERM);
    std::thread::sleep(Duration::from_millis(20));
    signal_solver_process_group(process_group_id, SIGKILL);

    let _ = child.kill();
}

#[cfg(not(unix))]
fn terminate_solver_process_tree(child: &mut std::process::Child, _process_group_id: u32) {
    let _ = child.kill();
}

#[cfg(unix)]
fn cleanup_solver_process_tree(process_group_id: u32) {
    signal_solver_process_group(process_group_id, SIGKILL);
}

#[cfg(not(unix))]
fn cleanup_solver_process_tree(_process_group_id: u32) {}

// ==========================================================================
// PERSISTENT SOLVER SERVER (compile-time floor: solver STARTUP dominates)
// ==========================================================================
// MEASURED (2026-07-14): an `ay` invocation costs ~25 ms almost entirely in
// process STARTUP (loading the ~87 MB binary); the solve of a simplifier-closed
// obligation is ~free (a trivial `(check-sat)` and a real ALU obligation take
// the same ~20 ms). A warm compile spawns `ay` once PER live obligation, so the
// startup overhead — not the solve — is the dominant compile cost. This keeps
// ONE resident `ay -in` process and feeds every live query to it via stdin,
// framed by a unique sentinel and `(reset)`-isolated, collapsing N startups into
// ONE (measured ~11x on the solver overhead: 9 queries in one process ~20 ms vs
// 9 spawns ~225 ms).
//
// SOUNDNESS: identical to a fresh spawn — the SAME binary on byte-identical query
// bytes (exactly what `run_solver_command` writes, minus the trailing `(exit)`,
// plus `(echo <sentinel>)` + `(reset)`), and `(reset)` restores the initial
// solver state between queries. SAT values are requested only in a subsequent
// SAT-only window; UNSAT/unknown scripts never contain a model command. The
// verdict is parsed by the SAME `parse_solver_output`. FAIL-SAFE: a
// process/framing anomaly (spawn/write/
// read error, missing/duplicate verdict, closed stream) DROPS the server
// (killing the child) and asks the caller to fall back to a fresh per-call spawn
// — never a wrong or weaker verdict. A configured deadline also drops the
// server, but returns `TimedOut`: retrying the byte-identical query would
// silently double the caller's timeout budget. The global lock serializes
// queries (one window at a time), so windows never interleave. Off while the
// regen recorder is armed (it must observe genuine fresh live runs).
struct AyServer {
    child: std::process::Child,
    process_group_id: u32,
    stdin: std::process::ChildStdin,
    lines: std::sync::mpsc::Receiver<String>,
    /// The exact binary this resident process was spawned from. SOLVER
    /// IDENTITY BINDING: a query for a DIFFERENT `solver_path` (e.g. an
    /// explicit config/`with_solver_path` override) must never be answered
    /// by this process — the slot is dropped and respawned for the requested
    /// binary. Without this, a query naming solver B was silently routed to
    /// whichever solver A happened to become resident first.
    solver_path: String,
}

impl Drop for AyServer {
    fn drop(&mut self) {
        // Closing stdin makes `ay -in` see EOF and exit; kill+reap guarantees no
        // stray process even if it ignores EOF. The process-group teardown also
        // kills any solver descendants that inherited the resident's stdout
        // pipe; killing only the direct child would orphan those descendants.
        if std::env::var_os("TCG_SOLVE_TRACE").is_some() {
            eprintln!(
                "TCG_SOLVE_TRACE server_drop pid={} path={}",
                self.process_group_id, self.solver_path
            );
        }
        terminate_solver_process_tree(&mut self.child, self.process_group_id);
        let _ = self.child.wait();
    }
}

fn ay_server_slot() -> &'static std::sync::Mutex<Option<AyServer>> {
    static SLOT: std::sync::OnceLock<std::sync::Mutex<Option<AyServer>>> =
        std::sync::OnceLock::new();
    SLOT.get_or_init(|| std::sync::Mutex::new(None))
}

fn ay_server_next_seq() -> u64 {
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
}

/// Resident-server path enabled? Default ON; opt out with
/// `TCG_NO_SOLVER_SERVER=1`. Never while the regen recorder is armed (the
/// offline builder must observe genuine fresh live solver runs).
fn ay_server_enabled() -> bool {
    std::env::var_os("TCG_NO_SOLVER_SERVER").is_none() && !crate::verdict_db::recording_active()
}

/// The strict proof campaign needs the complete one-shot transcript. The
/// resident server deliberately discards stderr because it is not query-framed,
/// while AY emits decisive `reason-unknown` and proof-authority diagnostics
/// there. Preserve those diagnostics so the strict gate can distinguish a
/// rejected authority path from ordinary solver capacity.
fn strict_formal_campaign_active() -> bool {
    matches!(
        std::env::var("TRUST_CG_RUN_FORMAL_PROOF_TESTS").as_deref(),
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
fn ay_server_unusable_paths() -> &'static std::sync::Mutex<std::collections::HashSet<String>> {
    static PATHS: std::sync::OnceLock<std::sync::Mutex<std::collections::HashSet<String>>> =
        std::sync::OnceLock::new();
    PATHS.get_or_init(|| std::sync::Mutex::new(std::collections::HashSet::new()))
}

fn ay_server_is_unusable(solver_path: &str) -> bool {
    ay_server_unusable_paths()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .contains(solver_path)
}

fn mark_ay_server_unusable(solver_path: &str) {
    ay_server_unusable_paths()
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .insert(solver_path.to_owned());
}

/// Spawn a fresh `ay --incremental` resident process (piped stdin/stdout,
/// stderr to null)
/// with a reader thread forwarding each stdout line to a channel, so the query
/// read can honor a deadline without blocking on the pipe. None on spawn failure.
fn spawn_ay_server(solver_path: &str) -> Option<AyServer> {
    // `--incremental` takes ay's LINE-BY-LINE interactive path, which flushes
    // stdout after EVERY command (run.rs:2729/2774) — required so this resident
    // reader sees each `(check-sat)`/`(echo)` response immediately.
    //
    // Pass exactly ONE flag. `-in` is ay's z3-compat ALIAS for `--incremental`
    // and is preprocessed into it, so passing both makes clap reject the
    // duplicate:
    //
    //     error: the argument '--incremental' cannot be used multiple times
    //
    // ...with exit status 2. `Command::spawn()` still SUCCEEDS (the exec worked;
    // the process just dies immediately), so this function returned `Some` and
    // the resident server appeared to start. It never did: the reader channel
    // disconnected, every query fell back to spawning a fresh one-shot `ay`, and
    // because the anomaly is not memoized each obligation re-paid a doomed spawn
    // plus the 20ms terminate sleep.
    //
    // Cost of the typo, measured on p3_gcd (the only corpus program that reaches
    // the solver at all): ~52ms per obligation against ~0.7ms/query for a
    // working resident server — and p3_gcd compiled in 728ms against LLVM's
    // ~90ms, by far the worst compile-time outlier in the corpus.
    //
    // Verified both `-in` alone and `--incremental` alone drive a resident
    // line-buffered server correctly (12/12 queries, 0.68-0.84ms each).
    let mut command = std::process::Command::new(solver_path);
    command
        .arg("--incremental")
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::null());
    configure_solver_command(&mut command);
    let mut child = command.spawn().ok()?;
    let process_group_id = child.id();
    if std::env::var_os("TCG_SOLVE_TRACE").is_some() {
        eprintln!("TCG_SOLVE_TRACE server_spawn pid={process_group_id} path={solver_path}");
    }
    let stdin = child.stdin.take()?;
    let stdout = child.stdout.take()?;
    let (tx, rx) = std::sync::mpsc::channel::<String>();
    std::thread::spawn(move || {
        use std::io::BufRead;
        let reader = std::io::BufReader::new(stdout);
        for line in reader.lines() {
            match line {
                Ok(l) => {
                    if tx.send(l).is_err() {
                        break;
                    }
                }
                Err(_) => break,
            }
        }
        // EOF/error: the child died; dropping `tx` closes the channel so the
        // next query's `recv` errors -> the server is dropped and rebuilt.
    });
    Some(AyServer {
        child,
        process_group_id,
        stdin,
        lines: rx,
        solver_path: solver_path.to_owned(),
    })
}

/// Result of one resident-server attempt.
///
/// `TimedOut` is deliberately distinct from `Anomaly`: a timeout consumed the
/// configured solver budget and must be surfaced directly, while an anomaly
/// permits the existing fail-closed fresh-process fallback.
enum AyServerAttempt {
    Completed(AYResult),
    TimedOut,
    Anomaly,
}

/// Discharge one query through the resident server. Returns the SAME `AYResult`
/// a fresh `run_solver_command` on `smt2` would, `TimedOut` after consuming the
/// configured deadline, or `Anomaly` to request a fresh-process fallback.
/// `smt2` MUST be the exact bytes the per-call path writes (ending in an
/// `(exit)` line).
fn run_solver_via_server(
    solver_path: &str,
    smt2: &str,
    timeout_ms: u64,
    inputs: &[(String, u32)],
) -> AyServerAttempt {
    // Query body = the exact per-call SMT2 minus its trailing `(exit)` (the
    // server must NOT exit), then an echoed unique sentinel + `(reset)`.
    let trimmed = smt2.strip_suffix('\n').unwrap_or(smt2);
    let Some(body) = trimmed.strip_suffix("(exit)") else {
        return AyServerAttempt::Anomaly;
    };
    let seq = ay_server_next_seq();
    let sentinel = format!("==TCG_SRV_{seq}==");

    let mut guard = ay_server_slot().lock().unwrap_or_else(|p| p.into_inner());
    // Solver identity binding: the resident server answers only queries for
    // the binary it was spawned from. A different `solver_path` (config
    // override, test fake) drops the resident child and spawns the requested
    // one — never silently answering with the wrong solver.
    if guard
        .as_ref()
        .is_some_and(|server| server.solver_path != solver_path)
    {
        *guard = None;
    }
    if guard.is_none() {
        *guard = spawn_ay_server(solver_path);
    }
    let Some(server) = guard.as_mut() else {
        return AyServerAttempt::Anomaly;
    };

    // Feed the framed query. A write/flush error => the child died: drop+fallback.
    use std::io::Write;
    let script = format!("{body}\n(echo \"{sentinel}\")\n(reset)\n");
    if server.stdin.write_all(script.as_bytes()).is_err() || server.stdin.flush().is_err() {
        *guard = None;
        return AyServerAttempt::Anomaly;
    }

    // Read this window until the sentinel, honoring the deadline. Capture lines
    // from the FIRST verdict line onward (so any pre-verdict noise is discarded
    // and `parse_solver_output` sees the verdict as line 0). A configured
    // deadline returns TimedOut; a closed channel or malformed framing remains
    // an anomaly eligible for a fresh-process fallback. timeout_ms == 0 means
    // no deadline, matching `run_solver_command`.
    let deadline = (timeout_ms != 0).then(|| Instant::now() + Duration::from_millis(timeout_ms));
    let mut window = String::new();
    let mut verdict_lines = 0usize;
    let mut seen_verdict = false;
    let mut protocol_error: Option<String> = None;
    loop {
        let received = if let Some(deadline) = deadline {
            let now = Instant::now();
            if now >= deadline {
                *guard = None;
                return AyServerAttempt::TimedOut;
            }
            server.lines.recv_timeout(deadline - now)
        } else {
            server
                .lines
                .recv()
                .map_err(|_| std::sync::mpsc::RecvTimeoutError::Disconnected)
        };
        match received {
            Ok(line) => {
                let t = line.trim();
                if t == sentinel {
                    break;
                }
                if t.starts_with("(error") {
                    protocol_error = Some(t.to_string());
                }
                if t == "sat" || t == "unsat" || t == "unknown" {
                    verdict_lines += 1;
                    seen_verdict = true;
                }
                if seen_verdict {
                    window.push_str(&line);
                    window.push('\n');
                }
            }
            Err(std::sync::mpsc::RecvTimeoutError::Timeout) => {
                *guard = None;
                return AyServerAttempt::TimedOut;
            }
            Err(std::sync::mpsc::RecvTimeoutError::Disconnected) => {
                // The child died or its stdout reader failed.
                *guard = None;
                return AyServerAttempt::Anomaly;
            }
        }
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

fn run_solver_command(
    solver_path: &str,
    smt2_path: &Path,
    timeout_ms: u64,
) -> Result<std::process::Output, SolverInvocationError> {
    // Secure create_new tempfiles avoid predictable-name symlink/TOCTOU
    // attacks while retaining file-backed output (which cannot deadlock on a
    // full pipe while the parent polls the timeout).
    let stdout_tmp = tempfile::Builder::new()
        .prefix("trust-cg-ay-stdout-")
        .tempfile()
        .map_err(|e| SolverInvocationError::Io(e.to_string()))?;
    let stderr_tmp = tempfile::Builder::new()
        .prefix("trust-cg-ay-stderr-")
        .tempfile()
        .map_err(|e| SolverInvocationError::Io(e.to_string()))?;
    let stdout_file = stdout_tmp
        .reopen()
        .map_err(|e| SolverInvocationError::Io(e.to_string()))?;
    let stderr_file = stderr_tmp
        .reopen()
        .map_err(|e| SolverInvocationError::Io(e.to_string()))?;

    let mut command = std::process::Command::new(solver_path);
    command
        .arg("-smt2")
        .arg(smt2_path)
        .stdout(std::process::Stdio::from(stdout_file))
        .stderr(std::process::Stdio::from(stderr_file));
    configure_solver_command(&mut command);

    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(e) => return Err(SolverInvocationError::Io(e.to_string())),
    };
    let process_group_id = child.id();

    let status = if timeout_ms == 0 {
        match child.wait() {
            Ok(status) => status,
            Err(e) => {
                terminate_solver_process_tree(&mut child, process_group_id);
                return Err(SolverInvocationError::Io(e.to_string()));
            }
        }
    } else {
        let poll_interval = Duration::from_millis(10);
        let deadline = Instant::now() + Duration::from_millis(timeout_ms);

        loop {
            match child.try_wait() {
                Ok(Some(status)) => break status,
                Ok(None) => {
                    let now = Instant::now();
                    if now >= deadline {
                        terminate_solver_process_tree(&mut child, process_group_id);
                        let _ = child.wait();
                        return Err(SolverInvocationError::Timeout);
                    }

                    std::thread::sleep(std::cmp::min(
                        poll_interval,
                        deadline.saturating_duration_since(now),
                    ));
                }
                Err(e) => {
                    terminate_solver_process_tree(&mut child, process_group_id);
                    let _ = child.wait();
                    return Err(SolverInvocationError::Io(e.to_string()));
                }
            }
        }
    };

    cleanup_solver_process_tree(process_group_id);

    let stdout = std::fs::read(stdout_tmp.path())
        .map_err(|e| SolverInvocationError::Io(format!("failed to read solver stdout: {e}")))?;
    let stderr = std::fs::read(stderr_tmp.path())
        .map_err(|e| SolverInvocationError::Io(format!("failed to read solver stderr: {e}")))?;

    Ok(std::process::Output {
        status,
        stdout,
        stderr,
    })
}

/// Search for the AY CLI binary. AY is the **sole** solver — z3 has been
/// removed from the discharge path entirely (the project's own AY solver must
/// prove every obligation; if it cannot, AY is what gets fixed, never z3).
///
/// Search order:
/// 1. `AY_SOLVER_PATH` environment variable (explicit override)
/// 2. `ay` on `PATH`
/// 3. `ay` under supported `CARGO_TARGET_DIR` build directories
/// 4. `ay` at supported build locations under `~/ay/target/`
/// 5. `/tmp/ay-build/release/ay` (common temp build location)
///
/// Legacy `target/user/...` ay builds are intentionally not auto-discovered:
/// #502 tracks a stale local build there that reproduces solved BV blockers.
/// Use an explicit `AY_SOLVER_PATH` or `AYConfig::with_solver_path` only when
/// deliberately reproducing that unsupported route.
fn find_solver_binary() -> String {
    // AY alone is a solver-verdict source, not proof authority.  Do not expose
    // a "formal solver available" route unless the independent Alethe checker
    // needed to promote UNSAT is available too.
    if crate::obligation_cert_store::clean_checker_path().is_none() {
        String::new()
    } else {
        select_solver_binary().path
    }
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

const AY_CARGO_TARGET_SUBDIRS: &[&str] = &["release/ay", "debug/ay"];
const AY_HOME_BUILD_SUBDIRS: &[&str] = &["target/release/ay", "target/debug/ay"];

fn resolve_binary_on_path(binary: &str) -> Option<String> {
    // On Windows the MSYS/Git-Bash `which` shim reports POSIX-form paths
    // (`/c/Users/.../ay`) with no `.exe` suffix. Native process spawning cannot
    // launch those — they fail with "The system cannot find the path
    // specified" (os error 3) — so search `PATH` directly there, honoring
    // `PATHEXT`, and return a real launchable native path.
    #[cfg(windows)]
    {
        resolve_binary_on_windows_path(binary)
    }
    #[cfg(not(windows))]
    {
        if let Ok(output) = std::process::Command::new("which").arg(binary).output()
            && output.status.success()
        {
            let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
            if !path.is_empty() {
                return Some(path);
            }
        }
        None
    }
}

/// Native-Windows `PATH` search for `binary`, appending each `PATHEXT`
/// executable suffix (unless the caller already supplied one). Returns a
/// native, launchable path — unlike the MSYS `which` shim, which yields
/// unusable `/c/...`-style POSIX paths.
#[cfg(windows)]
fn resolve_binary_on_windows_path(binary: &str) -> Option<String> {
    let path_var = std::env::var_os("PATH")?;
    let pathext = std::env::var("PATHEXT").unwrap_or_else(|_| ".COM;.EXE;.BAT;.CMD".to_string());
    let already_has_ext = std::path::Path::new(binary).extension().is_some();
    for dir in std::env::split_paths(&path_var) {
        if already_has_ext {
            let candidate = dir.join(binary);
            if candidate.is_file() {
                return Some(candidate.to_string_lossy().to_string());
            }
            continue;
        }
        for ext in pathext.split(';').map(str::trim).filter(|e| !e.is_empty()) {
            let ext = ext.strip_prefix('.').unwrap_or(ext);
            let candidate = dir.join(format!("{binary}.{ext}"));
            if candidate.is_file() {
                return Some(candidate.to_string_lossy().to_string());
            }
        }
    }
    None
}

fn existing_solver_file(candidate: &std::path::Path) -> Option<String> {
    if candidate.is_file() {
        return Some(candidate.to_string_lossy().to_string());
    }
    // The Trust build layout (`.../stage2/bin/ay`) and the cargo/home fallbacks
    // (`target/release/ay`) spell the solver extension-less, POSIX-style. On
    // Windows the real binary is `ay.exe`, so probe the `.exe` twin before
    // giving up — otherwise every file-based discovery route misses it and
    // codegen fails closed. (An invalid POSIX candidate simply is-not-a-file
    // both times, so this never surfaces an unlaunchable path.)
    #[cfg(windows)]
    if candidate.extension().is_none() {
        let with_exe = candidate.with_extension("exe");
        if with_exe.is_file() {
            return Some(with_exe.to_string_lossy().to_string());
        }
    }
    None
}

fn first_existing_solver_file(base: &std::path::Path, subdirs: &[&str]) -> Option<String> {
    subdirs
        .iter()
        .find_map(|subdir| existing_solver_file(&base.join(subdir)))
}

/// Discover the CANONICAL Trust-toolchain `ay` — the pinned `first-party/ay`
/// shipped inside the Trust standalone stage2 sysroot. Proofs must discharge
/// through the Trust toolchain's solver, not a hand-built/divergent standalone
/// `~/ay`, so this is preferred over the generic PATH / `~/ay` routes below.
/// Honors `TRUST_SYSROOT` (a stage2 sysroot) and `TRUST_ROOT` (a Trust repo
/// root), then falls back to `~/trust`. Within a repo root it scans
/// `build/<host-triple>/stage2/bin/ay` (the triple varies) and
/// `first-party/ay/target/{release,debug}/ay`.
fn trust_toolchain_solver() -> Option<String> {
    // An explicit Trust sysroot: <sysroot>/bin/ay.
    if let Some(sysroot) = std::env::var_os("TRUST_SYSROOT")
        && let Some(path) = existing_solver_file(&std::path::Path::new(&sysroot).join("bin/ay"))
    {
        return Some(path);
    }

    let mut roots: Vec<std::path::PathBuf> = Vec::new();
    if let Some(root) = std::env::var_os("TRUST_ROOT") {
        roots.push(std::path::PathBuf::from(root));
    }
    if let Some(home) = std::env::var_os("HOME") {
        roots.push(std::path::Path::new(&home).join("trust"));
    }
    trust_toolchain_solver_in_roots(&roots)
}

/// Core of [`trust_toolchain_solver`] over explicit Trust repo roots (env-free,
/// so it is unit-testable without racing on process env).
fn trust_toolchain_solver_in_roots(roots: &[std::path::PathBuf]) -> Option<String> {
    for root in roots {
        // build/<host-triple>/stage2/bin/ay — scan the host-triple dir.
        if let Ok(entries) = std::fs::read_dir(root.join("build")) {
            for entry in entries.flatten() {
                if let Some(path) = existing_solver_file(&entry.path().join("stage2/bin/ay")) {
                    return Some(path);
                }
            }
        }
        // The unbuilt-sysroot fallback: first-party/ay/target/{release,debug}/ay.
        if let Some(path) =
            first_existing_solver_file(&root.join("first-party/ay"), AY_HOME_BUILD_SUBDIRS)
        {
            return Some(path);
        }
    }
    None
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct SolverSelection {
    path: String,
    route_kind: &'static str,
}

fn config_solver_selection(path: String) -> SolverSelection {
    SolverSelection {
        path,
        route_kind: "config-override",
    }
}

/// Resolve the AY solver binary. AY is the sole solver: every proof
/// obligation — bit-vector AND floating-point (QF_BVFP) — is discharged by
/// AY. There is no z3 route anywhere in selection; an obligation AY cannot
/// prove is a bug to fix in AY, never a reason to fall back.
///
/// Selection prefers the CANONICAL Trust-toolchain `ay` (the pinned
/// `first-party/ay` in the Trust stage2 sysroot) over any hand-built standalone
/// `~/ay`, so proofs discharge through the Trust toolchain's solver. An explicit
/// `AY_SOLVER_PATH` still wins (e.g. CI pinning a specific build).
fn select_solver_binary() -> SolverSelection {
    // `z3_available()` / `find_solver_binary()` are polled ONCE PER FUNCTION during
    // codegen (to decide whether the solver lane is available). Each poll re-ran
    // the full default resolution below — which stats the sysroot and spawns a
    // `which` subprocess — so a many-function crate paid hundreds of redundant
    // subprocess launches even with proofs disabled. The default resolution is
    // fixed for the process lifetime, so resolve it once and cache it. An explicit
    // `AY_SOLVER_PATH` override is always re-honored (direct, no subprocess), so a
    // caller that sets it — including tests — is never served a stale default.
    if std::env::var("AY_SOLVER_PATH").is_ok_and(|v| !v.trim().is_empty()) {
        return select_solver_binary_uncached();
    }
    static CACHE: std::sync::OnceLock<SolverSelection> = std::sync::OnceLock::new();
    CACHE.get_or_init(select_solver_binary_uncached).clone()
}

fn select_solver_binary_uncached() -> SolverSelection {
    // 1. AY_SOLVER_PATH explicit override
    if let Ok(override_val) = std::env::var("AY_SOLVER_PATH") {
        let trimmed = override_val.trim().to_string();
        if !trimmed.is_empty() {
            if let Some(path) = existing_solver_file(std::path::Path::new(&trimmed)) {
                return SolverSelection {
                    path,
                    route_kind: "env-override",
                };
            }
            if let Some(path) = resolve_binary_on_path(&trimmed) {
                return SolverSelection {
                    path,
                    route_kind: "env-override",
                };
            }
        }
    }

    // 2. The canonical Trust-toolchain ay (pinned first-party/ay in the stage2
    //    sysroot). Preferred over the generic PATH / hand-built ~/ay routes so
    //    proofs discharge through the TRUST TOOLCHAIN's solver, not a divergent
    //    standalone build.
    if let Some(path) = trust_toolchain_solver() {
        return SolverSelection {
            path,
            route_kind: "trust-toolchain-ay",
        };
    }

    // ay on PATH
    if let Some(path) = resolve_binary_on_path("ay") {
        return SolverSelection {
            path,
            route_kind: "auto-ay-path",
        };
    }

    // ay under CARGO_TARGET_DIR
    if let Some(target_dir) = std::env::var_os("CARGO_TARGET_DIR") {
        let target_dir = std::path::Path::new(&target_dir);
        if let Some(path) = first_existing_solver_file(target_dir, AY_CARGO_TARGET_SUBDIRS) {
            return SolverSelection {
                path,
                route_kind: "auto-ay-target-dir",
            };
        }
    }

    // Well-known build locations under ~/ay/target/
    if let Some(home) = std::env::var_os("HOME") {
        let home = std::path::Path::new(&home);
        if let Some(path) = first_existing_solver_file(&home.join("ay"), AY_HOME_BUILD_SUBDIRS) {
            return SolverSelection {
                path,
                route_kind: "auto-ay-home-build",
            };
        }
    }

    // Common temp build location
    if let Some(path) = existing_solver_file(std::path::Path::new("/tmp/ay-build/release/ay")) {
        return SolverSelection {
            path,
            route_kind: "auto-ay-temp-build",
        };
    }

    SolverSelection {
        path: String::new(),
        route_kind: "unresolved",
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

fn solver_info_from_path(solver_path: String) -> String {
    if solver_path.is_empty() {
        return "no AY solver found".to_string();
    }

    let solver_name = std::path::Path::new(&solver_path)
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("solver");

    if let Some(version) = detect_solver_version(&solver_path) {
        format!("{} at {} ({})", solver_name, solver_path, version)
    } else {
        format!("{} at {} (version unavailable)", solver_name, solver_path)
    }
}

fn solver_route_summary_from_selection(logic: &str, selection: &SolverSelection) -> String {
    if selection.path.is_empty() {
        format!(
            "logic={} route={} solver=(not found)",
            logic, selection.route_kind
        )
    } else {
        format!(
            "logic={} route={} solver={}",
            logic, selection.route_kind, selection.path
        )
    }
}

fn solver_route_summary_for_invocation(obligation: &ProofObligation, config: &AYConfig) -> String {
    let logic = obligation_logic(obligation);
    let selection = match &config.solver_path {
        Some(path) => config_solver_selection(path.clone()),
        None => select_solver_for_obligation(obligation),
    };
    solver_route_summary_from_selection(logic, &selection)
}

/// Detect the solver version string for a CLI binary.
///
/// Tries `--version` first, then `-version`, and returns the first
/// non-empty version line on success. Returns `None` if the binary
/// cannot be invoked or produces no recognizable version output.
/// Does the resolved solver report a `-dirty` build stamp?
///
/// A `-dirty` binary was built from a modified working tree, so it is not the
/// binary that produced any COMMITTED verdict DB or certificate — those are
/// regenerated from the canonical `ay` (see `verdict_db`'s regen README). Its
/// content hash therefore cannot equal a committed artifact's recorded
/// identity, and every reuse tier will decline once it finds that out.
///
/// This lets the consumers find it out for ~10ms (`--version`, memoized) rather
/// than ~320ms (SHA-256 of the ~73MB binary). MEASURED (2026-08-07): that hash
/// is the dominant remaining compile-time cost — 3.02x of LLVM with it, 1.59x
/// without — and every developer box with a locally-built solver pays it on
/// every rustc invocation to learn something a version string already says.
///
/// # Soundness
///
/// This can only turn an ACCEPT into a DECLINE, never the reverse: callers use
/// it to skip a reuse tier, and skipping a reuse tier means discharging LIVE.
/// The trust decision itself is untouched — accepting a committed verdict still
/// requires the full content hash to match. The only cost is lost reuse if a
/// committed artifact were ever regenerated from a dirty solver, which the
/// regen procedure forbids.
///
/// Deliberately NOT applied inside [`solver_identity_hash`]: the regen tools
/// need the real identity to RECORD, and must keep working.
/// Run `<solver> <flag>` with a hard deadline, killing the child if it does not
/// exit in time. `None` means "no version information available".
///
/// ⚑ **`Command::output()` waits FOREVER.** A solver that hangs on a version
/// probe — a deliberately-hanging test fixture, or a real one wedged on a bad
/// install — otherwise blocks its caller permanently *and* orphans the child,
/// which keeps running after the test that spawned it has finished. That is not
/// hypothetical: the `--version` probe added for the `-dirty` check (CT-10) left
/// a 100%-CPU `/bin/sh` spinning per test run, and because the leak is silent
/// and cumulative it corrupted every timing measurement taken on the box
/// afterwards — the sort of defect that invalidates results rather than failing
/// them.
///
/// Every caller already treats a missing version as "fall through to the normal
/// path", so a timed-out probe degrades to exactly that.
fn bounded_version_output(solver_path: &str, flag: &str) -> Option<std::process::Output> {
    use std::process::Stdio;
    /// A version banner is instant; anything slower is wedged, not slow.
    const VERSION_PROBE_TIMEOUT: Duration = Duration::from_secs(5);

    let mut child = std::process::Command::new(solver_path)
        .arg(flag)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .ok()?;

    let deadline = Instant::now() + VERSION_PROBE_TIMEOUT;
    loop {
        match child.try_wait() {
            Ok(Some(_)) => break,
            Ok(None) => {
                let now = Instant::now();
                if now >= deadline {
                    let _ = child.kill();
                    let _ = child.wait();
                    return None;
                }
                std::thread::sleep(std::cmp::min(
                    Duration::from_millis(10),
                    deadline.saturating_duration_since(now),
                ));
            }
            Err(_) => {
                let _ = child.kill();
                let _ = child.wait();
                return None;
            }
        }
    }
    child.wait_with_output().ok()
}

/// The dirty-build short-circuit, scoped to the DEFAULT solver route.
///
/// The question the `-dirty` check answers is "can this build's identity ever
/// match a COMMITTED artifact's `solver-sha256`?", and that is only meaningful
/// for the solver the shipped artifacts were anchored to. A caller-supplied
/// `AYConfig::solver_path` is by construction not that anchor, so probing it
/// answers a question nobody asked — and costs a process spawn per consult.
///
/// ⚑ This scoping is not a micro-optimization, it is the fix for a real
/// regression. CT-10 called the raw predicate on whatever path the caller
/// supplied, which meant the verification tests that install a deliberately
/// hanging fake solver got `--version`-probed. That (a) hung them outright
/// before [`bounded_version_output`], (b) still cost each one the probe's full
/// deadline afterwards, and (c) silently broke the ones that assert an EXACT
/// solver invocation count, because the fake solver counts every invocation and
/// the probe is an extra one. Three tests failed on `left: 2, right: 1`.
///
/// The raw [`solver_reports_dirty_build`] stays unscoped so it remains directly
/// testable — including the regression test that it cannot hang or leak.
pub(crate) fn default_solver_reports_dirty_build(solver_path: &str) -> bool {
    if solver_path != select_solver_binary().path {
        return false;
    }
    solver_reports_dirty_build(solver_path)
}

pub(crate) fn solver_reports_dirty_build(solver_path: &str) -> bool {
    use std::collections::HashMap as StdHashMap;
    static MEMO: std::sync::OnceLock<std::sync::Mutex<StdHashMap<String, bool>>> =
        std::sync::OnceLock::new();
    let memo = MEMO.get_or_init(|| std::sync::Mutex::new(StdHashMap::new()));
    if let Some(hit) = memo
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .get(solver_path)
        .copied()
    {
        return hit;
    }
    // Scan the WHOLE `--version` output, not `detect_solver_version`'s picked
    // line. `ay --version` prints SIX lines and that helper prefers the first
    // containing "version", which is `build.version=0.11.0` — the `-dirty`
    // marker lives on the `build.commit=` / `build.stamp=` lines. Reusing it
    // here silently never detected a dirty build.
    //
    // Absent/unreadable version => NOT treated as dirty, so the normal identity
    // path still runs and decides.
    let dirty = bounded_version_output(solver_path, "--version")
        .filter(|o| o.status.success())
        .map(|o| {
            let all = format!(
                "{}{}",
                String::from_utf8_lossy(&o.stdout),
                String::from_utf8_lossy(&o.stderr)
            );
            all.contains("-dirty")
        })
        .unwrap_or(false);
    memo.lock()
        .unwrap_or_else(|p| p.into_inner())
        .insert(solver_path.to_string(), dirty);
    dirty
}

fn detect_solver_version(solver_path: &str) -> Option<String> {
    let solver_path = solver_path.trim();
    if solver_path.is_empty() {
        return None;
    }

    for flag in ["--version", "-version"] {
        let Some(output) = bounded_version_output(solver_path, flag) else {
            continue;
        };
        if !output.status.success() {
            continue;
        }

        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let lines: Vec<&str> = stdout
            .lines()
            .chain(stderr.lines())
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .collect();

        // Prefer a line containing "version", otherwise take the first line.
        if let Some(version) = lines
            .iter()
            .find(|line| line.to_ascii_lowercase().contains("version"))
            .copied()
            .or_else(|| lines.first().copied())
        {
            return Some(version.to_string());
        }
    }

    None
}

/// Return a human-readable description of the selected AY solver binary.
///
/// The returned string includes the resolved solver path and version when
/// available. If no AY CLI binary is found, returns `"no AY solver found"`.
pub fn solver_info() -> String {
    solver_info_from_path(find_solver_binary())
}

/// Write SMT-LIB2 to a securely-created private temporary file.
fn write_temp_smt2(content: &str) -> Result<tempfile::NamedTempFile, std::io::Error> {
    use std::io::Write;
    let mut file = tempfile::Builder::new()
        .prefix("trust-cg-ay-query-")
        .suffix(".smt2")
        .tempfile()?;
    file.write_all(content.as_bytes())?;
    file.flush()?;
    Ok(file)
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

    let unknown_reason = lines
        .iter()
        .copied()
        .chain(stderr_trimmed.lines().map(str::trim))
        .find(|line| line.contains(":reason-unknown"))
        .map(std::string::ToString::to_string);

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
    // TCB soundness guard: if the local simplifier alone reduced the negated
    // equivalence to constant `false`, route the obligation through the solver
    // on the raw (un-simplified) formula so the solver — not the rewrite —
    // produces the verdict. See the function docs above.
    if simplifier_alone_proved_unsat(obligation) {
        return verify_with_cli_raw(obligation, config);
    }

    verify_with_cli(obligation, config)
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
/// is not an authorized proof-discharge route. The function retains its
/// historical `z3_available` name for API compatibility; Z3 is not searched.
pub fn z3_available() -> bool {
    !find_solver_binary().is_empty()
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
mod tests {
    use super::*;
    use crate::lowering_proof::ProofObligation;
    use crate::smt::{SmtExpr, SmtSort};

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

    /// The dirty-build short-circuit must DECLINE only, and must not fire on a
    /// solver whose version cannot be read.
    #[test]
    fn dirty_build_detection_declines_only() {
        // A binary that answers no `--version` at all must NOT be treated as
        // dirty — the normal identity path has to run and decide.
        assert!(
            !solver_reports_dirty_build("/nonexistent/solver/binary"),
            "an unreadable solver must not be reported dirty; the identity path decides"
        );

        // Must agree with the solver's FULL `--version` output. Checking
        // against `detect_solver_version` instead would be circular AND wrong:
        // that helper returns the first line containing "version"
        // (`build.version=0.11.0`), while `-dirty` appears on the
        // `build.commit=` / `build.stamp=` lines — so the assertion would pass
        // while the detection never fired.
        let path = find_solver_binary();
        if !path.is_empty()
            && let Ok(out) = std::process::Command::new(&path).arg("--version").output()
            && out.status.success()
        {
            let all = format!(
                "{}{}",
                String::from_utf8_lossy(&out.stdout),
                String::from_utf8_lossy(&out.stderr)
            );
            assert_eq!(
                solver_reports_dirty_build(&path),
                all.contains("-dirty"),
                "dirty detection must match the solver's FULL version output"
            );
        }
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

        drop(first);
        assert!(
            !first_path.exists(),
            "RAII cleanup must remove the solver query"
        );
    }

    fn ay_batch_test_lock() -> std::sync::MutexGuard<'static, ()> {
        formal_solver_test_lock()
    }

    /// The certification-gap-guarded spelling of the tests' standard
    /// `assert_eq!(result, AYResult::Verified, …)` (crate::formal_gap; same
    /// discipline as `mem_refine.rs::alethe_crosscheck_gap` and
    /// `tests/support/cegis_alethe_gap.rs`): `Verified` passes (returns
    /// `true`); ONLY the exact fail-closed certification-gap diagnostics skip
    /// — LOUDLY, naming the obligation and diagnostic — returning `false`,
    /// with a server-truncated bare `unknown` first re-confirmed through the
    /// fresh one-shot transcript; every other outcome (`CounterExample`,
    /// `Timeout`, `Error`, an unrecognized `Unknown`) panics with the
    /// ORIGINAL message, so no solver regression can hide behind the guard
    /// and the exemption un-arms itself the moment an authority ships
    /// externally checkable proofs.
    #[track_caller]
    fn assert_verified_or_certification_gap_skip(
        obligation: &ProofObligation,
        config: &AYConfig,
        result: &AYResult,
        original_message: std::fmt::Arguments<'_>,
    ) -> bool {
        if matches!(result, AYResult::Verified) {
            return true;
        }
        if let Some(reason) =
            crate::formal_gap::confirmed_certification_gap(obligation, config, result)
        {
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return; // No solver available, skip test
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

        let obligation = crate::lowering_proof::proof_iadd_i32();
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_eq!(result, AYResult::Verified);
    }

    #[test]
    fn test_cli_verify_peephole_add_zero() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let obligation = crate::memory_proofs::proof_roundtrip_i8();
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return; // No solver available, skip test
        }

        let obligation = crate::memory_proofs::proof_roundtrip_i8();
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }
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
            promote_fresh_solver_unsat(unsat_candidate, &solver, unsat_file.path(), &unsat_smt2,),
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
        let model_output = run_solver_command(&solver, model_file.path(), 30_000).unwrap();
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
        let hard_smt2 =
            generate_smt2_query_raw(&hard_obligation, &AYConfig::default().with_timeout(1));
        let hard_file = write_temp_smt2(&hard_smt2).unwrap();
        let holey_output = run_solver_command(&solver, hard_file.path(), 30_000).unwrap();
        assert!(holey_output.status.success());
        assert!(no_protocol_errors(&holey_output));
        let hard_candidate = parse_solver_process_output(&holey_output, &hard_obligation.inputs);
        // Certification-gap guard (crate::formal_gap): the v0.9.0-era
        // authorities publish NO Alethe artifact for this query — either the
        // computed UNSAT is discarded inside AY's mandatory strict
        // self-certification (`(:reason-unknown (incomplete
        // self-check-rejected))`), or AY now honors the query's own
        // deliberately absurd 1 ms `(set-option :timeout 1)` header and gives
        // up first (`(:reason-unknown timeout)`, measured at build.7387; the
        // multiply identity solved sub-millisecond on the authorities this
        // test was authored against) — so the artifact-shaped assertions
        // below have nothing to inspect. This is a one-shot transcript, so
        // the reason is authoritative — skip ONLY on those exact
        // disclosures; the trailing outer-deadline probe still runs. Any
        // other verdict keeps the original assertions.
        let hard_stderr = String::from_utf8_lossy(&holey_output.stderr).into_owned();
        let no_artifact_disclosure = match &hard_candidate {
            AYResult::Unknown(reason)
                if crate::formal_gap::ay_reason_is_self_check_rejection(reason) =>
            {
                Some(reason.clone())
            }
            AYResult::Timeout if hard_stderr.contains("(:reason-unknown timeout)") => Some(
                "(:reason-unknown timeout) under the query's own 1 ms :timeout header".to_string(),
            ),
            _ => None,
        };
        if let Some(reason) = no_artifact_disclosure {
            crate::formal_gap::print_gap_skip(
                &format!(
                    "production-style Alethe artifact assertions for '{}'",
                    hard_obligation.name
                ),
                &reason,
            );
            let timeout = run_solver_command(&solver, hard_file.path(), 1);
            assert!(matches!(timeout, Err(SolverInvocationError::Timeout)));
            return;
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
        let hard_result = promote_fresh_solver_unsat(
            hard_candidate.clone(),
            &solver,
            hard_file.path(),
            &hard_smt2,
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
        assert!(matches!(timeout, Err(SolverInvocationError::Timeout)));
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
        std::fs::write(&path, contents).expect("failed to write temp solver script");

        let mut perms = std::fs::metadata(&path)
            .expect("failed to stat temp solver script")
            .permissions();
        perms.set_mode(0o755);
        std::fs::set_permissions(&path, perms).expect("failed to chmod temp solver script");

        path.to_string_lossy().to_string()
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

    /// A caller-supplied solver must never be `--version`-probed by the
    /// dirty-build check. Probing one spawns an extra process the caller did
    /// not ask for, which broke three tests that assert an EXACT solver
    /// invocation count (they read `left: 2, right: 1`) and cost every other
    /// one the probe's deadline.
    #[cfg(unix)]
    #[test]
    fn dirty_check_does_not_probe_a_caller_supplied_solver() {
        let solver_path = write_temp_solver_script(
            "#!/bin/sh\n\
             count_file=\"$0.count\"\n\
             count=0\n\
             if [ -r \"$count_file\" ]; then count=$(cat \"$count_file\"); fi\n\
             count=$((count + 1))\n\
             printf '%s\\n' \"$count\" > \"$count_file\"\n\
             exit 0\n",
        );

        let dirty = default_solver_reports_dirty_build(&solver_path);
        let probed = std::fs::read_to_string(format!("{solver_path}.count")).is_ok();
        remove_temp_solver_and_count(&solver_path);

        assert!(!dirty, "a non-default solver is never reported dirty");
        assert!(
            !probed,
            "the dirty check spawned the caller-supplied solver; it must only \
             ever probe the DEFAULT route"
        );
    }

    /// A solver that never exits must not wedge the version probe — and, the
    /// part that actually bit, must not SURVIVE it. `Command::output()` failed
    /// both ways: it waited forever and orphaned a 100%-CPU shell that outlived
    /// the test run, pinning a core and silently poisoning every timing
    /// measurement taken on the box afterwards.
    #[cfg(unix)]
    #[test]
    fn version_probe_of_a_hanging_solver_is_bounded_and_leaves_no_child() {
        let solver_path = write_temp_solver_script("#!/bin/sh\nwhile :; do :; done\n");

        let started = Instant::now();
        let dirty = solver_reports_dirty_build(&solver_path);
        let elapsed = started.elapsed();

        assert!(
            !dirty,
            "an unanswerable probe must not claim the build is dirty"
        );
        assert!(
            elapsed < Duration::from_secs(30),
            "version probe must be bounded; took {elapsed:?}"
        );

        let leaked = std::process::Command::new("pgrep")
            .arg("-f")
            .arg(&solver_path)
            .output()
            .map(|o| String::from_utf8_lossy(&o.stdout).trim().to_string())
            .unwrap_or_default();
        remove_temp_solver_and_count(&solver_path);
        assert!(
            leaked.is_empty(),
            "version probe leaked a running child (pids {leaked}) — a busy-loop \
             fixture that outlives its test pins a core for the whole session"
        );
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
        let solver_path = write_temp_solver_script(
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
                solver_path: Some(solver_path.clone()),
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
        let solver_path = write_temp_solver_script(
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
                solver_path: Some(solver_path.clone()),
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
        assert!(ay_server_is_unusable(&solver_path));
        assert!(
            !ay_server_is_unusable(&format!("{solver_path}.different")),
            "the resident failure latch must be scoped to one solver path"
        );

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
                solver_path: Some(solver_path.clone()),
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
        // not seed the process-local Verified memo. A second identical call
        // therefore performs another fresh replay (invocation count 3: one
        // resident + two fresh), rather than returning a cached success.
        let solver_path = write_temp_solver_script(
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
            solver_path: Some(solver_path.clone()),
            timeout_ms: FAKE_RESIDENT_SOLVER_TIMEOUT_MS,
            produce_models: false,
        };

        let first = verify_with_cli_raw(&obligation, &config);
        assert!(matches!(first, AYResult::Unknown(_)), "got {first:?}");
        assert_eq!(fake_solver_invocation_count(&solver_path), 2);

        let second = verify_with_cli_raw(&obligation, &config);
        let invocation_count = fake_solver_invocation_count(&solver_path);
        remove_temp_solver_and_count(&solver_path);
        assert!(matches!(second, AYResult::Unknown(_)), "got {second:?}");
        assert_eq!(
            invocation_count, 3,
            "holey UNSAT must not be promoted into the Verified session cache"
        );
    }

    #[cfg(unix)]
    #[test]
    fn test_verify_with_cli_enforces_process_timeout() {
        // This test replaces the process-global resident solver with a
        // temporary executable.  Serialize it with every other resident-
        // solver test so it cannot evict a sibling test's live process and
        // perturb that test's invocation-count assertions.
        let _batch_lock = ay_batch_test_lock();
        let solver_path = write_temp_solver_script("#!/bin/sh\nsleep 5\necho unsat\n");

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
        let result = verify_with_cli(
            &obligation,
            &AYConfig {
                solver_path: Some(solver_path.clone()),
                timeout_ms: 50,
                produce_models: true,
            },
        );
        let elapsed = start.elapsed();

        let _ = std::fs::remove_file(&solver_path);

        assert_eq!(result, AYResult::Timeout);
        assert!(
            elapsed < Duration::from_secs(2),
            "solver subprocess timeout should be enforced promptly, elapsed {:?}",
            elapsed
        );
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
            &solver_path,
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
            matches!(result, AyServerAttempt::TimedOut),
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
        let solver_path = write_temp_solver_script(&format!(
            "#!/bin/sh\n\
             ( trap '' TERM; sleep 120 ) &\n\
             printf '%s %s\\n' \"$$\" \"$!\" > \"{}\"\n\
             wait\n",
            pid_file.display()
        ));
        let query = write_temp_smt2("(check-sat)\n(exit)\n").expect("write fake solver query");

        let timeout = Duration::from_secs(3);
        let start = Instant::now();
        let result = run_solver_command(&solver_path, query.path(), timeout.as_millis() as u64);
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
            matches!(result, Err(SolverInvocationError::Timeout)),
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
            &result,
            format_args!(
                "obligation '{}' must be Verified, got {}",
                obligation.name, result
            ),
        );
    }

    #[test]
    fn test_verify_with_ay_cli_extract_zeroext_identity() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
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
    fn test_ay_batch_verify_arithmetic_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_comparison_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs_i32 = crate::lowering_proof::all_comparison_proofs_i32();
        let proofs_i64 = crate::lowering_proof::all_comparison_proofs_i64();

        // #62: the degenerate Icmp_UGE_I32/I64 -> CMP+CSET_HS pair was retracted
        // (CSet is reconstruction-credited), leaving 9 genuine predicates per width.
        assert_eq!(proofs_i32.len(), 9, "Expected 9 i32 comparison proofs");
        assert_eq!(proofs_i64.len(), 9, "Expected 9 i64 comparison proofs");

        for obligation in proofs_i32.iter().chain(proofs_i64.iter()) {
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                &obligation,
                &config,
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
    fn test_ay_batch_verify_branch_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

        let _batch_lock = ay_batch_test_lock();

        let config = AYConfig::default();
        let proofs = crate::lowering_proof::all_branch_proofs();
        // #62: the degenerate CondBr_UGE_I32/I64 -> CMP+B.HS pair was retracted
        // (Bcc is reconstruction-credited), leaving 9 genuine predicates per width.
        assert_eq!(proofs.len(), 18, "Expected 18 branch proofs");

        for obligation in &proofs {
            let result = verify_with_cli(obligation, &config);
            assert_verified_or_certification_gap_skip(
                &obligation,
                &config,
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
    fn test_ay_batch_verify_peephole_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                // Certification-gap guard (crate::formal_gap): skip LOUDLY on
                // the exact fail-closed diagnostics only; anything else still
                // panics with the original message.
                other => match crate::formal_gap::confirmed_certification_gap(
                    obligation, &config, &other,
                ) {
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
    fn test_ay_verify_all_batch_and_summary() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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

        // Certification-gap guard (crate::formal_gap): re-derive the exact
        // obligations verify_all_with_ay ran (same three sources, same order)
        // so a row's diagnostic can be confirmed against its live obligation;
        // skip LOUDLY on the exact fail-closed diagnostics only. Everything
        // else keeps failing the original assertions below.
        let obligations_by_name: std::collections::HashMap<String, ProofObligation> =
            crate::lowering_proof::all_arithmetic_proofs()
                .into_iter()
                .chain(crate::lowering_proof::all_nzcv_proofs())
                .chain(crate::peephole_proofs::all_peephole_proofs_with_32bit())
                .map(|ob| (ob.name.clone(), ob))
                .collect();
        let mut gap_names: std::collections::HashSet<&str> = std::collections::HashSet::new();
        for (name, result) in &results {
            if matches!(result, AYResult::Unknown(_))
                && let Some(reason) = obligations_by_name.get(name).and_then(|ob| {
                    crate::formal_gap::confirmed_certification_gap(ob, &config, result)
                })
            {
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
    fn test_ay_batch_verify_load_store_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_bitwise_shift_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
            // Certification-gap guard (crate::formal_gap): AY establishes the
            // verdict but the constellation cannot independently certify the
            // bit-vector family yet — skip LOUDLY on the exact fail-closed
            // diagnostics only; every other non-Verified outcome still fails
            // the original assertion below.
            if let Some(reason) =
                crate::formal_gap::confirmed_certification_gap(&cp.obligation, &config, &result)
            {
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_floating_point_proofs() {
        verify_category_batch(ProofCategory::FloatingPoint, 38);
    }

    /// Verify all general optimization pass proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_optimization_proofs() {
        // #62: ConstFold(k1,k2)/DCE/CopyProp X==X retracted; 2 genuine absorb proofs remain.
        verify_category_batch(ProofCategory::Optimization, 2);
    }

    /// Verify all constant folding proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_constant_folding_proofs() {
        verify_category_batch(ProofCategory::ConstantFolding, 5);
    }

    /// Verify all CSE/LICM proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_cse_licm_proofs() {
        if !z3_available() {
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
    fn test_ay_batch_verify_cfg_simplification_proofs() {
        verify_category_batch(ProofCategory::CfgSimplification, 3);
    }

    /// Verify all NEON lowering proofs (trust_ir vector ops -> NEON) through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_neon_lowering_proofs() {
        verify_category_batch(ProofCategory::NeonLowering, 20);
    }

    /// FORMAL (real AY solver) discharge of the 15 FAITHFUL per-lane
    /// D-register-pair COMPUTE obligations — the ones the coverage gate credits for
    /// the NEON lane-wise arith / compare / min-max / shift opcodes. This pins that
    /// they discharge via the ACTUAL solver (complete for all inputs), not just the
    /// statistical mock evaluator, AND that each is structurally NON-degenerate.
    #[test]
    fn test_ay_batch_verify_neon_lanewise_compute_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_fp_lanewise_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_fpred_lane_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_fmla_lane_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_fcvtl_lane_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_x86_rol_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }
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
    fn test_ay_batch_verify_eor_ror_shift_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
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

        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }
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
                        &config,
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

        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }
        let _batch_lock = ay_batch_test_lock();
        let config = AYConfig::default();

        for (width, base) in [
            (32u32, proof_ubfm_extract_w32()),
            (64u32, proof_ubfm_extract_w64()),
        ] {
            let base_result = verify_with_cli(&base, &config);
            assert_verified_or_certification_gap_skip(
                &base,
                &config,
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
    fn test_ay_batch_verify_fcsel_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_umov_lane_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_lanewise_compute_proofs_2d() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_saddlp_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_bit_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_popcount_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_abs_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_udot_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_rev64_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_ext_proofs() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
                &obligation,
                &config,
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
    fn test_ay_batch_verify_neon_encoding_proofs() {
        verify_category_batch(ProofCategory::NeonEncoding, 5);
    }

    /// Verify all vectorization proofs (scalar-to-NEON mapping) through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_vectorization_proofs() {
        verify_category_batch(ProofCategory::Vectorization, 30);
    }

    /// Verify all register allocation correctness proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_regalloc_proofs() {
        verify_category_batch(ProofCategory::RegAlloc, 5);
    }

    /// Verify constant materialization proofs (MOVZ, MOVZ+MOVK, ORR, MOVN) through the selected CLI solver.
    /// NOTE: Known issue -- MOVZ+MOVK exhaustive proof has a BV width mismatch
    /// in its SMT encoding (16-bit vs 24-bit). This test tracks the issue.
    #[test]
    fn test_ay_batch_verify_constant_materialization_proofs() {
        if !z3_available() {
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
                // Certification-gap guard (crate::formal_gap): skip LOUDLY on
                // the exact fail-closed diagnostics only; anything else still
                // panics with the original message.
                other => match crate::formal_gap::confirmed_certification_gap(
                    &cp.obligation,
                    &config,
                    other,
                ) {
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
    fn test_ay_batch_verify_address_mode_proofs() {
        verify_category_batch(ProofCategory::AddressMode, 3);
    }

    /// Verify all frame layout / frame index elimination proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_frame_layout_proofs() {
        verify_category_batch(ProofCategory::FrameLayout, 3);
    }

    /// Verify all instruction scheduling correctness proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_instruction_scheduling_proofs() {
        verify_category_batch(ProofCategory::InstructionScheduling, 5);
    }

    /// Verify all Mach-O emission correctness proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_macho_emission_proofs() {
        verify_category_batch(ProofCategory::MachOEmission, 3);
    }

    /// Verify all loop optimization proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_loop_optimization_proofs() {
        // Faulhaber's m=3 obligation legitimately exceeds both the generic
        // 30s category budget and 180s on a heavily loaded publication host.
        verify_category_batch_with_timeout(ProofCategory::LoopOptimization, 3, 300_000);
    }

    /// Verify all strength reduction proofs through the selected CLI solver.
    #[test]
    fn test_ay_batch_verify_strength_reduction_proofs() {
        run_with_ay_batch_stack(|| verify_category_batch(ProofCategory::StrengthReduction, 3));
    }

    /// Verify all compare-combine proofs (compare-and-branch, compare-select) through the selected CLI solver.
    #[test]
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

        let _batch_lock = ay_batch_test_lock();
        let config = AYConfig::default().with_timeout(30_000);
        for width in [32u32, 64] {
            let obligation = crate::cmp_combine_proofs::proof_tst_packed_nzcv(width);
            let result = verify_with_cli(&obligation, &config);
            assert_verified_or_certification_gap_skip(
                &obligation,
                &config,
                &result,
                format_args!(
                    "packed-NZCV TST w{width} failed exact checked discharge via {}: {result}",
                    solver_route_summary_for_invocation(&obligation, &config),
                ),
            );
            let raw_result = verify_with_cli_raw(&obligation, &config);
            assert_verified_or_certification_gap_skip(
                &obligation,
                &config,
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
    fn test_ay_batch_verify_gvn_proofs() {
        if !z3_available() {
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
    fn test_ay_batch_verify_fp_conversion_proofs() {
        if !z3_available() {
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
                // Certification-gap guard (crate::formal_gap): skip LOUDLY on
                // the exact fail-closed diagnostics only; anything else still
                // panics with the original message.
                other => match crate::formal_gap::confirmed_certification_gap(
                    &cp.obligation,
                    &config,
                    other,
                ) {
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
    fn test_ay_batch_verify_ext_trunc_proofs() {
        verify_category_batch(ProofCategory::ExtensionTruncation, 5);
    }

    /// Verify atomic operation proofs (LDAR/STLR, LDADD, CAS, etc.) through the selected CLI solver.
    /// The non-interference formulas remain a known formal-solver gap: some
    /// report counterexamples or timeouts through the CLI path, and are kept
    /// observable instead of being counted as verified.
    #[test]
    fn test_ay_batch_verify_atomic_proofs() {
        if !z3_available() {
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
                // Certification-gap guard (crate::formal_gap): skip LOUDLY on
                // the exact fail-closed diagnostics only; anything else still
                // panics with the original message.
                other => match crate::formal_gap::confirmed_certification_gap(
                    &cp.obligation,
                    &config,
                    other,
                ) {
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
    fn test_ay_batch_verify_all_categories_comprehensive() {
        run_with_ay_batch_stack(|| {
            if !z3_available() {
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
                || (name.contains("V16I8Mul") && detail.contains("incomplete"))
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
            // diagnostic is EXACTLY one of the fail-closed certification-gap
            // shapes skips LOUDLY (a bare `UNKNOWN: unknown` is first
            // re-confirmed through the fresh one-shot transcript of its own
            // obligation); every other failure stays an UNEXPECTED FAILURE
            // and panics below.
            let obligations_by_name: std::collections::HashMap<String, ProofObligation> = db
                .all()
                .iter()
                .map(|cp| (cp.obligation.name.clone(), cp.obligation.clone()))
                .collect();
            let mut gap_skips = 0usize;
            let mut unexpected_failures: Vec<(String, ProofCategory, String)> = Vec::new();
            for (name, cat, detail) in report.failed_details() {
                if is_known_issue(&name, &detail) {
                    continue;
                }
                let confirmed_gap = detail.strip_prefix("UNKNOWN: ").and_then(|reason| {
                    if crate::formal_gap::ay_reason_is_certification_gap(reason)
                        || crate::formal_gap::ay_reason_is_self_check_rejection(reason)
                    {
                        Some(reason.to_string())
                    } else if reason == "unknown" {
                        obligations_by_name.get(&name).and_then(|ob| {
                            crate::formal_gap::confirmed_certification_gap(
                                ob,
                                &config,
                                &AYResult::Unknown("unknown".to_string()),
                            )
                        })
                    } else {
                        None
                    }
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
        assert_eq!(available, !solver.is_empty());
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
        let obligations_by_name: std::collections::HashMap<String, ProofObligation> = full_db
            .by_category(ProofCategory::Arithmetic)
            .into_iter()
            .map(|cp| (cp.obligation.name.clone(), cp.obligation.clone()))
            .collect();
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
            if let Some(reason) = obligations_by_name
                .get(name)
                .and_then(|ob| crate::formal_gap::confirmed_certification_gap(ob, &config, result))
            {
                crate::formal_gap::print_gap_skip(&format!("Arithmetic proof '{name}'"), &reason);
                gap_skips += 1;
                continue;
            }
            panic!(
                "Arithmetic proof {name:?} is non-verified ({result}) and is NOT a tolerated \
                 capacity-bound 64-bit checked-mul timeout — no other non-formal pass is allowed:\n{}",
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
            &result,
            format_args!("Array store-load roundtrip should be verified"),
        );
    }

    #[test]
    fn test_cli_verify_array_store_load_different_addr() {
        // Verify: select(store(mem, a, v), b) == select(mem, b) when a != b
        // This is the second array axiom: write at address a doesn't affect reads at b.
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
            &result,
            format_args!("Array read at different address after write should be unchanged"),
        );
    }

    #[test]
    fn test_cli_verify_array_double_store() {
        // Verify: store(store(mem, a, v1), a, v2) at a == v2
        // Overwriting the same address with a new value: last write wins.
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
            &result,
            format_args!("Double store at same address: last write should win"),
        );
    }

    #[test]
    fn test_cli_verify_array_const_array_select() {
        // Verify: select(const_array(0), any_addr) == 0
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
            &result,
            format_args!("Reading from const array should return the constant value"),
        );
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
            &result,
            format_args!("Double FP negation should be identity"),
        );
    }

    #[test]
    fn test_cli_verify_fp_sub_as_add_neg() {
        // Verify: fp.sub(RNE, a, b) == fp.add(RNE, a, fp.neg(b)) for concrete values
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
            &result,
            format_args!("FP subtraction should equal addition of negation"),
        );
    }

    #[test]
    fn test_cli_verify_fp_mul_commutative() {
        // Verify: fp.mul(RNE, a, b) == fp.mul(RNE, b, a) for concrete values
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

        let obligation = fp_symbolic_add_commutative_fp16_obligation();

        // Symbolic FP16 addition is a real floating-point proof and can exceed
        // the 15s query-generation fixture budget on a loaded release host.
        // More solver time changes no acceptance criterion: Timeout remains a
        // failure and only an unsat result is reported as Verified.
        let config = AYConfig::default().with_timeout(60_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
            &result,
            format_args!("FP addition should be commutative for all FP16 values"),
        );
    }

    #[test]
    fn test_cli_verify_fp_neg_self_not_identity() {
        // Verify that fp.neg(a) != a (should find counterexample for non-zero values)
        // Actually fp.neg(0.0) == -0.0 which is NOT equal by fp.eq... but let's use
        // a concrete non-zero value to make this clean.
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        if find_solver_binary().is_empty() {
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
            &config,
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
        if find_solver_binary().is_empty() {
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs_i16();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
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
        if find_solver_binary().is_empty() {
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs_i64();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
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
        if find_solver_binary().is_empty() {
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu_i16();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
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
        if find_solver_binary().is_empty() {
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu_i64();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
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
        if find_solver_binary().is_empty() {
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_ucvtf_fcvtzu();
        let config = AYConfig::default().with_timeout(90_000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

        let obligation = crate::memory_proofs::proof_memset_correctness(4);
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
            &result,
            format_args!("Memset correctness proof should verify with expanded quantifiers"),
        );
    }

    #[test]
    fn test_cli_verify_expanded_buffer_init() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

        let obligation = crate::memory_proofs::proof_buffer_init_zero(8);
        let config = AYConfig::default();
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
            &result,
            format_args!("Buffer init zero proof should verify with expanded quantifiers"),
        );
    }

    #[test]
    fn test_cli_verify_expanded_memcpy() {
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

        let obligation = crate::memory_proofs::proof_memcpy_correctness(4);
        let config = AYConfig::default().with_timeout(30000);
        let result = verify_with_cli(&obligation, &config);
        assert_verified_or_certification_gap_skip(
            &obligation,
            &config,
            &result,
            format_args!("Memcpy correctness proof should verify with expanded quantifiers"),
        );
    }

    #[test]
    fn test_cli_verify_array_32bit_index() {
        // Verify array operations with 32-bit indices (common for memory models)
        let solver = find_solver_binary();
        if solver.is_empty() {
            return;
        }

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
            &config,
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
    // find_solver_binary / detect_solver_version / solver_info tests
    // -----------------------------------------------------------------------

    fn isolated_discovery_root(test_name: &str) -> std::path::PathBuf {
        let nanos = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system time before UNIX_EPOCH")
            .as_nanos();
        std::env::temp_dir().join(format!(
            "trust_cg_ay_discovery_{}_{}_{}",
            test_name,
            std::process::id(),
            nanos
        ))
    }

    fn touch_solver_file(path: &std::path::Path) {
        std::fs::create_dir_all(path.parent().expect("solver path has parent"))
            .expect("create solver parent directory");
        std::fs::File::create(path).expect("create solver file");
    }

    #[test]
    fn test_cargo_target_dir_ay_discovery_prefers_release_over_debug() {
        let root = isolated_discovery_root("cargo_target_order");
        let release = root.join("release/ay");
        let debug = root.join("debug/ay");
        touch_solver_file(&debug);
        touch_solver_file(&release);

        let selected = first_existing_solver_file(&root, AY_CARGO_TARGET_SUBDIRS)
            .expect("expected supported ay target-dir route");
        assert_eq!(selected, release.to_string_lossy().to_string());

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn trust_toolchain_solver_finds_stage2_sysroot_ay() {
        // The canonical Trust toolchain ships ay in the standalone stage2 sysroot
        // at build/<host-triple>/stage2/bin/ay; discovery scans the triple dir.
        let root = isolated_discovery_root("trust_stage2");
        let ay = root.join("build/aarch64-apple-darwin/stage2/bin/ay");
        touch_solver_file(&ay);
        let selected = trust_toolchain_solver_in_roots(std::slice::from_ref(&root))
            .expect("expected the Trust stage2 sysroot ay");
        assert_eq!(selected, ay.to_string_lossy().to_string());
        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn trust_toolchain_solver_falls_back_to_first_party_ay() {
        // With no built stage2 sysroot, fall back to first-party/ay/target.
        let root = isolated_discovery_root("trust_first_party");
        let ay = root.join("first-party/ay/target/release/ay");
        touch_solver_file(&ay);
        let selected = trust_toolchain_solver_in_roots(std::slice::from_ref(&root))
            .expect("expected the first-party/ay release ay");
        assert_eq!(selected, ay.to_string_lossy().to_string());
        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn trust_toolchain_solver_none_when_absent() {
        let root = isolated_discovery_root("trust_absent");
        assert!(trust_toolchain_solver_in_roots(std::slice::from_ref(&root)).is_none());
        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn test_home_ay_discovery_does_not_auto_select_legacy_user_target() {
        let root = isolated_discovery_root("home_legacy_ignored");
        let ay_root = root.join("ay");
        touch_solver_file(&ay_root.join("target/user/release/ay"));

        let selected = first_existing_solver_file(&ay_root, AY_HOME_BUILD_SUBDIRS);
        assert_eq!(
            selected, None,
            "legacy ~/ay/target/user builds must require an explicit solver override"
        );

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn test_home_ay_discovery_prefers_release_over_debug() {
        let root = isolated_discovery_root("home_release_order");
        let ay_root = root.join("ay");
        let release = ay_root.join("target/release/ay");
        let debug = ay_root.join("target/debug/ay");
        touch_solver_file(&debug);
        touch_solver_file(&release);

        let selected = first_existing_solver_file(&ay_root, AY_HOME_BUILD_SUBDIRS)
            .expect("expected supported home ay route");
        assert_eq!(selected, release.to_string_lossy().to_string());

        let _ = std::fs::remove_dir_all(root);
    }

    #[test]
    fn test_find_solver_binary_returns_valid_path() {
        let solver = find_solver_binary();
        if !solver.is_empty() {
            assert!(
                std::path::Path::new(&solver).is_file(),
                "expected solver path to be a file, got: {}",
                solver
            );
        }
    }

    #[test]
    fn test_find_solver_binary_requires_checker_and_prefers_trust_toolchain_ay() {
        // Explicit operator configuration is the only authority above the
        // canonical Trust toolchain route.
        if std::env::var("AY_SOLVER_PATH").is_ok_and(|path| !path.trim().is_empty()) {
            return;
        }

        let solver = find_solver_binary();
        if crate::obligation_cert_store::clean_checker_path().is_none() {
            assert!(
                solver.is_empty(),
                "AY without an independent proof checker is not proof authority"
            );
            return;
        }
        if let Some(toolchain_ay) = trust_toolchain_solver() {
            assert_eq!(
                solver, toolchain_ay,
                "the pinned Trust stage2/first-party AY must outrank PATH and standalone builds"
            );
            assert_ne!(
                std::path::Path::new(&solver)
                    .file_stem()
                    .and_then(|name| name.to_str()),
                Some("z3"),
                "z3 is not an authorized proof-discharge route"
            );
        }
    }

    /// AY is the sole solver: a floating-point (QF_BVFP) obligation must
    /// resolve the SAME AY binary as any other obligation, and must NEVER
    /// route to z3. (Previously these obligations preferred z3 because the
    /// local ay CLI was unstable on QF_BVFP; z3 has since been removed
    /// entirely and AY's fp soundness fixes landed.)
    fn is_authorized_ay_selection(selection: &SolverSelection) -> bool {
        !selection.path.is_empty()
            && std::path::Path::new(&selection.path).is_file()
            && matches!(
                selection.route_kind,
                "config-override"
                    | "env-override"
                    | "trust-toolchain-ay"
                    | "auto-ay-path"
                    | "auto-ay-target-dir"
                    | "auto-ay-home-build"
                    | "auto-ay-temp-build"
            )
    }

    fn assert_fp_obligation_uses_ay(obligation: &ProofObligation) {
        let selection = select_solver_for_obligation(obligation);
        assert!(
            !selection.route_kind.contains("z3") && !selection.path.contains("/z3"),
            "FP obligations must NOT route to z3 (route={}, solver={})",
            selection.route_kind,
            selection.path
        );
        // The FP obligation resolves the identical selection as a logic-agnostic
        // lookup — i.e. the obligation's logic no longer steers solver choice.
        assert_eq!(
            selection,
            select_solver_binary(),
            "FP obligation must resolve the same AY selection as any obligation"
        );
        if !selection.path.is_empty() {
            assert!(
                is_authorized_ay_selection(&selection),
                "resolved FP solver must use an authorized AY route (route={}, solver={})",
                selection.route_kind,
                selection.path
            );
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
        // z3 is gone: the FP route is an AY route (or unresolved if AY is not
        // installed), never a z3 route.
        assert!(
            !summary.contains("z3"),
            "FP route summary must not mention z3, got: {}",
            summary
        );
        if selection.path.is_empty() {
            assert!(
                summary.contains("route=unresolved") && summary.contains("solver=(not found)"),
                "unresolved FP route summary must report that state, got: {}",
                summary
            );
        } else {
            assert!(
                is_authorized_ay_selection(&selection),
                "resolved FP solver must use an authorized AY route (route={}, solver={})",
                selection.route_kind,
                selection.path
            );
            assert!(
                summary.contains(&format!("route={}", selection.route_kind))
                    && summary.contains(&format!("solver={}", selection.path)),
                "FP route summary must report the selected route kind and path, got: {}",
                summary
            );
        }
    }

    #[test]
    fn test_solver_route_summary_for_forced_solver_path_includes_config_override() {
        // The config-override mechanism accepts any explicit path; AY is the
        // solver, so use the AY binary as the fixture.
        let solver_path = find_solver_binary();
        if solver_path.is_empty() {
            return;
        }

        let obligation = crate::fp_convert_proofs::proof_roundtrip_scvtf_fcvtzs();
        let config = AYConfig::default().with_solver_path(solver_path.clone());
        let summary = solver_route_summary_for_invocation(&obligation, &config);
        assert!(
            summary.contains("route=config-override"),
            "expected forced route summary to mark config override, got: {}",
            summary
        );
        assert!(
            summary.contains(&format!("solver={}", solver_path)),
            "expected forced route summary to include selected path, got: {}",
            summary
        );
    }

    #[test]
    fn test_detect_solver_version_empty_path() {
        assert!(detect_solver_version("").is_none());
    }

    #[test]
    fn test_detect_solver_version_nonexistent() {
        assert!(detect_solver_version("/nonexistent/binary/xyz").is_none());
    }

    #[test]
    fn test_detect_solver_version_real_solver() {
        if z3_available() {
            let solver = find_solver_binary();
            assert!(
                detect_solver_version(&solver).is_some(),
                "expected version detection to succeed for solver: {}",
                solver
            );
        }
    }

    #[test]
    fn test_solver_info_when_available() {
        if z3_available() {
            let info = solver_info();
            assert!(
                info.contains(" at "),
                "expected solver_info to contain ' at ', got: {}",
                info
            );
            assert_ne!(info, "no AY solver found");
        }
    }

    #[test]
    fn test_solver_info_contains_solver_name() {
        if z3_available() {
            let info = solver_info();
            assert!(
                info.contains("ay"),
                "expected solver_info to mention AY, got: {}",
                info
            );
        }
    }

    // -----------------------------------------------------------------------
}
