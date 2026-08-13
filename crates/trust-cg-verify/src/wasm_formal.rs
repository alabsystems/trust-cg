// trust-cg-verify/wasm_formal.rs - formal SMT discharge for the wasm proofs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Formal discharge of wasm refinement [`ProofObligation`]s via the `ay` SMT
//! solver — the **default** verification path for the wasm proof suite (the
//! statistical `verify_by_evaluation` is kept only as a cross-check). Each
//! obligation's negated equivalence is solved; `unsat` means proven for ALL
//! inputs.
//!
//! `ay` is REQUIRED: a wasm proof test fails if the central AY bridge cannot
//! resolve or discharge through the canonical Trust-toolchain solver. There is
//! no local finder and no fallback to sampling.

#![cfg(test)]

use crate::lowering_proof::ProofObligation;

/// The solver's verdict on a single obligation's negated-equivalence formula.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formal {
    /// `unsat` — the lowering is correct for all inputs (proven).
    Proven,
    /// `sat` — a counterexample exists (refuted).
    Refuted,
    /// Anything else (`unknown`, error, timeout) — never treated as a pass.
    Inconclusive(String),
}

/// Solve one obligation formally; return the verdict.
pub fn discharge(ob: &ProofObligation) -> Formal {
    use crate::ay_bridge::{AYConfig, AYResult, formal_solver_test_lock, verify_with_ay};

    let _solver_lock = formal_solver_test_lock();
    // These array/FP obligations previously ran without a deadline. Retain
    // robust headroom while gaining the bridge's bounded process cleanup and
    // fail-closed timeout result.
    let config = AYConfig::default().with_timeout(180_000);
    match verify_with_ay(ob, &config) {
        AYResult::Verified => Formal::Proven,
        AYResult::SolverUnsat => Formal::Inconclusive(
            "solver UNSAT lacked an independently accepted exact proof".to_string(),
        ),
        AYResult::CounterExample(_) => Formal::Refuted,
        AYResult::Timeout => Formal::Inconclusive("timeout".to_string()),
        AYResult::Unknown(reason) => Formal::Inconclusive(format!("unknown: {reason}")),
        AYResult::Error(error) => Formal::Inconclusive(format!("error: {error}")),
    }
}

/// Assert an obligation is formally PROVEN (`unsat`). Panics otherwise.
#[track_caller]
pub fn prove(ob: &ProofObligation) {
    match discharge(ob) {
        Formal::Proven => {}
        other => panic!(
            "obligation `{}` NOT formally proven via ay: {other:?}",
            ob.name
        ),
    }
}

/// Assert an obligation is formally REFUTED (`sat`) — for anti-tautology guards.
#[track_caller]
pub fn refute(ob: &ProofObligation) {
    match discharge(ob) {
        Formal::Refuted => {}
        other => panic!(
            "obligation `{}` should be refuted (sat) but ay said: {other:?}",
            ob.name
        ),
    }
}
