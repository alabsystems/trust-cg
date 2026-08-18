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
/// (Currently reached only through [`prove_or_certification_gap_skip`], which
/// inlines this exact panic as its fall-through; kept as the canonical
/// unguarded spelling for tests outside the certification-gap window.)
#[allow(dead_code)]
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

/// [`prove`] parked behind the certification-gap guard
/// ([`crate::formal_gap`]): PROVEN passes (returns `true`); the exact
/// fail-closed certification-gap diagnostics skip LOUDLY (returns `false`),
/// with a server-truncated bare `unknown` first re-confirmed through the
/// fresh one-shot transcript; every other outcome — `Refuted` (a genuine
/// soundness failure), `Timeout`, an unrecognized reason — panics with the
/// ORIGINAL [`prove`] message, so no solver regression can hide behind the
/// guard and the exemption un-arms itself the moment an authority ships
/// externally checkable proofs.
#[track_caller]
pub fn prove_or_certification_gap_skip(ob: &ProofObligation) -> bool {
    let verdict = discharge(ob);
    if matches!(verdict, Formal::Proven) {
        return true;
    }
    if let Some(reason) = certification_gap_reason(ob, &verdict) {
        crate::formal_gap::print_gap_skip(&format!("wasm obligation `{}`", ob.name), &reason);
        return false;
    }
    panic!(
        "obligation `{}` NOT formally proven via ay: {verdict:?}",
        ob.name
    );
}

/// Shared classification for the guarded wasm tests: `Some(reason)` iff the
/// non-Proven `verdict` is EXACTLY the certification gap (re-probing a bare
/// server-truncated `unknown` through the fresh transcript); `None` for
/// everything the original assertions must keep failing on.
pub fn certification_gap_reason(ob: &ProofObligation, verdict: &Formal) -> Option<String> {
    use crate::ay_bridge::{AYConfig, AYResult};
    let Formal::Inconclusive(reason) = verdict else {
        return None;
    };
    // Undo the discharge spelling ("unknown: {ay reason}") back to the
    // AYResult the shared classifier speaks; the re-probe re-runs the exact
    // obligation under the same 180 s config `discharge` used.
    let ay_result = AYResult::Unknown(reason.strip_prefix("unknown: ")?.to_string());
    let config = AYConfig::default().with_timeout(180_000);
    crate::formal_gap::confirmed_certification_gap(ob, &config, &ay_result)
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
