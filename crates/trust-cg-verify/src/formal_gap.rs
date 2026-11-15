// trust-cg-verify/formal_gap.rs - the shared certification-gap probe for
// solver-coupled lib tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The SHARED certification-gap rule behind the solver-coupled `src/`
//! `#[cfg(test)]` guards — the in-crate sibling of the plugin's
//! `rustc-codegen-trust-cg` `solver_test_support`, and the same rule:
//!
//! **A test skips only on a capability that is absent, named and tracked.**
//! A verdict on a proof, or a failure to produce one, fails the test.
//!
//! A guarded test prints a loud `certification-gap skip:` notice naming the
//! obligation and AY's disclosure, and keeps every original assertion as the
//! fall-through, so the exemption cannot rot: it un-skips itself the moment
//! AY can certify the family.
//!
//! # The one gap a test may skip on
//!
//! Since 0cceae8f ("require checked AY proof authority", 2026-08-03) a lib
//! obligation is `Verified` ONLY when AY's `unsat` is INDEPENDENTLY certified:
//! a non-empty Alethe artifact that the external Clean/Carcara checker fully
//! verifies, with AY's own `ay.proof.certificate` disclosure clean. When AY
//! refutes a bit-vector query by blasting, its Alethe export carries the coarse
//! `BvBitBlast` lemma as a disclosed `hole` step (`incomplete AY proof
//! certificate: c ay.proof.certificate … unproved_steps=1 foreign_assumes=no
//! trust_free=no`). ay `docs/ay-asks/2026-08-13-bv-certified-families` item 1
//! tracks that missing checkable lowering. That shape, recognised by
//! [`crate::gap_classify::ay_reason_is_disclosed_proof_hole`], is the only
//! skip.
//!
//! # What fails
//!
//! * A WORKING checker's rejection of the exact proof (`AY reported UNSAT but
//!   <clean> — which verified a known-good control proof, so it is a working
//!   checker — rejected or could not fully verify THIS Alethe proof`): a verdict
//!   on the proof, filed by production as a soundness failure
//!   (`proof_gate::unknown_is_hard_failure`). Measured before this rule, with AY
//!   build.8256 and clean 8606: 93 skipped obligations in this lib suite.
//! * AY's own self-check rejection (`(:reason-unknown (incomplete
//!   self-check-rejected))`), which production also files as a soundness
//!   failure. The reason the bridge keeps does not say WHY the self-check
//!   rejected the proof, so the v0.9.0-era resource envelope (item 2 of the
//!   same ay ask) cannot be told apart from a proof AY's strict validation found
//!   invalid (with build.8256 the plugin's measured rejections are "step t0
//!   uses unsupported hole rule", "step t1 uses unverified trust rule" and
//!   "assumes term … outside the supplied problem obligation").
//! * A replay that could not complete, no usable checker, an empty or
//!   unreadable proof, `unusable AY proof evidence:`, a certificate declaring
//!   foreign assumptions, a bare `unknown`, a timeout and an error.
//!
//! A bare `unknown` is not re-probed through a fresh transcript any more. The
//! production route answers the resident server's `unsat` with a fresh
//! proof-bearing replay, so a disclosed hole reaches the test through that
//! route directly; a bare `unknown` means the production route itself did not
//! decide the query, and a different route's answer cannot excuse that.
//!
//! # Multi-obligation checks
//!
//! A check that must refine several obligations reports each one's verdict
//! ([`crate::mir_semantics::ObligationVerdict`]). [`test_outcome`] folds them
//! for a test, so a disclosed hole on one obligation never hides another
//! obligation's refutation or failure.

#![cfg(test)]

use crate::ay_bridge::AYResult;
use crate::cegis::CegisResult;
use crate::gap_classify::ay_reason_is_disclosed_proof_hole;
use crate::mir_semantics::{ObligationVerdict, RefinementOutcome};

/// `Some(reason)` iff `result` is AY's disclosed proof hole — the one tracked
/// gap a test may skip on (see the module docs). Every other outcome returns
/// `None` and the guarded test falls through to its original assertion:
/// `Verified` (the gap is closed), `CounterExample` (a soundness failure),
/// a checker or self-check rejection, a bare or other `Unknown`, `Timeout` and
/// `Error`.
pub fn disclosed_proof_hole(result: &AYResult) -> Option<String> {
    match result {
        AYResult::Unknown(reason) if ay_reason_is_disclosed_proof_hole(reason) => {
            Some(reason.clone())
        }
        _ => None,
    }
}

/// The [`RefinementOutcome`] spelling of [`disclosed_proof_hole`]:
/// `Some(reason)` while the outcome is `Inconclusive` on AY's disclosed proof
/// hole (`discharge_refinement` wraps AY's reason as `"unknown: {reason}"`).
/// `Refined`, `Refuted` and every other inconclusive reason return `None`.
pub fn refinement_gap_reason(outcome: &RefinementOutcome) -> Option<&str> {
    match outcome {
        RefinementOutcome::Inconclusive { reason } => reason
            .strip_prefix("unknown: ")
            .is_some_and(ay_reason_is_disclosed_proof_hole)
            .then_some(reason.as_str()),
        RefinementOutcome::Refined | RefinementOutcome::Refuted { .. } => None,
    }
}

/// The outcome a solver-coupled test asserts on, over EVERY obligation's own
/// verdict. With a solver installed:
///
/// 1. the first FAILURE: an `Inconclusive` that is NOT the disclosed hole (a
///    checker or self-check rejection, a bare unknown, a timeout, an error);
/// 2. otherwise a `Refuted` obligation, wherever it sits;
/// 3. otherwise the first disclosed hole;
/// 4. otherwise `Refined`.
///
/// So with a solver a test fails whenever any of its obligations is rejected or
/// otherwise undecided, whatever it expects: a test expecting `Refined` also
/// fails on any refutation and skips only when every undecided obligation is
/// the tracked hole, and a test expecting `Refuted` passes exactly when some
/// obligation is refuted and none failed.
///
/// Without a solver, `discharge_refinement` falls back to the evaluator, whose
/// undecided answers are not verdicts on a proof, so a refutation outranks them
/// (1 and 2 swap).
///
/// When any verdict is not `Refined`, every obligation's verdict is printed
/// first (the harness shows it with the failing test).
pub fn test_outcome(check: &str, verdicts: &[ObligationVerdict]) -> RefinementOutcome {
    fold_verdicts(check, verdicts, crate::ay_bridge::z3_available())
}

/// [`test_outcome`] with the solver's presence given.
fn fold_verdicts(
    check: &str,
    verdicts: &[ObligationVerdict],
    solver_present: bool,
) -> RefinementOutcome {
    if verdicts
        .iter()
        .any(|verdict| !matches!(verdict.outcome, RefinementOutcome::Refined))
    {
        eprintln!("{}", render_verdicts(check, verdicts));
    }
    let is_hole = |verdict: &&ObligationVerdict| refinement_gap_reason(&verdict.outcome).is_some();
    let refuted = verdicts
        .iter()
        .find(|verdict| matches!(verdict.outcome, RefinementOutcome::Refuted { .. }));
    let failure = verdicts.iter().find(|verdict| {
        matches!(verdict.outcome, RefinementOutcome::Inconclusive { .. }) && !is_hole(verdict)
    });
    let decisive = if solver_present {
        failure.or(refuted)
    } else {
        refuted.or(failure)
    };
    decisive
        .or_else(|| verdicts.iter().find(is_hole))
        .map_or(RefinementOutcome::Refined, |verdict| {
            verdict.outcome.clone()
        })
}

/// One line per obligation: its position, name and verdict.
pub fn render_verdicts(check: &str, verdicts: &[ObligationVerdict]) -> String {
    let mut rendered = format!("{check}: {} obligation verdict(s)", verdicts.len());
    for (index, verdict) in verdicts.iter().enumerate() {
        rendered.push_str(&format!(
            "\n  #{} {}: {:?}",
            index + 1,
            verdict.obligation,
            verdict.outcome
        ));
    }
    rendered
}

/// The uniform loud skip line for every guarded lib test: grep-able prefix,
/// the obligation (or context) it covers, and the exact live disclosure that
/// authorized the skip.
pub fn print_gap_skip(context: &str, reason: &str) {
    eprintln!(
        "certification-gap skip: {context}: {reason} — AY answered unsat and its own proof \
         certificate discloses an unproved hole step (the BvBitBlast Alethe lowering tracked \
         as ay docs/ay-asks/2026-08-13-bv-certified-families item 1), so the result could not \
         be independently certified. The original assertion resumes automatically once AY \
         ships a checkable proof."
    );
}

/// The uniform loud line for a lib test that returns early because an
/// EXTERNAL authority it depends on is absent — the ay solver plus a capable
/// independent Clean/Carcara checker, or an explicit env override the test
/// insists on. One grep-able stderr line, `SKIP <test>: <reason>`; the caller
/// keeps its own `return`, so the skip condition and control flow are exactly
/// what they were — only the silence is gone.
pub fn skip_test(test: &str, reason: &str) {
    eprintln!("SKIP {test}: {reason}");
}

/// Gate for a lib test whose assertion is ABOUT a proof (an accepted rule, a
/// proven candidate, a certified equivalence): `true` when AY and a capable
/// independent checker are installed, so the test must assert the proof;
/// otherwise the loud `SKIP <test>:` line naming [`NO_PROOF_AUTHORITY`] and
/// `false`. A test gated on it keeps every assertion that does not need the
/// authority outside the gate.
pub fn proof_authority_present(test: &str) -> bool {
    let present = crate::ay_bridge::z3_available();
    if !present {
        skip_test(test, NO_PROOF_AUTHORITY);
    }
    present
}

/// The [`CegisResult`] spelling of [`disclosed_proof_hole`]: `Some(reason)`
/// iff `CegisLoop::verify` returned AY's `unknown` and that reason is the
/// disclosed proof hole. A checker or self-check rejection, any other
/// `unknown`, a solver that could not run, and every non-error result return
/// `None`.
pub fn cegis_gap_reason(result: &CegisResult) -> Option<&str> {
    result
        .solver_unknown_reason()
        .filter(|reason| ay_reason_is_disclosed_proof_hole(reason))
}

/// What [`assert_cegis_equivalent`] concluded, when it did not fail the test.
#[derive(Debug, PartialEq, Eq)]
pub enum CegisCheck {
    /// CEGIS returned a certified `Equivalent`.
    Proved,
    /// The test skipped, loudly, on a named, tracked absent capability.
    Skipped,
}

/// Assert that CEGIS proved a TRUE equivalence. A counterexample always
/// fails. With proof authority installed only a certified `Equivalent`
/// passes, and AY's disclosed proof hole skips loudly; a rejected proof, any
/// other `unknown`, a timeout, the iteration cap and a solver error fail.
/// Without proof authority the test skips by name.
pub fn assert_cegis_equivalent(test: &str, result: &CegisResult) -> CegisCheck {
    check_cegis_equivalent(test, result, crate::ay_bridge::z3_available())
}

/// [`assert_cegis_equivalent`] with the authority's presence given.
fn check_cegis_equivalent(test: &str, result: &CegisResult, authority: bool) -> CegisCheck {
    assert!(
        !result.is_not_equivalent(),
        "{test}: a true equivalence was REFUTED: {result:?}"
    );
    if !authority {
        skip_test(test, NO_PROOF_AUTHORITY);
        return CegisCheck::Skipped;
    }
    if let Some(reason) = cegis_gap_reason(result) {
        print_gap_skip(test, reason);
        return CegisCheck::Skipped;
    }
    assert!(
        result.is_equivalent(),
        "{test}: expected a certified Equivalent, got {result:?}"
    );
    CegisCheck::Proved
}

/// `skip_test` reason: `ay_bridge::z3_available()` is false — no ay solver
/// paired with a CAPABLE independent checker (AY alone is not proof authority).
pub const NO_PROOF_AUTHORITY: &str = "no admitted ay solver with a capable Clean/Carcara \
     checker (build with a Trust toolchain that ships bin/ay: the only AY admitted, by the \
     sha256 recorded at build time, see ay_identity; set TCG_EXTERNAL_CLEAN_CHECKER / \
     install clean to run)";

/// `skip_test` reason: an ay binary may exist but no capable independent
/// checker does, so nothing can be promoted to `Verified`.
pub const NO_CLEAN_CHECKER: &str = "no capable independent Clean/Carcara checker \
     (set TCG_EXTERNAL_CLEAN_CHECKER / install clean to run)";

/// `skip_test` reason: the test runs only against an EXPLICITLY named checker
/// binary and that override is not set. (The AY is never named by the test:
/// it is the one `ay_identity` admits.)
pub const NO_EXPLICIT_AUTHORITY_ENV: &str = "TCG_EXTERNAL_CLEAN_CHECKER is not set (set it \
     to run; the AY is the identity-admitted toolchain AY)";

#[cfg(test)]
mod tests {
    use super::*;

    const HOLE: &str = "incomplete AY proof certificate: c ay.proof.certificate \
         path=/tmp/q.alethe unproved_steps=1 foreign_assumes=no trust_free=no \
         ay_self_checkable=yes";
    const SELF_CHECK_REJECTED: &str = "(:reason-unknown (incomplete self-check-rejected))";
    const CHECKER_REJECTED: &str = "AY reported UNSAT but /pkg/clean/8606/bin/clean — which \
         verified a known-good control proof, so it is a working checker — rejected or could \
         not fully verify THIS Alethe proof";

    fn unknown(reason: &str) -> RefinementOutcome {
        RefinementOutcome::Inconclusive {
            reason: format!("unknown: {reason}"),
        }
    }

    fn verdict(outcome: RefinementOutcome) -> ObligationVerdict {
        ObligationVerdict {
            obligation: "ob".to_string(),
            outcome,
        }
    }

    fn reason(outcome: RefinementOutcome) -> String {
        match outcome {
            RefinementOutcome::Inconclusive { reason } => reason,
            other => panic!("expected an inconclusive outcome, got {other:?}"),
        }
    }

    #[test]
    fn only_the_disclosed_hole_is_a_gap() {
        assert_eq!(
            disclosed_proof_hole(&AYResult::Unknown(HOLE.to_string())).as_deref(),
            Some(HOLE)
        );
        assert!(refinement_gap_reason(&unknown(HOLE)).is_some());
        for failure in [
            SELF_CHECK_REJECTED,
            CHECKER_REJECTED,
            "AY reported UNSAT but Clean replay could not complete: spawn failed",
            "AY reported UNSAT but emitted an empty Alethe proof",
            "unusable AY proof evidence: c warning: the proof is holey",
            "incomplete AY proof certificate: c ay.proof.certificate path=/tmp/q.alethe \
             unproved_steps=0 foreign_assumes=no trust_free=no ay_self_checkable=yes",
            "unknown",
        ] {
            assert!(
                disclosed_proof_hole(&AYResult::Unknown(failure.to_string())).is_none(),
                "{failure:?}"
            );
            assert!(
                refinement_gap_reason(&unknown(failure)).is_none(),
                "{failure:?}"
            );
        }
        // The wrapper is required on a refinement outcome, and never on a raw
        // result.
        assert!(
            refinement_gap_reason(&RefinementOutcome::Inconclusive {
                reason: HOLE.to_string()
            })
            .is_none()
        );
        assert!(disclosed_proof_hole(&AYResult::Unknown(format!("unknown: {HOLE}"))).is_none());
        for result in [
            AYResult::Verified,
            AYResult::SolverUnsat,
            AYResult::Timeout,
            AYResult::CounterExample(vec![]),
            AYResult::Error(HOLE.to_string()),
        ] {
            assert!(disclosed_proof_hole(&result).is_none(), "{result:?}");
        }
        assert!(refinement_gap_reason(&RefinementOutcome::Refined).is_none());
    }

    fn cegis_unknown(reason: &str) -> CegisResult {
        CegisResult::Error(format!("{}{reason}", crate::cegis::SOLVER_UNKNOWN_PREFIX))
    }

    #[test]
    fn only_the_disclosed_hole_is_a_cegis_gap() {
        assert_eq!(cegis_gap_reason(&cegis_unknown(HOLE)), Some(HOLE));
        for result in [
            cegis_unknown(SELF_CHECK_REJECTED),
            cegis_unknown(CHECKER_REJECTED),
            cegis_unknown("unknown"),
            // The hole text without the prefix `CegisLoop::verify` mints is
            // not AY's answer.
            CegisResult::Error(HOLE.to_string()),
            CegisResult::Error("AY solver not found".to_string()),
            CegisResult::Timeout,
            CegisResult::MaxIterationsReached { counterexamples: 0 },
            CegisResult::Equivalent {
                proof_hash: 0,
                iterations: 1,
            },
        ] {
            assert!(cegis_gap_reason(&result).is_none(), "{result:?}");
        }
    }

    #[test]
    fn a_rejected_cegis_proof_fails_and_only_a_named_gap_skips() {
        let proved = CegisResult::Equivalent {
            proof_hash: 0,
            iterations: 1,
        };
        let refuted = CegisResult::NotEquivalent {
            counterexample: crate::cegis::ConcreteInput::from_pairs(&[("x", 1)]),
            found_by_concrete: false,
        };
        assert_eq!(
            check_cegis_equivalent("t", &proved, true),
            CegisCheck::Proved
        );
        assert_eq!(
            check_cegis_equivalent("t", &cegis_unknown(HOLE), true),
            CegisCheck::Skipped
        );
        for failure in [
            cegis_unknown(SELF_CHECK_REJECTED),
            cegis_unknown(CHECKER_REJECTED),
            cegis_unknown("unknown"),
            CegisResult::Error("AY solver not found".to_string()),
            CegisResult::Timeout,
            CegisResult::MaxIterationsReached { counterexamples: 0 },
            refuted.clone(),
        ] {
            let outcome = std::panic::catch_unwind(|| check_cegis_equivalent("t", &failure, true));
            assert!(outcome.is_err(), "with authority {failure:?} must fail");
        }
        // Without the authority the test skips by name, but a refutation of a
        // true equivalence still fails it.
        assert_eq!(
            check_cegis_equivalent("t", &cegis_unknown(SELF_CHECK_REJECTED), false),
            CegisCheck::Skipped
        );
        assert!(std::panic::catch_unwind(|| check_cegis_equivalent("t", &refuted, false)).is_err());
    }

    #[test]
    fn a_hole_hides_nothing_and_a_failure_fails_every_test_with_a_solver() {
        let refuted = || RefinementOutcome::Refuted {
            counterexample: "[x = 1]".to_string(),
        };
        for solver_present in [true, false] {
            // A failure outranks a hole, in either order.
            for order in [
                [unknown(HOLE), unknown(SELF_CHECK_REJECTED)],
                [unknown(SELF_CHECK_REJECTED), unknown(HOLE)],
            ] {
                let verdicts: Vec<_> = order.into_iter().map(verdict).collect();
                assert_eq!(
                    reason(fold_verdicts("order", &verdicts, solver_present)),
                    format!("unknown: {SELF_CHECK_REJECTED}")
                );
            }
            // A refutation outranks a hole, wherever it sits.
            for verdicts in [
                vec![verdict(unknown(HOLE)), verdict(refuted())],
                vec![verdict(refuted()), verdict(unknown(HOLE))],
            ] {
                assert!(matches!(
                    fold_verdicts("refuted", &verdicts, solver_present),
                    RefinementOutcome::Refuted { .. }
                ));
            }
            // Only holes: the first hole, which the guard skips on.
            let verdicts = vec![
                verdict(RefinementOutcome::Refined),
                verdict(unknown(HOLE)),
                verdict(unknown(HOLE)),
            ];
            assert!(
                refinement_gap_reason(&fold_verdicts("holes", &verdicts, solver_present)).is_some()
            );
            assert!(matches!(
                fold_verdicts(
                    "none",
                    &[verdict(RefinementOutcome::Refined)],
                    solver_present
                ),
                RefinementOutcome::Refined
            ));
            assert!(matches!(
                fold_verdicts("empty", &[], solver_present),
                RefinementOutcome::Refined
            ));
        }
        // With a solver a failure fails even a test expecting a refutation,
        // wherever the two sit; without one the refutation outranks it.
        for verdicts in [
            vec![
                verdict(unknown(HOLE)),
                verdict(unknown(CHECKER_REJECTED)),
                verdict(refuted()),
            ],
            vec![verdict(refuted()), verdict(unknown(CHECKER_REJECTED))],
        ] {
            assert_eq!(
                reason(fold_verdicts("with a solver", &verdicts, true)),
                format!("unknown: {CHECKER_REJECTED}")
            );
            assert!(matches!(
                fold_verdicts("without a solver", &verdicts, false),
                RefinementOutcome::Refuted { .. }
            ));
        }
    }
}
