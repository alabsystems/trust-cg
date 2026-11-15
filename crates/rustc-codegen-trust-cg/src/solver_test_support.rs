// rustc_codegen_trust_cg/solver_test_support.rs - the one certification-gap
// predicate for the solver-coupled unit tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Support shared by the unit tests that discharge real AY obligations
//! (`mem_refine::tests`, the `dom_bce` tests in `lib.rs`).
//!
//! Those tests run on the PRODUCTION solver route
//! (`trust_cg_verify::ay_bridge::verify_with_ay`: the resident `ay
//! --incremental` server, with a fresh proof-bearing replay of every candidate
//! UNSAT). They are not rerouted to a test-only lane: a test of a refinement
//! lane that the production route cannot pass must fail, not skip.
//!
//! # The one gap a test may skip on
//!
//! A test skips its discharge assertion only when AY's answer names a missing
//! capability that is tracked: AY answered `unsat`, and its own
//! `c ay.proof.certificate` line reports unproved (hole) steps and no foreign
//! assumptions (`incomplete AY proof certificate: c ay.proof.certificate …
//! unproved_steps=1 foreign_assumes=no …`). ay
//! `docs/ay-asks/2026-08-13-bv-certified-families` (item 1) tracks this
//! disclosure as the missing checkable lowering of AY's `BvBitBlast` lemma;
//! AY build.8256 prints the hole as a bare `:rule hole` step over bit-vector
//! terms without naming the lemma. The predicate is
//! `trust_cg_verify::gap_classify::ay_reason_is_disclosed_proof_hole`, next to
//! the bridge that mints the reason. The solver-absent lane
//! ([`ay_reason_is_certification_gap`]) is the only other skip.
//!
//! # What is NOT a gap
//!
//! Each of these fails the test:
//! * a working checker rejecting the exact proof ("AY reported UNSAT but
//!   <clean> — which verified a known-good control proof, so it is a working
//!   checker — rejected or could not fully verify THIS Alethe proof"). This is
//!   a verdict on the proof, and production files it as a soundness failure
//!   (`trust_cg_verify::proof_gate`). Measured with AY build.8256 and clean
//!   8606: `tests::dom_bce_implication_lt_discharges` gets this rejection.
//!   Carcara reports "checking failed on step 't5' with rule 'not_equiv2'" on
//!   the hole-free (`unproved_steps=0 trust_free=yes`) proof AY emits for
//!   `(x <u 1024) => (x <u 1024)`;
//! * a replay that could not complete, no usable checker, an empty or
//!   unreadable proof, or `unusable AY proof evidence:` (the broader
//!   `gap_classify::ay_reason_is_certification_gap` accepts all of these and
//!   the rejection above, so this crate does not use it);
//! * a certificate that declares foreign assumptions;
//! * AY's self-check rejection (`(:reason-unknown (incomplete
//!   self-check-rejected))`). Production promotes it to a hard soundness failure
//!   (`proof_gate::unknown_is_hard_failure`). With build.8256 it is a
//!   proof-validation failure, not the v0.9.0-era resource envelope;
//! * a bare `unknown`, a timeout and a solver error.
//!
//! # Checks with several obligations
//!
//! Every obligation is discharged, whatever an earlier one answered, and each
//! verdict is kept ([`ObligationVerdict`]). [`test_outcome`] folds them, so a
//! gap on one obligation hides neither a refutation nor a failure of another.
//! (Measured with a fake AY that discloses a hole on query 1 and rejects its
//! own proof after it: `correct_field_store_is_not_refuted`,
//! `correct_deref_field_store_is_not_refuted` and `correct_copy_is_not_refuted`
//! used to skip after one query, because `check_memory_sequence` stopped at
//! the first undecided obligation.) That answer sequence is reproduced through
//! the production route in trust-cg-verify
//! (`mir_semantics::tests::a_hole_on_the_first_obligation_*`): a fake AY is
//! admissible only in that crate's own `cfg(test)` build (`ay_identity`), so
//! this crate's twin folds the same verdict sequence over the obligations the
//! three discharges build.

use trust_cg_verify::ay_bridge::AYResult;
use trust_cg_verify::mir_semantics::{ObligationVerdict, RefinementOutcome};

/// The skip notice every test parked behind [`ay_reason_is_certification_gap`]
/// prints. It names both gaps the predicate accepts and where the first is
/// tracked.
pub(crate) const CERTIFICATION_GAP_SKIP_NOTICE: &str = "skipping assertion: AY answered \
     `unsat`, but its own proof certificate reports an unproved hole step (tracked as ay \
     docs/ay-asks/2026-08-13-bv-certified-families item 1), so the result could not be \
     certified; or no solver is installed and the lane refused to credit a statistical verdict";

/// Is `reason` (an `AYResult::Unknown` reason with any `"unknown: "` wrapper
/// already stripped) a gap this crate's tests may skip on?
///
/// * the disclosed proof hole
///   ([`trust_cg_verify::gap_classify::ay_reason_is_disclosed_proof_hole`]);
/// * the solver-absent lane refusing to credit a statistical verdict (the
///   release gate's anonymous clone has no solver).
pub(crate) fn ay_reason_is_certification_gap(reason: &str) -> bool {
    trust_cg_verify::gap_classify::ay_reason_is_disclosed_proof_hole(reason)
        || (reason.contains("no solver available") && reason.contains("statistical"))
}

/// [`ay_reason_is_certification_gap`] over a raw [`AYResult`].
pub(crate) fn ay_result_is_certification_gap(result: &AYResult) -> bool {
    matches!(result, AYResult::Unknown(reason) if ay_reason_is_certification_gap(reason))
}

/// [`ay_reason_is_certification_gap`] over a [`RefinementOutcome`]
/// (`discharge_refinement` wraps an `Unknown` reason as `"unknown: {reason}"`).
pub(crate) fn refinement_is_certification_gap(outcome: &RefinementOutcome) -> bool {
    match outcome {
        RefinementOutcome::Inconclusive { reason } => {
            ay_reason_is_certification_gap(reason.strip_prefix("unknown: ").unwrap_or(reason))
        }
        RefinementOutcome::Refined | RefinementOutcome::Refuted { .. } => false,
    }
}

/// The outcome a solver-coupled test asserts on, over EVERY obligation's own
/// verdict. With a solver installed:
///
/// 1. the first FAILURE: an `Inconclusive` that is not a gap
///    ([`refinement_is_certification_gap`]) — AY's self-check rejection, a
///    working checker's rejection, a bare unknown, a timeout, an error;
/// 2. otherwise a `Refuted` obligation, wherever it sits;
/// 3. otherwise the first gap;
/// 4. otherwise `Refined`.
///
/// So with a solver a test fails whenever any of its obligations is rejected or
/// otherwise undecided, whatever it expects: a test expecting `Refined` also
/// fails on any refutation and skips only when every undecided obligation is a
/// gap, and a test expecting `Refuted` passes exactly when some obligation is
/// refuted and none failed.
///
/// Without a solver, `discharge_refinement` falls back to the evaluator, which
/// decides only exhaustively-enumerable obligations; its undecided answers are
/// not verdicts on a proof, so a refutation outranks them (1 and 2 swap), as
/// the solver-less tests always assumed.
///
/// When any verdict is not `Refined`, every obligation's verdict is printed (the
/// harness shows it with a failing test).
pub(crate) fn test_outcome(check: &str, verdicts: &[ObligationVerdict]) -> RefinementOutcome {
    fold_verdicts(check, verdicts, trust_cg_verify::ay_bridge::z3_available())
}

/// [`test_outcome`] with the solver's presence given.
pub(crate) fn fold_verdicts(
    check: &str,
    verdicts: &[ObligationVerdict],
    solver_present: bool,
) -> RefinementOutcome {
    if verdicts
        .iter()
        .any(|verdict| !matches!(verdict.outcome, RefinementOutcome::Refined))
    {
        let mut report = format!("{check}: {} obligation verdict(s)", verdicts.len());
        for (index, verdict) in verdicts.iter().enumerate() {
            report.push_str(&format!(
                "\n  #{} {}: {:?}",
                index + 1,
                verdict.obligation,
                verdict.outcome
            ));
        }
        eprintln!("{report}");
    }
    let is_gap = |verdict: &&ObligationVerdict| refinement_is_certification_gap(&verdict.outcome);
    let inconclusive = |verdict: &&ObligationVerdict| {
        matches!(verdict.outcome, RefinementOutcome::Inconclusive { .. })
    };
    let refuted = verdicts
        .iter()
        .find(|verdict| matches!(verdict.outcome, RefinementOutcome::Refuted { .. }));
    let failure = verdicts
        .iter()
        .find(|verdict| inconclusive(verdict) && !is_gap(verdict));
    let decisive = if solver_present {
        failure.or(refuted)
    } else {
        refuted.or(failure)
    };
    decisive
        .or_else(|| verdicts.iter().find(is_gap))
        .map_or(RefinementOutcome::Refined, |verdict| {
            verdict.outcome.clone()
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The disclosed-hole reason measured on 14 plugin tests (AY build.8256).
    const MEASURED_HOLE: &str = "incomplete AY proof certificate: c ay.proof.certificate \
         path=/tmp/q.alethe unproved_steps=1 foreign_assumes=no trust_free=no \
         ay_self_checkable=yes";

    /// The checker rejection measured on `tests::dom_bce_implication_lt_discharges`
    /// (AY build.8256, clean 8606).
    const MEASURED_CHECKER_REJECTION: &str = "AY reported UNSAT but \
         /pkg/store/clean/8606/bin/clean — which verified a known-good control proof, so it is a \
         working checker — rejected or could not fully verify THIS Alethe proof";

    #[test]
    fn every_skippable_shape_is_recognised_and_a_bare_unknown_is_not() {
        assert!(refinement_is_certification_gap(
            &RefinementOutcome::Inconclusive {
                reason: format!("unknown: {MEASURED_HOLE}"),
            }
        ));
        assert!(ay_result_is_certification_gap(&AYResult::Unknown(
            MEASURED_HOLE.to_string()
        )));
        // The solver-absent lane.
        assert!(refinement_is_certification_gap(
            &RefinementOutcome::Inconclusive {
                reason: "no solver available: refusing to credit a >8-bit/FP refinement \
                         obligation on a statistical (100k-sample) verdict"
                    .to_string(),
            }
        ));
        // A bare unknown (the resident server's shape), a timeout, and real
        // verdicts are never gaps.
        assert!(!refinement_is_certification_gap(
            &RefinementOutcome::Inconclusive {
                reason: "unknown: unknown".to_string(),
            }
        ));
        assert!(!refinement_is_certification_gap(
            &RefinementOutcome::Inconclusive {
                reason: "solver timeout".to_string(),
            }
        ));
        assert!(!ay_result_is_certification_gap(&AYResult::Unknown(
            "unknown".to_string()
        )));
        assert!(!ay_result_is_certification_gap(&AYResult::Timeout));
        assert!(!refinement_is_certification_gap(
            &RefinementOutcome::Refined
        ));
    }

    #[test]
    fn a_checker_rejection_is_a_failure_not_a_gap() {
        // The broader canonical predicate accepts every one of these; a test in
        // this crate must fail on each.
        for reason in [
            MEASURED_CHECKER_REJECTION,
            // The spelling production minted before 9ec5f97c (the old hand
            // copies matched it).
            "AY reported UNSAT but clean rejected or could not fully verify the exact Alethe proof",
            "AY reported UNSAT but Clean replay could not complete: spawn failed",
            "AY reported UNSAT but it CANNOT BE CHECKED here — no usable checker. This is a \
             toolchain problem, not evidence about the proof.",
            "AY reported UNSAT but emitted an empty Alethe proof",
            "unusable AY proof evidence: c warning: the proof is holey",
            "incomplete AY proof certificate: c ay.proof.certificate path=/tmp/q.alethe \
             unproved_steps=0 foreign_assumes=yes trust_free=no ay_self_checkable=yes",
            // No unproved step and no foreign assumption: the bridge mints this
            // from `trust_free=no` alone, and it is not a hole.
            "incomplete AY proof certificate: c ay.proof.certificate path=/tmp/q.alethe \
             unproved_steps=0 foreign_assumes=no trust_free=no ay_self_checkable=yes",
        ] {
            assert!(
                trust_cg_verify::gap_classify::ay_reason_is_certification_gap(reason),
                "control: the broader predicate accepts {reason:?}"
            );
            assert!(
                !ay_result_is_certification_gap(&AYResult::Unknown(reason.to_string())),
                "{reason:?}"
            );
            assert!(
                !refinement_is_certification_gap(&RefinementOutcome::Inconclusive {
                    reason: format!("unknown: {reason}"),
                }),
                "{reason:?}"
            );
        }
    }

    #[test]
    fn the_solver_absent_lane_needs_both_its_phrases() {
        // The lane's reason names the missing solver AND the statistical
        // verdict it refused to credit. Either phrase alone is some other
        // reason, and a test must fail on it.
        assert!(ay_reason_is_certification_gap(
            "no solver available: refusing to credit a >8-bit/FP refinement obligation on a \
             statistical (100k-sample) verdict"
        ));
        for reason in [
            "no solver available: the obligation could not be evaluated",
            "error: No AY solver found (no solver available on this route)",
            "the statistical sampler found no satisfying assignment for the preconditions",
            "unknown: a statistical estimate is not a proof",
        ] {
            assert!(!ay_reason_is_certification_gap(reason), "{reason:?}");
            assert!(
                !refinement_is_certification_gap(&RefinementOutcome::Inconclusive {
                    reason: reason.to_string(),
                }),
                "{reason:?}"
            );
        }
    }

    #[test]
    fn a_gap_hides_nothing_and_a_failure_fails_every_test_with_a_solver() {
        let verdict = |outcome| ObligationVerdict {
            obligation: "ob".to_string(),
            outcome,
        };
        let hole = || RefinementOutcome::Inconclusive {
            reason: format!("unknown: {MEASURED_HOLE}"),
        };
        let rejected = || RefinementOutcome::Inconclusive {
            reason: "unknown: (:reason-unknown (incomplete self-check-rejected))".to_string(),
        };
        let refuted = || RefinementOutcome::Refuted {
            counterexample: "[x = 1]".to_string(),
        };
        let reason = |outcome: RefinementOutcome| match outcome {
            RefinementOutcome::Inconclusive { reason } => reason,
            other => panic!("expected an inconclusive outcome, got {other:?}"),
        };
        assert!(refinement_is_certification_gap(&hole()));
        assert!(!refinement_is_certification_gap(&rejected()));

        for solver_present in [true, false] {
            // A failure outranks a gap, in either order.
            for order in [[hole(), rejected()], [rejected(), hole()]] {
                let verdicts: Vec<_> = order.into_iter().map(verdict).collect();
                assert_eq!(
                    reason(fold_verdicts("order", &verdicts, solver_present)),
                    reason(rejected())
                );
            }
            // A refutation outranks a gap, wherever it sits.
            for verdicts in [
                vec![verdict(hole()), verdict(refuted())],
                vec![verdict(refuted()), verdict(hole())],
            ] {
                assert!(matches!(
                    fold_verdicts("refuted", &verdicts, solver_present),
                    RefinementOutcome::Refuted { .. }
                ));
            }
            // Only gaps (and refinements): the first gap, which a test skips on.
            let verdicts = vec![
                verdict(RefinementOutcome::Refined),
                verdict(hole()),
                verdict(hole()),
            ];
            assert!(refinement_is_certification_gap(&fold_verdicts(
                "gaps",
                &verdicts,
                solver_present
            )));
            assert!(matches!(
                fold_verdicts(
                    "refined",
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
        // wherever the two sit; without one (the evaluator lane) the
        // refutation outranks an undecided obligation.
        for verdicts in [
            vec![verdict(hole()), verdict(rejected()), verdict(refuted())],
            vec![verdict(refuted()), verdict(rejected())],
        ] {
            assert_eq!(
                reason(fold_verdicts("with a solver", &verdicts, true)),
                reason(rejected())
            );
            assert!(matches!(
                fold_verdicts("without a solver", &verdicts, false),
                RefinementOutcome::Refuted { .. }
            ));
        }
    }

    #[test]
    fn a_self_check_rejection_is_a_failure_not_a_gap() {
        // Production files this as a soundness failure; a test must fail on
        // it, with or without the reason-bearing transcript.
        let transcript = "unknown\n(:reason-unknown (incomplete self-check-rejected))";
        assert!(trust_cg_verify::gap_classify::ay_reason_is_self_check_rejection(transcript));
        assert!(!ay_result_is_certification_gap(&AYResult::Unknown(
            transcript.to_string()
        )));
        assert!(!refinement_is_certification_gap(
            &RefinementOutcome::Inconclusive {
                reason: format!("unknown: {transcript}"),
            }
        ));
    }
}
