// trust-cg-verify/tests/support/cegis_checker_gap.rs - the exact Layer B
// independent-checker availability probe.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Layer B's reflexivity proof is hole-free and externally checkable. This
// helper exempts only a machine that has AY but no usable Clean/Carcara
// checker; malformed, holey, missing, or rejected proof evidence remains a
// hard test failure.

use trust_cg_verify::{CegisLoop, CegisResult, SmtExpr};

const CHECKER_UNAVAILABLE_PREFIX: &str =
    "solver returned unknown: AY reported UNSAT but it CANNOT BE CHECKED here —";

/// True only when the exact Layer B obligation reached an AY UNSAT result but
/// this machine has no usable independent checker.
///
/// The exact diagnostic is minted only by the checker-discovery failure in
/// `promote_fresh_solver_unsat`. A proof-generation regression or rejection
/// by a working checker deliberately does not match and therefore cannot hide
/// behind this environment exemption.
pub fn independent_checker_unavailable_blocks_layer_b() -> bool {
    let width = 32;
    let src = SmtExpr::var("y", width).bvadd(SmtExpr::bv_const(7, width));
    let tgt = SmtExpr::var("y", width).bvadd(SmtExpr::bv_const(7, width));
    let vars = [("y".to_string(), width)];
    let mut cegis = CegisLoop::new(1, 1_000);

    matches!(
        cegis.verify(&src, &tgt, &vars),
        CegisResult::Error(reason) if checker_is_unavailable(&reason)
    )
}

fn checker_is_unavailable(reason: &str) -> bool {
    reason.starts_with(CHECKER_UNAVAILABLE_PREFIX)
}

pub const INDEPENDENT_CHECKER_GAP_SKIP_NOTICE: &str = "skipping assertion: AY emitted the exact, \
     hole-free Layer B proof, but this machine has no usable independent \
     Clean/Carcara checker";

#[cfg(test)]
mod tests {
    use super::checker_is_unavailable;

    #[test]
    fn exemption_matches_only_checker_discovery_failure() {
        assert!(checker_is_unavailable(
            "solver returned unknown: AY reported UNSAT but it CANNOT BE CHECKED here — no usable checker"
        ));

        for reason in [
            "solver returned unknown: incomplete AY proof certificate: unproved_steps=1",
            "solver returned unknown: unusable AY proof evidence: artifact is holey",
            "solver returned unknown: AY reported UNSAT but emitted an empty Alethe proof",
            "solver returned unknown: AY reported UNSAT but a working checker rejected THIS Alethe proof",
            "solver returned unknown: (:reason-unknown (incomplete self-check-rejected))",
        ] {
            assert!(
                !checker_is_unavailable(reason),
                "proof regression must not be mistaken for an unavailable checker: {reason}"
            );
        }
    }
}
