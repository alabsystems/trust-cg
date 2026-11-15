// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The U10 stack-limit check lemma as a solver-backed gate
//! (`docs/u10-prologue-stack-limit.md` §7).
//!
//! The always-on test evaluates the one QF_BV obligation in-process on edge
//! cases (a test). With `TRUST_CG_RUN_FORMAL_PROOF_TESTS=1`, the strict proof
//! lane's gate, the obligation goes to AY through `ay_bridge::verify_with_ay`.
//! A counterexample fails the test (it would refute the check). Only a
//! `Verified` answer (unsat, with a proof Clean checked) is solver-backed
//! evidence, and the test prints `U10_LEMMA_SOLVER_VERDICT` so the lane
//! record can cite exactly what this host's AY answered; any other answer is
//! no proof, and the lemma's evidence stays the in-process tests. On
//! 2026-09-30 this host's AY answered `unknown` (an incomplete certificate,
//! one unproved step), as it did for every non-degenerate obligation of the
//! instruction-word solver probe.

use trust_cg_verify::aarch64_stack_limit::{lemma_branches, lemma_obligation, lemma_reference};
use trust_cg_verify::ay_bridge::{AYConfig, AYResult, verify_with_ay};

#[test]
fn the_lemma_obligation_states_the_check() {
    let obligation = lemma_obligation();
    assert_eq!(obligation.inputs.len(), 3);
    assert!(
        !obligation.is_degenerate(),
        "the two sides are distinct terms"
    );
    for (p, l, f) in [
        (0u64, 0u64, 0u64),
        (16, 32, 0),
        (32, 16, 16),
        (32, 16, 17),
        (u64::MAX, 0, u64::MAX),
        (0, u64::MAX, 1),
        (u64::MAX, u64::MAX, 0),
    ] {
        assert_eq!(
            lemma_branches(p, l, f),
            lemma_reference(p, l, f),
            "{p} {l} {f}"
        );
    }
}

#[test]
fn the_lemma_has_no_counterexample_and_reports_its_solver_verdict() {
    if std::env::var("TRUST_CG_RUN_FORMAL_PROOF_TESTS").as_deref() != Ok("1") {
        eprintln!(
            "the_lemma_has_no_counterexample_and_reports_its_solver_verdict: set \
             TRUST_CG_RUN_FORMAL_PROOF_TESTS=1 to run"
        );
        return;
    }
    let result = verify_with_ay(&lemma_obligation(), &AYConfig::default());
    let solver_backed = matches!(result, AYResult::Verified);
    println!("U10_LEMMA_SOLVER_VERDICT solver_backed={solver_backed} {result}");
    assert!(
        !matches!(result, AYResult::CounterExample(_)),
        "a counterexample to the stack-limit lemma: {result}"
    );
}
