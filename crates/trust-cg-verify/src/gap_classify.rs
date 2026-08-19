// trust-cg-verify/gap_classify.rs - the canonical certification-gap reason
// classifiers (pure string predicates, normally compiled)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The CANONICAL pure-string classifiers for AY certification-gap reasons —
//! promoted out of the `#[cfg(test)]`-only [`crate::formal_gap`] module so
//! every out-of-crate exemption predicate (`rustc-codegen-trust-cg`'s
//! `mem_refine.rs::alethe_crosscheck_gap` and its `lib.rs` `AYResult` sibling,
//! `tests/support/cegis_alethe_gap.rs`) can DELEGATE here instead of
//! hand-copying the strings. The hand copies drifted exactly because these
//! predicates were trapped in a private test-only module; keeping them here,
//! normally compiled and public, is the structural fix.
//!
//! Only the two pure classifiers live here. The fresh-transcript re-probe
//! machinery (`confirmed_certification_gap`, `refinement_gap_reason`,
//! `print_gap_skip`) stays test-only in [`crate::formal_gap`], which
//! re-exports these two so its internal call sites are unchanged.
//!
//! These predicates authorize TEST-SIDE self-skips only. The production gate
//! (`proof_gate::unknown_is_hard_failure`) is intentionally NOT built on them:
//! it must keep promoting `self-check-rejected` to a hard
//! `FailureClass::Soundness` failure.

/// Does an `AYResult::Unknown` reason carry one of the three exact
/// fail-closed CHECKED-AUTHORITY diagnostics `ay_bridge` mints when AY
/// establishes UNSAT but the independent-certification half of the chain
/// cannot confirm it? (The wrapped spellings — `"unknown: {…}"` from
/// `wasm_formal::discharge` / `mir_semantics`, `"solver returned unknown:
/// {…}"` from `CegisLoop::verify`, `"ay returned unknown: {…}"` from
/// `fsym_summary` — strip their prefix before calling this.)
pub fn ay_reason_is_certification_gap(reason: &str) -> bool {
    reason.starts_with("incomplete AY proof certificate:")
        || reason.starts_with("unusable AY proof evidence:")
        || reason.starts_with("AY reported UNSAT but")
}

/// Does a FRESH-TRANSCRIPT reason carry AY's self-check capability
/// disclosure — the v0.9.0-era `(:reason-unknown (incomplete
/// self-check-rejected))`, meaning AY computed the UNSAT verdict and its
/// mandatory strict self-certification declined the proof on a resource
/// envelope (`RUP expansion work exceeds limit`)? Matched ONLY on
/// reason-bearing transcripts (never on the server-truncated bare
/// `"unknown"` — the resident `ay --incremental` server discards stderr, so
/// through the server this shape truncates and a bare unknown must keep
/// failing).
///
/// The verdictless window is specific to the v0.9.0-era authorities
/// (ay 3cb091d23c, "bound bit-vector expression export"): ay main
/// (build.7534+) publishes `unsat` with the hole disclosure again — which the
/// established `incomplete AY proof certificate:` shape already accepts — so
/// every exemption built on this predicate self-retires when the installed
/// authority upgrades.
pub fn ay_reason_is_self_check_rejection(reason: &str) -> bool {
    reason.contains("incomplete self-check-rejected")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn certification_gap_matches_the_three_checked_authority_diagnostics() {
        assert!(ay_reason_is_certification_gap(
            "incomplete AY proof certificate: unproved_steps=1 trust_free=no"
        ));
        assert!(ay_reason_is_certification_gap(
            "unusable AY proof evidence: artifact is holey"
        ));
        assert!(ay_reason_is_certification_gap(
            "AY reported UNSAT but the checker rejected the exact Alethe proof"
        ));
        // Prefixes, not substrings: the wrapped spellings must be stripped
        // before calling.
        assert!(!ay_reason_is_certification_gap(
            "unknown: incomplete AY proof certificate: …"
        ));
        assert!(!ay_reason_is_certification_gap("unknown"));
    }

    #[test]
    fn self_check_rejection_matches_only_reason_bearing_transcripts() {
        assert!(ay_reason_is_self_check_rejection(
            "(:reason-unknown (incomplete self-check-rejected))"
        ));
        // The server-truncated bare unknown must NEVER classify as the gap.
        assert!(!ay_reason_is_self_check_rejection("unknown"));
        assert!(!ay_reason_is_self_check_rejection(""));
    }
}
