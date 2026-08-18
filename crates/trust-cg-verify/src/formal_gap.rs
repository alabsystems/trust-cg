// trust-cg-verify/formal_gap.rs - the shared certification-gap probe for
// solver-coupled lib tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The SHARED certification-gap probe behind the solver-coupled `src/`
//! `#[cfg(test)]` guards — the in-crate sibling of the two established
//! precedents (`rustc-codegen-trust-cg`'s `mem_refine.rs::
//! alethe_crosscheck_gap` and `tests/support/cegis_alethe_gap.rs`): a guarded
//! test skips its commit assertion ONLY while the exact fail-closed
//! certification-gap diagnostic is reproduced live, prints a loud
//! `certification-gap skip:` notice naming the obligation and diagnostic, and
//! keeps every original assertion as the fall-through — so the exemption
//! cannot rot and un-skips itself the moment the constellation can certify
//! the lane.
//!
//! # What the gap is (measured 2026-08-13)
//!
//! Since 0cceae8f (“require checked AY proof authority”, 2026-08-03) a lib
//! obligation is `Verified` ONLY when AY's `unsat` is INDEPENDENTLY
//! certified: a non-empty Alethe artifact that the external Clean/Carcara
//! checker fully verifies, with AY's own `ay.proof.certificate` disclosure
//! clean. Before that commit a raw solver `unsat` minted `Verified` directly
//! (`"unsat" => AYResult::Verified`), and the whole suite was green with a
//! solver — the full-database strict gate bounded capacity debt to five
//! audited rows the same morning (6f77b922, 2026-08-03 02:03). The
//! constellation cannot yet certify the bit-vector families:
//!
//! * **`incomplete AY proof certificate: …`** — AY proves `unsat` but its
//!   Alethe export carries the coarse `BvBitBlast` lemma as an attributed
//!   honest `hole` (`unproved_steps=1 … trust_free=no`); carcara has no rule
//!   for AY's blaster, so the bridge fail-closes on AY's own disclosure.
//! * **`unusable AY proof evidence: …`** — AY warned the artifact is holey
//!   or that no proof file could be published.
//! * **`AY reported UNSAT but …`** — the promotion path could not confirm
//!   (empty/unreadable Alethe artifact, no independent checker installed, or
//!   the checker rejected / could not fully verify the exact proof — e.g.
//!   the folded-subterm `assume` re-spell fixed on ay main in c7a7488828
//!   that released v0.9.0 authorities still ship).
//! * **`(:reason-unknown (incomplete self-check-rejected))`** — new at the
//!   v0.9.0 authorities (ay 3cb091d23c, 2026-08-11, “bound bit-vector
//!   expression export”): for the larger blasts (full 32-bit shifter,
//!   popcount SWAR, whole-register NEON, symbolic-array GPU maps) AY
//!   COMPUTES UNSAT and then its mandatory strict self-certification rejects
//!   the proof on a resource envelope (`RUP expansion work exceeds limit`),
//!   publishing `unknown` instead of the verdict. ay v0.8.0 (6118a522,
//!   pre-envelope) still answered `unsat` for these, and ay main
//!   (build.7534+) publishes `unsat` with the hole disclosure again — the
//!   verdictless window is specific to the v0.9.0-era authorities.
//!
//! The resident `ay --incremental` server deliberately discards stderr (it
//! is not query-framed), so through the server the last class truncates to a
//! bare `Unknown("unknown")`. A bare unknown is NOT accepted as a gap on its
//! face: [`confirmed_certification_gap`] re-probes the exact obligation
//! through the fresh one-shot transcript
//! ([`crate::ay_bridge::verify_fresh_transcript_for_gap_probe`]) and demands
//! AY's own published reason — a regression-unknown (a genuinely undecided
//! query) re-probes to a different reason and the guarded test falls through
//! to its original assertion and FAILS.
//!
//! Soundness of the guard: every guarded obligation is a known-true VC whose
//! refutation lane stays fully armed — a `CounterExample` (the only verdict
//! that can indicate a miscompile), a `Timeout`, an unexpected diagnostic, or
//! a panic all still fail the original assertion. Only the exact
//! “right verdict, uncertifiable proof” shapes skip, loudly. The ay-side
//! capability ask is recorded in ay's `docs/ay-asks/` (BvBitBlast Alethe
//! lowering for the shift/cast/fcmp/popcount/array families + the v0.9.0
//! self-check-envelope verdict discard).

#![cfg(test)]

use crate::ay_bridge::{AYConfig, AYResult};
use crate::lowering_proof::ProofObligation;

/// Does an [`AYResult::Unknown`] reason carry one of the three exact
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
/// envelope? Matched ONLY on reason-bearing transcripts (never on the
/// server-truncated bare `"unknown"`).
pub fn ay_reason_is_self_check_rejection(reason: &str) -> bool {
    reason.contains("incomplete self-check-rejected")
}

/// The certification-gap classifier over a live [`AYResult`]: `Some(reason)`
/// iff `result` is EXACTLY one of the fail-closed certification-gap shapes,
/// re-probing a server-truncated bare `Unknown("unknown")` through the fresh
/// one-shot transcript (same obligation, same config, resident server and
/// every cache tier bypassed) to recover AY's own published reason.
///
/// Every other outcome returns `None` and the guarded test must fall through
/// to its original assertion: `Verified` (the gap is closed — assertions must
/// run), `CounterExample` (a genuine soundness failure — assertions must
/// fail), `Timeout`/`Error`/an unrecognized `Unknown` reason (regressions or
/// environment defects — assertions must fail). A bare unknown whose fresh
/// re-probe comes back `Verified` also returns `None`: the constellation just
/// proved it CAN certify the obligation, so the original flake must surface.
pub fn confirmed_certification_gap(
    obligation: &ProofObligation,
    config: &AYConfig,
    result: &AYResult,
) -> Option<String> {
    match result {
        AYResult::Unknown(reason) if ay_reason_is_certification_gap(reason) => Some(reason.clone()),
        AYResult::Unknown(reason) if ay_reason_is_self_check_rejection(reason) => {
            Some(reason.clone())
        }
        // The resident server discards stderr, so AY's reason is lost; only
        // an EXACT bare "unknown" is eligible for the fresh re-probe.
        AYResult::Unknown(reason) if reason == "unknown" => {
            match crate::ay_bridge::verify_fresh_transcript_for_gap_probe(obligation, config) {
                AYResult::Unknown(fresh) if ay_reason_is_self_check_rejection(&fresh) => Some(
                    format!("{fresh} (fresh-transcript re-probe of a server-truncated unknown)"),
                ),
                AYResult::Unknown(fresh) if ay_reason_is_certification_gap(&fresh) => Some(
                    format!("{fresh} (fresh-transcript re-probe of a server-truncated unknown)"),
                ),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The [`crate::mir_semantics::RefinementOutcome`] spelling of the gap (the
/// `mem_refine.rs::alethe_crosscheck_gap` sibling shared by the MIR and
/// loop-back-edge refinement tests): `Some(reason)` while the outcome is
/// `Inconclusive` on EXACTLY one of the fail-closed certification-gap
/// diagnostics (`discharge_refinement` wraps AY's reason as
/// `"unknown: {reason}"`). `Refuted`, a bare or unrecognized unknown,
/// timeout, and error all return `None` so the guarded test falls through to
/// its original assertion.
pub fn refinement_gap_reason(outcome: &crate::mir_semantics::RefinementOutcome) -> Option<&str> {
    match outcome {
        crate::mir_semantics::RefinementOutcome::Inconclusive { reason } => {
            let stripped = reason.strip_prefix("unknown: ")?;
            (ay_reason_is_certification_gap(stripped)
                || ay_reason_is_self_check_rejection(stripped))
            .then_some(reason.as_str())
        }
        _ => None,
    }
}

/// The uniform loud skip line for every guarded lib test: grep-able prefix,
/// the obligation (or context) it covers, and the exact live diagnostic that
/// authorized the skip.
pub fn print_gap_skip(context: &str, reason: &str) {
    eprintln!(
        "certification-gap skip: {context}: {reason} — AY establishes the verdict but the \
         constellation cannot independently certify this bit-vector family yet (BvBitBlast \
         Alethe lowering gap / v0.9.0 strict self-check envelope; see ay docs/ay-asks \
         2026-08-13-bv-certified-families). The original assertion resumes automatically \
         once an authority ships externally checkable proofs."
    );
}
