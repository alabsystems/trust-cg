// trust-cg-verify/tests/support/cegis_alethe_gap.rs - the Layer A
// Alethe-export-gap probe shared by the CEGIS integration tests.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The same self-policing pattern as `mem_refine.rs::alethe_crosscheck_gap`:
// a guarded test skips its commit assertions ONLY while the exact
// fail-closed diagnostic is reproduced live, prints a loud notice, and keeps
// every original assertion as the fall-through — so the exemption cannot rot
// and un-skips itself the moment the constellation can certify the lane.

// Each including test binary compiles its own copy and may use only one of
// the probes; the other must not warn it red.
#![allow(dead_code)]

use trust_cg_verify::{CegisLoop, CegisResult, SmtExpr};

/// True while the constellation cannot INDEPENDENTLY CERTIFY the exact Layer
/// A obligation (`x * 0 == 0` at width 32) even though AY proves it UNSAT.
///
/// Mechanism (measured at the ay v0.9.0 authority 1f8238bb, and identical at
/// v0.8.0): AY solves the obligation by elaboration folding, and its Alethe
/// export for the BV bit-blast lane is not externally checkable —
/// * the coarse `BvBitBlast` lemma prints as an attributed `:rule hole`
///   (carcara's `bitblast_*` suite has no rule for ay's blaster; only the
///   bvand/bvor-idempotent, double-bvnot, and ground-disequality families
///   are derived, ay 563046a8bb), so an external checker reports the
///   document *holey*, never *valid*; and
/// * pre-fix authorities additionally re-spell the `assume` through a
///   folded-subterm surface override (`(bvmul x #x00000000)` recorded as the
///   spelling OF `#x00000000`), so carcara rejects the document on `assume`
///   matching before the hole is even reached (fixed on ay main; rides the
///   next authority).
///
/// trust-cg's bridge therefore fail-closes by design — either immediately on
/// AY's own `ay.proof.certificate … unproved_steps=1` disclosure
/// (`incomplete AY proof certificate`), or in `promote_fresh_solver_unsat`
/// when the independent checker cannot confirm (`AY reported UNSAT but …`).
/// `CegisLoop::verify` wraps whichever fired as `CegisResult::Error("solver
/// returned unknown: {…}")` (see [`CERTIFICATION_GAP_PREFIXES`]), and the
/// pass counts a verifier error and never commits — which is the
/// differential the guarded tests observe.
///
/// The probe re-runs the EXACT obligation through the same public
/// verification chain the pass uses (`CegisLoop::new(1, 1_000)`, default
/// solver discovery) and matches the exact diagnostic prefix. Every other
/// outcome — `Equivalent` (the gap is closed: assertions must run),
/// `NotEquivalent`/`Timeout` (a genuine solver regression: assertions must
/// fail), unrelated `Error`s (environment defects: assertions must fail) —
/// returns `false` and the guarded test falls through to its original
/// assertions.
pub fn alethe_export_gap_blocks_layer_a() -> bool {
    let width = 32;
    let src = SmtExpr::var("x", width).bvmul(SmtExpr::bv_const(0, width));
    let tgt = SmtExpr::bv_const(0, width);
    alethe_export_gap_blocks(&src, &tgt, &[("x".to_string(), width)])
}

/// True while the constellation cannot independently certify the exact Layer
/// B obligation (`y + 7 == y + 7` at width 32, the Movz+AddRR fusion the
/// tests build). Unlike Layer A this proof IS fully exportable today
/// (faithful `assume` + `eq_reflexive`, trust-free, hole-free), so this probe
/// matches only while the INDEPENDENT-CHECKER half of the chain is missing —
/// e.g. a `clean` binary built without the `carcara-verify` feature
/// (docs/EXTERNAL_CONSUMERS.md mandates `ay-smt` + `carcara-verify` for
/// external consumers), or no checker installed at all. With a
/// carcara-enabled checker present it returns `false` and the guarded tests
/// run their full original assertions.
pub fn alethe_export_gap_blocks_layer_b() -> bool {
    let width = 32;
    let src = SmtExpr::var("y", width).bvadd(SmtExpr::bv_const(7, width));
    let tgt = SmtExpr::var("y", width).bvadd(SmtExpr::bv_const(7, width));
    alethe_export_gap_blocks(&src, &tgt, &[("y".to_string(), width)])
}

/// Shared probe core: run the exact obligation through the same public
/// verification chain the pass uses and demand the exact fail-closed
/// certification-gap diagnostic.
/// The three exact diagnostics `ay_bridge` mints when AY establishes UNSAT
/// but the INDEPENDENT-CERTIFICATION half of the chain cannot confirm it,
/// each wrapped by `CegisLoop::verify` as `"solver returned unknown: {…}"`:
/// * `incomplete AY proof certificate: …` — AY's own `ay.proof.certificate`
///   disclosure reports `unproved_steps!=0` / `foreign_assumes!=no` /
///   `trust_free!=yes` (the honest-`hole` wire encoding);
/// * `unusable AY proof evidence: …` — AY warned the artifact is holey or
///   that no proof file could be published;
/// * `AY reported UNSAT but …` — the promotion path could not confirm (no
///   readable/non-empty Alethe artifact, no independent Clean/Carcara
///   checker installed, or the checker rejected / could not fully verify
///   the exact proof).
/// Any other outcome — `Equivalent`, `NotEquivalent`, `Timeout`, or an
/// unrelated `Error` — is NOT the certification gap and must fail the
/// guarded test's original assertions.
const CERTIFICATION_GAP_PREFIXES: [&str; 3] = [
    "solver returned unknown: incomplete AY proof certificate:",
    "solver returned unknown: unusable AY proof evidence:",
    "solver returned unknown: AY reported UNSAT but",
];

fn alethe_export_gap_blocks(src: &SmtExpr, tgt: &SmtExpr, vars: &[(String, u32)]) -> bool {
    let mut cegis = CegisLoop::new(1, 1_000);
    match cegis.verify(src, tgt, &vars.to_vec()) {
        CegisResult::Error(reason) => CERTIFICATION_GAP_PREFIXES
            .iter()
            .any(|prefix| reason.starts_with(prefix)),
        _ => false,
    }
}

/// The skip notice printed by every test parked behind
/// [`alethe_export_gap_blocks_layer_a`].
pub const ALETHE_EXPORT_GAP_SKIP_NOTICE: &str = "skipping assertion: AY proves the Layer A obligation UNSAT but its \
     Alethe export for the BV bit-blast lane is not externally checkable \
     (attributed `hole` on the wire; pre-fix authorities also re-spell the \
     assume), so the bridge fail-closed instead of minting Verified";
