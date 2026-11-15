// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! Diagnostic mapping controls only; these do not discharge a body theorem.

use super::{x86_body_replay_trace, x86_body_row_result};
use crate::function_verifier::InstructionVerificationResult;
use crate::lowering_proof::{MachineSideProvenance, ProofObligation};
use crate::smt::SmtExpr;
use crate::verify::VerificationResult;
use crate::x86_source_bound_body::{X86_BODY_NEEDS_REPLAY, X86_BODY_OBLIGATION_NAME};

fn obligation() -> ProofObligation {
    // Distinct expressions make the classification's degeneracy bit explicit.
    // A fabricated outcome below tests formatting, never replay authority.
    ProofObligation {
        name: X86_BODY_OBLIGATION_NAME.into(),
        trust_ir_expr: SmtExpr::var("source", 64),
        aarch64_expr: SmtExpr::var("machine", 64),
        inputs: vec![("source".into(), 64), ("machine".into(), 64)],
        preconditions: Vec::new(),
        fp_inputs: Vec::new(),
        category: None,
        machine_side_provenance: MachineSideProvenance::Reconstructed {
            from_opcode: "diagnostic_fixture_only".into(),
            arity: 2,
        },
    }
}

#[test]
fn x86_replay_trace_without_explanation_keeps_existing_outcome_text() {
    for (verdict, expected) in [
        (None, "none (no independently checked proof)"),
        (Some(VerificationResult::Valid), "Valid"),
        (
            Some(VerificationResult::Invalid {
                counterexample: "e_rdi = 1".into(),
            }),
            "Invalid (refuted)",
        ),
        (
            Some(VerificationResult::Unknown {
                reason: "budget".into(),
            }),
            "Unknown (budget)",
        ),
    ] {
        assert_eq!(x86_body_replay_trace(&verdict, None, false), expected);
    }
}

#[test]
fn x86_replay_trace_retains_exact_refusals_without_granting_credit() {
    for explanation in [
        "replay refused: TCG_REFINE_SOLVER=0",
        "AY ERROR: and_pos indexed conjunct is absent from its effective source\nexit.code=1",
        "negative memo (AY not run): AY UNKNOWN: incomplete",
        "Valid; this untrusted text cannot grant proof credit",
    ] {
        assert_eq!(
            x86_body_replay_trace(&None, Some(explanation), false),
            format!("none (no independently checked proof); reason={explanation}"),
        );
        assert!(matches!(
            x86_body_row_result(&obligation(), None, false),
            InstructionVerificationResult::Unverified { reason } if reason == X86_BODY_NEEDS_REPLAY
        ));
    }
}

#[test]
fn x86_replay_trace_preserves_producer_provenance_and_existing_valid_row_bytes() {
    let verdict = Some(VerificationResult::Valid);
    let before = format!(
        "{:?}",
        x86_body_row_result(&obligation(), verdict.clone(), false)
    );
    let producer = "source=closed-definition-proof ay-ran=false checker-sha256=actual-identity";
    assert_eq!(
        x86_body_replay_trace(&verdict, Some(producer), false),
        format!("Valid; reason={producer}"),
    );
    let after = format!("{:?}", x86_body_row_result(&obligation(), verdict, false));
    assert_eq!(before, after, "trace text cannot alter evidence fields");
}

#[test]
fn x86_replay_trace_never_reclassifies_refuted_or_unknown_outcomes() {
    for (verdict, expected_trace, expected_detail) in [
        (
            VerificationResult::Invalid {
                counterexample: "e_rdi = 1".into(),
            },
            "Invalid (refuted); reason=Valid",
            "e_rdi = 1",
        ),
        (
            VerificationResult::Unknown {
                reason: "budget".into(),
            },
            "Unknown (budget); reason=Valid",
            "Unknown: budget",
        ),
    ] {
        let verdict = Some(verdict);
        assert_eq!(
            x86_body_replay_trace(&verdict, Some("Valid"), false),
            expected_trace
        );
        assert!(matches!(
            x86_body_row_result(&obligation(), verdict, false),
            InstructionVerificationResult::Failed { proof_name, detail }
                if proof_name == X86_BODY_OBLIGATION_NAME && detail == expected_detail
        ));
    }
}

/// Slice 21 (ruling OD-200): a refutation of an FP-abstract theorem (one
/// with a rounding event or row, whose pairings claim operand patterns equal
/// and whose results are FP leaves) is no counterexample: its rows are left
/// uncredited, never failed, and its trace reads `Unknown (FP abstraction)`;
/// a `Valid` replay still credits. A theorem without one keeps the refutation.
#[test]
fn an_fp_abstract_refutation_is_uncredited_and_never_reported_refuted() {
    let refuted = || {
        Some(VerificationResult::Invalid {
            counterexample: "fe0 = 1".into(),
        })
    };
    assert!(matches!(
        x86_body_row_result(&obligation(), refuted(), true),
        InstructionVerificationResult::Unverified { reason }
            if reason == super::X86_BODY_FP_ABSTRACT_SAT
    ));
    assert_eq!(
        x86_body_replay_trace(&refuted(), None, true),
        "Unknown (FP abstraction: a satisfying model is no counterexample)"
    );
    assert!(matches!(
        x86_body_row_result(&obligation(), Some(VerificationResult::Valid), true),
        InstructionVerificationResult::Verified { .. }
    ));
    assert!(matches!(
        x86_body_row_result(&obligation(), None, true),
        InstructionVerificationResult::Unverified { reason } if reason == X86_BODY_NEEDS_REPLAY
    ));
    assert!(matches!(
        x86_body_row_result(&obligation(), refuted(), false),
        InstructionVerificationResult::Failed { .. }
    ));
    assert_eq!(
        x86_body_replay_trace(&refuted(), None, false),
        "Invalid (refuted)"
    );
}
