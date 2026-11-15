// trust-cg-verify/gap_classify.rs - the canonical certification-gap reason
// classifiers (pure string predicates, normally compiled)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The CANONICAL pure-string classifiers for AY certification-gap reasons,
//! normally compiled and public so the out-of-crate test predicate
//! (`rustc-codegen-trust-cg`'s `solver_test_support`) DELEGATES here instead of
//! hand-copying the strings. The hand copies drifted exactly because these
//! predicates were once trapped in a private test-only module.
//!
//! [`ay_reason_is_disclosed_proof_hole`] is the ONE shape a solver-coupled test
//! may skip on, in this crate ([`crate::formal_gap`]) and in the plugin. The
//! broader [`ay_reason_is_certification_gap`] and
//! [`ay_reason_is_self_check_rejection`] describe reasons; they authorize no
//! skip. [`ay_reason_is_soundness_gate_refusal`] names the one unknown that is
//! neither: AY's own model gate caught an invalid model and withheld the
//! verdict. Both describers reject it, and the production gate treats it as a
//! hard failure.
//!
//! The production gate (`proof_gate::unknown_is_hard_failure`) is
//! intentionally NOT built on them: it promotes `self-check-rejected` and a
//! working checker's rejection to a hard `FailureClass::Soundness` failure.

/// The exact banner AY prints on stderr when its ALWAYS-ON model gate catches
/// one of AY's OWN theory-search paths returning a model that falsifies an
/// assertion, and AY fail-closes to `unknown`.
///
/// AY's own wording: "AY fail-closed to `unknown` (this is SOUND); it
/// indicates an internal solver bug worth reporting."
pub const AY_SOUNDNESS_GATE_BANNER: &str = "[AY SOUNDNESS GATE] caught an INVALID model";

/// The reason `ay_bridge::ay_soundness_gate_reason` mints for that banner.
///
/// It is deliberately NOT one of the certification-gap spellings: a caught
/// invalid model is AY disclosing an INTERNAL SOLVER DEFECT on this exact
/// query, not "right verdict, uncertifiable proof". The two must never be
/// confused, so the gap predicates below reject it explicitly rather than
/// relying on the strings failing to overlap.
pub const AY_SOUNDNESS_GATE_REASON: &str =
    "AY soundness gate caught an INVALID model (internal ay defect, verdict withheld)";

/// Does an `AYResult::Unknown` reason carry AY's caught-invalid-model
/// disclosure?
///
/// This is the ONE unknown class that is neither solver capacity nor a
/// certification gap: AY's theory search produced a model its own gate
/// rejected, so AY withheld the verdict. The obligation may be perfectly
/// valid — the AUTHORITY is defective on this query. It is fail-closed
/// everywhere: never a gap-skip (below), and a hard failure in
/// `proof_gate::unknown_is_hard_failure`.
pub fn ay_reason_is_soundness_gate_refusal(reason: &str) -> bool {
    reason.contains(AY_SOUNDNESS_GATE_REASON) || reason.contains(AY_SOUNDNESS_GATE_BANNER)
}

/// Does an `AYResult::Unknown` reason carry one of the three exact
/// fail-closed CHECKED-AUTHORITY diagnostics `ay_bridge` mints when AY
/// establishes UNSAT but the independent-certification half of the chain
/// cannot confirm it? (The wrapped spellings — `"unknown: {…}"` from
/// `wasm_formal::discharge` / `mir_semantics`, `"solver returned unknown:
/// {…}"` from `CegisLoop::verify`, `"ay returned unknown: {…}"` from
/// `fsym_summary` — strip their prefix before calling this.)
///
/// A caught-invalid-model refusal is excluded FIRST and unconditionally: AY
/// can publish the soundness-gate banner alongside an ordinary
/// `:reason-unknown` tail, and a reason that carries both is a defective
/// authority, not a certification gap.
pub fn ay_reason_is_certification_gap(reason: &str) -> bool {
    !ay_reason_is_soundness_gate_refusal(reason)
        && (reason.starts_with("incomplete AY proof certificate:")
            || reason.starts_with("unusable AY proof evidence:")
            || reason.starts_with("AY reported UNSAT but"))
}

/// The prefix `ay_bridge` gives AY's own `c ay.proof.certificate` disclosure
/// when that disclosure says the proof accompanying an `unsat` is incomplete.
pub const INCOMPLETE_AY_PROOF_CERTIFICATE: &str = "incomplete AY proof certificate: ";

/// Is `reason` (an `AYResult::Unknown` reason, wrapper already stripped) a
/// DISCLOSED PROOF HOLE: AY answered `unsat`, and its own certificate line
/// (`incomplete AY proof certificate: c ay.proof.certificate …`) states at
/// least one unproved step (`unproved_steps=N`, N > 0) and no foreign
/// assumption (`foreign_assumes=no`)?
///
/// This is the one AY answer a solver-coupled test may skip on, because it
/// names a capability that is absent and tracked: ay
/// `docs/ay-asks/2026-08-13-bv-certified-families` (item 1) records this exact
/// disclosure as the missing Clean/Carcara-checkable lowering of AY's
/// `BvBitBlast` lemma. (AY build.8256 prints the hole as a bare `:rule hole`
/// step over bit-vector terms and does not name the lemma.) It is AY stating
/// what its proof lacks, not a checker's verdict on the proof.
///
/// Everything else [`ay_reason_is_certification_gap`] accepts is refused here,
/// and a test must fail on it:
/// * `AY reported UNSAT but <checker> — which verified a known-good control
///   proof, so it is a working checker — rejected or could not fully verify
///   THIS Alethe proof`: a working checker did not accept the exact proof;
/// * `AY reported UNSAT but Clean replay could not complete: …`: the replay
///   failed;
/// * `AY reported UNSAT but it CANNOT BE CHECKED here — …`: no usable checker.
///   Tests check that a solver and checker are available before they run the
///   solver, so reaching this means the toolchain broke mid-run;
/// * `AY reported UNSAT but emitted an empty` / `no readable Alethe proof`, and
///   `unusable AY proof evidence: …`: AY did not publish usable evidence;
/// * a certificate that declares a foreign assumption, states no unproved
///   step, or has an unreadable step count.
pub fn ay_reason_is_disclosed_proof_hole(reason: &str) -> bool {
    let Some(line) = reason.strip_prefix(INCOMPLETE_AY_PROOF_CERTIFICATE) else {
        return false;
    };
    if !line.starts_with("c ay.proof.certificate ") {
        return false;
    }
    let mut unproved_steps: Option<Option<u64>> = None;
    let mut foreign_assumes: Option<&str> = None;
    for field in line.split_whitespace() {
        if let Some(value) = field.strip_prefix("unproved_steps=") {
            unproved_steps = Some(value.parse().ok());
        } else if let Some(value) = field.strip_prefix("foreign_assumes=") {
            foreign_assumes = Some(value);
        }
    }
    matches!(unproved_steps, Some(Some(steps)) if steps > 0) && foreign_assumes == Some("no")
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
/// The verdictless window was specific to the v0.9.0-era authorities
/// (ay 3cb091d23c, "bound bit-vector expression export"). The reason alone does
/// not say WHY the self-check rejected the proof: with AY build.8256 the
/// rejections measured in the plugin's tests are strict proof-validation
/// failures ("step t0 uses unsupported hole rule", "step t1 uses unverified
/// trust rule"). No test skips on it.
pub fn ay_reason_is_self_check_rejection(reason: &str) -> bool {
    !ay_reason_is_soundness_gate_refusal(reason)
        && reason.contains("incomplete self-check-rejected")
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
    fn a_disclosed_proof_hole_is_the_only_skippable_shape() {
        // The measured shape (AY build.8256).
        let hole = "incomplete AY proof certificate: c ay.proof.certificate \
                    path=/tmp/q.alethe unproved_steps=1 foreign_assumes=no trust_free=no \
                    ay_self_checkable=yes";
        assert!(ay_reason_is_disclosed_proof_hole(hole));
        assert!(ay_reason_is_certification_gap(hole));
        assert!(ay_reason_is_disclosed_proof_hole(
            "incomplete AY proof certificate: c ay.proof.certificate unproved_steps=3 \
             foreign_assumes=no"
        ));

        // The broader predicate accepts each of these; a test must fail on them.
        for reason in [
            // A working checker did not accept THIS proof (measured, clean 8606).
            "AY reported UNSAT but /pkg/clean/8606/bin/clean — which verified a known-good \
             control proof, so it is a working checker — rejected or could not fully verify \
             THIS Alethe proof",
            "AY reported UNSAT but Clean replay could not complete: spawn failed",
            "AY reported UNSAT but it CANNOT BE CHECKED here — no usable checker. This is a \
             toolchain problem, not evidence about the proof.",
            "AY reported UNSAT but emitted an empty Alethe proof",
            "AY reported UNSAT but emitted no readable Alethe proof at /tmp/q.alethe: gone",
            "unusable AY proof evidence: c warning: the proof is holey",
            // No unproved step is not a hole, even with no foreign assumption:
            // `ay_bridge` mints this reason from `trust_free=no` alone.
            "incomplete AY proof certificate: c ay.proof.certificate path=/tmp/q.alethe \
             unproved_steps=0 foreign_assumes=no trust_free=no ay_self_checkable=yes",
            // A foreign assumption is not a hole.
            "incomplete AY proof certificate: c ay.proof.certificate path=/tmp/q.alethe \
             unproved_steps=0 foreign_assumes=yes trust_free=no",
            "incomplete AY proof certificate: c ay.proof.certificate path=/tmp/q.alethe \
             unproved_steps=1 foreign_assumes=yes trust_free=no",
            // The certificate must state its step count and its assumptions.
            "incomplete AY proof certificate: c ay.proof.certificate trust_free=no",
            "incomplete AY proof certificate: c ay.proof.certificate unproved_steps=1",
            "incomplete AY proof certificate: c ay.proof.certificate unproved_steps=x \
             foreign_assumes=no",
            "incomplete AY proof certificate: unproved_steps=1 foreign_assumes=no",
        ] {
            assert!(
                ay_reason_is_certification_gap(reason),
                "control: the broader predicate accepts {reason:?}"
            );
            assert!(
                !ay_reason_is_disclosed_proof_hole(reason),
                "a test must not skip on {reason:?}"
            );
        }
        // Prefixes, not substrings; and never a verdict or a bare unknown.
        assert!(!ay_reason_is_disclosed_proof_hole(&format!(
            "unknown: {hole}"
        )));
        assert!(!ay_reason_is_disclosed_proof_hole("unknown"));
        assert!(!ay_reason_is_disclosed_proof_hole(
            "(:reason-unknown (incomplete self-check-rejected))"
        ));
    }

    #[test]
    fn soundness_gate_refusal_is_never_a_certification_gap() {
        // The minted reason, and the raw banner it is minted from.
        for reason in [
            AY_SOUNDNESS_GATE_REASON,
            AY_SOUNDNESS_GATE_BANNER,
            "AY soundness gate caught an INVALID model (internal ay defect, verdict \
             withheld): AY fail-closed on this exact query; its published reason was \
             (:reason-unknown incomplete)",
        ] {
            assert!(ay_reason_is_soundness_gate_refusal(reason), "{reason}");
            assert!(!ay_reason_is_certification_gap(reason), "{reason}");
            assert!(!ay_reason_is_self_check_rejection(reason), "{reason}");
            assert!(!ay_reason_is_disclosed_proof_hole(reason), "{reason}");
        }
    }

    #[test]
    fn soundness_gate_refusal_outranks_an_accompanying_gap_spelling() {
        // AY may publish the caught-invalid-model banner AND a
        // `self-check-rejected` tail for the same query. The defective
        // authority wins: neither gap predicate may accept it, or a caught
        // invalid model would be laundered into a loud-but-tolerated skip.
        let both = format!(
            "{AY_SOUNDNESS_GATE_REASON}: AY fail-closed on this exact query; its published \
             reason was (:reason-unknown (incomplete self-check-rejected))"
        );
        assert!(ay_reason_is_soundness_gate_refusal(&both));
        assert!(!ay_reason_is_self_check_rejection(&both));
        assert!(!ay_reason_is_certification_gap(&both));
        assert!(!ay_reason_is_disclosed_proof_hole(&both));
        // Control: the same tail WITHOUT the gate banner still classifies.
        assert!(ay_reason_is_self_check_rejection(
            "(:reason-unknown (incomplete self-check-rejected))"
        ));
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
