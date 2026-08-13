// trust-cg-codegen/proof_evidence.rs - Proof-evidence honesty (WP-0)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Proof-evidence honesty: make "nothing ran" *representable and emitted*.
//!
//! # The defect this module closes
//!
//! trust-cg needs its proof-oriented claims to remain inspectable. A consumer
//! reading a compiled artifact could not, before this module, distinguish three
//! very different situations:
//!
//! 1. an obligation was **proved** by a solver,
//! 2. an obligation was **checked statistically** (edge cases + N random
//!    trials — high confidence, not a proof),
//! 3. **nothing ran at all**.
//!
//! The reason is structural: on the routes where nothing runs, the evidence
//! field was simply **absent** rather than negative. One consumer
//! compiles with `verify: false` and `DispatchVerifyMode::Off`, so none of the
//! per-instruction lowering proofs, TV gates, or function verifiers execute on
//! that path — and nothing in the artifact said so. An absent fact is
//! indistinguishable from a passing one.
//!
//! This module supplies the three pieces that fix that:
//!
//! * [`route_evidence`] — every compile route produces a
//!   [`ProofEvidenceSummary`], and a route where nothing ran produces an
//!   explicit [`ProofEvidenceVerdict::MissingEvidence`] at
//!   [`EvidenceStrength::NotRun`].
//! * [`accepted_assumptions_for_route`] — what the artifact is *relying on*
//!   rather than checking, as a machine-readable channel.
//! * [`refuse_required_strength`] — strength is **refusable**, not merely
//!   reportable. A compile requested at a strength this host cannot reach is
//!   rejected instead of being quietly certified at a weaker strength.
//!
//! # What this module deliberately does NOT do
//!
//! It changes what is **reported**, never what is **checked**. It flips no
//! default, weakens no gate, and runs no verifier. Every summary it produces
//! is a description of work that some other component did or did not do.

use std::sync::OnceLock;

use trust_cg_verify::VerificationStrength;
use trust_cg_verify::ay_bridge::z3_available;
use trust_cg_verify::dataflow_integrity::{
    AARCH64_DATAFLOW_INTEGRITY_DEFAULT, DataflowIntegrityMode, X86_DATAFLOW_INTEGRITY_DEFAULT,
    dataflow_integrity_mode,
};
use trust_cg_verify::lowering_proof::VerificationConfig;

use crate::jit_contract::{
    ASSUMPTION_DISPATCH_VERIFY_OFF, ASSUMPTION_MANIFEST_PIN_NOT_REDERIVED,
    ASSUMPTION_NO_SOLVER_AVAILABLE, ASSUMPTION_STATISTICAL_DISCHARGE,
    ASSUMPTION_TV3_WARN_NOT_ENFORCE, ASSUMPTION_VERIFICATION_DISABLED, AcceptedAssumption,
    DeterministicArtifactManifest, EvidenceStrength, ProofEvidenceRejectionCode,
    ProofEvidenceSummary, ProofEvidenceVerdict, ProofPolicy, RequiredEvidenceStrength,
};
use crate::target::Target;

/// Stable verifier name used by summaries that describe a compile route rather
/// than a specific solver run.
pub const ROUTE_EVIDENCE_VERIFIER: &str = "trust-cg.compile_route";

/// Stable diagnostic code for a compile refused because the host cannot reach
/// the requested discharge strength.
pub const PROOF_STRENGTH_UNAVAILABLE_CODE: &str = "proof_strength_unavailable";

/// Host facts that determine what strength any obligation can be discharged at
/// on this machine, right now.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EvidenceEnvironment {
    /// Whether an `ay`/`z3` solver binary is reachable.
    ///
    /// When false, **no** obligation can be discharged formally on this host,
    /// no matter what the caller asks for.
    pub solver_available: bool,
    /// Number of random trials a statistical discharge uses.
    pub statistical_sample_count: u64,
    /// Maximum bit width (with <= 2 inputs) that is enumerated exhaustively.
    pub exhaustive_threshold_bits: u32,
    /// Active TV-3 dataflow-integrity enforcement mode for the host arch.
    pub dataflow_integrity: DataflowIntegrityMode,
}

fn solver_available_cached() -> bool {
    // `z3_available()` shells out to `which`; probe once per process.
    static AVAILABLE: OnceLock<bool> = OnceLock::new();
    *AVAILABLE.get_or_init(z3_available)
}

/// Default TV-3 enforcement mode for `target`, before env overrides.
pub const fn dataflow_integrity_default_for(target: Target) -> DataflowIntegrityMode {
    match target {
        Target::Aarch64 => AARCH64_DATAFLOW_INTEGRITY_DEFAULT,
        _ => X86_DATAFLOW_INTEGRITY_DEFAULT,
    }
}

/// Snapshot the host's discharge environment.
///
/// The solver probe is cached for the process (it spawns a subprocess); the
/// dataflow-integrity mode is re-read each call because it is env-overridable
/// and tests flip it.
pub fn evidence_environment() -> EvidenceEnvironment {
    evidence_environment_for(Target::host())
}

/// Snapshot the discharge environment as it applies to `target`.
pub fn evidence_environment_for(target: Target) -> EvidenceEnvironment {
    let config = VerificationConfig::default();
    EvidenceEnvironment {
        solver_available: solver_available_cached(),
        statistical_sample_count: config.sample_count,
        exhaustive_threshold_bits: config.exhaustive_threshold,
        dataflow_integrity: dataflow_integrity_mode(dataflow_integrity_default_for(target)),
    }
}

impl EvidenceEnvironment {
    /// Strongest strength any obligation of the given shape can reach here.
    ///
    /// Mirrors [`VerificationStrength::for_obligation_with_config`] exactly for
    /// the sampling/enumeration split, then upgrades to
    /// [`EvidenceStrength::Formal`] only when a solver is actually reachable.
    pub fn strength_for(&self, width_bits: u32, input_count: usize) -> EvidenceStrength {
        if self.solver_available {
            return EvidenceStrength::Formal {
                solver: "ay".to_owned(),
            };
        }
        if input_count <= 2 && width_bits <= self.exhaustive_threshold_bits {
            EvidenceStrength::Exhaustive
        } else {
            EvidenceStrength::Statistical {
                sample_count: self.statistical_sample_count,
            }
        }
    }

    /// Whether this host can reach `required` at all.
    pub fn can_reach(&self, required: RequiredEvidenceStrength) -> bool {
        match required {
            RequiredEvidenceStrength::Any => true,
            // Exhaustive enumeration is always available for narrow
            // obligations, and a solver covers everything.
            RequiredEvidenceStrength::Complete => true,
            RequiredEvidenceStrength::Formal => self.solver_available,
        }
    }
}

/// Translate a `trust-cg-verify` strength into the reportable contract
/// strength, so a route that actually ran a verifier reports the verifier's
/// own answer rather than a re-derived guess.
pub fn strength_from_verification(strength: &VerificationStrength) -> EvidenceStrength {
    match strength {
        VerificationStrength::Exhaustive => EvidenceStrength::Exhaustive,
        VerificationStrength::Statistical { sample_count } => EvidenceStrength::Statistical {
            sample_count: *sample_count,
        },
        VerificationStrength::Formal => EvidenceStrength::Formal {
            solver: "ay".to_owned(),
        },
    }
}

/// What a compile route actually ran, as reported by the route itself.
///
/// Every field is a statement about execution, not about intent: `false` means
/// the corresponding check did not run on this compile.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct RouteFacts {
    /// Per-instruction / function-level verification ran.
    pub instruction_verification_ran: bool,
    /// Dispatch-plan verification ran (`verify_dispatch != Off`).
    pub dispatch_verification_ran: bool,
    /// Per-instruction lowering proof certificates were emitted.
    pub proof_certificates_emitted: bool,
    /// A proof/translation-validation evidence report was attached.
    pub evidence_report_present: bool,
    /// A conformance/coverage manifest was accepted as a pin rather than
    /// re-derived from the sources it summarizes.
    pub manifest_pin_accepted: bool,
}

impl RouteFacts {
    /// Whether anything discharged a *lowering obligation* on this route.
    ///
    /// Dispatch-plan verification is deliberately excluded. It checks a
    /// heterogeneous dispatch property, not the correctness of any instruction
    /// lowering, so counting it would let a compile that proved nothing about
    /// its own code report a discharge strength. That is the same
    /// absence-reads-as-presence failure WP-0 exists to close, just one level
    /// up.
    pub const fn obligations_discharged(&self) -> bool {
        self.instruction_verification_ran
            || self.proof_certificates_emitted
            || self.evidence_report_present
    }

    /// Whether any check at all ran on this route, dispatch included.
    pub const fn anything_ran(&self) -> bool {
        self.obligations_discharged() || self.dispatch_verification_ran
    }
}

/// The assumptions a route is relying on, given the host environment.
///
/// The list is sorted by id and deduplicated by
/// [`ProofEvidenceSummary::with_accepted_assumptions`].
pub fn accepted_assumptions_for_route(
    facts: RouteFacts,
    environment: &EvidenceEnvironment,
) -> Vec<AcceptedAssumption> {
    let mut assumptions = Vec::new();

    if !facts.instruction_verification_ran {
        assumptions.push(AcceptedAssumption::new(
            ASSUMPTION_VERIFICATION_DISABLED,
            "instruction-level verification was disabled for this compile: no per-instruction \
             lowering proof, no function verifier, and no translation-validation gate ran",
        ));
    }
    if !facts.dispatch_verification_ran {
        assumptions.push(AcceptedAssumption::new(
            ASSUMPTION_DISPATCH_VERIFY_OFF,
            "dispatch-plan verification was switched off for this compile",
        ));
    }
    if facts.manifest_pin_accepted {
        assumptions.push(AcceptedAssumption::new(
            ASSUMPTION_MANIFEST_PIN_NOT_REDERIVED,
            "a caller-supplied manifest was accepted as a pin: its declared bindings were checked \
             for internal consistency, not re-derived from the sources they summarize",
        ));
    }
    if !environment.solver_available {
        assumptions.push(AcceptedAssumption::new(
            ASSUMPTION_NO_SOLVER_AVAILABLE,
            "no ay/z3 solver binary is reachable on this host, so no obligation on this compile \
             could be discharged formally",
        ));
        if facts.obligations_discharged() {
            assumptions.push(AcceptedAssumption::new(
                ASSUMPTION_STATISTICAL_DISCHARGE,
                format!(
                    "obligations wider than {} bits (or with more than 2 inputs) were discharged \
                     by sampling: edge cases plus {} random trials are assumed to generalize to \
                     the full input space",
                    environment.exhaustive_threshold_bits, environment.statistical_sample_count
                ),
            ));
        }
    }
    if environment.dataflow_integrity == DataflowIntegrityMode::Warn {
        assumptions.push(AcceptedAssumption::new(
            ASSUMPTION_TV3_WARN_NOT_ENFORCE,
            "the TV-3 dataflow-integrity validator is in warn mode on this target: a violation is \
             reported but does not fail the compile closed",
        ));
    }

    assumptions
}

/// Strength a route reached, given what it ran and where it ran.
///
/// 32/64-bit obligations dominate every real compile, so the honest aggregate
/// is the strength the *widest* obligation could reach — never the best case.
fn route_strength(facts: RouteFacts, environment: &EvidenceEnvironment) -> EvidenceStrength {
    if facts.obligations_discharged() {
        environment.strength_for(64, 2)
    } else {
        EvidenceStrength::NotRun
    }
}

/// Verdict a route can state on its own, without knowing a compile's outcome.
///
/// Nothing ran is a fact the configuration alone settles, so it is stated as
/// [`ProofEvidenceVerdict::MissingEvidence`]. When obligations *were*
/// discharged the outcome is not this function's to know, so it reports
/// [`ProofEvidenceVerdict::Unknown`] and leaves the real verdict to
/// [`ProofEvidenceSummary::with_verdict`]. Deliberately never `Verified`: a
/// configuration must not be able to certify itself.
fn route_verdict(facts: RouteFacts) -> (ProofEvidenceVerdict, Option<ProofEvidenceRejectionCode>) {
    if facts.obligations_discharged() {
        (ProofEvidenceVerdict::Unknown, None)
    } else {
        (
            ProofEvidenceVerdict::MissingEvidence,
            Some(ProofEvidenceRejectionCode::MissingEvidence),
        )
    }
}

/// Build the evidence summary for a compile route.
///
/// When nothing ran this returns an explicit
/// [`ProofEvidenceVerdict::MissingEvidence`] summary at
/// [`EvidenceStrength::NotRun`] — never an absent one. When something did run,
/// the summary reports the strength that work was carried out at plus the
/// assumptions it rests on, and leaves the verdict `Unknown` for the caller to
/// restate once the real outcome is in.
pub fn route_evidence(
    verifier: impl Into<String>,
    facts: RouteFacts,
    environment: &EvidenceEnvironment,
) -> ProofEvidenceSummary {
    let (verdict, rejection_code) = route_verdict(facts);
    ProofEvidenceSummary::missing(verifier)
        .with_verdict(verdict, rejection_code)
        .with_strength(route_strength(facts, environment))
        .with_accepted_assumptions(accepted_assumptions_for_route(facts, environment))
}

/// Build the route evidence bound to a manifest's checksums.
///
/// Binding keeps a negative statement attributable: a consumer can tell which
/// artifact nothing ran on.
pub fn route_evidence_for_manifest(
    verifier: impl Into<String>,
    facts: RouteFacts,
    environment: &EvidenceEnvironment,
    manifest: &DeterministicArtifactManifest,
) -> ProofEvidenceSummary {
    let (verdict, rejection_code) = route_verdict(facts);
    ProofEvidenceSummary::missing_for_manifest(verifier, manifest)
        .with_verdict(verdict, rejection_code)
        .with_strength(route_strength(facts, environment))
        .with_accepted_assumptions(accepted_assumptions_for_route(facts, environment))
}

/// A compile refused because the host cannot reach the requested strength.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StrengthRefusal {
    /// Strength the caller demanded.
    pub required: RequiredEvidenceStrength,
    /// Strongest strength this host can actually produce.
    pub available: EvidenceStrength,
    /// Human-readable statement of why the demand cannot be met.
    pub detail: String,
}

impl StrengthRefusal {
    /// Stable diagnostic code for this refusal.
    pub const fn code(&self) -> &'static str {
        PROOF_STRENGTH_UNAVAILABLE_CODE
    }
}

/// Refuse a policy whose required discharge strength this host cannot reach.
///
/// This is the fail-closed half of proof-evidence honesty. Reporting alone is
/// not enough: a caller that asks for solver-backed certificates on a box with
/// no solver must get a **rejection**, because a downgraded-but-labelled
/// statistical certificate still ends up installed. Returns `None` when the
/// policy is satisfiable (which includes every policy at the default
/// [`RequiredEvidenceStrength::Any`], so no existing caller changes behaviour).
pub fn refuse_required_strength(
    policy: &ProofPolicy,
    environment: &EvidenceEnvironment,
) -> Option<StrengthRefusal> {
    let required = policy.required_strength;
    if environment.can_reach(required) {
        return None;
    }

    let available = environment.strength_for(64, 2);
    Some(StrengthRefusal {
        required,
        detail: format!(
            "proof policy requires discharge strength '{}', but no ay/z3 solver binary is \
             reachable on this host; the strongest available strength is '{}'. Refusing rather \
             than emitting a weaker certificate under a stronger label.",
            required.as_str(),
            available.as_str()
        ),
        available,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::jit_contract::ProofEvidenceVerdict;

    fn solverless() -> EvidenceEnvironment {
        EvidenceEnvironment {
            solver_available: false,
            statistical_sample_count: 100_000,
            exhaustive_threshold_bits: 8,
            dataflow_integrity: DataflowIntegrityMode::Warn,
        }
    }

    fn solver_present() -> EvidenceEnvironment {
        EvidenceEnvironment {
            solver_available: true,
            ..solverless()
        }
    }

    #[test]
    fn nothing_ran_reports_missing_evidence_not_absence() {
        let evidence = route_evidence(
            ROUTE_EVIDENCE_VERIFIER,
            RouteFacts::default(),
            &solverless(),
        );
        assert_eq!(evidence.verdict, ProofEvidenceVerdict::MissingEvidence);
        assert_eq!(evidence.strength, EvidenceStrength::NotRun);
        assert!(evidence.is_missing_evidence());
    }

    #[test]
    fn nothing_ran_lists_the_assumptions_it_rests_on() {
        let evidence = route_evidence(
            ROUTE_EVIDENCE_VERIFIER,
            RouteFacts::default(),
            &solverless(),
        );
        let ids = evidence.accepted_assumption_ids();
        assert!(ids.contains(&ASSUMPTION_VERIFICATION_DISABLED));
        assert!(ids.contains(&ASSUMPTION_DISPATCH_VERIFY_OFF));
        assert!(ids.contains(&ASSUMPTION_NO_SOLVER_AVAILABLE));
        assert!(ids.contains(&ASSUMPTION_TV3_WARN_NOT_ENFORCE));
        // Nothing ran, so there is no statistical discharge to assume.
        assert!(!ids.contains(&ASSUMPTION_STATISTICAL_DISCHARGE));
    }

    #[test]
    fn a_run_route_on_a_solverless_host_reports_statistical_with_the_sample_count() {
        let facts = RouteFacts {
            instruction_verification_ran: true,
            dispatch_verification_ran: true,
            proof_certificates_emitted: true,
            evidence_report_present: true,
            manifest_pin_accepted: false,
        };
        let evidence = route_evidence(ROUTE_EVIDENCE_VERIFIER, facts, &solverless());
        assert_eq!(
            evidence.strength,
            EvidenceStrength::Statistical {
                sample_count: 100_000
            }
        );
        assert!(
            evidence
                .accepted_assumption_ids()
                .contains(&ASSUMPTION_STATISTICAL_DISCHARGE)
        );
    }

    #[test]
    fn narrow_obligations_report_exhaustive() {
        assert_eq!(
            solverless().strength_for(8, 2),
            EvidenceStrength::Exhaustive
        );
        assert_eq!(
            solverless().strength_for(8, 3),
            EvidenceStrength::Statistical {
                sample_count: 100_000
            }
        );
    }

    #[test]
    fn a_formal_requirement_is_refused_without_a_solver_and_admitted_with_one() {
        let policy = ProofPolicy::require_certificates(["ay"])
            .with_required_strength(RequiredEvidenceStrength::Formal);
        let refusal = refuse_required_strength(&policy, &solverless())
            .expect("a formal requirement must be refused on a solver-less host");
        assert_eq!(refusal.required, RequiredEvidenceStrength::Formal);
        assert_eq!(refusal.code(), PROOF_STRENGTH_UNAVAILABLE_CODE);
        assert!(refuse_required_strength(&policy, &solver_present()).is_none());
    }

    #[test]
    fn the_default_requirement_never_refuses() {
        let policy = ProofPolicy::require_certificates(["ay"]);
        assert_eq!(policy.required_strength, RequiredEvidenceStrength::Any);
        assert!(refuse_required_strength(&policy, &solverless()).is_none());
        assert!(refuse_required_strength(&ProofPolicy::disabled(), &solverless()).is_none());
    }

    #[test]
    fn verifier_strengths_translate_without_upgrading() {
        assert_eq!(
            strength_from_verification(&VerificationStrength::Exhaustive),
            EvidenceStrength::Exhaustive
        );
        assert_eq!(
            strength_from_verification(&VerificationStrength::Statistical {
                sample_count: 100_000
            }),
            EvidenceStrength::Statistical {
                sample_count: 100_000
            }
        );
        assert!(matches!(
            strength_from_verification(&VerificationStrength::Formal),
            EvidenceStrength::Formal { .. }
        ));
        // The translation must preserve completeness exactly: a sampled
        // discharge that arrived as incomplete must not leave as complete.
        for strength in [
            VerificationStrength::Exhaustive,
            VerificationStrength::Statistical { sample_count: 1 },
            VerificationStrength::Formal,
        ] {
            assert_eq!(
                strength_from_verification(&strength).is_complete(),
                strength.is_complete(),
                "completeness must survive translation for {strength}"
            );
        }
    }

    #[test]
    fn assumptions_are_sorted_and_deduplicated() {
        let evidence = ProofEvidenceSummary::missing(ROUTE_EVIDENCE_VERIFIER)
            .with_accepted_assumptions([
                AcceptedAssumption::new(ASSUMPTION_TV3_WARN_NOT_ENFORCE, "b"),
                AcceptedAssumption::new(ASSUMPTION_NO_SOLVER_AVAILABLE, "a"),
                AcceptedAssumption::new(ASSUMPTION_NO_SOLVER_AVAILABLE, "a"),
            ]);
        assert_eq!(
            evidence.accepted_assumption_ids(),
            vec![
                ASSUMPTION_NO_SOLVER_AVAILABLE,
                ASSUMPTION_TV3_WARN_NOT_ENFORCE
            ]
        );
    }

    #[test]
    fn the_evidence_channel_is_additive_over_the_v1_encoding() {
        // A summary that reports nothing must checksum exactly as it did
        // before the channel existed; one that reports something must not.
        let base = ProofEvidenceSummary::verified(
            "test",
            crate::jit_contract::ArtifactChecksum::new(1),
            crate::jit_contract::ArtifactChecksum::new(2),
            crate::jit_contract::ArtifactChecksum::new(3),
            crate::jit_contract::ArtifactChecksum::new(4),
            crate::jit_contract::ArtifactChecksum::new(5),
        );
        assert_eq!(base.strength, EvidenceStrength::NotReported);
        let with_channel = base.clone().with_strength(EvidenceStrength::Exhaustive);
        assert_ne!(base.checksum(), with_channel.checksum());

        let untouched = base.clone().with_accepted_assumptions([]);
        assert_eq!(base.checksum(), untouched.checksum());
    }
}
