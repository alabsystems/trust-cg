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

use trust_cg_verify::VerificationStrength;
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
    /// Whether an authorized AY solver + Alethe checker route is reachable.
    ///
    /// When false, **no** obligation can be discharged formally on this host,
    /// no matter what the caller asks for. The converse does NOT hold: a
    /// solver does not make every obligation class formally dischargeable.
    /// Target-reconstructed obligations lack exact source-op/type/operand
    /// binding and are sampled above the exhaustive threshold, so the aggregate
    /// route strength stays `Statistical` either way (and sampled instructions
    /// are never credited).
    pub solver_available: bool,
    /// Identity of the AY a solver verdict on this host is bound to: the
    /// `trust_cg_verify::ay_identity` admission (recorded build and the SHA-256
    /// of its bytes). `None` when no AY is admitted with a capable checker. It
    /// names the solver; it upgrades nothing: [`Self::strength_for`] never
    /// reports `Formal`, and a `Formal` strength translated from a verifier
    /// result ([`strength_from_verification`]) carries the identity the caller
    /// passes.
    pub solver: Option<String>,
    /// Why the resolution that set [`Self::solver_available`] admitted no AY:
    /// its [`trust_cg_verify::ay_bridge::route_refusal_note_for`] note, with
    /// the `TCG-AY-IDENTITY-*` code and reason (for a cache directory another
    /// user could write, the directory, its mode and the remedy). `None` when
    /// an AY is admitted, when no capable independent checker was found (AY
    /// is then not resolved), and for a build that records no AY. The
    /// required-strength refusal and the no-solver disclosure this snapshot
    /// decides carry it; nothing resolves AY again to name the cause
    /// (OD-XHOST-STRENGTH-NOTE-20261016, as LD-66 does for proof promotion).
    pub solver_refusal_note: Option<String>,
    /// Number of random trials a statistical discharge uses.
    pub statistical_sample_count: u64,
    /// Maximum bit width (with <= 2 inputs) that is enumerated exhaustively.
    pub exhaustive_threshold_bits: u32,
    /// Active TV-3 dataflow-integrity enforcement mode for the host arch.
    pub dataflow_integrity: DataflowIntegrityMode,
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
/// AY/Clean selection and dataflow-integrity policy are resolved per snapshot.
/// The tool-discovery layer retains its identity-aware probe caches; an outer
/// process-wide boolean would conceal changed overrides and managed packages.
pub fn evidence_environment() -> EvidenceEnvironment {
    evidence_environment_for(Target::host())
}

/// Snapshot the discharge environment as it applies to `target`.
pub fn evidence_environment_for(target: Target) -> EvidenceEnvironment {
    let config = VerificationConfig::default();
    // One resolution decides the route and names why it is refused.
    let (solver, solver_refusal_note) =
        match trust_cg_verify::ay_bridge::admitted_proof_solver_or_refusal() {
            Ok(solver) => (Some(solver.identity().describe()), None),
            Err(refusal) => (
                None,
                refusal
                    .as_ref()
                    .and_then(trust_cg_verify::ay_bridge::route_refusal_note_for),
            ),
        };
    EvidenceEnvironment {
        solver_available: solver.is_some(),
        solver,
        solver_refusal_note,
        statistical_sample_count: config.sample_count,
        exhaustive_threshold_bits: config.exhaustive_threshold,
        dataflow_integrity: dataflow_integrity_mode(dataflow_integrity_default_for(target)),
    }
}

impl EvidenceEnvironment {
    /// Conservative aggregate strength obligations of the given shape can
    /// reach on this compile route.
    ///
    /// Mirrors [`VerificationStrength::for_obligation_with_config`] exactly for
    /// the sampling/enumeration split. Solver presence cannot upgrade it: no
    /// route discharges every obligation class formally, and the former
    /// formal-on-miss upgrade of registry theorems was deleted with registry
    /// credit. Neither can an exact source/operand binding
    /// (`trust_cg_verify::x86_source_operand_binding`) that covers only SOME
    /// reconstructable classes on ONE backend: this is a ROUTE-level
    /// conservative answer over every class, and a per-instruction verdict that
    /// did better is reported by the verifier itself through
    /// [`strength_from_verification`], never re-derived here.
    pub fn strength_for(&self, width_bits: u32, input_count: usize) -> EvidenceStrength {
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
/// own answer rather than a re-derived guess. `formal_solver` is the identity
/// of the AY that produced a `Formal` verdict (see
/// [`EvidenceEnvironment::solver`]); it is recorded in the strength.
pub fn strength_from_verification(
    strength: &VerificationStrength,
    formal_solver: &str,
) -> EvidenceStrength {
    match strength {
        VerificationStrength::Exhaustive => EvidenceStrength::Exhaustive,
        VerificationStrength::Statistical { sample_count } => EvidenceStrength::Statistical {
            sample_count: *sample_count,
        },
        VerificationStrength::Formal => EvidenceStrength::Formal {
            solver: formal_solver.to_owned(),
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
            with_solver_refusal_note(
                "the AY + independent Clean proof route is unavailable on this host, so no \
                 obligation on this compile could be discharged formally"
                    .to_owned(),
                environment,
            ),
        ));
    }
    // Sampling must be disclosed whenever obligations were discharged, not
    // merely when a solver binary is missing: target-reconstructed obligations
    // have no complete Formal route on any host, and an artifact that keeps
    // quiet about sampling repeats the absence-reads-as-presence failure WP-0
    // exists to close. The disclosure says what the sampling is worth: nothing
    // is credited on it.
    if facts.obligations_discharged() {
        assumptions.push(AcceptedAssumption::new(
            ASSUMPTION_STATISTICAL_DISCHARGE,
            format!(
                "obligations wider than {} bits (or with more than 2 inputs) that lack a complete \
                 Formal route were checked only by sampling (edge cases plus {} random trials); \
                 sampling is reported, never credited, so no instruction resting on it may be \
                 promoted",
                environment.exhaustive_threshold_bits, environment.statistical_sample_count
            ),
        ));
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

// ---------------------------------------------------------------------------
// Proof promotion
// ---------------------------------------------------------------------------

/// Category (and rule name) of the structural certificate for an x86-64 body
/// whose every verifier row is a trap skip or a by-design unverified control
/// transfer AND whose LIR source is a bare diverging transfer
/// (`compiler::x86_64_call_only_body_certificate` requires both). It discharges
/// no instruction theorem and has no `ProofDatabase` obligation, so consumers
/// that resolve certificates against the database (the CLI's lowering sidecars)
/// skip it by this exact name; it is shared here so the producer and every
/// consumer spell it once.
///
/// It is an AUDIT NAME, not evidence. [`certificate_is_discharge_evidence`] is
/// what every promotion gate counts, and it excludes this category, so naming
/// the exemption cannot by itself make a bundle look non-empty or make a
/// function look semantics-verified.
pub const CALL_ONLY_BODY_CATEGORY: &str = "call_only_body";

/// Category of the per-row certificate for a row the verifier leaves unverified
/// BY DESIGN because its correctness rests on something other than an
/// instruction theorem: a direct or indirect CALL/JMP and a RET (the CFG edge
/// and the relocation), a `MOV r, imm`, or emission padding
/// (`compiler::unverified_instruction_certificate`). It is emitted
/// `verified: true` so the row does not block promotion, but it discharges no
/// obligation itself, so [`certificate_is_discharge_evidence`] excludes it.
/// A row whose credit cites a per-compile decode check gets this category only
/// when that check gated the compile; otherwise it gets
/// [`COVERED_ELSEWHERE_WITHHELD_CATEGORY`] instead.
pub const COVERED_ELSEWHERE_CATEGORY: &str = "covered_elsewhere";

/// Category of the `verified: false` certificate issued IN PLACE OF a
/// [`COVERED_ELSEWHERE_CATEGORY`] row whose credit cites a per-compile decode
/// check (ENC-3 for the x86-64 `MOV r, imm`, ENC-5 for AArch64 `AlignNop`)
/// that did not gate this compile: the check ran in warn mode, was off, or no
/// encode ran. It blocks promotion, and it is NOT a structural category, so
/// [`certificate_is_discharge_evidence`] counts it and a per-function verdict
/// that requires every evidence row to be verified fails on it.
pub const COVERED_ELSEWHERE_WITHHELD_CATEGORY: &str = "covered_elsewhere_withheld";

/// Category of the x86-64 System V ABI envelope certificate the verifying JIT
/// attaches to an empty void body or a `call f; ud2` panic entry
/// (`trust_cg_verify::x86_source_bound_envelope`). It IS discharge evidence:
/// it names a theorem over the function's final bytes and fixup manifest (the
/// return target, stack balance, callee-saved registers and caller memory, or
/// the callee-entry alignment, trap return slot and caller memory). The
/// theorem is replayed in parts, and a function carries one `verified: true`
/// certificate per part only when EVERY part's replay was Valid (an AY proof
/// Clean independently accepted, each). Otherwise it carries one named
/// `verified: false` refusal, which blocks promotion.
pub const X86_ABI_ENVELOPE_CATEGORY: &str = "x86_abi_envelope";

/// Whether `cert` asserts a DISCHARGED obligation — an instruction theorem, an
/// opcode inventory, an object relocation inventory — rather than a
/// STRUCTURAL claim: that the body had nothing to discharge
/// ([`CALL_ONLY_BODY_CATEGORY`]) or that the row's obligation rests elsewhere
/// ([`COVERED_ELSEWHERE_CATEGORY`]).
///
/// A promotion gate that asks "did this produce any evidence at all" must ask it
/// with this predicate, not with `is_empty`. Both structural categories are
/// emitted `verified: true`, so counting either as evidence lets a bundle (or a
/// function) with no discharged obligation satisfy a non-empty evidence
/// requirement. That happened: until 2026-09-28 this predicate excluded only
/// the exemption, and the verifying JIT's certification step
/// (`x86_jit_certify_functions`, `CachedVerified` and `AlwaysVerify`) returned
/// Ok with per-function `verified = true` for an x86-64 `call f; ud2` body
/// (certificates `[call_only_body, covered_elsewhere]`) and an empty `ret` body
/// (`[covered_elsewhere]`) with nothing discharged, while it refused the
/// trap-only body (`[call_only_body]`). That was measured on an arm64 host,
/// through the uncached path only (no verification authority was discovered, so
/// no cache key formed) and without executing x86-64 code; that an Ok here is
/// what lets the JIT publish is known by reading the code, not by a run. The
/// verifier's rule for a non-exempt
/// body says the same thing: covered-elsewhere or skipped rows alone cannot
/// establish proof-grade function semantics (`non_vacuous_function_evidence`).
///
/// This says nothing about the STRENGTH of the evidence a certificate carries:
/// [`certificate_blocks_promotion`] is what reads a verdict. The two questions
/// are independent, and a gate needs both.
pub fn certificate_is_discharge_evidence(cert: &crate::compiler::ProofCertificate) -> bool {
    cert.category != CALL_ONLY_BODY_CATEGORY && cert.category != COVERED_ELSEWHERE_CATEGORY
}

/// Whether `certs` carries at least one discharged obligation (see
/// [`certificate_is_discharge_evidence`]) — the non-empty half of a fail-closed
/// promotion gate, stated here so the bundle's producer
/// (`Compiler::gate_jit_proofs_promotable`) and every independent re-checker
/// (the rustc bridge's own bundle gate) spell it once.
pub fn bundle_has_discharge_evidence(certs: &[crate::compiler::ProofCertificate]) -> bool {
    certs.iter().any(certificate_is_discharge_evidence)
}

/// Whether `cert` must block proof promotion.
///
/// Every certificate that is not `verified` blocks, on every host. There is no
/// admitted tier: statistical sampling is not proof, so the verifiers report a
/// sampled instruction as unverified and it blocks here like any other gap.
/// (Before the E0.2 credit withdrawal an aggregate `statistical_validation`
/// entry was admitted on hosts without a live formal route, which was every
/// host.)
pub fn certificate_blocks_promotion(cert: &crate::compiler::ProofCertificate) -> bool {
    !cert.verified
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
        detail: with_solver_refusal_note(
            format!(
                "proof policy requires discharge strength '{}', but the required formal discharge \
                 route is unavailable on this host; the strongest available strength is '{}'. \
                 Refusing rather than emitting a weaker certificate under a stronger label.",
                required.as_str(),
                available.as_str()
            ),
            environment,
        ),
        available,
    })
}

/// `text` followed by the AY refusal the environment's own resolution found
/// ([`EvidenceEnvironment::solver_refusal_note`]), when there is one: how the
/// required-strength refusal and the no-solver disclosure name the cause.
/// Nothing is resolved here.
fn with_solver_refusal_note(text: String, environment: &EvidenceEnvironment) -> String {
    match environment.solver_refusal_note.as_deref() {
        Some(note) => format!("{text}; {note}"),
        None => text,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::jit_contract::ProofEvidenceVerdict;

    /// Every category string the x86-64 certificate paths emit, classified.
    /// The discharge predicate is a DENYLIST, so a new structural category
    /// would silently count as evidence; a category missing from this table
    /// is a review point, and each structural one must stay excluded.
    #[test]
    fn x86_certificate_categories_are_classified() {
        let certificate = |category: &str| crate::compiler::ProofCertificate {
            ay_refusal_note: None,
            #[cfg(feature = "verify")]
            source_bound_obligation: None,
            rule_name: "row".into(),
            verified: true,
            category: category.into(),
            strength: String::new(),
            function_name: "f".into(),
        };
        for (category, discharges) in [
            (CALL_ONLY_BODY_CATEGORY, false),
            (COVERED_ELSEWHERE_CATEGORY, false),
            (COVERED_ELSEWHERE_WITHHELD_CATEGORY, true),
            (X86_ABI_ENVELOPE_CATEGORY, true),
            ("opcode_inventory", true),
            ("relocation_inventory", true),
            ("verification_precondition", true),
            ("statistical_validation", true),
            ("instruction", true),
            ("arithmetic", true),
            ("control", true),
            ("X86-64 Lowering", true),
        ] {
            assert_eq!(
                certificate_is_discharge_evidence(&certificate(category)),
                discharges,
                "{category}"
            );
        }
    }

    fn solverless() -> EvidenceEnvironment {
        EvidenceEnvironment {
            solver_available: false,
            solver: None,
            solver_refusal_note: None,
            statistical_sample_count: 100_000,
            exhaustive_threshold_bits: 8,
            dataflow_integrity: DataflowIntegrityMode::Warn,
        }
    }

    const TEST_AY_IDENTITY: &str = "ay 0.0.0 build 0 commit 0000000000000000000000000000000000000000 \
         sha256 1111111111111111111111111111111111111111111111111111111111111111";

    fn solver_present() -> EvidenceEnvironment {
        EvidenceEnvironment {
            solver_available: true,
            solver: Some(TEST_AY_IDENTITY.to_owned()),
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
    fn a_solver_present_host_still_discloses_the_sampled_discharge() {
        // "A solver exists" does NOT imply "this compile discharged formally".
        // A route that ran must say it sampled, whether or not a solver binary
        // happens to be installed.
        let facts = RouteFacts {
            instruction_verification_ran: true,
            dispatch_verification_ran: true,
            proof_certificates_emitted: true,
            evidence_report_present: true,
            manifest_pin_accepted: false,
        };

        let sampled = route_evidence(ROUTE_EVIDENCE_VERIFIER, facts, &solver_present());
        let ids = sampled.accepted_assumption_ids();
        assert!(
            ids.contains(&ASSUMPTION_STATISTICAL_DISCHARGE),
            "a solver with no live formal-discharge route still samples: {ids:?}"
        );
        assert!(
            !ids.contains(&ASSUMPTION_NO_SOLVER_AVAILABLE),
            "a solver IS available here; that fact must stay accurate: {ids:?}"
        );
        let disclosure = sampled
            .accepted_assumptions
            .iter()
            .find(|assumption| assumption.id == ASSUMPTION_STATISTICAL_DISCHARGE)
            .expect("the sampled discharge is disclosed");
        assert!(
            disclosure.detail.contains("never credited"),
            "the disclosure must not present sampling as credit: {disclosure:?}"
        );
    }

    #[test]
    fn solver_presence_never_upgrades_the_route_strength() {
        // `can_reach` keeps its pinned host-capability meaning.
        assert!(!solverless().can_reach(RequiredEvidenceStrength::Formal));
        assert!(solver_present().can_reach(RequiredEvidenceStrength::Formal));
        // But no host has a complete Formal route for every obligation class,
        // so a 64-bit aggregate stays Statistical with or without a solver.
        for environment in [solverless(), solver_present()] {
            assert_eq!(
                environment.strength_for(64, 2),
                EvidenceStrength::Statistical {
                    sample_count: 100_000
                },
                "{environment:?}"
            );
        }
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

    /// The fifth closure audit's second finding: a Formal requirement refused
    /// on a host whose AY the identity rule refused said only that the route
    /// was unavailable, and so did the no-solver disclosure. Both now carry
    /// the AY refusal the environment's own resolution found, appended to
    /// the unchanged text, and nothing when it found none
    /// (OD-XHOST-STRENGTH-NOTE-20261016).
    #[test]
    fn a_formal_refusal_and_the_no_solver_disclosure_carry_the_routes_ay_refusal() {
        let policy = ProofPolicy::require_certificates(["ay"])
            .with_required_strength(RequiredEvidenceStrength::Formal);
        let plain = refuse_required_strength(&policy, &solverless())
            .expect("refused")
            .detail;
        let disclosure = |environment: &EvidenceEnvironment| {
            accepted_assumptions_for_route(RouteFacts::default(), environment)
                .into_iter()
                .find(|assumption| assumption.id == ASSUMPTION_NO_SOLVER_AVAILABLE)
                .expect("the no-solver disclosure")
                .detail
        };
        let plain_disclosure = disclosure(&solverless());
        assert!(
            !plain.contains("TCG-AY-IDENTITY") && !plain_disclosure.contains("TCG-AY-IDENTITY")
        );
        let note = "the proof route was resolved with no AY admitted, so nothing on it could be \
                    discharged formally: [TCG-AY-IDENTITY-UNMATERIALIZED] /c/trust-cg has mode 0775";
        let refused = EvidenceEnvironment {
            solver_refusal_note: Some(note.to_owned()),
            ..solverless()
        };
        let refusal = refuse_required_strength(&policy, &refused).expect("refused");
        assert_eq!(refusal.code(), PROOF_STRENGTH_UNAVAILABLE_CODE);
        assert_eq!(refusal.detail, format!("{plain}; {note}"));
        assert_eq!(disclosure(&refused), format!("{plain_disclosure}; {note}"));
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
            strength_from_verification(&VerificationStrength::Exhaustive, TEST_AY_IDENTITY),
            EvidenceStrength::Exhaustive
        );
        assert_eq!(
            strength_from_verification(
                &VerificationStrength::Statistical {
                    sample_count: 100_000
                },
                TEST_AY_IDENTITY
            ),
            EvidenceStrength::Statistical {
                sample_count: 100_000
            }
        );
        assert_eq!(
            strength_from_verification(&VerificationStrength::Formal, TEST_AY_IDENTITY),
            EvidenceStrength::Formal {
                solver: TEST_AY_IDENTITY.to_owned()
            }
        );
        // The translation must preserve completeness exactly: a sampled
        // discharge that arrived as incomplete must not leave as complete.
        for strength in [
            VerificationStrength::Exhaustive,
            VerificationStrength::Statistical { sample_count: 1 },
            VerificationStrength::Formal,
        ] {
            assert_eq!(
                strength_from_verification(&strength, TEST_AY_IDENTITY).is_complete(),
                strength.is_complete(),
                "completeness must survive translation for {strength}"
            );
        }
    }

    fn unverified_cert(category: &str, strength: &str) -> crate::compiler::ProofCertificate {
        crate::compiler::ProofCertificate {
            ay_refusal_note: None,
            #[cfg(feature = "verify")]
            source_bound_obligation: None,
            rule_name: format!("{category}_instruction_0"),
            verified: false,
            category: category.to_owned(),
            strength: strength.to_owned(),
            function_name: "answer".to_owned(),
        }
    }

    /// E0.2 inverse of the removed statistical admission: sampled evidence
    /// never promotes, on any host. The aggregate `statistical_validation`
    /// shape that used to be admitted where formal discharge was unreachable
    /// (every host) blocks exactly like every other unverified certificate.
    #[test]
    fn statistical_evidence_never_promotes() {
        let sampled = unverified_cert(
            "statistical_validation",
            "3 instruction(s) were validated only by bounded statistical sampling",
        );
        assert!(certificate_blocks_promotion(&sampled));
        let sampled_instruction = unverified_cert(
            "unverified",
            trust_cg_verify::function_verifier::STATISTICAL_EVIDENCE_IS_NOT_CREDIT,
        );
        assert!(certificate_blocks_promotion(&sampled_instruction));
        for category in [
            "unverified",
            "opcode_inventory",
            "non_vacuous_function_evidence",
            "relocation_inventory",
            "",
        ] {
            assert!(
                certificate_blocks_promotion(&unverified_cert(category, "gap")),
                "category `{category}` must block promotion"
            );
        }
    }

    #[test]
    fn a_verified_certificate_never_blocks() {
        let mut cert = unverified_cert("Arithmetic", "Exhaustive");
        cert.verified = true;
        assert!(!certificate_blocks_promotion(&cert));
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
    /// Scheduling availability must follow the current tool selection, and
    /// the identity it reports is the ADMITTED AY's. The explicit AY here is a
    /// byte-identical COPY of the toolchain AY (the only bytes the identity
    /// rule admits, wherever they live); a script standing in for AY is
    /// refused. The checker is a stub: no obligation or certificate is proved.
    #[cfg(unix)]
    #[test]
    fn evidence_environment_rechecks_explicit_ay_and_clean_overrides() {
        use std::os::unix::fs::PermissionsExt;

        let dir = tempfile::tempdir().unwrap();
        let checker = dir.path().join("checker-probe-stub");
        let script_ay = dir.path().join("script-standing-in-for-ay");
        std::fs::write(
            &checker,
            "#!/bin/sh\nprintf 'External certificate verification: PASSED\\n  Type: Alethe SMT proof\\n  Proof status: fully verified\\n'\n",
        ).unwrap();
        std::fs::write(&script_ay, "#!/bin/sh\nexit 1\n").unwrap();
        for path in [&checker, &script_ay] {
            std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
        }
        let toolchain_ay = trust_cg_process_env::with_env_overrides_removed(
            &["AY_SOLVER_PATH"],
            trust_cg_verify::ay_identity::resolve_for_process,
        );
        let copy = toolchain_ay.as_ref().ok().map(|ay| {
            let copy = dir.path().join("copy-of-the-toolchain-ay");
            std::fs::copy(ay.path(), &copy).unwrap();
            (copy, ay.identity().describe())
        });
        trust_cg_process_env::with_env_overrides(
            &[("TCG_EXTERNAL_CLEAN_CHECKER", checker.to_str().unwrap())],
            || {
                trust_cg_process_env::with_env_overrides(
                    &[("AY_SOLVER_PATH", script_ay.to_str().unwrap())],
                    || {
                        let environment = evidence_environment();
                        assert!(!environment.solver_available, "a script is never the AY");
                        assert_eq!(environment.solver, None);
                        // The same resolution names why
                        // (OD-XHOST-STRENGTH-NOTE-20261016); a build that records
                        // no AY has no note to carry.
                        let recorded =
                            trust_cg_verify::ay_identity::recorded_toolchain_ay_identity().is_ok();
                        match environment.solver_refusal_note.as_deref() {
                            Some(note) => assert!(
                                recorded
                                    && note.starts_with(
                                        trust_cg_verify::ay_bridge::ROUTE_REFUSAL_NOTE_HEAD
                                    )
                                    && note.contains("[TCG-AY-IDENTITY-"),
                                "{note}"
                            ),
                            None => assert!(!recorded, "a refused AY with no note"),
                        }
                    },
                );
                trust_cg_process_env::with_env_overrides(&[("AY_SOLVER_PATH", "")], || {
                    assert!(!evidence_environment().solver_available);
                });
                match &copy {
                    Some((copy, identity)) => trust_cg_process_env::with_env_overrides(
                        &[("AY_SOLVER_PATH", copy.to_str().unwrap())],
                        || {
                            let environment = evidence_environment();
                            assert!(environment.solver_available);
                            assert_eq!(environment.solver.as_deref(), Some(identity.as_str()));
                            trust_cg_process_env::with_env_overrides(
                                &[("TCG_EXTERNAL_CLEAN_CHECKER", "")],
                                || {
                                    let environment = evidence_environment();
                                    assert!(!environment.solver_available);
                                    assert_eq!(environment.solver, None);
                                    // No checker: AY is not resolved, so
                                    // no AY refusal is named.
                                    assert_eq!(environment.solver_refusal_note, None);
                                },
                            );
                            assert!(evidence_environment().solver_available);
                        },
                    ),
                    None => trust_cg_process_env::with_env_overrides_removed(
                        &["AY_SOLVER_PATH"],
                        || {
                            assert!(
                                !evidence_environment().solver_available,
                                "no admitted toolchain AY ({toolchain_ay:?}) means no solver"
                            );
                        },
                    ),
                }
            },
        );
    }
}
