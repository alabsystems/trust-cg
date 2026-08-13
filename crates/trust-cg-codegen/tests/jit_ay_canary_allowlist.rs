// trust-cg-codegen/tests/jit_ay_canary_allowlist.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::jit_ay_canary_allowlist::{
    AYCanaryBcpProofFact, AYCanaryBcpProofFactEvidence, AYCanaryLraProofFact,
    AYCanaryLraProofFactEvidence,
};
use trust_cg_codegen::{
    AYCanaryAllowlist, AYCanaryAllowlistDecision, AYCanaryAllowlistKey, AYCanaryCandidate,
    AYCanaryCandidateMode, AYCanaryDecisionStatus, AYCanaryEquivalenceEvidence,
    AYCanaryExecutionObservation, AYCanaryFamily, AYCanaryGenerationFence,
    AYCanaryInvalidationState, AYCanaryLayoutProof, AYCanaryManifestBinding,
    AYCanaryParentGateEvidence, AYCanaryProofDecision, AYCanaryRejectionReason,
    AYCanaryValidationProvenance, JIT_AY_CANARY_ALLOWLIST_SCHEMA,
    JIT_AY_CANARY_ALLOWLIST_SCHEMA_VERSION, Target,
};

fn generations() -> AYCanaryGenerationFence {
    AYCanaryGenerationFence::new(7, 13, 17, 19)
}

fn key_for_family(family: AYCanaryFamily) -> AYCanaryAllowlistKey {
    let solver_program_sha256 = match family {
        AYCanaryFamily::SparseSubstitute => "sha256:ay-lra-solver-program",
        AYCanaryFamily::BasisRegionScanner => "sha256:ay-lra-basis-region-program",
        AYCanaryFamily::WatchListBcp => "sha256:ay-watch-list-bcp-program",
    };
    let manifest_sha256 = match family {
        AYCanaryFamily::SparseSubstitute => "sha256:manifest-ay-lra-sparse-substitute",
        AYCanaryFamily::BasisRegionScanner => "sha256:manifest-ay-lra-basis-region",
        AYCanaryFamily::WatchListBcp => "sha256:manifest-ay-watch-list-bcp",
    };
    AYCanaryAllowlistKey::new(
        solver_program_sha256,
        family,
        generations(),
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "proof-policy:v1:strict-ay-native",
        "sha256:layout-ay-sparse-basis-watch",
        manifest_sha256,
    )
}

fn key() -> AYCanaryAllowlistKey {
    key_for_family(AYCanaryFamily::SparseSubstitute)
}

fn family_tag(family: AYCanaryFamily) -> &'static str {
    match family {
        AYCanaryFamily::SparseSubstitute => "lra-sparse-substitute",
        AYCanaryFamily::BasisRegionScanner => "lra-basis-region",
        AYCanaryFamily::WatchListBcp => "watch-list-bcp",
    }
}

fn manifest_for_key(key: &AYCanaryAllowlistKey) -> AYCanaryManifestBinding {
    let family_tag = family_tag(key.family);
    let wrapper_id = match key.family {
        AYCanaryFamily::SparseSubstitute => "wrapper:ay:lra:sparse-substitute:v1",
        AYCanaryFamily::BasisRegionScanner => "wrapper:ay:lra:basis-region:v1",
        AYCanaryFamily::WatchListBcp => "wrapper:ay:bcp:watch-list:v1",
    };
    let symbols = match key.family {
        AYCanaryFamily::SparseSubstitute => vec![
            "ay_lra_sparse_substitute".to_owned(),
            "ay_lra_basis_region".to_owned(),
        ],
        AYCanaryFamily::BasisRegionScanner => vec!["ay_lra_basis_region".to_owned()],
        AYCanaryFamily::WatchListBcp => vec!["ay_watch_list_bcp".to_owned()],
    };
    AYCanaryManifestBinding {
        source_sha256: format!("sha256:source-ay-{family_tag}"),
        trust_ir_sha256: format!("sha256:trust_ir-ay-{family_tag}"),
        native_payload_sha256: format!("sha256:native-ay-{family_tag}"),
        abi_checksum: "sha256:abi-aarch64-darwin-ay".to_owned(),
        layout_checksum: key.layout_checksum.clone(),
        compiler_config_sha256: "sha256:compiler-config-o3-ay-strict".to_owned(),
        target_facts_sha256: key.target_facts_sha256.clone(),
        proof_policy: key.proof_policy.clone(),
        consumer_kind: "ay".to_owned(),
        wrapper_id: wrapper_id.to_owned(),
        symbols,
        replay_root_sha256: format!("sha256:replay-root-ay-{family_tag}"),
        telemetry_key: match key.family {
            AYCanaryFamily::SparseSubstitute => "telemetry:ay:lra:sparse-substitute".to_owned(),
            AYCanaryFamily::BasisRegionScanner => "telemetry:ay:lra:basis-region".to_owned(),
            AYCanaryFamily::WatchListBcp => "telemetry:ay:watch-list-bcp".to_owned(),
        },
        manifest_sha256: key.manifest_sha256.clone(),
    }
}

fn layout_for_manifest(manifest: &AYCanaryManifestBinding) -> AYCanaryLayoutProof {
    AYCanaryLayoutProof {
        pointer_inputs: true,
        bounds: true,
        mutability: true,
        aliasing: true,
        rollback_state: true,
        generation_fences: true,
        consumer_owned_memory: true,
        wrapper_id: manifest.wrapper_id.clone(),
    }
}

fn lra_proof_report_sha256(
    key: &AYCanaryAllowlistKey,
    manifest: &AYCanaryManifestBinding,
) -> String {
    AYCanaryLraProofFactEvidence::aarch64_required_for(key, manifest)
        .expect("ay LRA sparse/basis canary requires AArch64 proof facts")
        .canonical_report_sha256()
}

fn bcp_proof_report_sha256(
    key: &AYCanaryAllowlistKey,
    manifest: &AYCanaryManifestBinding,
) -> String {
    AYCanaryBcpProofFactEvidence::aarch64_required_for(key, manifest)
        .expect("ay watch-list BCP canary requires AArch64 proof facts")
        .canonical_report_sha256()
}

fn proof_report_sha256(key: &AYCanaryAllowlistKey, manifest: &AYCanaryManifestBinding) -> String {
    match key.family {
        AYCanaryFamily::SparseSubstitute | AYCanaryFamily::BasisRegionScanner => {
            lra_proof_report_sha256(key, manifest)
        }
        AYCanaryFamily::WatchListBcp => bcp_proof_report_sha256(key, manifest),
    }
}

fn provenance_for(
    key: &AYCanaryAllowlistKey,
    manifest: &AYCanaryManifestBinding,
) -> AYCanaryValidationProvenance {
    AYCanaryValidationProvenance {
        proof_report_sha256: proof_report_sha256(key, manifest),
        tv_report_sha256: format!("sha256:tv-report-{}", family_tag(key.family)),
        replay_root_sha256: manifest.replay_root_sha256.clone(),
        consumer_equivalence_sha256: format!("sha256:equivalence-{}", family_tag(key.family)),
        validator_id: match key.family {
            AYCanaryFamily::SparseSubstitute | AYCanaryFamily::BasisRegionScanner => {
                "trust-cg-tv:ay:v1:typed-lra-facts"
            }
            AYCanaryFamily::WatchListBcp => "trust-cg-tv:ay:v1:typed-bcp-facts",
        }
        .to_owned(),
        proof_policy_decision: AYCanaryProofDecision::Accepted,
    }
}

fn observation() -> AYCanaryExecutionObservation {
    AYCanaryExecutionObservation {
        result_sha256: "sha256:result-ay-lra-sparse-substitute".to_owned(),
        proof_sha256: "sha256:proof-ay-lra-sparse-substitute".to_owned(),
        witness_sha256: "sha256:witness-ay-lra-sparse-substitute".to_owned(),
        score_sha256: "sha256:score-ay-lra-sparse-substitute".to_owned(),
        status_sha256: "sha256:status-ay-lra-sparse-substitute".to_owned(),
        replay_verdict_sha256: "sha256:replay-verdict-ay-lra-sparse-substitute".to_owned(),
        wrong_answer_regressions: 0,
        proof_regressions: 0,
        witness_regressions: 0,
        score_regressions: 0,
        timeout_unknown_regressions: 0,
        crash_regressions: 0,
    }
}

fn equivalence() -> AYCanaryEquivalenceEvidence {
    let observation = observation();
    AYCanaryEquivalenceEvidence {
        baseline: observation.clone(),
        native: observation,
    }
}

fn invalidation_for(
    key: &AYCanaryAllowlistKey,
    manifest: &AYCanaryManifestBinding,
) -> AYCanaryInvalidationState {
    AYCanaryInvalidationState {
        current_generations: key.generations,
        target_facts_sha256: key.target_facts_sha256.clone(),
        proof_policy: key.proof_policy.clone(),
        compiler_config_sha256: manifest.compiler_config_sha256.clone(),
        manifest_sha256: manifest.manifest_sha256.clone(),
        source_sha256: manifest.source_sha256.clone(),
        trust_ir_sha256: manifest.trust_ir_sha256.clone(),
        native_payload_sha256: manifest.native_payload_sha256.clone(),
        kill_switch_active: false,
        revoked: false,
    }
}

fn full_candidate_for_family(
    family: AYCanaryFamily,
    mode: AYCanaryCandidateMode,
) -> AYCanaryCandidate {
    let key = key_for_family(family);
    let manifest = manifest_for_key(&key);
    let layout = layout_for_manifest(&manifest);
    let provenance = provenance_for(&key, &manifest);
    let invalidation = invalidation_for(&key, &manifest);
    AYCanaryCandidate {
        mode,
        key,
        manifest: Some(manifest),
        layout: Some(layout),
        provenance: Some(provenance),
        equivalence: Some(equivalence()),
        invalidation: Some(invalidation),
    }
}

fn full_candidate(mode: AYCanaryCandidateMode) -> AYCanaryCandidate {
    full_candidate_for_family(AYCanaryFamily::SparseSubstitute, mode)
}

fn accepted_parent_gates() -> AYCanaryParentGateEvidence {
    AYCanaryParentGateEvidence {
        install_gate_accepted: true,
        consumer_gate_accepted: true,
        downstream_ay_no_regression_accepted: true,
    }
}

fn allowlist_with_key() -> AYCanaryAllowlist {
    let key = key();
    let mut allowlist = AYCanaryAllowlist::new();
    allowlist.add_exact(&key);
    allowlist
}

fn assert_no_authority(decision: &AYCanaryAllowlistDecision, reason: AYCanaryRejectionReason) {
    assert_eq!(decision.reason, reason);
    assert!(decision.baseline_authoritative);
    assert!(!decision.native_authoritative);
    assert!(decision.is_pre_activation_only());
    assert!(decision.side_effects.all_blocked());
    assert!(!decision.side_effects.callable_handle_published);
    assert!(!decision.side_effects.installable_cache_hit_accepted);
    assert!(!decision.side_effects.ay_registry_inserted);
    assert!(!decision.side_effects.release_install_published);
    assert!(!decision.side_effects.baseline_replaced);
    assert_eq!(decision.side_effects.useful_native_delta, 0);
    assert_eq!(decision.telemetry.schema, JIT_AY_CANARY_ALLOWLIST_SCHEMA);
    assert_eq!(
        decision.telemetry.schema_version,
        JIT_AY_CANARY_ALLOWLIST_SCHEMA_VERSION
    );
    assert_eq!(decision.telemetry.issue, 742);
    assert_eq!(
        decision.telemetry.record_sha256,
        decision.telemetry.canonical_record_sha256()
    );
    assert!(decision.telemetry.side_effects.all_blocked());
}

#[test]
fn ay_canary_allowlist_exact_tuple_stays_pre_activation() {
    let allowlist = allowlist_with_key();
    let candidate = full_candidate(AYCanaryCandidateMode::CanaryInstallable);

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(
        decision.status,
        AYCanaryDecisionStatus::AllowlistedRequiresProductGate
    );
    assert_no_authority(
        &decision,
        AYCanaryRejectionReason::ProductActivationRequired,
    );
    assert_eq!(
        decision.telemetry.replay_root_sha256.as_deref(),
        Some("sha256:replay-root-ay-lra-sparse-substitute")
    );
    assert_eq!(
        decision.telemetry.telemetry_key.as_deref(),
        Some("telemetry:ay:lra:sparse-substitute")
    );
}

#[test]
fn ay_canary_allowlist_basis_tuple_stays_pre_activation_with_typed_lra_facts() {
    let candidate = full_candidate_for_family(
        AYCanaryFamily::BasisRegionScanner,
        AYCanaryCandidateMode::CanaryInstallable,
    );
    let mut allowlist = AYCanaryAllowlist::new();
    allowlist.add_exact(&candidate.key);

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(
        decision.status,
        AYCanaryDecisionStatus::AllowlistedRequiresProductGate
    );
    assert_no_authority(
        &decision,
        AYCanaryRejectionReason::ProductActivationRequired,
    );
}

#[test]
fn ay_canary_allowlist_watch_list_bcp_tuple_stays_pre_activation_with_typed_bcp_facts() {
    let candidate = full_candidate_for_family(
        AYCanaryFamily::WatchListBcp,
        AYCanaryCandidateMode::CanaryInstallable,
    );
    let manifest = candidate.manifest.as_ref().unwrap();
    let proof_facts = AYCanaryBcpProofFactEvidence::aarch64_required_for(&candidate.key, manifest)
        .expect("watch-list BCP candidate has typed BCP evidence");
    let mut allowlist = AYCanaryAllowlist::new();
    allowlist.add_exact(&candidate.key);

    assert_eq!(proof_facts.bindings.len(), 7);
    assert!(
        proof_facts
            .bindings
            .iter()
            .any(|binding| binding.fact == AYCanaryBcpProofFact::WatchLayout)
    );
    assert!(
        proof_facts
            .bindings
            .iter()
            .any(|binding| binding.fact == AYCanaryBcpProofFact::ClauseArenaBounds)
    );
    assert!(
        proof_facts
            .bindings
            .iter()
            .any(|binding| { binding.fact == AYCanaryBcpProofFact::AssignmentTrailFreshness })
    );
    assert!(
        proof_facts
            .bindings
            .iter()
            .any(|binding| binding.fact == AYCanaryBcpProofFact::PendingQueueBounds)
    );
    assert!(
        proof_facts
            .bindings
            .iter()
            .any(|binding| binding.fact == AYCanaryBcpProofFact::GenerationMatch)
    );
    assert!(
        proof_facts
            .bindings
            .iter()
            .any(|binding| binding.fact == AYCanaryBcpProofFact::ResultAbi)
    );
    assert!(
        proof_facts
            .bindings
            .iter()
            .any(|binding| binding.fact == AYCanaryBcpProofFact::ReplayComparison)
    );
    assert_eq!(
        candidate.provenance.as_ref().unwrap().proof_report_sha256,
        proof_facts.canonical_report_sha256()
    );

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(
        decision.status,
        AYCanaryDecisionStatus::AllowlistedRequiresProductGate
    );
    assert_no_authority(
        &decision,
        AYCanaryRejectionReason::ProductActivationRequired,
    );
    assert_eq!(
        decision.telemetry.replay_root_sha256.as_deref(),
        Some("sha256:replay-root-ay-watch-list-bcp")
    );
    assert_eq!(
        decision.telemetry.telemetry_key.as_deref(),
        Some("telemetry:ay:watch-list-bcp")
    );
}

#[test]
fn ay_canary_allowlist_rejects_missing_typed_lra_fact_metadata() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    let proof_report_sha256 = {
        let manifest = candidate.manifest.as_ref().unwrap();
        let mut evidence =
            AYCanaryLraProofFactEvidence::aarch64_required_for(&candidate.key, manifest)
                .expect("sparse candidate has typed LRA evidence");
        evidence
            .bindings
            .retain(|binding| binding.fact != AYCanaryLraProofFact::OutputCapacityBounds);
        evidence.canonical_report_sha256()
    };
    candidate.provenance.as_mut().unwrap().proof_report_sha256 = proof_report_sha256;

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, AYCanaryRejectionReason::FailedProof);
}

#[test]
fn ay_canary_allowlist_rejects_mismatched_typed_lra_fact_metadata() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    let proof_report_sha256 = {
        let manifest = candidate.manifest.as_ref().unwrap();
        let mut evidence =
            AYCanaryLraProofFactEvidence::aarch64_required_for(&candidate.key, manifest)
                .expect("sparse candidate has typed LRA evidence");
        let binding = evidence
            .bindings
            .iter_mut()
            .find(|binding| binding.fact == AYCanaryLraProofFact::CoefficientOverflow)
            .expect("coefficient overflow proof fact is required");
        binding.lemma_id.push_str(".spoofed");
        evidence.canonical_report_sha256()
    };
    candidate.provenance.as_mut().unwrap().proof_report_sha256 = proof_report_sha256;

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, AYCanaryRejectionReason::FailedProof);
}

#[test]
fn ay_canary_allowlist_rejects_watch_list_bcp_missing_typed_bcp_fact_metadata() {
    let mut candidate = full_candidate_for_family(
        AYCanaryFamily::WatchListBcp,
        AYCanaryCandidateMode::CanaryInstallable,
    );
    let mut allowlist = AYCanaryAllowlist::new();
    allowlist.add_exact(&candidate.key);
    let proof_report_sha256 = {
        let manifest = candidate.manifest.as_ref().unwrap();
        let mut evidence =
            AYCanaryBcpProofFactEvidence::aarch64_required_for(&candidate.key, manifest)
                .expect("watch-list BCP candidate has typed BCP evidence");
        evidence
            .bindings
            .retain(|binding| binding.fact != AYCanaryBcpProofFact::PendingQueueBounds);
        evidence.canonical_report_sha256()
    };
    candidate.provenance.as_mut().unwrap().proof_report_sha256 = proof_report_sha256;

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, AYCanaryRejectionReason::FailedProof);
}

#[test]
fn ay_canary_allowlist_rejects_watch_list_bcp_tampered_typed_bcp_fact_metadata() {
    let mut candidate = full_candidate_for_family(
        AYCanaryFamily::WatchListBcp,
        AYCanaryCandidateMode::CanaryInstallable,
    );
    let mut allowlist = AYCanaryAllowlist::new();
    allowlist.add_exact(&candidate.key);
    let proof_report_sha256 = {
        let manifest = candidate.manifest.as_ref().unwrap();
        let mut evidence =
            AYCanaryBcpProofFactEvidence::aarch64_required_for(&candidate.key, manifest)
                .expect("watch-list BCP candidate has typed BCP evidence");
        let binding = evidence
            .bindings
            .iter_mut()
            .find(|binding| binding.fact == AYCanaryBcpProofFact::GenerationMatch)
            .expect("generation-match proof fact is required");
        binding.lemma_id.push_str(".spoofed");
        evidence.canonical_report_sha256()
    };
    candidate.provenance.as_mut().unwrap().proof_report_sha256 = proof_report_sha256;

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, AYCanaryRejectionReason::FailedProof);
}

#[test]
fn ay_canary_allowlist_binds_trust_ir_source_identity_into_lra_facts() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    let manifest = candidate.manifest.as_mut().unwrap();
    manifest.source_sha256 = "sha256:source-ay-lra-sparse-substitute-v2".to_owned();
    manifest.trust_ir_sha256 = "sha256:trust_ir-ay-lra-sparse-substitute-v2".to_owned();
    let invalidation = candidate.invalidation.as_mut().unwrap();
    invalidation.source_sha256 = manifest.source_sha256.clone();
    invalidation.trust_ir_sha256 = manifest.trust_ir_sha256.clone();

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, AYCanaryRejectionReason::FailedProof);
}

#[test]
fn ay_canary_allowlist_rejects_watch_list_bcp_path_with_lra_proof_facts() {
    let watch_key = key_for_family(AYCanaryFamily::WatchListBcp);
    let watch_manifest = manifest_for_key(&watch_key);
    let mut allowlist = AYCanaryAllowlist::new();
    allowlist.add_exact(&watch_key);

    let mut candidate = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    candidate.key = watch_key.clone();
    candidate.manifest = Some(watch_manifest.clone());
    candidate.layout = Some(layout_for_manifest(&watch_manifest));
    candidate.invalidation = Some(invalidation_for(&watch_key, &watch_manifest));
    candidate.provenance.as_mut().unwrap().replay_root_sha256 =
        watch_manifest.replay_root_sha256.clone();

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, AYCanaryRejectionReason::FailedProof);
}

#[test]
fn ay_canary_allowlist_rejects_non_allowlisted_tuples() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    candidate.key = AYCanaryAllowlistKey::new(
        "sha256:ay-lra-solver-program-other",
        AYCanaryFamily::SparseSubstitute,
        generations(),
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "proof-policy:v1:strict-ay-native",
        "sha256:layout-ay-sparse-basis-watch",
        "sha256:manifest-ay-lra-sparse-substitute",
    );

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, AYCanaryRejectionReason::NonAllowlisted);
}

#[test]
fn ay_canary_allowlist_rejects_non_callable_modes() {
    let allowlist = allowlist_with_key();
    let cases = [
        (
            AYCanaryCandidateMode::ProfileOnly,
            AYCanaryRejectionReason::ProfileOnlyNonCallable,
        ),
        (
            AYCanaryCandidateMode::ReplayOnly,
            AYCanaryRejectionReason::ReplayOnlyNonCallable,
        ),
        (
            AYCanaryCandidateMode::ShadowOnly,
            AYCanaryRejectionReason::ShadowOnlyNonCallable,
        ),
    ];

    for (mode, expected) in cases {
        let candidate = full_candidate(mode);
        let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

        assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
        assert_no_authority(&decision, expected);
    }
}

#[test]
fn ay_canary_allowlist_blocks_missing_parent_gate_evidence() {
    let allowlist = allowlist_with_key();
    let candidate = full_candidate(AYCanaryCandidateMode::CanaryInstallable);

    let decision = allowlist.evaluate(&candidate, AYCanaryParentGateEvidence::default());

    assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
    assert_no_authority(
        &decision,
        AYCanaryRejectionReason::MissingProductGateEvidence,
    );
}

#[test]
fn ay_canary_allowlist_negative_evidence_cases_fail_closed() {
    let allowlist = allowlist_with_key();

    let mut missing_manifest = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    missing_manifest.manifest = None;

    let mut layout_mismatch = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    layout_mismatch.layout.as_mut().unwrap().bounds = false;

    let mut failed_proof = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    failed_proof
        .provenance
        .as_mut()
        .unwrap()
        .proof_policy_decision = AYCanaryProofDecision::Rejected;

    let mut stale_generation = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    stale_generation
        .invalidation
        .as_mut()
        .unwrap()
        .current_generations = AYCanaryGenerationFence::new(7, 13, 17, 20);

    let mut missing_telemetry = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    missing_telemetry
        .manifest
        .as_mut()
        .unwrap()
        .telemetry_key
        .clear();

    let mut revoked = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    revoked.invalidation.as_mut().unwrap().revoked = true;

    let mut kill_switch = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    kill_switch
        .invalidation
        .as_mut()
        .unwrap()
        .kill_switch_active = true;

    let mut missing_equivalence = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    missing_equivalence.equivalence = None;

    let mut regression_mismatch = full_candidate(AYCanaryCandidateMode::CanaryInstallable);
    regression_mismatch
        .equivalence
        .as_mut()
        .unwrap()
        .native
        .wrong_answer_regressions = 1;

    let cases = [
        (missing_manifest, AYCanaryRejectionReason::MissingManifest),
        (layout_mismatch, AYCanaryRejectionReason::LayoutMismatch),
        (failed_proof, AYCanaryRejectionReason::FailedProof),
        (stale_generation, AYCanaryRejectionReason::StaleGeneration),
        (missing_telemetry, AYCanaryRejectionReason::MissingTelemetry),
        (revoked, AYCanaryRejectionReason::Revoked),
        (kill_switch, AYCanaryRejectionReason::KillSwitchActive),
        (
            missing_equivalence,
            AYCanaryRejectionReason::MissingEquivalence,
        ),
        (
            regression_mismatch,
            AYCanaryRejectionReason::AYRegressionEvidenceMismatch,
        ),
    ];

    for (candidate, expected) in cases {
        let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

        assert_eq!(decision.status, AYCanaryDecisionStatus::Rejected);
        assert_no_authority(&decision, expected);
    }
}
