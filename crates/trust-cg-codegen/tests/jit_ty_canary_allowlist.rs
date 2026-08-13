// trust-cg-codegen/tests/jit_ty_canary_allowlist.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::jit_ty_canary_allowlist::TY_CANARY_TRUST_IR_PROOF_FACT_BINDINGS_PREFIX;
use trust_cg_codegen::{
    JIT_TY_CANARY_ALLOWLIST_SCHEMA, JIT_TY_CANARY_ALLOWLIST_SCHEMA_VERSION, Target,
    TyCanaryAllowlist, TyCanaryAllowlistDecision, TyCanaryAllowlistKey, TyCanaryCandidate,
    TyCanaryCandidateMode, TyCanaryDecisionStatus, TyCanaryEquivalenceEvidence,
    TyCanaryExecutionObservation, TyCanaryFamily, TyCanaryGenerationTuple,
    TyCanaryInvalidationState, TyCanaryLayoutProof, TyCanaryManifestBinding,
    TyCanaryParentGateEvidence, TyCanaryProofDecision, TyCanaryRejectionReason,
    TyCanaryValidationProvenance,
};

fn generations() -> TyCanaryGenerationTuple {
    TyCanaryGenerationTuple::new(11, 23, 37, 41)
}

fn key() -> TyCanaryAllowlistKey {
    TyCanaryAllowlistKey::new(
        "sha256:ty-mcl-spec",
        "sha256:ty-mcl-action-next",
        TyCanaryFamily::ActionCluster,
        generations(),
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "proof-policy:v1:strict-ty-native",
        "sha256:layout-flat-parent-fingerprint",
        "sha256:manifest-ty-mcl-action-next",
    )
}

fn manifest() -> TyCanaryManifestBinding {
    TyCanaryManifestBinding {
        source_sha256: "sha256:source-ty-mcl".to_owned(),
        trust_ir_sha256: "sha256:trust_ir-ty-mcl-next".to_owned(),
        native_payload_sha256: "sha256:native-ty-mcl-next".to_owned(),
        abi_checksum: "sha256:abi-aarch64-darwin-ty".to_owned(),
        layout_checksum: "sha256:layout-flat-parent-fingerprint".to_owned(),
        compiler_config_sha256: "sha256:compiler-config-o3-strict".to_owned(),
        target_facts_sha256: "sha256:target-facts-aarch64-darwin".to_owned(),
        proof_policy: "proof-policy:v1:strict-ty-native".to_owned(),
        consumer_kind: "ty".to_owned(),
        wrapper_id: "wrapper:ty:mcl:next:v1".to_owned(),
        symbols: vec!["ty_mcl_next".to_owned(), "ty_mcl_fingerprint".to_owned()],
        replay_root_sha256: "sha256:replay-root-ty-mcl-next".to_owned(),
        telemetry_key: "telemetry:ty:mcl:next".to_owned(),
        manifest_sha256: "sha256:manifest-ty-mcl-action-next".to_owned(),
    }
}

fn layout() -> TyCanaryLayoutProof {
    TyCanaryLayoutProof {
        flat_state_buffers: true,
        parent_buffers: true,
        fingerprint_buffers: true,
        callback_runtime_symbols: true,
        return_status_buffers: true,
        generation_fences: true,
        mutability_aliasing: true,
        wrapper_id: "wrapper:ty:mcl:next:v1".to_owned(),
    }
}

fn provenance_for_manifest(manifest: &TyCanaryManifestBinding) -> TyCanaryValidationProvenance {
    TyCanaryValidationProvenance {
        proof_report_sha256: "sha256:proof-report-ty-mcl-next".to_owned(),
        tv_report_sha256: "sha256:tv-report-ty-mcl-next".to_owned(),
        replay_root_sha256: "sha256:replay-root-ty-mcl-next".to_owned(),
        consumer_equivalence_sha256: "sha256:equivalence-ty-mcl-next".to_owned(),
        validator_id: "trust-cg-tv:ty:v1".to_owned(),
        proof_policy_decision: TyCanaryProofDecision::Accepted,
    }
    .with_required_trust_ir_proof_fact_bindings(manifest)
}

fn observation() -> TyCanaryExecutionObservation {
    TyCanaryExecutionObservation {
        generated_state_count: 64,
        distinct_state_count: 19,
        parent_indexes_sha256: "sha256:parents-ty-mcl-next".to_owned(),
        fingerprints_sha256: "sha256:fingerprints-ty-mcl-next".to_owned(),
        final_verdict: "ok".to_owned(),
        status_codes_sha256: "sha256:status-codes-ty-mcl-next".to_owned(),
        callback_visible_sha256: "sha256:callbacks-ty-mcl-next".to_owned(),
        replay_verdict_sha256: "sha256:replay-verdict-ty-mcl-next".to_owned(),
    }
}

fn equivalence() -> TyCanaryEquivalenceEvidence {
    let observation = observation();
    TyCanaryEquivalenceEvidence {
        baseline: observation.clone(),
        native: observation,
    }
}

fn invalidation() -> TyCanaryInvalidationState {
    let manifest = manifest();
    TyCanaryInvalidationState {
        current_generations: generations(),
        target_facts_sha256: "sha256:target-facts-aarch64-darwin".to_owned(),
        proof_policy: "proof-policy:v1:strict-ty-native".to_owned(),
        compiler_config_sha256: manifest.compiler_config_sha256,
        manifest_sha256: manifest.manifest_sha256,
        source_sha256: manifest.source_sha256,
        trust_ir_sha256: manifest.trust_ir_sha256,
        native_payload_sha256: manifest.native_payload_sha256,
        kill_switch_active: false,
        revoked: false,
    }
}

fn full_candidate(mode: TyCanaryCandidateMode) -> TyCanaryCandidate {
    let manifest = manifest();
    TyCanaryCandidate {
        mode,
        key: key(),
        manifest: Some(manifest.clone()),
        layout: Some(layout()),
        provenance: Some(provenance_for_manifest(&manifest)),
        equivalence: Some(equivalence()),
        invalidation: Some(invalidation()),
    }
}

fn accepted_parent_gates() -> TyCanaryParentGateEvidence {
    TyCanaryParentGateEvidence {
        install_gate_accepted: true,
        consumer_gate_accepted: true,
        three_spec_cli_accepted: true,
    }
}

fn allowlist_with_key() -> TyCanaryAllowlist {
    let key = key();
    let mut allowlist = TyCanaryAllowlist::new();
    allowlist.add_exact(&key);
    allowlist
}

fn assert_no_authority(decision: &TyCanaryAllowlistDecision, reason: TyCanaryRejectionReason) {
    assert_eq!(decision.reason, reason);
    assert!(decision.baseline_authoritative);
    assert!(!decision.native_authoritative);
    assert!(decision.is_pre_activation_only());
    assert!(decision.side_effects.all_blocked());
    assert!(!decision.side_effects.callable_handle_published);
    assert!(!decision.side_effects.installable_cache_hit_accepted);
    assert!(!decision.side_effects.ty_native_activated);
    assert!(!decision.side_effects.baseline_replaced);
    assert_eq!(decision.side_effects.useful_native_delta, 0);
    assert_eq!(decision.telemetry.schema, JIT_TY_CANARY_ALLOWLIST_SCHEMA);
    assert_eq!(
        decision.telemetry.schema_version,
        JIT_TY_CANARY_ALLOWLIST_SCHEMA_VERSION
    );
    assert_eq!(decision.telemetry.issue, 741);
    assert_eq!(
        decision.telemetry.record_sha256,
        decision.telemetry.canonical_record_sha256()
    );
    assert!(decision.telemetry.side_effects.all_blocked());
}

fn proof_fact_binding_records(provenance: &TyCanaryValidationProvenance) -> Vec<&str> {
    provenance
        .validator_id
        .split_once(TY_CANARY_TRUST_IR_PROOF_FACT_BINDINGS_PREFIX)
        .expect("test provenance should include proof-fact binding records")
        .1
        .split(',')
        .collect()
}

#[test]
fn ty_canary_allowlist_exact_tuple_stays_pre_activation() {
    let allowlist = allowlist_with_key();
    let candidate = full_candidate(TyCanaryCandidateMode::CanaryInstallable);

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(
        decision.status,
        TyCanaryDecisionStatus::AllowlistedRequiresProductGate
    );
    assert_no_authority(
        &decision,
        TyCanaryRejectionReason::ProductActivationRequired,
    );
    assert_eq!(
        decision.telemetry.replay_root_sha256.as_deref(),
        Some("sha256:replay-root-ty-mcl-next")
    );
    assert_eq!(
        decision.telemetry.telemetry_key.as_deref(),
        Some("telemetry:ty:mcl:next")
    );
}

#[test]
fn ty_canary_allowlist_rejects_non_allowlisted_tuples() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    candidate.key = TyCanaryAllowlistKey::new(
        "sha256:ty-mcl-spec-other",
        "sha256:ty-mcl-action-next",
        TyCanaryFamily::ActionCluster,
        generations(),
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "proof-policy:v1:strict-ty-native",
        "sha256:layout-flat-parent-fingerprint",
        "sha256:manifest-ty-mcl-action-next",
    );

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, TyCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, TyCanaryRejectionReason::NonAllowlisted);
}

#[test]
fn ty_canary_allowlist_rejects_non_callable_modes() {
    let allowlist = allowlist_with_key();
    let cases = [
        (
            TyCanaryCandidateMode::ProfileOnly,
            TyCanaryRejectionReason::ProfileOnlyNonCallable,
        ),
        (
            TyCanaryCandidateMode::ReplayOnly,
            TyCanaryRejectionReason::ReplayOnlyNonCallable,
        ),
        (
            TyCanaryCandidateMode::ShadowOnly,
            TyCanaryRejectionReason::ShadowOnlyNonCallable,
        ),
    ];

    for (mode, expected) in cases {
        let candidate = full_candidate(mode);
        let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

        assert_eq!(decision.status, TyCanaryDecisionStatus::Rejected);
        assert_no_authority(&decision, expected);
    }
}

#[test]
fn ty_canary_allowlist_blocks_missing_parent_gate_evidence() {
    let allowlist = allowlist_with_key();
    let candidate = full_candidate(TyCanaryCandidateMode::CanaryInstallable);

    let decision = allowlist.evaluate(&candidate, TyCanaryParentGateEvidence::default());

    assert_eq!(decision.status, TyCanaryDecisionStatus::Rejected);
    assert_no_authority(
        &decision,
        TyCanaryRejectionReason::MissingProductGateEvidence,
    );
}

#[test]
fn ty_canary_allowlist_negative_evidence_cases_fail_closed() {
    let allowlist = allowlist_with_key();

    let mut missing_manifest = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    missing_manifest.manifest = None;

    let mut layout_mismatch = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    layout_mismatch.layout.as_mut().unwrap().fingerprint_buffers = false;

    let mut failed_proof = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    failed_proof
        .provenance
        .as_mut()
        .unwrap()
        .proof_policy_decision = TyCanaryProofDecision::Rejected;

    let mut stale_generation = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    stale_generation
        .invalidation
        .as_mut()
        .unwrap()
        .current_generations = TyCanaryGenerationTuple::new(11, 23, 37, 42);

    let mut missing_telemetry = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    missing_telemetry
        .manifest
        .as_mut()
        .unwrap()
        .telemetry_key
        .clear();

    let mut revoked = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    revoked.invalidation.as_mut().unwrap().revoked = true;

    let mut kill_switch = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    kill_switch
        .invalidation
        .as_mut()
        .unwrap()
        .kill_switch_active = true;

    let mut missing_equivalence = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    missing_equivalence.equivalence = None;

    let cases = [
        (missing_manifest, TyCanaryRejectionReason::MissingManifest),
        (layout_mismatch, TyCanaryRejectionReason::LayoutMismatch),
        (failed_proof, TyCanaryRejectionReason::FailedProof),
        (stale_generation, TyCanaryRejectionReason::StaleGeneration),
        (missing_telemetry, TyCanaryRejectionReason::MissingTelemetry),
        (revoked, TyCanaryRejectionReason::Revoked),
        (kill_switch, TyCanaryRejectionReason::KillSwitchActive),
        (
            missing_equivalence,
            TyCanaryRejectionReason::MissingEquivalence,
        ),
    ];

    for (candidate, expected) in cases {
        let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

        assert_eq!(decision.status, TyCanaryDecisionStatus::Rejected);
        assert_no_authority(&decision, expected);
    }
}

#[test]
fn ty_canary_allowlist_rejects_missing_proof_fact_binding() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    candidate.provenance.as_mut().unwrap().validator_id = "trust-cg-tv:ty:v1".to_owned();

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, TyCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, TyCanaryRejectionReason::FailedProof);
}

#[test]
fn ty_canary_allowlist_rejects_duplicate_proof_fact_binding() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    let provenance = candidate.provenance.as_mut().unwrap();
    let duplicate_record = proof_fact_binding_records(provenance)[0].to_owned();
    provenance.validator_id.push(',');
    provenance.validator_id.push_str(&duplicate_record);

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, TyCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, TyCanaryRejectionReason::FailedProof);
}

#[test]
fn ty_canary_allowlist_rejects_stale_proof_fact_binding() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    candidate.manifest.as_mut().unwrap().trust_ir_sha256 =
        "sha256:trust_ir-ty-mcl-next-v2".to_owned();

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, TyCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, TyCanaryRejectionReason::FailedProof);
}

#[test]
fn ty_canary_allowlist_rejects_tampered_proof_fact_binding() {
    let allowlist = allowlist_with_key();
    let mut candidate = full_candidate(TyCanaryCandidateMode::CanaryInstallable);
    let provenance = candidate.provenance.as_mut().unwrap();
    provenance.validator_id = provenance
        .validator_id
        .replacen("=verified=", "=missing=", 1);

    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());

    assert_eq!(decision.status, TyCanaryDecisionStatus::Rejected);
    assert_no_authority(&decision, TyCanaryRejectionReason::FailedProof);
}
