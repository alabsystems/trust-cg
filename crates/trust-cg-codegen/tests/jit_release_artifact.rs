// trust-cg-codegen/tests/jit_release_artifact.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::BTreeMap;

use trust_cg_codegen::jit_contract::{
    ArtifactChecksum, HOST_JIT_TARGET_FEATURE_PROFILE_CURRENT_POLICY_KEY,
    HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA, HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY,
    HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY, HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY,
    trust_ir_hardware_vector_contract_manifest_row_count,
    trust_ir_hardware_vector_contract_manifest_sha256,
    trust_ir_hardware_vector_contract_metadata_entries,
};
use trust_cg_codegen::jit_install_gate::{
    NATIVE_INSTALL_GATE_PACKET_SCHEMA, NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_REPLAY_SCHEMA, NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
    NativeInstallGateActions, NativeInstallGateArtifactPacket, NativeInstallGateAuthority,
    NativeInstallGateConsumerVerdictBinding, NativeInstallGateDenyControlPlane,
    NativeInstallGateDenyReason, NativeInstallGateDenyScope, NativeInstallGateDisposition,
    NativeInstallGateFreshnessObservation, NativeInstallGateFreshnessPacket,
    NativeInstallGatePacket, NativeInstallGateRejectionCode, NativeInstallGateReplayBinding,
    NativeInstallGateReplayIdentity, NativeInstallGateRevalidationInput, NativeInstallGateSurface,
    NativeInstallGateTelemetryPacket, NativeInstallGateValidationPacket,
    TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE, TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA,
    persist_native_install_gate_packet_bindings,
};
use trust_cg_codegen::jit_release::{
    JIT_RELEASE_BUNDLE_SCHEMA, JIT_RELEASE_BUNDLE_SCHEMA_VERSION,
    RELEASE_NATIVE_PAYLOAD_SHA256_KEY, RELEASE_PROOF_OPTIMIZATION_CITATION_SUMMARY_SCHEMA,
    RELEASE_PROOF_OPTIMIZATION_CITATION_SUMMARY_SCHEMA_VERSION,
    RELEASE_SOURCE_LOCK_AY_REVISION_KEY, RELEASE_SOURCE_LOCK_METADATA_SCHEMA,
    RELEASE_SOURCE_LOCK_METADATA_SCHEMA_VERSION, RELEASE_SOURCE_LOCK_SCHEMA_KEY,
    RELEASE_SOURCE_LOCK_SCHEMA_VERSION_KEY, RELEASE_SOURCE_LOCK_SHA256_KEY,
    RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY,
    RELEASE_SOURCE_LOCK_TY_REVISION_KEY, RELEASE_SOURCE_SHA256_KEY, RELEASE_TRUST_IR_SHA256_KEY,
    RELEASE_TY_NATIVE_FUSED_PROOF_OPT_CERTIFICATE_ID_KEY,
    RELEASE_TY_NATIVE_FUSED_PROOF_OPT_FUNCTION_NAME_KEY,
    RELEASE_TY_NATIVE_FUSED_PROOF_OPT_SOURCE_REGION_HASH_KEY,
    RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TARGET_REGION_HASH_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY, RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA,
    RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY, RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY,
    RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY, ReleaseArtifactManifestReference,
    ReleaseBundleFileReference, ReleaseBundleInstallCode, ReleaseBundleInstallStatus,
    ReleaseNativeInstallGateMetadata, ReleaseProofReportReference, ReleaseReplayBundleMetadata,
    ReleaseTyNativeFusedReplayMetadata,
};
use trust_cg_codegen::pipeline::{
    ProofOptimizationCertificateCitation, ProofOptimizationConsumedFactCitation,
};

fn file(path: &str, sha256: &str) -> ReleaseBundleFileReference {
    ReleaseBundleFileReference::new(path, sha256)
}

fn proof(path: &str, sha256: &str) -> ReleaseProofReportReference {
    ReleaseProofReportReference::new(path, sha256)
        .with_policy("require_replay")
        .with_verdict("accepted")
        .with_solver("trust-cg-verify")
        .with_obligation_set("obligations:entry")
        .with_timeout_ms(250)
}

fn release_freshness_domains(
    consumer: &str,
    generation: u64,
) -> Vec<NativeInstallGateFreshnessObservation> {
    let mut domains = vec![
        "shared_artifact",
        "shared_proof_policy",
        "shared_target_abi",
        "shared_release_bundle",
        "shared_revocation",
        "shared_kill_switch",
    ];
    match consumer {
        "ay" => domains.extend([
            "ay_solver",
            "ay_sparse",
            "ay_basis",
            "ay_watch_list",
            "ay_proof_witness",
            "ay_rollback",
            "ay_registry",
        ]),
        "ty" => domains.extend([
            "ty_runtime",
            "ty_action",
            "ty_invariant",
            "ty_liveness",
            "ty_fingerprint",
            "ty_flat_state",
            "ty_helper_abi",
            "ty_library_publication",
        ]),
        _ => {}
    }
    domains
        .into_iter()
        .map(|domain| NativeInstallGateFreshnessObservation::new(domain, generation, generation))
        .collect()
}

fn accepted_release_gate(
    consumer: &str,
    consumer_mode: &str,
    artifact_id: &str,
    manifest_checksum: ArtifactChecksum,
    proof_tv_checksum: &str,
    telemetry_sha256: &str,
) -> ReleaseNativeInstallGateMetadata {
    let mut packet = NativeInstallGatePacket {
        schema: NATIVE_INSTALL_GATE_PACKET_SCHEMA,
        schema_version: NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION,
        gate_issue: 681,
        design_issue: 682,
        consumer: consumer.to_owned(),
        consumer_mode: consumer_mode.to_owned(),
        surface: NativeInstallGateSurface::ReleaseBundle,
        artifact: NativeInstallGateArtifactPacket {
            artifact_id: artifact_id.to_owned(),
            manifest_schema: "trust-cg.jit.artifact_manifest.v1".to_owned(),
            manifest_schema_version: 1,
            manifest_checksum,
            source_sha256: "sha256:source".to_owned(),
            trust_ir_sha256: "sha256:trust_ir".to_owned(),
            native_payload_sha256: "sha256:native".to_owned(),
            target_checksum: ArtifactChecksum::new(0x2001),
            abi_checksum: ArtifactChecksum::new(0x2002),
            layout_checksum: ArtifactChecksum::new(0x2003),
            proof_policy_checksum: ArtifactChecksum::new(0x2004),
            invalidation_checksum: ArtifactChecksum::new(0x2005),
            manifest_metadata: BTreeMap::new(),
        },
        validation: NativeInstallGateValidationPacket {
            layout_status: "accepted",
            layout_evidence_sha256: Some("sha256:layout".to_owned()),
            layout_wrapper_identity: Some("release-wrapper.v1".to_owned()),
            layout_validation_provenance: Some("trust-cg.release.layout_adapter.v1".to_owned()),
            layout_invalidation_checksum: Some(ArtifactChecksum::new(0x2005)),
            layout_generation_domains: vec!["release_generation".to_owned()],
            proof_verdict: "verified",
            proof_reject_code: None,
            proof_verifier: Some("trust-cg-verify".to_owned()),
            proof_report_sha256: Some(proof_tv_checksum.to_owned()),
            obligation_set: Some("obligations:entry".to_owned()),
            timeout_ms: Some(250),
        },
        freshness: NativeInstallGateFreshnessPacket {
            artifact_generation: 7,
            current_generation: 7,
            freshness_domains: release_freshness_domains(consumer, 7),
            revoked: false,
            deny_control: None,
        },
        replay_identity: Some(NativeInstallGateReplayIdentity {
            schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
            schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
            replay_root_sha256: "sha256:release-replay-root".to_owned(),
            replay_consumer: consumer.to_owned(),
            replay_family: consumer_mode.to_owned(),
            artifact_id: artifact_id.to_owned(),
            source_sha256: "sha256:source".to_owned(),
            trust_ir_sha256: "sha256:trust_ir".to_owned(),
            native_payload_sha256: "sha256:native".to_owned(),
            replay_record_sha256: String::new(),
        }),
        telemetry: Some(NativeInstallGateTelemetryPacket {
            schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
            schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
            event_id: "release-gate-event".to_owned(),
            counter_scope: String::new(),
            record_sha256: String::new(),
            artifact_id: artifact_id.to_owned(),
            manifest_checksum,
            proof_report_sha256: Some(proof_tv_checksum.to_owned()),
            layout_checksum: ArtifactChecksum::new(0x2003),
            invalidation_checksum: ArtifactChecksum::new(0x2005),
            disposition: NativeInstallGateDisposition::Installable,
            rejection_code: None,
            install_authority: NativeInstallGateAuthority::CanaryCallable,
            useful_native_delta: 0,
        }),
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        disposition: NativeInstallGateDisposition::Installable,
        rejection_code: None,
        install_authority: NativeInstallGateAuthority::CanaryCallable,
        packet_hash: ArtifactChecksum::new(0),
        replay_binding: NativeInstallGateReplayBinding {
            packet_hash: ArtifactChecksum::new(0),
            replay_root_sha256: String::new(),
        },
        consumer_verdict: NativeInstallGateConsumerVerdictBinding {
            consumer: String::new(),
            consumer_mode: String::new(),
            surface: NativeInstallGateSurface::ReleaseBundle,
            verdict_id: String::new(),
            verdict_sha256: String::new(),
        },
        actions: NativeInstallGateActions::for_surface(NativeInstallGateSurface::ReleaseBundle),
    };
    persist_native_install_gate_packet_bindings(&mut packet);
    ReleaseNativeInstallGateMetadata::new(packet, telemetry_sha256)
}

fn bind_test_source_lock_metadata(
    mut bundle: ReleaseReplayBundleMetadata,
    downstream_revision: &str,
) -> ReleaseReplayBundleMetadata {
    let (source_sha256, trust_ir_sha256, native_payload_sha256) = {
        let gate = bundle.install_gate.as_ref().expect("release gate");
        (
            gate.packet.artifact.source_sha256.clone(),
            gate.packet.artifact.trust_ir_sha256.clone(),
            gate.packet.artifact.native_payload_sha256.clone(),
        )
    };
    let downstream_revision_key = match bundle.consumer.as_str() {
        "ay" => RELEASE_SOURCE_LOCK_AY_REVISION_KEY,
        "ty" => RELEASE_SOURCE_LOCK_TY_REVISION_KEY,
        consumer => panic!("unsupported test consumer {consumer}"),
    };

    bundle.metadata.remove(RELEASE_SOURCE_LOCK_AY_REVISION_KEY);
    bundle.metadata.remove(RELEASE_SOURCE_LOCK_TY_REVISION_KEY);
    bundle.metadata.insert(
        RELEASE_SOURCE_LOCK_SCHEMA_KEY.to_owned(),
        RELEASE_SOURCE_LOCK_METADATA_SCHEMA.to_owned(),
    );
    bundle.metadata.insert(
        RELEASE_SOURCE_LOCK_SCHEMA_VERSION_KEY.to_owned(),
        RELEASE_SOURCE_LOCK_METADATA_SCHEMA_VERSION.to_string(),
    );
    bundle.metadata.insert(
        RELEASE_SOURCE_LOCK_SHA256_KEY.to_owned(),
        bundle.source_lock.sha256.clone(),
    );
    bundle.metadata.insert(
        RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY.to_owned(),
        "trust-cg-revision-test".to_owned(),
    );
    bundle.metadata.insert(
        RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY.to_owned(),
        "trust_ir-revision-test".to_owned(),
    );
    bundle.metadata.insert(
        downstream_revision_key.to_owned(),
        downstream_revision.to_owned(),
    );
    bundle
        .metadata
        .insert(RELEASE_SOURCE_SHA256_KEY.to_owned(), source_sha256);
    bundle
        .metadata
        .insert(RELEASE_TRUST_IR_SHA256_KEY.to_owned(), trust_ir_sha256);
    bundle.metadata.insert(
        RELEASE_NATIVE_PAYLOAD_SHA256_KEY.to_owned(),
        native_payload_sha256,
    );
    bundle
}

fn base_bundle() -> ReleaseReplayBundleMetadata {
    let manifest_checksum = ArtifactChecksum::new(0x1234);
    let telemetry = file("telemetry/compile-telemetry.json", "sha256:telemetry");
    let bundle = ReleaseReplayBundleMetadata::new(
        "ay",
        "solver_program_native_kernel",
        "artifact-1",
        ReleaseArtifactManifestReference::new(
            "artifact.manifest.json",
            "sha256:artifact-json",
            1,
            manifest_checksum,
        ),
        file("source-lock.json", "sha256:source-lock"),
        proof("proofs/proof-a.json", "sha256:proof-a"),
        telemetry.clone(),
        file("release/package.json", "sha256:release-package"),
        file("replay/replay.json", "sha256:replay"),
        file("gate-results.json", "sha256:gate-results"),
    )
    .with_proof_reports([
        proof("proofs/proof-b.json", "sha256:proof-b"),
        proof("proofs/proof-a.json", "sha256:proof-a"),
    ])
    .with_install_gate(accepted_release_gate(
        "ay",
        "solver_program_native_kernel",
        "artifact-1",
        manifest_checksum,
        "sha256:proof-a",
        &telemetry.sha256,
    ));
    bind_test_source_lock_metadata(bundle, "ay-revision-test")
}

fn ty_native_fused_bundle() -> ReleaseReplayBundleMetadata {
    let manifest_checksum = ArtifactChecksum::new(0x5678);
    let telemetry = file(
        "telemetry/ty-native-fused-telemetry.json",
        "sha256:ty-telemetry-file",
    );
    let install_gate = accepted_release_gate(
        "ty",
        TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
        "request-1-1-native-fused",
        manifest_checksum,
        "sha256:ty-proof-validation",
        &telemetry.sha256,
    );
    let bundle = ReleaseReplayBundleMetadata::new(
        "ty",
        TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
        "request-1-1-native-fused",
        ReleaseArtifactManifestReference::new(
            "artifact.manifest.json",
            "sha256:ty-artifact-json",
            1,
            manifest_checksum,
        ),
        file("source-lock.json", "sha256:ty-source-lock"),
        proof("proofs/ty-proof.json", "sha256:ty-proof-validation"),
        telemetry,
        file("release/package.json", "sha256:ty-release-package"),
        file("replay/request-1-1.json", "sha256:ty-replay"),
        file("gate-results.json", "sha256:ty-gate-results"),
    )
    .with_install_gate_metadata_bindings(install_gate);
    let citation = ty_native_fused_proof_opt_citation("sha256:ty-proof-validation");
    let bundle = bundle
        .with_proof_optimization_certificates([citation.clone()])
        .with_ty_native_fused_proof_optimization_citation_identity(&citation);
    bind_test_source_lock_metadata(bundle, "ty-revision-test")
}

fn assert_non_installable_decision(
    bundle: &ReleaseReplayBundleMetadata,
    code: ReleaseBundleInstallCode,
    code_str: &str,
) {
    let decision = bundle.install_decision();

    assert!(!decision.is_installable());
    assert_eq!(decision.status, ReleaseBundleInstallStatus::NonInstallable);
    assert_eq!(decision.status.as_str(), "non_installable");
    assert_eq!(decision.code, code);
    assert_eq!(decision.code.as_str(), code_str);
}

fn assert_install_decision_json(
    bundle: &ReleaseReplayBundleMetadata,
    status: &str,
    code: &str,
    installable: bool,
) {
    let json = bundle.to_json_value();
    let decision = &json["install_decision"];

    assert_eq!(decision["status"].as_str(), Some(status));
    assert_eq!(decision["code"].as_str(), Some(code));
    assert_eq!(decision["installable"].as_bool(), Some(installable));
}

fn proof_opt_citation(
    function_name: &str,
    certificate_id: &str,
) -> ProofOptimizationCertificateCitation {
    ProofOptimizationCertificateCitation {
        function_name: function_name.to_owned(),
        certificate_id: certificate_id.to_owned(),
        proof_hash: "00000000000000000000000000000002".to_owned(),
        validation_hash: "00000000000000000000000000000003".to_owned(),
        source_region_hash: "00000000000000000000000000000004".to_owned(),
        target_region_hash: "00000000000000000000000000000005".to_owned(),
        transform_name: "proof-opts.no-overflow".to_owned(),
        transform_version: 1,
        admission: "proof-annotation+proof-facts".to_owned(),
        kind: "CheckedToUnchecked".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: vec![ProofOptimizationConsumedFactCitation {
            name: "NoUndef".to_owned(),
            payload: None,
        }],
    }
}

fn ty_native_fused_proof_opt_citation(
    validation_hash: &str,
) -> ProofOptimizationCertificateCitation {
    ProofOptimizationCertificateCitation {
        function_name: "request-1-1".to_owned(),
        certificate_id: "ty-native-fused-parent-loop:request-1-1:cert-v1".to_owned(),
        proof_hash: "sha256:ty-proof".to_owned(),
        validation_hash: validation_hash.to_owned(),
        source_region_hash: "sha256:ty-source-region".to_owned(),
        target_region_hash: "sha256:ty-target-region".to_owned(),
        transform_name: "ty-native-fused-parent-loop".to_owned(),
        transform_version: 1,
        admission: "proof-annotation+proof-facts".to_owned(),
        kind: "TyNativeFusedParentLoop".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
            .iter()
            .map(
                |(metadata_key, fact)| ProofOptimizationConsumedFactCitation {
                    name: (*fact).to_owned(),
                    payload: Some((*metadata_key).to_owned()),
                },
            )
            .collect(),
    }
}

fn assert_missing_proof_report_metadata(bundle: &ReleaseReplayBundleMetadata) {
    assert_non_installable_decision(
        bundle,
        ReleaseBundleInstallCode::MissingProofReportMetadata,
        "missing_proof_report_metadata",
    );
    assert_install_decision_json(
        bundle,
        "non_installable",
        "missing_proof_report_metadata",
        false,
    );
}

fn assert_missing_source_lock_metadata(bundle: &ReleaseReplayBundleMetadata) {
    assert_non_installable_decision(
        bundle,
        ReleaseBundleInstallCode::MissingSourceLockMetadata,
        "missing_source_lock_metadata",
    );
    assert_install_decision_json(
        bundle,
        "non_installable",
        "missing_source_lock_metadata",
        false,
    );
}

fn assert_source_lock_metadata_mismatch(bundle: &ReleaseReplayBundleMetadata) {
    assert_non_installable_decision(
        bundle,
        ReleaseBundleInstallCode::SourceLockMetadataMismatch,
        "source_lock_metadata_mismatch",
    );
    assert_install_decision_json(
        bundle,
        "non_installable",
        "source_lock_metadata_mismatch",
        false,
    );
}

#[test]
fn release_bundle_json_and_checksum_are_order_stable() {
    let mut left = base_bundle();
    left.metadata.insert("profile".to_owned(), "o1".to_owned());
    left.metadata.insert("consumer".to_owned(), "ay".to_owned());

    let mut right = base_bundle();
    right.proof_reports.reverse();
    right
        .metadata
        .insert("consumer".to_owned(), "ay".to_owned());
    right.metadata.insert("profile".to_owned(), "o1".to_owned());

    assert_eq!(left.to_pretty_json(), right.to_pretty_json());
    assert_eq!(left.checksum(), right.checksum());

    let json: serde_json::Value =
        serde_json::from_str(&left.to_pretty_json()).expect("bundle JSON should parse");
    assert_eq!(json["schema"].as_str(), Some(JIT_RELEASE_BUNDLE_SCHEMA));
    assert_eq!(
        json["schema_version"].as_u64(),
        Some(u64::from(JIT_RELEASE_BUNDLE_SCHEMA_VERSION))
    );
    assert_eq!(json["artifact_id"].as_str(), Some("artifact-1"));
    assert_eq!(
        json["artifact_manifest"]["manifest_checksum"].as_str(),
        Some("trust-cg-stable128:00000000000000000000000000001234")
    );
    assert_eq!(
        json["source_lock"]["path"].as_str(),
        Some("source-lock.json")
    );
    assert_eq!(
        json["proof_reports"][0]["path"].as_str(),
        Some("proofs/proof-a.json")
    );
    assert_eq!(
        json["telemetry"]["sha256"].as_str(),
        Some("sha256:telemetry")
    );
    assert_eq!(
        json["release_package"]["path"].as_str(),
        Some("release/package.json")
    );
    assert_eq!(json["replay"]["sha256"].as_str(), Some("sha256:replay"));
    assert_eq!(
        json["gate_results"]["sha256"].as_str(),
        Some("sha256:gate-results")
    );
    assert_eq!(
        json["install_gate"]["schema"].as_str(),
        Some(NATIVE_INSTALL_GATE_PACKET_SCHEMA)
    );
    assert_eq!(
        json["install_gate"]["disposition"].as_str(),
        Some("installable")
    );
    assert_eq!(
        json["install_gate"]["proof_tv_checksum"].as_str(),
        Some("sha256:proof-a")
    );
    assert_eq!(
        json["install_gate"]["telemetry_checksum"].as_str(),
        Some("sha256:telemetry")
    );
    assert!(
        json["install_gate"]["packet_hash"]
            .as_str()
            .is_some_and(|hash| hash.starts_with("trust-cg-stable128:"))
    );
    assert_eq!(
        json["install_gate"]["telemetry_event_id"].as_str(),
        Some("release-gate-event")
    );
    assert!(
        json["install_gate"]["telemetry_record_sha256"]
            .as_str()
            .is_some_and(|hash| hash.starts_with("sha256:"))
    );
    assert_eq!(
        json["install_gate"]["counter_scope"].as_str(),
        Some("ay:solver_program_native_kernel:release_bundle:artifact-1")
    );
    assert_eq!(
        json["install_gate"]["useful_native_delta"].as_u64(),
        Some(0)
    );
    assert!(
        json["install_gate"]["replay_root_sha256"]
            .as_str()
            .is_some_and(|hash| hash.starts_with("sha256:"))
    );
    assert_eq!(
        json["install_gate"]["actions"]["release_installable"].as_bool(),
        Some(true)
    );
    assert_eq!(
        json["install_gate"]["actions"]["useful_native_eligible"].as_bool(),
        Some(true)
    );
    assert_eq!(
        json["install_decision"]["status"].as_str(),
        Some("installable")
    );
    assert_eq!(
        json["install_decision"]["code"].as_str(),
        Some("installable")
    );
    assert_eq!(
        json["install_decision"]["installable"].as_bool(),
        Some(true)
    );
}

#[test]
fn release_bundle_json_carries_proof_optimization_certificate_citations() {
    let bundle = base_bundle().with_proof_optimization_certificates([
        proof_opt_citation("f_b", "0000000000000000000000000000000b"),
        proof_opt_citation("f_a", "0000000000000000000000000000000a"),
    ]);

    let json = bundle.to_json_value();
    let citations = json["proof_optimization_certificates"]
        .as_array()
        .expect("release bundle should serialize proof optimization citations");
    assert_eq!(citations.len(), 2);
    assert_eq!(citations[0]["function_name"].as_str(), Some("f_a"));
    assert_eq!(
        citations[0]["certificate_id"].as_str(),
        Some("0000000000000000000000000000000a")
    );
    assert_eq!(
        citations[0]["proof_hash"].as_str(),
        Some("00000000000000000000000000000002")
    );
    assert_eq!(
        citations[0]["validation_hash"].as_str(),
        Some("00000000000000000000000000000003")
    );
}

#[test]
fn release_bundle_json_carries_proof_optimization_citation_summary() {
    let mut applied = proof_opt_citation("f_a", "0000000000000000000000000000000a");
    applied.kind = "GuardEliminated".to_owned();
    applied.consumed_facts = vec![ProofOptimizationConsumedFactCitation {
        name: "ValidShift".to_owned(),
        payload: None,
    }];

    let mut rejected = proof_opt_citation("f_b", "0000000000000000000000000000000b");
    rejected.kind = "GuardEliminated".to_owned();
    rejected.status = "rejected".to_owned();
    rejected.rejection_code = Some("missing_fact".to_owned());
    rejected.rejection_fact = Some("NonZeroDivisor".to_owned());
    rejected.rejection_detail = Some("division guard proof fact was unavailable".to_owned());
    rejected.consumed_facts = vec![ProofOptimizationConsumedFactCitation {
        name: "NonZeroDivisor".to_owned(),
        payload: Some("v1".to_owned()),
    }];

    let bundle =
        base_bundle().with_proof_optimization_certificates([rejected.clone(), applied.clone()]);

    let json = bundle.to_json_value();
    let citations = json["proof_optimization_certificates"]
        .as_array()
        .expect("release bundle should serialize proof optimization citations");
    let summary = json["proof_optimization_citation_summary"]
        .as_object()
        .expect("release bundle should serialize proof optimization citation summary");

    assert_eq!(
        summary["schema"].as_str(),
        Some(RELEASE_PROOF_OPTIMIZATION_CITATION_SUMMARY_SCHEMA)
    );
    assert_eq!(
        summary["schema_version"].as_u64(),
        Some(u64::from(
            RELEASE_PROOF_OPTIMIZATION_CITATION_SUMMARY_SCHEMA_VERSION
        ))
    );
    assert_eq!(summary["certificate_count"].as_u64(), Some(2));
    assert_eq!(summary["function_count"].as_u64(), Some(2));
    assert_eq!(summary["applied_count"].as_u64(), Some(1));
    assert_eq!(summary["rejected_count"].as_u64(), Some(1));
    assert_eq!(summary["functions"][0].as_str(), Some("f_a"));
    assert_eq!(summary["functions"][1].as_str(), Some("f_b"));
    assert_eq!(summary["status_counts"]["applied"].as_u64(), Some(1));
    assert_eq!(summary["status_counts"]["rejected"].as_u64(), Some(1));
    assert_eq!(summary["kind_counts"]["GuardEliminated"].as_u64(), Some(2));
    assert_eq!(
        summary["transform_counts"]["proof-opts.no-overflow@1"].as_u64(),
        Some(2)
    );
    assert_eq!(
        summary["consumed_fact_counts"]["NonZeroDivisor"].as_u64(),
        Some(1)
    );
    assert_eq!(
        summary["consumed_fact_counts"]["ValidShift"].as_u64(),
        Some(1)
    );
    assert_eq!(
        summary["rejection_code_counts"]["missing_fact"].as_u64(),
        Some(1)
    );

    assert_eq!(
        citations[0]["certificate_id"].as_str(),
        Some(applied.certificate_id.as_str())
    );
    assert_eq!(
        citations[1]["certificate_id"].as_str(),
        Some(rejected.certificate_id.as_str())
    );
}

#[test]
fn release_bundle_json_carries_fact_only_pair_combined_proof_optimization_summary() {
    let citation = ProofOptimizationCertificateCitation {
        function_name: "pair_aligned".to_owned(),
        certificate_id: "0000000000000000000000000000002a".to_owned(),
        proof_hash: "0000000000000000000000000000002b".to_owned(),
        validation_hash: "0000000000000000000000000000002c".to_owned(),
        source_region_hash: "0000000000000000000000000000002d".to_owned(),
        target_region_hash: "0000000000000000000000000000002e".to_owned(),
        transform_name: "proof-opts.aligned.pair-combined".to_owned(),
        transform_version: 1,
        admission: "proof-facts".to_owned(),
        kind: "PairCombined".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: vec![ProofOptimizationConsumedFactCitation {
            name: "Aligned".to_owned(),
            payload: Some("16".to_owned()),
        }],
    };

    let bundle = base_bundle().with_proof_optimization_certificates([citation.clone()]);

    let json = bundle.to_json_value();
    let citations = json["proof_optimization_certificates"]
        .as_array()
        .expect("release bundle should serialize proof optimization citations");
    let summary = json["proof_optimization_citation_summary"]
        .as_object()
        .expect("release bundle should serialize proof optimization citation summary");

    assert_eq!(citations.len(), 1);
    assert_eq!(citations[0]["function_name"].as_str(), Some("pair_aligned"));
    assert_eq!(
        citations[0]["certificate_id"].as_str(),
        Some(citation.certificate_id.as_str())
    );
    assert_eq!(
        citations[0]["transform_name"].as_str(),
        Some("proof-opts.aligned.pair-combined")
    );
    assert_eq!(citations[0]["transform_version"].as_u64(), Some(1));
    assert_eq!(citations[0]["admission"].as_str(), Some("proof-facts"));
    assert_eq!(citations[0]["kind"].as_str(), Some("PairCombined"));
    assert_eq!(citations[0]["status"].as_str(), Some("applied"));
    assert!(citations[0]["rejection_code"].is_null());
    assert_eq!(
        citations[0]["consumed_facts"].as_array().map(Vec::len),
        Some(1)
    );
    assert_eq!(
        citations[0]["consumed_facts"][0]["name"].as_str(),
        Some("Aligned")
    );
    assert_eq!(
        citations[0]["consumed_facts"][0]["payload"].as_str(),
        Some("16")
    );

    assert_eq!(summary["certificate_count"].as_u64(), Some(1));
    assert_eq!(summary["function_count"].as_u64(), Some(1));
    assert_eq!(summary["applied_count"].as_u64(), Some(1));
    assert_eq!(summary["rejected_count"].as_u64(), Some(0));
    assert_eq!(summary["functions"][0].as_str(), Some("pair_aligned"));
    assert_eq!(summary["status_counts"]["applied"].as_u64(), Some(1));
    assert_eq!(summary["kind_counts"]["PairCombined"].as_u64(), Some(1));
    assert_eq!(
        summary["transform_counts"]["proof-opts.aligned.pair-combined@1"].as_u64(),
        Some(1)
    );
    assert_eq!(summary["consumed_fact_counts"]["Aligned"].as_u64(), Some(1));
    assert!(
        summary["rejection_code_counts"]
            .as_object()
            .is_some_and(serde_json::Map::is_empty)
    );
}

#[test]
fn release_bundle_json_carries_gvn_valid_borrow_load_reuse_citation_shape() {
    let citation = ProofOptimizationCertificateCitation {
        function_name: "reuse_load_across_borrowed_store".to_owned(),
        certificate_id: "0000000000000000000000000000003a".to_owned(),
        proof_hash: "0000000000000000000000000000003b".to_owned(),
        validation_hash: "0000000000000000000000000000003c".to_owned(),
        source_region_hash: "0000000000000000000000000000003d".to_owned(),
        target_region_hash: "0000000000000000000000000000003e".to_owned(),
        transform_name: "gvn.valid-borrow.load-eliminated".to_owned(),
        transform_version: 1,
        admission: "proof-reorderable-load-store".to_owned(),
        kind: "PairEliminated".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: vec![
            ProofOptimizationConsumedFactCitation {
                name: "ValidBorrow".to_owned(),
                payload: None,
            },
            ProofOptimizationConsumedFactCitation {
                name: "ValidBorrow".to_owned(),
                payload: None,
            },
        ],
    };

    let bundle = base_bundle().with_proof_optimization_certificates([citation.clone()]);

    let json = bundle.to_json_value();
    let citations = json["proof_optimization_certificates"]
        .as_array()
        .expect("release bundle should serialize proof optimization citations");
    let summary = json["proof_optimization_citation_summary"]
        .as_object()
        .expect("release bundle should serialize proof optimization citation summary");

    assert_eq!(citations.len(), 1);
    assert_eq!(
        citations[0]["function_name"].as_str(),
        Some("reuse_load_across_borrowed_store")
    );
    assert_eq!(
        citations[0]["certificate_id"].as_str(),
        Some(citation.certificate_id.as_str())
    );
    assert_eq!(
        citations[0]["transform_name"].as_str(),
        Some("gvn.valid-borrow.load-eliminated")
    );
    assert_eq!(citations[0]["transform_version"].as_u64(), Some(1));
    assert_eq!(
        citations[0]["admission"].as_str(),
        Some("proof-reorderable-load-store")
    );
    assert_eq!(citations[0]["kind"].as_str(), Some("PairEliminated"));
    assert_ne!(citations[0]["kind"].as_str(), Some("PairCombined"));
    assert_eq!(citations[0]["status"].as_str(), Some("applied"));
    assert!(citations[0]["rejection_code"].is_null());
    assert_eq!(
        citations[0]["consumed_facts"].as_array().map(Vec::len),
        Some(2)
    );
    assert_eq!(
        citations[0]["consumed_facts"][0]["name"].as_str(),
        Some("ValidBorrow")
    );
    assert!(citations[0]["consumed_facts"][0]["payload"].is_null());
    assert_eq!(
        citations[0]["consumed_facts"][1]["name"].as_str(),
        Some("ValidBorrow")
    );
    assert!(citations[0]["consumed_facts"][1]["payload"].is_null());

    assert_eq!(summary["certificate_count"].as_u64(), Some(1));
    assert_eq!(summary["function_count"].as_u64(), Some(1));
    assert_eq!(summary["applied_count"].as_u64(), Some(1));
    assert_eq!(summary["rejected_count"].as_u64(), Some(0));
    assert_eq!(
        summary["functions"][0].as_str(),
        Some("reuse_load_across_borrowed_store")
    );
    assert_eq!(summary["status_counts"]["applied"].as_u64(), Some(1));
    assert_eq!(summary["kind_counts"]["PairEliminated"].as_u64(), Some(1));
    assert!(summary["kind_counts"]["PairCombined"].is_null());
    assert_eq!(
        summary["transform_counts"]["gvn.valid-borrow.load-eliminated@1"].as_u64(),
        Some(1)
    );
    assert!(summary["transform_counts"]["proof-opts.aligned.pair-combined@1"].is_null());
    assert_eq!(
        summary["consumed_fact_counts"]["ValidBorrow"].as_u64(),
        Some(2)
    );
    assert!(
        summary["rejection_code_counts"]
            .as_object()
            .is_some_and(serde_json::Map::is_empty)
    );
}

#[test]
fn release_bundle_proof_optimization_summary_is_order_stable_and_not_an_install_gate() {
    let mut rejected = proof_opt_citation("f_b", "0000000000000000000000000000000b");
    rejected.status = "rejected".to_owned();
    rejected.rejection_code = Some("missing_fact".to_owned());
    let applied = proof_opt_citation("f_a", "0000000000000000000000000000000a");

    let left =
        base_bundle().with_proof_optimization_certificates([rejected.clone(), applied.clone()]);
    let right = base_bundle().with_proof_optimization_certificates([applied, rejected]);

    assert_eq!(left.to_pretty_json(), right.to_pretty_json());
    assert_eq!(left.checksum(), right.checksum());
    assert!(left.install_decision().is_installable());
    assert_install_decision_json(&left, "installable", "installable", true);
}

#[test]
fn release_bundle_metadata_carries_trust_ir_hardware_vector_contract_from_gate() {
    let bundle = base_bundle();
    let mut install_gate = accepted_release_gate(
        "ay",
        "solver_program_native_kernel",
        "artifact-1",
        bundle.artifact_manifest.manifest_checksum,
        "sha256:proof-a",
        &bundle.telemetry.sha256,
    );
    install_gate.packet.artifact.manifest_metadata =
        trust_ir_hardware_vector_contract_metadata_entries();
    persist_native_install_gate_packet_bindings(&mut install_gate.packet);
    let bundle = bundle.with_install_gate_metadata_bindings(install_gate);

    assert!(bundle.install_decision().is_installable());

    let json = bundle.to_json_value();
    let metadata = json["metadata"]
        .as_object()
        .expect("release metadata should serialize as an object");
    let expected_manifest_sha256 = trust_ir_hardware_vector_contract_manifest_sha256();
    assert_eq!(
        metadata
            .get(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY)
            .and_then(serde_json::Value::as_str),
        Some(expected_manifest_sha256.as_str())
    );
    let expected_row_count = trust_ir_hardware_vector_contract_manifest_row_count().to_string();
    assert_eq!(
        metadata
            .get(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY)
            .and_then(serde_json::Value::as_str),
        Some(expected_row_count.as_str())
    );
    assert_eq!(
        json["install_gate"]["artifact_metadata"]
            .get(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY)
            .and_then(serde_json::Value::as_str),
        Some(expected_manifest_sha256.as_str())
    );
}

#[test]
fn release_bundle_metadata_carries_host_jit_target_feature_profile_from_gate() {
    let bundle = base_bundle();
    let mut install_gate = accepted_release_gate(
        "ay",
        "solver_program_native_kernel",
        "artifact-1",
        bundle.artifact_manifest.manifest_checksum,
        "sha256:proof-a",
        &bundle.telemetry.sha256,
    );
    install_gate.packet.artifact.manifest_metadata.extend([
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY.to_owned(),
            HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA.to_owned(),
        ),
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY.to_owned(),
            "x86_64-unknown-linux".to_owned(),
        ),
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_CURRENT_POLICY_KEY.to_owned(),
            "manifest-target-features".to_owned(),
        ),
        (
            HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY.to_owned(),
            "sha256:target-feature-profile".to_owned(),
        ),
    ]);
    persist_native_install_gate_packet_bindings(&mut install_gate.packet);
    let bundle = bundle.with_install_gate_metadata_bindings(install_gate);

    assert!(bundle.install_decision().is_installable());

    let json = bundle.to_json_value();
    assert_eq!(
        json["metadata"]
            .get(HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY)
            .and_then(serde_json::Value::as_str),
        Some(HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA)
    );
    assert_eq!(
        json["metadata"]
            .get(HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY)
            .and_then(serde_json::Value::as_str),
        Some("x86_64-unknown-linux")
    );
    assert_eq!(
        json["install_gate"]["artifact_metadata"]
            .get(HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY)
            .and_then(serde_json::Value::as_str),
        Some("sha256:target-feature-profile")
    );
}

#[test]
fn release_bundle_metadata_binds_ty_native_fused_replay_release_identity() {
    let bundle = ty_native_fused_bundle();
    let gate = bundle.install_gate.as_ref().expect("TY release gate");
    let replay = gate
        .packet
        .replay_identity
        .as_ref()
        .expect("TY replay identity");
    let telemetry = gate.packet.telemetry.as_ref().expect("TY telemetry");
    let typed_metadata =
        ReleaseTyNativeFusedReplayMetadata::from_install_gate(gate).expect("TY metadata");

    assert_eq!(
        typed_metadata.manifest_checksum,
        ArtifactChecksum::new(0x5678)
    );
    assert_eq!(typed_metadata.replay_root_sha256, replay.replay_root_sha256);
    assert_eq!(
        typed_metadata.replay_record_sha256,
        replay.replay_record_sha256
    );
    assert_eq!(typed_metadata.telemetry_event_id, telemetry.event_id);
    assert_eq!(
        typed_metadata.telemetry_record_sha256,
        telemetry.record_sha256
    );
    assert_eq!(typed_metadata.gate_packet_hash, gate.packet.packet_hash);
    assert_eq!(
        typed_metadata.proof_validation_sha256,
        gate.packet
            .validation
            .proof_report_sha256
            .clone()
            .expect("proof validation hash")
    );
    assert!(bundle.install_decision().is_installable());

    let json = bundle.to_json_value();
    let metadata = json["metadata"]
        .as_object()
        .expect("TY release metadata should serialize as an object");
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY)
            .and_then(serde_json::Value::as_str),
        Some(RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA)
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY)
            .and_then(serde_json::Value::as_str),
        Some("1")
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY)
            .and_then(serde_json::Value::as_str),
        Some("trust-cg-stable128:00000000000000000000000000005678")
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY)
            .and_then(serde_json::Value::as_str),
        Some(replay.replay_root_sha256.as_str())
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY)
            .and_then(serde_json::Value::as_str),
        Some(replay.replay_record_sha256.as_str())
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY)
            .and_then(serde_json::Value::as_str),
        Some(telemetry.event_id.as_str())
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY)
            .and_then(serde_json::Value::as_str),
        Some(telemetry.record_sha256.as_str())
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY)
            .and_then(serde_json::Value::as_str)
            .expect("gate packet hash metadata"),
        gate.packet.packet_hash.to_string()
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY)
            .and_then(serde_json::Value::as_str),
        gate.packet.validation.proof_report_sha256.as_deref()
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_PROOF_OPT_FUNCTION_NAME_KEY)
            .and_then(serde_json::Value::as_str),
        Some("request-1-1")
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_PROOF_OPT_CERTIFICATE_ID_KEY)
            .and_then(serde_json::Value::as_str),
        Some("ty-native-fused-parent-loop:request-1-1:cert-v1")
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_PROOF_OPT_SOURCE_REGION_HASH_KEY)
            .and_then(serde_json::Value::as_str),
        Some("sha256:ty-source-region")
    );
    assert_eq!(
        metadata
            .get(RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TARGET_REGION_HASH_KEY)
            .and_then(serde_json::Value::as_str),
        Some("sha256:ty-target-region")
    );

    let left_checksum = bundle.checksum();
    let mut changed = ty_native_fused_bundle();
    changed.metadata.insert(
        RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY.to_owned(),
        "sha256:changed-replay-root".to_owned(),
    );
    assert_ne!(left_checksum, changed.checksum());
}

#[test]
fn ty_native_fused_release_bundle_consumed_proof_optimization_citation_is_installable() {
    let bundle = ty_native_fused_bundle();
    let decision = bundle.install_decision();

    assert!(decision.is_installable());
    assert_eq!(decision.status, ReleaseBundleInstallStatus::Installable);
    assert_eq!(decision.code, ReleaseBundleInstallCode::Installable);
    assert_install_decision_json(&bundle, "installable", "installable", true);
}

#[test]
fn ty_native_fused_release_bundle_wrong_proof_optimization_citation_identity_is_non_installable() {
    let mut wrong_certificate = ty_native_fused_proof_opt_citation("sha256:ty-proof-validation");
    wrong_certificate.certificate_id =
        "ty-native-fused-parent-loop:wrong-request:cert-v1".to_owned();

    let mut stale_certificate = ty_native_fused_proof_opt_citation("sha256:ty-proof-validation");
    stale_certificate.certificate_id = "ty-native-fused-parent-loop:request-1-1:cert-v0".to_owned();

    let mut wrong_function = ty_native_fused_proof_opt_citation("sha256:ty-proof-validation");
    wrong_function.function_name = "wrong-request".to_owned();
    wrong_function.certificate_id = "ty-native-fused-parent-loop:wrong-request:cert-v1".to_owned();

    let mut wrong_source = ty_native_fused_proof_opt_citation("sha256:ty-proof-validation");
    wrong_source.source_region_hash = "sha256:wrong-trust_ir-region".to_owned();

    let mut wrong_target = ty_native_fused_proof_opt_citation("sha256:ty-proof-validation");
    wrong_target.target_region_hash = "sha256:wrong-native-region".to_owned();

    for (name, citation) in [
        ("certificate", wrong_certificate),
        ("stale certificate", stale_certificate),
        ("function", wrong_function),
        ("source", wrong_source),
        ("target", wrong_target),
    ] {
        let bundle = ty_native_fused_bundle().with_proof_optimization_certificates([citation]);
        let decision = bundle.install_decision();

        assert!(!decision.is_installable(), "{name}");
        assert_eq!(
            decision.code,
            ReleaseBundleInstallCode::MissingProofOptimizationCitation,
            "{name}"
        );
        assert_install_decision_json(
            &bundle,
            "non_installable",
            "missing_proof_optimization_citation",
            false,
        );
    }
}

#[test]
fn ty_native_fused_release_bundle_missing_bound_proof_optimization_identity_is_non_installable() {
    for key in [
        RELEASE_TY_NATIVE_FUSED_PROOF_OPT_FUNCTION_NAME_KEY,
        RELEASE_TY_NATIVE_FUSED_PROOF_OPT_CERTIFICATE_ID_KEY,
        RELEASE_TY_NATIVE_FUSED_PROOF_OPT_SOURCE_REGION_HASH_KEY,
        RELEASE_TY_NATIVE_FUSED_PROOF_OPT_TARGET_REGION_HASH_KEY,
    ] {
        let mut bundle = ty_native_fused_bundle();
        assert!(
            bundle.metadata.remove(key).is_some(),
            "test fixture should bind {key}"
        );

        assert_non_installable_decision(
            &bundle,
            ReleaseBundleInstallCode::MissingProofOptimizationCitation,
            "missing_proof_optimization_citation",
        );
        assert_install_decision_json(
            &bundle,
            "non_installable",
            "missing_proof_optimization_citation",
            false,
        );
    }
}

#[test]
fn ty_native_fused_release_bundle_missing_proof_optimization_citation_is_non_installable() {
    let bundle = ty_native_fused_bundle().with_proof_optimization_certificates([]);

    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::MissingProofOptimizationCitation,
        "missing_proof_optimization_citation",
    );
    assert_install_decision_json(
        &bundle,
        "non_installable",
        "missing_proof_optimization_citation",
        false,
    );
}

#[test]
fn ty_native_fused_release_bundle_proof_optimization_citation_missing_fact_is_non_installable() {
    let mut citation = ty_native_fused_proof_opt_citation("sha256:ty-proof-validation");
    citation
        .consumed_facts
        .retain(|fact| fact.name != "state_vector_bounds");
    let bundle = ty_native_fused_bundle().with_proof_optimization_certificates([citation]);

    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::ProofOptimizationCitationMissingFact,
        "proof_optimization_citation_missing_fact",
    );
    assert_install_decision_json(
        &bundle,
        "non_installable",
        "proof_optimization_citation_missing_fact",
        false,
    );
}

#[test]
fn ty_native_fused_release_bundle_stale_proof_optimization_validation_hash_is_non_installable() {
    let citation = ty_native_fused_proof_opt_citation("sha256:stale-proof-validation");
    let bundle = ty_native_fused_bundle().with_proof_optimization_certificates([citation]);

    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::ProofOptimizationValidationHashMismatch,
        "proof_optimization_validation_hash_mismatch",
    );
    assert_install_decision_json(
        &bundle,
        "non_installable",
        "proof_optimization_validation_hash_mismatch",
        false,
    );
}

#[test]
fn ty_native_fused_release_bundle_missing_bound_replay_metadata_is_non_installable() {
    for key in [
        RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY,
    ] {
        let mut bundle = ty_native_fused_bundle();
        assert!(
            bundle.metadata.remove(key).is_some(),
            "test fixture should bind {key}"
        );

        assert_non_installable_decision(
            &bundle,
            ReleaseBundleInstallCode::MissingReplayMetadata,
            "missing_replay_metadata",
        );
        assert_install_decision_json(&bundle, "non_installable", "missing_replay_metadata", false);
    }
}

#[test]
fn ty_native_fused_release_bundle_blank_bound_replay_metadata_is_non_installable() {
    for (key, value) in [
        (RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY, ""),
        (RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY, " \t\n"),
        (RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY, ""),
        (RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY, " \t\n"),
        (RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY, ""),
        (
            RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY,
            " \t\n",
        ),
        (
            RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY,
            "",
        ),
        (RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY, " \t\n"),
        (
            RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY,
            "",
        ),
    ] {
        let mut bundle = ty_native_fused_bundle();
        assert!(
            bundle.metadata.contains_key(key),
            "test fixture should bind {key}"
        );
        bundle.metadata.insert(key.to_owned(), value.to_owned());

        assert_non_installable_decision(
            &bundle,
            ReleaseBundleInstallCode::MissingReplayMetadata,
            "missing_replay_metadata",
        );
        assert_install_decision_json(&bundle, "non_installable", "missing_replay_metadata", false);
    }
}

#[test]
fn ty_native_fused_release_bundle_tampered_bound_replay_metadata_is_non_installable() {
    for (key, value) in [
        (
            RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY,
            "sha256:stale-release-replay-root",
        ),
        (
            RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY,
            "sha256:stale-proof-validation",
        ),
    ] {
        let mut bundle = ty_native_fused_bundle();
        bundle.metadata.insert(key.to_owned(), value.to_owned());

        assert_non_installable_decision(
            &bundle,
            ReleaseBundleInstallCode::GateMetadataMismatch,
            "gate_metadata_mismatch",
        );
        assert_install_decision_json(&bundle, "non_installable", "gate_metadata_mismatch", false);
    }
}

#[test]
fn release_bundle_suppresses_ty_native_fused_metadata_for_mismatched_gate_bundle() {
    let bundle_manifest_checksum = ArtifactChecksum::new(0x5678);
    let telemetry = file(
        "telemetry/ty-native-fused-telemetry.json",
        "sha256:ty-telemetry-file",
    );
    let mismatched_gate = accepted_release_gate(
        "ty",
        TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
        "request-1-1-native-fused-other",
        ArtifactChecksum::new(0x5679),
        "sha256:ty-proof-validation",
        &telemetry.sha256,
    );
    let bundle = ReleaseReplayBundleMetadata::new(
        "ty",
        TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
        "request-1-1-native-fused",
        ReleaseArtifactManifestReference::new(
            "artifact.manifest.json",
            "sha256:ty-artifact-json",
            1,
            bundle_manifest_checksum,
        ),
        file("source-lock.json", "sha256:ty-source-lock"),
        proof("proofs/ty-proof.json", "sha256:ty-proof-validation"),
        telemetry,
        file("release/package.json", "sha256:ty-release-package"),
        file("replay/request-1-1.json", "sha256:ty-replay"),
        file("gate-results.json", "sha256:ty-gate-results"),
    )
    .with_install_gate_metadata_bindings(mismatched_gate);

    let json = bundle.to_json_value();
    let metadata = json["metadata"]
        .as_object()
        .expect("release metadata should serialize as an object");
    for key in [
        RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_SCHEMA_VERSION_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_MANIFEST_CHECKSUM_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_ROOT_SHA256_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_RECORD_SHA256_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_EVENT_ID_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_TELEMETRY_RECORD_SHA256_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_GATE_PACKET_HASH_KEY,
        RELEASE_TY_NATIVE_FUSED_REPLAY_PROOF_VALIDATION_SHA256_KEY,
    ] {
        assert!(
            !metadata.contains_key(key),
            "mismatched gate must not inject {key}"
        );
    }
    assert!(
        json["install_gate"].is_object(),
        "the mismatched gate packet should still be attached for diagnostics"
    );
    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::GateMetadataMismatch,
        "gate_metadata_mismatch",
    );
    assert_install_decision_json(&bundle, "non_installable", "gate_metadata_mismatch", false);
}

#[test]
fn release_bundle_checksum_changes_when_bound_hash_changes() {
    let left = base_bundle();
    let mut right = base_bundle();

    right.telemetry.sha256 = "sha256:changed-telemetry".to_owned();

    assert_ne!(left.to_pretty_json(), right.to_pretty_json());
    assert_ne!(left.checksum(), right.checksum());
}

#[test]
fn release_bundle_supported_consumers_are_installable() {
    for consumer in ["ay", "ty"] {
        let mut bundle = base_bundle();
        bundle.consumer = consumer.to_owned();
        let telemetry_sha256 = bundle.telemetry.sha256.clone();
        bundle.install_gate = Some(accepted_release_gate(
            consumer,
            &bundle.consumer_mode,
            &bundle.artifact_id,
            bundle.artifact_manifest.manifest_checksum,
            "sha256:proof-a",
            &telemetry_sha256,
        ));
        bundle = bind_test_source_lock_metadata(bundle, &format!("{consumer}-revision-test"));

        let decision = bundle.install_decision();

        assert!(decision.is_installable());
        assert_eq!(decision.status, ReleaseBundleInstallStatus::Installable);
        assert_eq!(decision.status.as_str(), "installable");
        assert_eq!(decision.code, ReleaseBundleInstallCode::Installable);
        assert_eq!(decision.code.as_str(), "installable");
    }
}

#[test]
fn release_bundle_unsupported_schema_or_version_is_non_installable() {
    let mut unsupported_schema = base_bundle();
    unsupported_schema.schema = "trust-cg.phase6.release_replay_bundle.v2".to_owned();
    assert_non_installable_decision(
        &unsupported_schema,
        ReleaseBundleInstallCode::UnsupportedSchema,
        "unsupported_schema",
    );

    let mut unsupported_version = base_bundle();
    unsupported_version.schema_version = JIT_RELEASE_BUNDLE_SCHEMA_VERSION + 1;
    assert_non_installable_decision(
        &unsupported_version,
        ReleaseBundleInstallCode::UnsupportedSchema,
        "unsupported_schema",
    );
}

#[test]
fn release_bundle_unsupported_consumer_is_non_installable() {
    let mut bundle = base_bundle();
    bundle.consumer = "unsupported-consumer".to_owned();

    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::UnsupportedConsumer,
        "unsupported_consumer",
    );
}

#[test]
fn release_bundle_missing_replay_metadata_serializes_non_installable_decision() {
    let mut bundle = base_bundle();
    bundle.replay.path.clear();

    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::MissingReplayMetadata,
        "missing_replay_metadata",
    );
    assert_install_decision_json(&bundle, "non_installable", "missing_replay_metadata", false);
}

#[test]
fn release_bundle_missing_gate_metadata_is_non_installable() {
    let mut bundle = base_bundle();
    bundle.install_gate = None;

    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::MissingGateMetadata,
        "missing_gate_metadata",
    );
    assert_install_decision_json(&bundle, "non_installable", "missing_gate_metadata", false);
}

#[test]
fn release_bundle_source_lock_metadata_is_required_for_install() {
    for key in [
        RELEASE_SOURCE_LOCK_SCHEMA_KEY,
        RELEASE_SOURCE_LOCK_SCHEMA_VERSION_KEY,
        RELEASE_SOURCE_LOCK_SHA256_KEY,
        RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY,
        RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY,
        RELEASE_SOURCE_LOCK_AY_REVISION_KEY,
        RELEASE_SOURCE_SHA256_KEY,
        RELEASE_TRUST_IR_SHA256_KEY,
        RELEASE_NATIVE_PAYLOAD_SHA256_KEY,
    ] {
        let mut bundle = base_bundle();
        assert!(
            bundle.metadata.remove(key).is_some(),
            "test fixture should bind {key}"
        );

        assert_missing_source_lock_metadata(&bundle);
    }

    let mut ty_bundle = ty_native_fused_bundle();
    assert!(
        ty_bundle
            .metadata
            .remove(RELEASE_SOURCE_LOCK_TY_REVISION_KEY)
            .is_some(),
        "TY fixture should bind downstream source-lock revision"
    );
    assert_missing_source_lock_metadata(&ty_bundle);
}

#[test]
fn release_bundle_source_lock_metadata_rejects_placeholder_revisions() {
    for (key, value) in [
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, ""),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, " \t\n"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "unknown"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "tbd"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "n/a"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "none"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "latest"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "main"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "master"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "refs/heads/main"),
        (RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY, "origin/master"),
        (RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY, "UNKNOWN"),
        (RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY, "TBD"),
        (RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY, "N/A"),
        (RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY, "NONE"),
        (RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY, "LATEST"),
        (RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY, "MAIN"),
        (RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY, "MASTER"),
        (RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY, "heads/main"),
        (
            RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY,
            "remotes/origin/master",
        ),
        (RELEASE_SOURCE_LOCK_AY_REVISION_KEY, "TODO"),
        (RELEASE_SOURCE_LOCK_AY_REVISION_KEY, "TODO: pin ay"),
        (RELEASE_SOURCE_LOCK_AY_REVISION_KEY, "todo-later"),
    ] {
        let mut bundle = base_bundle();
        assert!(
            bundle.metadata.contains_key(key),
            "test fixture should bind {key}"
        );
        bundle.metadata.insert(key.to_owned(), value.to_owned());

        assert_missing_source_lock_metadata(&bundle);
    }

    let mut ty_bundle = ty_native_fused_bundle();
    ty_bundle.metadata.insert(
        RELEASE_SOURCE_LOCK_TY_REVISION_KEY.to_owned(),
        "unknown".to_owned(),
    );
    assert_missing_source_lock_metadata(&ty_bundle);
}

#[test]
fn release_bundle_source_lock_metadata_rejects_remote_tracking_revision_refs() {
    for (key, value) in [
        (
            RELEASE_SOURCE_LOCK_TRUST_CG_REVISION_KEY,
            "refs/remotes/origin/main",
        ),
        (
            RELEASE_SOURCE_LOCK_TRUST_IR_REVISION_KEY,
            "refs/remotes/upstream/release-hardening",
        ),
        (
            RELEASE_SOURCE_LOCK_AY_REVISION_KEY,
            "refs/remotes/internal/feature/r18-release",
        ),
        (RELEASE_SOURCE_LOCK_AY_REVISION_KEY, "remotes/internal/main"),
    ] {
        let mut bundle = base_bundle();
        assert!(
            bundle.metadata.contains_key(key),
            "test fixture should bind {key}"
        );
        bundle.metadata.insert(key.to_owned(), value.to_owned());

        assert_missing_source_lock_metadata(&bundle);
    }

    let mut ty_bundle = ty_native_fused_bundle();
    ty_bundle.metadata.insert(
        RELEASE_SOURCE_LOCK_TY_REVISION_KEY.to_owned(),
        "refs/remotes/origin/main".to_owned(),
    );
    assert_missing_source_lock_metadata(&ty_bundle);
}

#[test]
fn release_bundle_source_lock_metadata_mismatch_is_non_installable() {
    for (key, value) in [
        (
            RELEASE_SOURCE_LOCK_SCHEMA_KEY,
            "trust-cg.release.source_lock_metadata.future",
        ),
        (RELEASE_SOURCE_LOCK_SCHEMA_VERSION_KEY, "2"),
        (RELEASE_SOURCE_LOCK_SHA256_KEY, "sha256:other-source-lock"),
        (RELEASE_SOURCE_SHA256_KEY, "sha256:other-source"),
        (RELEASE_TRUST_IR_SHA256_KEY, "sha256:other-trust_ir"),
        (
            RELEASE_NATIVE_PAYLOAD_SHA256_KEY,
            "sha256:other-native-payload",
        ),
    ] {
        let mut bundle = base_bundle();
        assert!(
            bundle.metadata.contains_key(key),
            "test fixture should bind {key}"
        );
        bundle.metadata.insert(key.to_owned(), value.to_owned());

        assert_source_lock_metadata_mismatch(&bundle);
    }

    let mut mismatched_gate = base_bundle();
    mismatched_gate
        .install_gate
        .as_mut()
        .expect("base gate")
        .packet
        .artifact
        .source_sha256 = "sha256:gate-source-other".to_owned();
    assert_source_lock_metadata_mismatch(&mismatched_gate);
}

#[test]
fn release_bundle_gate_metadata_mismatch_is_non_installable() {
    for (gate, label) in [
        {
            let mut gate = base_bundle().install_gate.expect("base gate");
            gate.packet.artifact.manifest_checksum = ArtifactChecksum::new(0x9999);
            (gate, "manifest checksum")
        },
        {
            let mut gate = base_bundle().install_gate.expect("base gate");
            gate.packet.validation.proof_report_sha256 = Some("sha256:missing-proof".to_owned());
            (gate, "proof/tv checksum")
        },
        {
            let mut gate = base_bundle().install_gate.expect("base gate");
            gate.telemetry_sha256 = "sha256:other-telemetry".to_owned();
            (gate, "telemetry checksum")
        },
    ] {
        let mut bundle = base_bundle();
        bundle.install_gate = Some(gate);

        assert_non_installable_decision(
            &bundle,
            ReleaseBundleInstallCode::GateMetadataMismatch,
            "gate_metadata_mismatch",
        );
        assert!(
            !bundle.to_pretty_json().contains("\"installable\": true"),
            "{label}"
        );
    }
}

#[test]
fn release_bundle_rejected_gate_metadata_is_non_installable() {
    let mut bundle = base_bundle();
    let mut gate = bundle.install_gate.clone().expect("base gate");
    gate.packet.disposition = NativeInstallGateDisposition::Rejected;
    gate.packet.rejection_code = Some(NativeInstallGateRejectionCode::StaleInvalidation);
    gate.packet.actions = NativeInstallGateActions::none();
    bundle.install_gate = Some(gate);

    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::GateRejected,
        "gate_rejected",
    );
    assert_install_decision_json(&bundle, "non_installable", "gate_rejected", false);
}

#[test]
fn release_bundle_revalidates_gate_packet_freshness() {
    let mut bundle = base_bundle();
    let mut gate = bundle.install_gate.clone().expect("base gate");
    gate.packet.freshness.current_generation += 1;
    persist_native_install_gate_packet_bindings(&mut gate.packet);
    bundle.install_gate = Some(gate);

    assert_non_installable_decision(
        &bundle,
        ReleaseBundleInstallCode::GateStaleInvalidation,
        "gate_stale_invalidation",
    );
    assert_install_decision_json(&bundle, "non_installable", "gate_stale_invalidation", false);
}

#[test]
fn release_bundle_restore_revalidates_live_current_with_typed_gate_codes() {
    let bundle = base_bundle();
    let packet = &bundle.install_gate.as_ref().expect("base gate").packet;

    let mut stale = NativeInstallGateRevalidationInput::from_packet(packet);
    stale.current_generation += 1;
    let stale_decision = bundle.install_decision_with_gate_current(&stale);
    assert!(!stale_decision.is_installable());
    assert_eq!(
        stale_decision.status,
        ReleaseBundleInstallStatus::NonInstallable
    );
    assert_eq!(
        stale_decision.code,
        ReleaseBundleInstallCode::GateStaleInvalidation
    );
    assert_eq!(stale_decision.code.as_str(), "gate_stale_invalidation");

    let mut revoked = NativeInstallGateRevalidationInput::from_packet(packet);
    revoked.revoked = true;
    let revoked_decision = bundle.install_decision_with_gate_current(&revoked);
    assert!(!revoked_decision.is_installable());
    assert_eq!(
        revoked_decision.status,
        ReleaseBundleInstallStatus::NonInstallable
    );
    assert_eq!(revoked_decision.code, ReleaseBundleInstallCode::GateRevoked);
    assert_eq!(revoked_decision.code.as_str(), "gate_revoked");

    let mut denied = NativeInstallGateRevalidationInput::from_packet(packet);
    denied.deny_control = Some(
        NativeInstallGateDenyControlPlane::active(
            NativeInstallGateDenyScope::Global,
            NativeInstallGateDenyReason::KillSwitch,
        )
        .with_canonical_deny_sha256(),
    );
    let denied_decision = bundle.install_decision_with_gate_current(&denied);
    assert!(!denied_decision.is_installable());
    assert_eq!(
        denied_decision.status,
        ReleaseBundleInstallStatus::NonInstallable
    );
    assert_eq!(
        denied_decision.code,
        ReleaseBundleInstallCode::GateKillSwitch
    );
    assert_eq!(denied_decision.code.as_str(), "gate_kill_switch");
}

#[test]
fn release_bundle_missing_artifact_manifest_metadata_serializes_non_installable_decision() {
    for (mut manifest, label) in [
        (
            ReleaseArtifactManifestReference::new(
                "",
                "sha256:artifact-json",
                1,
                ArtifactChecksum::new(0x1234),
            ),
            "missing path",
        ),
        (
            ReleaseArtifactManifestReference::new(
                "artifact.manifest.json",
                "",
                1,
                ArtifactChecksum::new(0x1234),
            ),
            "missing sha256",
        ),
        (
            ReleaseArtifactManifestReference::new(
                "artifact.manifest.json",
                "sha256:artifact-json",
                0,
                ArtifactChecksum::new(0x1234),
            ),
            "missing schema version",
        ),
    ] {
        let mut bundle = base_bundle();
        std::mem::swap(&mut bundle.artifact_manifest, &mut manifest);

        assert_non_installable_decision(
            &bundle,
            ReleaseBundleInstallCode::MissingReplayMetadata,
            "missing_replay_metadata",
        );
        assert_install_decision_json(&bundle, "non_installable", "missing_replay_metadata", false);
        assert!(
            !bundle.to_pretty_json().contains("\"installable\": true"),
            "{label}"
        );
    }
}

#[test]
fn release_bundle_missing_proof_file_binding_serializes_non_installable_decision() {
    for (path, sha256, label) in [
        ("", "sha256:proof-missing-path", "missing path"),
        ("proofs/proof-missing-sha.json", "", "missing sha256"),
    ] {
        let bundle =
            base_bundle().with_proof_reports([proof(path, sha256).with_verdict("accepted")]);

        assert_missing_proof_report_metadata(&bundle);
        assert!(
            !bundle.to_pretty_json().contains("\"installable\": true"),
            "{label}"
        );
    }
}

#[test]
fn release_bundle_accepted_proof_missing_policy_is_non_installable() {
    let mut bundle = base_bundle().with_proof_reports([proof(
        "proofs/proof-missing-policy.json",
        "sha256:proof-missing-policy",
    )]);
    bundle.proof_reports[0].policy = None;

    assert_missing_proof_report_metadata(&bundle);
}

#[test]
fn release_bundle_accepted_proof_missing_solver_is_non_installable() {
    let mut bundle = base_bundle().with_proof_reports([proof(
        "proofs/proof-missing-solver.json",
        "sha256:proof-missing-solver",
    )]);
    bundle.proof_reports[0].solver = None;

    assert_missing_proof_report_metadata(&bundle);
}

#[test]
fn release_bundle_accepted_proof_missing_obligation_set_is_non_installable() {
    let mut bundle = base_bundle().with_proof_reports([proof(
        "proofs/proof-missing-obligation-set.json",
        "sha256:proof-missing-obligation-set",
    )]);
    bundle.proof_reports[0].obligation_set = None;

    assert_missing_proof_report_metadata(&bundle);
}

#[test]
fn release_bundle_accepted_proof_missing_timeout_ms_is_non_installable() {
    let mut bundle = base_bundle().with_proof_reports([proof(
        "proofs/proof-missing-timeout-ms.json",
        "sha256:proof-missing-timeout-ms",
    )]);
    bundle.proof_reports[0].timeout_ms = None;

    assert_missing_proof_report_metadata(&bundle);
}

#[test]
fn release_bundle_timeout_or_rejected_proofs_are_replay_only() {
    for (verdict, code, code_str) in [
        (
            "proof_timeout",
            ReleaseBundleInstallCode::ProofTimeout,
            "proof_timeout",
        ),
        (
            "rejected",
            ReleaseBundleInstallCode::ProofRejected,
            "proof_rejected",
        ),
    ] {
        let bundle = base_bundle().with_proof_reports([proof(
            "proofs/proof-timeout-or-rejected.json",
            "sha256:proof-timeout-or-rejected",
        )
        .with_verdict(verdict)]);

        let decision = bundle.install_decision();

        assert!(!decision.is_installable());
        assert_eq!(decision.status, ReleaseBundleInstallStatus::ReplayOnly);
        assert_eq!(decision.status.as_str(), "replay_only");
        assert_eq!(decision.code, code);
        assert_eq!(decision.code.as_str(), code_str);
        assert_install_decision_json(&bundle, "replay_only", code_str, false);
    }
}
