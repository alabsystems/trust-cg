use trust_cg_codegen::async_compile_service::{
    ASYNC_COMPILE_TELEMETRY_SCHEMA, AsyncCacheLookupOutcome, AsyncCompileService,
    AsyncCompileServiceConfig, AsyncCompileState, AsyncCompileTelemetryEvent,
    AsyncInstallGateBlockerCode, AsyncSubmitRejectCode,
};
use trust_cg_codegen::compile_service::ArtifactInstallDisposition;
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, ArtifactChecksum, ArtifactManifestV1, Endianness, InvalidationKey,
    JitArtifactKind, LayoutManifest, ProofPolicy,
};
use trust_cg_codegen::jit_install_gate::{
    NATIVE_INSTALL_GATE_PACKET_SCHEMA, NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_REPLAY_SCHEMA, NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
    NativeInstallGateActions, NativeInstallGateArtifactPacket, NativeInstallGateAuthority,
    NativeInstallGateConsumerVerdictBinding, NativeInstallGateDisposition,
    NativeInstallGateFreshnessObservation, NativeInstallGateFreshnessPacket,
    NativeInstallGatePacket, NativeInstallGateRejectionCode, NativeInstallGateReplayBinding,
    NativeInstallGateReplayIdentity, NativeInstallGateSurface, NativeInstallGateTelemetryPacket,
    NativeInstallGateValidationPacket, persist_native_install_gate_packet_bindings,
};
use trust_cg_codegen::target::{Target, TargetSpec};
use trust_cg_codegen::{
    CancellationToken, CompileDiagnostic, CompileGeneration, CompileGenerationFence,
    CompileRequest, CompileRequestId, CompiledArtifact, InstallIntent,
};

const ASYNC_PROOF_TV_CHECKSUM: &str = "sha256:async-proof";
const ASYNC_TELEMETRY_CHECKSUM: &str = "sha256:async-telemetry";

fn ay_freshness_domains(generation: u64) -> Vec<NativeInstallGateFreshnessObservation> {
    [
        "shared_artifact",
        "shared_proof_policy",
        "shared_target_abi",
        "shared_release_bundle",
        "shared_revocation",
        "shared_kill_switch",
        "ay_solver",
        "ay_sparse",
        "ay_basis",
        "ay_watch_list",
        "ay_proof_witness",
        "ay_rollback",
        "ay_registry",
    ]
    .into_iter()
    .map(|domain| NativeInstallGateFreshnessObservation::new(domain, generation, generation))
    .collect()
}

fn request(id: &str, generation: u64) -> CompileRequest {
    CompileRequest::new(id, CompileGeneration::new(generation))
}

fn artifact(generation: CompileGeneration) -> CompiledArtifact {
    CompiledArtifact::metadata_only("async-test-artifact", generation)
}

fn rejected_artifact(generation: CompileGeneration) -> CompiledArtifact {
    let mut artifact = artifact(generation);
    artifact.install.disposition = ArtifactInstallDisposition::Rejected;
    artifact
}

fn deterministic_manifest(artifact_id: &str, generation: u64) -> ArtifactManifestV1 {
    // `CompileRequest::new` selects HostJitFast. Keep every positive fixture
    // on the exact target/ABI/core-layout contract derived by that compiler;
    // caller-authored compatibility descriptors are intentionally not
    // authoritative after manifest preflight hardening.
    let architecture = Target::host();
    let target = trust_cg_codegen::jit_contract::TargetDescriptor::for_trust_cg_target_spec(
        TargetSpec::default_for_architecture(architecture),
    );
    let abi = AbiDescriptor::for_trust_cg_target_os(architecture, target.operating_system.clone());
    let layout = LayoutManifest::lp64(Endianness::Little, architecture.stack_alignment() as u16);
    let proof_policy = ProofPolicy::disabled();
    let invalidation = InvalidationKey::new(
        "sha256:async-test-module",
        "trust-cg-codegen:async-test",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        generation,
    );

    ArtifactManifestV1::new(
        artifact_id,
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    )
}

fn artifact_with_manifest(
    generation: CompileGeneration,
    manifest: ArtifactManifestV1,
) -> CompiledArtifact {
    artifact(generation).with_artifact_manifest(manifest)
}

fn artifact_with_manifest_and_gate(
    generation: CompileGeneration,
    manifest: ArtifactManifestV1,
    native_install_gate: NativeInstallGatePacket,
) -> CompiledArtifact {
    let mut artifact = artifact_with_manifest(generation, manifest);
    artifact.install.native_install_gate = Some(native_install_gate);
    artifact
}

fn manifest_cache_key(manifest: &ArtifactManifestV1) -> String {
    format!(
        "{}:{}:{}:{}",
        manifest.schema,
        manifest.schema_version,
        manifest.artifact_id,
        manifest.checksum()
    )
}

fn gate_packet(
    manifest: &ArtifactManifestV1,
    surface: NativeInstallGateSurface,
    disposition: NativeInstallGateDisposition,
    rejection_code: Option<NativeInstallGateRejectionCode>,
) -> NativeInstallGatePacket {
    let actions = if disposition.is_installable() && rejection_code.is_none() {
        NativeInstallGateActions::for_surface(surface)
    } else {
        NativeInstallGateActions::none()
    };
    let install_authority = if disposition.is_installable() {
        NativeInstallGateAuthority::CanaryCallable
    } else {
        NativeInstallGateAuthority::None
    };
    let mut packet = NativeInstallGatePacket {
        schema: NATIVE_INSTALL_GATE_PACKET_SCHEMA,
        schema_version: NATIVE_INSTALL_GATE_PACKET_SCHEMA_VERSION,
        gate_issue: 681,
        design_issue: 682,
        consumer: "ay".to_owned(),
        consumer_mode: "async-test".to_owned(),
        surface,
        artifact: NativeInstallGateArtifactPacket {
            artifact_id: manifest.artifact_id.clone(),
            manifest_schema: manifest.schema.clone(),
            manifest_schema_version: manifest.schema_version,
            manifest_checksum: manifest.checksum(),
            source_sha256: "sha256:async-source".to_owned(),
            trust_ir_sha256: "sha256:async-trust_ir".to_owned(),
            native_payload_sha256: "sha256:async-native".to_owned(),
            target_checksum: manifest.target.checksum(),
            abi_checksum: manifest.abi.checksum(),
            layout_checksum: manifest.layout.checksum(),
            proof_policy_checksum: manifest.proof_policy.checksum(),
            invalidation_checksum: manifest.invalidation.checksum(),
            manifest_metadata: manifest.metadata.clone(),
        },
        validation: NativeInstallGateValidationPacket {
            layout_status: "accepted",
            layout_evidence_sha256: Some("sha256:async-layout".to_owned()),
            layout_wrapper_identity: Some("async-wrapper.v1".to_owned()),
            layout_validation_provenance: Some("trust-cg.async.layout_adapter.v1".to_owned()),
            layout_invalidation_checksum: Some(manifest.invalidation.checksum()),
            layout_generation_domains: vec!["async_generation".to_owned()],
            proof_verdict: if disposition.is_installable() {
                "verified"
            } else {
                "stale_evidence"
            },
            proof_reject_code: rejection_code.map(NativeInstallGateRejectionCode::as_str),
            proof_verifier: Some("trust-cg-verify".to_owned()),
            proof_report_sha256: Some(ASYNC_PROOF_TV_CHECKSUM.to_owned()),
            obligation_set: Some("async-obligations".to_owned()),
            timeout_ms: Some(250),
        },
        freshness: NativeInstallGateFreshnessPacket {
            artifact_generation: manifest.invalidation.generation,
            current_generation: manifest.invalidation.generation,
            freshness_domains: ay_freshness_domains(manifest.invalidation.generation),
            revoked: false,
            deny_control: None,
        },
        replay_identity: Some(NativeInstallGateReplayIdentity {
            schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
            schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
            replay_root_sha256: "sha256:async-replay".to_owned(),
            replay_consumer: "ay".to_owned(),
            replay_family: "async-test".to_owned(),
            artifact_id: manifest.artifact_id.clone(),
            source_sha256: "sha256:async-source".to_owned(),
            trust_ir_sha256: "sha256:async-trust_ir".to_owned(),
            native_payload_sha256: "sha256:async-native".to_owned(),
            replay_record_sha256: String::new(),
        }),
        telemetry: Some(NativeInstallGateTelemetryPacket {
            schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
            schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
            event_id: ASYNC_TELEMETRY_CHECKSUM.to_owned(),
            counter_scope: String::new(),
            record_sha256: String::new(),
            artifact_id: manifest.artifact_id.clone(),
            manifest_checksum: manifest.checksum(),
            proof_report_sha256: Some(ASYNC_PROOF_TV_CHECKSUM.to_owned()),
            layout_checksum: manifest.layout.checksum(),
            invalidation_checksum: manifest.invalidation.checksum(),
            disposition,
            rejection_code,
            install_authority,
            useful_native_delta: 0,
        }),
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        disposition,
        rejection_code,
        install_authority,
        packet_hash: ArtifactChecksum::new(0),
        replay_binding: NativeInstallGateReplayBinding {
            packet_hash: ArtifactChecksum::new(0),
            replay_root_sha256: String::new(),
        },
        consumer_verdict: NativeInstallGateConsumerVerdictBinding {
            consumer: String::new(),
            consumer_mode: String::new(),
            surface,
            verdict_id: String::new(),
            verdict_sha256: String::new(),
        },
        actions,
    };
    persist_native_install_gate_packet_bindings(&mut packet);
    packet
}

fn telemetry_event_count(
    service: &AsyncCompileService,
    event: AsyncCompileTelemetryEvent,
) -> usize {
    service
        .telemetry_packets()
        .iter()
        .filter(|packet| packet.event == event)
        .count()
}

fn telemetry_packet_for_request<'a>(
    service: &'a AsyncCompileService,
    event: AsyncCompileTelemetryEvent,
    request_id: &CompileRequestId,
) -> &'a trust_cg_codegen::async_compile_service::AsyncCompileTelemetryPacket {
    service
        .telemetry_packets()
        .iter()
        .find(|packet| packet.event == event && packet.request_id == request_id.as_str())
        .expect("telemetry packet for request")
}

fn record_accepted_cache_insert(service: &mut AsyncCompileService, manifest: &ArtifactManifestV1) {
    service.record_manifest_cache_insert_gate_entry_with_identity(
        manifest,
        AsyncCacheLookupOutcome::HitInstallable,
        gate_packet(
            manifest,
            NativeInstallGateSurface::CacheInsert,
            NativeInstallGateDisposition::Installable,
            None,
        ),
        Some(ASYNC_PROOF_TV_CHECKSUM.to_owned()),
        Some(ASYNC_TELEMETRY_CHECKSUM.to_owned()),
    );
}

fn assert_metadata_only_telemetry(service: &AsyncCompileService) {
    assert_eq!(service.telemetry_summary().useful_native, 0);
    assert!(
        service
            .telemetry_packets()
            .iter()
            .all(|packet| !packet.useful_native_eligible)
    );
}

#[test]
fn telemetry_event_codes_are_stable_lower_snake_case() {
    let events = [
        (AsyncCompileTelemetryEvent::Submit, "submit"),
        (
            AsyncCompileTelemetryEvent::ImmediateReject,
            "immediate_reject",
        ),
        (AsyncCompileTelemetryEvent::Queued, "queued"),
        (AsyncCompileTelemetryEvent::Running, "running"),
        (AsyncCompileTelemetryEvent::Cancel, "cancel"),
        (AsyncCompileTelemetryEvent::StaleDrop, "stale_drop"),
        (AsyncCompileTelemetryEvent::Finish, "finish"),
        (AsyncCompileTelemetryEvent::Poll, "poll"),
        (AsyncCompileTelemetryEvent::ExplainReject, "explain_reject"),
        (AsyncCompileTelemetryEvent::Failed, "failed"),
        (AsyncCompileTelemetryEvent::ProfileOnly, "profile_only"),
        (
            AsyncCompileTelemetryEvent::CompiledResponse,
            "compiled_response",
        ),
    ];

    for (event, code) in events {
        assert_eq!(event.as_str(), code);
    }
}

#[test]
fn cache_lookup_outcome_codes_are_stable_lower_snake_case() {
    let outcomes = [
        (AsyncCacheLookupOutcome::HitInstallable, "hit_installable"),
        (AsyncCacheLookupOutcome::HitReplayOnly, "hit_replay_only"),
        (AsyncCacheLookupOutcome::Miss, "miss"),
        (AsyncCacheLookupOutcome::Stale, "stale"),
        (AsyncCacheLookupOutcome::Corrupt, "corrupt"),
        (AsyncCacheLookupOutcome::SchemaMismatch, "schema_mismatch"),
        (
            AsyncCacheLookupOutcome::UnsupportedRequiredFeature,
            "unsupported_required_feature",
        ),
        (
            AsyncCacheLookupOutcome::GateMetadataMissing,
            "gate_metadata_missing",
        ),
        (
            AsyncCacheLookupOutcome::GateMetadataMismatch,
            "gate_metadata_mismatch",
        ),
        (AsyncCacheLookupOutcome::GateRejected, "gate_rejected"),
    ];

    for (outcome, code) in outcomes {
        assert_eq!(outcome.as_str(), code);
    }
}

#[test]
fn submit_poll_start_and_finish_installable() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-installable-artifact", 1);
    let request = request("async-installable", 1).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();
    async_service.record_native_install_gate_packet(
        request_id.clone(),
        gate_packet(
            &manifest,
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::Installable,
            None,
        ),
    );

    let accepted = async_service.submit(request).expect("submit accepted");
    assert_eq!(accepted.state, AsyncCompileState::Queued);
    assert_eq!(
        async_service.poll(&request_id).state,
        AsyncCompileState::Queued
    );

    let ticket = async_service.start_next().expect("worker ticket");
    assert_eq!(
        async_service.poll(&request_id).state,
        AsyncCompileState::Running
    );

    let generation = ticket.generation;
    let response = async_service
        .service()
        .compile_with(ticket.request.clone(), || {
            Ok(artifact_with_manifest(generation, manifest))
        });
    let poll = async_service.finish(ticket, response);

    assert_eq!(poll.state, AsyncCompileState::CompiledInstallable);
    assert!(poll.is_installable());
    assert!(poll.response.expect("response").explain_reject().is_none());
    assert_eq!(
        telemetry_event_count(&async_service, AsyncCompileTelemetryEvent::CompiledResponse),
        1
    );
    assert_eq!(async_service.telemetry_summary().compiled, 1);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn installable_response_without_async_gate_metadata_fails_closed() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-missing-gate-artifact", 30);
    let request = request("async-missing-gate", 30).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();

    async_service.submit(request).expect("submit accepted");
    let poll = async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || Ok(artifact_with_manifest(generation, manifest)))
        })
        .expect("worker result");

    assert_eq!(poll.state, AsyncCompileState::Rejected);
    assert!(!poll.is_installable());
    let response = poll.response.expect("blocked response");
    assert_eq!(response.disposition, ArtifactInstallDisposition::Rejected);
    assert_eq!(
        response
            .artifact
            .as_ref()
            .expect("artifact")
            .install
            .disposition,
        ArtifactInstallDisposition::Rejected
    );
    assert_eq!(
        response.diagnostics.last().expect("gate diagnostic").code,
        "async.native_install_gate_missing_metadata"
    );
    let packet = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Finish,
        &request_id,
    );
    assert_eq!(
        packet.native_install_gate_blocker,
        Some(AsyncInstallGateBlockerCode::MissingGateMetadata)
    );
    assert_eq!(
        async_service.poll(&request_id).state,
        AsyncCompileState::Rejected
    );
    assert_eq!(async_service.telemetry_summary().reject, 1);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn installable_response_rejected_or_mismatched_async_gate_metadata_fails_closed() {
    for (label, manifest, gate, blocker, diagnostic_code) in {
        let manifest = deterministic_manifest("async-invalid-gate-artifact", 31);
        let rejected_gate = gate_packet(
            &manifest,
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::Rejected,
            Some(NativeInstallGateRejectionCode::ProofVerifierFailure),
        );
        let mismatched_gate = gate_packet(
            &deterministic_manifest("async-other-gate-artifact", 31),
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::Installable,
            None,
        );
        [
            (
                "rejected",
                manifest.clone(),
                rejected_gate,
                AsyncInstallGateBlockerCode::GateRejected,
                "async.native_install_gate_rejected",
            ),
            (
                "mismatched",
                manifest,
                mismatched_gate,
                AsyncInstallGateBlockerCode::GateMetadataMismatch,
                "async.native_install_gate_metadata_mismatch",
            ),
        ]
    } {
        let mut async_service = AsyncCompileService::default();
        let request =
            request(&format!("async-{label}-gate"), 31).with_artifact_manifest(manifest.clone());
        let request_id = request.request_id.clone();
        async_service.record_native_install_gate_packet(request_id.clone(), gate);

        async_service.submit(request).expect("submit accepted");
        let poll = async_service
            .run_next_with(|service, request| {
                let generation = request.generation;
                service.compile_with(request, || Ok(artifact_with_manifest(generation, manifest)))
            })
            .expect("worker result");

        assert_eq!(poll.state, AsyncCompileState::Rejected, "{label}");
        assert!(!poll.is_installable(), "{label}");
        let response = poll.response.expect("blocked response");
        assert_eq!(
            response.diagnostics.last().expect("gate diagnostic").code,
            diagnostic_code,
            "{label}"
        );
        let packet = telemetry_packet_for_request(
            &async_service,
            AsyncCompileTelemetryEvent::Finish,
            &request_id,
        );
        assert_eq!(packet.native_install_gate_blocker, Some(blocker), "{label}");
        assert_metadata_only_telemetry(&async_service);
    }
}

#[test]
fn async_finish_extracts_response_native_install_gate_packet() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-response-derived-gate", 32);
    let response_gate = gate_packet(
        &manifest,
        NativeInstallGateSurface::AsyncPoll,
        NativeInstallGateDisposition::Installable,
        None,
    );
    let request = request("async-response-gate", 32).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();

    async_service.submit(request).expect("submit accepted");
    let poll = async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || {
                Ok(artifact_with_manifest_and_gate(
                    generation,
                    manifest,
                    response_gate,
                ))
            })
        })
        .expect("worker result");

    assert_eq!(poll.state, AsyncCompileState::CompiledInstallable);
    assert!(poll.is_installable());
    let packet = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::CompiledResponse,
        &request_id,
    );
    assert_eq!(
        packet
            .native_install_gate
            .as_ref()
            .expect("response-derived gate")
            .surface,
        NativeInstallGateSurface::AsyncPoll
    );
    assert_eq!(packet.native_install_gate_blocker, None);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn async_finish_response_gate_overrides_seeded_accepted_packet() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-response-rejected-gate", 33);
    let seeded_gate = gate_packet(
        &manifest,
        NativeInstallGateSurface::AsyncPoll,
        NativeInstallGateDisposition::Installable,
        None,
    );
    let response_gate = gate_packet(
        &manifest,
        NativeInstallGateSurface::AsyncPoll,
        NativeInstallGateDisposition::Rejected,
        Some(NativeInstallGateRejectionCode::ProofVerifierFailure),
    );
    let request =
        request("async-response-gate-precedence", 33).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();
    async_service.record_native_install_gate_packet(request_id.clone(), seeded_gate);

    async_service.submit(request).expect("submit accepted");
    let poll = async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || {
                Ok(artifact_with_manifest_and_gate(
                    generation,
                    manifest,
                    response_gate,
                ))
            })
        })
        .expect("worker result");

    assert_eq!(poll.state, AsyncCompileState::Rejected);
    assert!(!poll.is_installable());
    let response = poll.response.expect("blocked response");
    assert_eq!(
        response.diagnostics.last().expect("gate diagnostic").code,
        "async.native_install_gate_rejected"
    );
    let packet = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Finish,
        &request_id,
    );
    assert_eq!(
        packet
            .native_install_gate
            .as_ref()
            .expect("response gate")
            .rejection_code,
        Some(NativeInstallGateRejectionCode::ProofVerifierFailure)
    );
    assert_eq!(
        packet.native_install_gate_blocker,
        Some(AsyncInstallGateBlockerCode::GateRejected)
    );
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn profile_only_response_polls_non_installable() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-profile-only-artifact", 2);
    let mut request = request("async-profile-only", 2).with_artifact_manifest(manifest.clone());
    request.install_intent = InstallIntent::CompileOnly;
    let request_id = request.request_id.clone();
    async_service.record_native_install_gate_packet(
        request_id.clone(),
        gate_packet(
            &manifest,
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::ProfileOnly,
            Some(NativeInstallGateRejectionCode::ProfileOnlyNonInstallable),
        ),
    );

    async_service.submit(request).expect("submit accepted");
    let poll = async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || Ok(artifact_with_manifest(generation, manifest)))
        })
        .expect("worker result");

    assert_eq!(poll.request_id, request_id);
    assert_eq!(poll.state, AsyncCompileState::ProfileOnly);
    assert!(!poll.is_installable());
    assert_eq!(
        poll.response
            .as_ref()
            .expect("response")
            .artifact
            .as_ref()
            .expect("artifact")
            .install
            .disposition,
        ArtifactInstallDisposition::ProfileOnly
    );
    assert_eq!(
        telemetry_event_count(&async_service, AsyncCompileTelemetryEvent::ProfileOnly),
        1
    );
    assert_eq!(async_service.telemetry_summary().profile_only, 1);
    let packet = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::ProfileOnly,
        &request_id,
    );
    assert_eq!(
        packet
            .native_install_gate
            .as_ref()
            .expect("profile gate")
            .disposition,
        NativeInstallGateDisposition::ProfileOnly
    );
    assert_eq!(packet.native_install_gate_blocker, None);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn immediate_submit_rejections_use_stable_codes() {
    let mut queue_full = AsyncCompileService::with_default_service(AsyncCompileServiceConfig {
        max_queued: 0,
        ..AsyncCompileServiceConfig::default()
    });
    let reject = queue_full
        .submit(request("queue-full", 1))
        .expect_err("queue full");
    assert_eq!(reject.code, AsyncSubmitRejectCode::QueueFull);
    assert_eq!(reject.code.as_str(), "queue_full");
    assert_eq!(reject.state, AsyncCompileState::Rejected);
    let packet = queue_full
        .telemetry_packets()
        .iter()
        .find(|packet| packet.event == AsyncCompileTelemetryEvent::ImmediateReject)
        .expect("queue-full telemetry packet");
    assert_eq!(packet.schema, ASYNC_COMPILE_TELEMETRY_SCHEMA);
    assert_eq!(packet.reason_code.as_deref(), Some("queue_full"));
    assert_eq!(packet.install_disposition.as_deref(), Some("rejected"));
    assert_eq!(queue_full.telemetry_summary().submit, 1);
    assert_eq!(queue_full.telemetry_summary().reject, 1);
    assert_metadata_only_telemetry(&queue_full);

    let mut budget_exceeded =
        AsyncCompileService::with_default_service(AsyncCompileServiceConfig {
            max_total_submitted: Some(0),
            ..AsyncCompileServiceConfig::default()
        });
    let reject = budget_exceeded
        .submit(request("budget-exceeded", 1))
        .expect_err("budget exceeded");
    assert_eq!(reject.code, AsyncSubmitRejectCode::BudgetExceeded);
    assert_eq!(reject.code.as_str(), "budget_exceeded");

    let mut stale = AsyncCompileService::default();
    let mut stale_request = request("stale-submit", 1);
    stale_request.stale_before = Some(CompileGeneration::new(2));
    let reject = stale.submit(stale_request).expect_err("stale");
    assert_eq!(reject.code, AsyncSubmitRejectCode::StaleGeneration);
    assert_eq!(reject.code.as_str(), "stale_generation");
    assert_eq!(reject.state, AsyncCompileState::StaleGeneration);

    let mut cancelled = AsyncCompileService::default();
    let mut cancelled_request = request("cancelled-submit", 1);
    cancelled_request.cancellation = CancellationToken::cancelled();
    let reject = cancelled.submit(cancelled_request).expect_err("cancelled");
    assert_eq!(reject.code, AsyncSubmitRejectCode::Cancelled);
    assert_eq!(reject.code.as_str(), "cancelled");
    assert_eq!(reject.state, AsyncCompileState::Cancelled);
    assert_metadata_only_telemetry(&cancelled);
}

#[test]
fn cancelled_queued_work_never_starts_backend_compilation() {
    let mut async_service = AsyncCompileService::default();
    let request = request("cancel-queued", 3);
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    let poll = async_service.cancel(&request_id);
    assert_eq!(poll.state, AsyncCompileState::Cancelled);
    assert!(
        async_service
            .run_next_with(|_, _| panic!("must not compile"))
            .is_none()
    );

    let reject = async_service
        .explain_reject(&request_id)
        .expect("cancel explanation");
    assert_eq!(reject.code.as_str(), "cancelled");
    assert_eq!(
        telemetry_event_count(&async_service, AsyncCompileTelemetryEvent::Cancel),
        1
    );
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn cancelled_before_start_telemetry_includes_terminal_join_fields() {
    let cancellation = CancellationToken::new();
    let mut async_service = AsyncCompileService::default();
    let mut request = request("cancel-before-start", 13);
    request.cancellation = cancellation.clone();
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    cancellation.cancel();
    assert!(async_service.start_next().is_none());

    let poll = async_service.poll(&request_id);
    assert_eq!(poll.state, AsyncCompileState::Cancelled);
    assert_eq!(
        poll.response.expect("terminal response").disposition,
        ArtifactInstallDisposition::Rejected
    );

    let packet = async_service
        .telemetry_packets()
        .iter()
        .find(|packet| {
            packet.event == AsyncCompileTelemetryEvent::Cancel
                && packet.request_id == request_id.as_str()
        })
        .expect("cancel-before-start telemetry packet");
    assert_eq!(packet.request_provenance, request_id.as_str());
    assert_eq!(packet.generation, Some(13));
    assert_eq!(packet.async_state, AsyncCompileState::Cancelled);
    assert_eq!(packet.reason_code.as_deref(), Some("cancelled"));
    assert_eq!(packet.install_disposition.as_deref(), Some("rejected"));
    assert!(packet.artifact_ref.is_none());
    assert!(packet.manifest_ref.is_none());
    assert!(packet.proof_ref.is_none());
    assert!(!packet.useful_native_eligible);
}

#[test]
fn cancelled_running_work_cannot_publish_installable_response() {
    let mut async_service = AsyncCompileService::default();
    let request = request("cancel-running", 4);
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    let ticket = async_service.start_next().expect("worker ticket");
    let cancelled = async_service.cancel(&request_id);
    assert_eq!(cancelled.state, AsyncCompileState::Cancelled);

    let generation = ticket.generation;
    let response = async_service
        .service()
        .compile_with(ticket.request.clone(), || Ok(artifact(generation)));
    let poll = async_service.finish(ticket, response);

    assert_eq!(poll.state, AsyncCompileState::Cancelled);
    assert!(!poll.is_installable());
    assert!(poll.response.expect("response").artifact.is_none());
    assert_eq!(
        telemetry_event_count(&async_service, AsyncCompileTelemetryEvent::Cancel),
        1
    );
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn stale_before_start_telemetry_includes_terminal_join_fields() {
    let fence = CompileGenerationFence::new();
    let mut async_service = AsyncCompileService::default();
    let mut request = request("stale-before-start", 14);
    request.generation_fence = Some(fence.clone());
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    fence.mark_stale_before(CompileGeneration::new(15));
    assert!(async_service.start_next().is_none());

    let poll = async_service.poll(&request_id);
    assert_eq!(poll.state, AsyncCompileState::StaleGeneration);
    assert_eq!(
        poll.response.expect("terminal response").disposition,
        ArtifactInstallDisposition::Rejected
    );

    let packet = async_service
        .telemetry_packets()
        .iter()
        .find(|packet| {
            packet.event == AsyncCompileTelemetryEvent::StaleDrop
                && packet.request_id == request_id.as_str()
        })
        .expect("stale-before-start telemetry packet");
    assert_eq!(packet.request_provenance, request_id.as_str());
    assert_eq!(packet.generation, Some(14));
    assert_eq!(packet.async_state, AsyncCompileState::StaleGeneration);
    assert_eq!(packet.reason_code.as_deref(), Some("stale_generation"));
    assert_eq!(packet.install_disposition.as_deref(), Some("rejected"));
    assert!(packet.artifact_ref.is_none());
    assert!(packet.manifest_ref.is_none());
    assert!(packet.proof_ref.is_none());
    assert!(!packet.useful_native_eligible);
}

#[test]
fn stale_generation_running_work_cannot_publish_installable_response() {
    let fence = CompileGenerationFence::new();
    let mut async_service = AsyncCompileService::default();
    let mut request = request("stale-running", 10);
    request.generation_fence = Some(fence.clone());
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    let ticket = async_service.start_next().expect("worker ticket");
    fence.mark_stale_before(CompileGeneration::new(11));
    assert_eq!(
        async_service.poll(&request_id).state,
        AsyncCompileState::StaleGeneration
    );

    let generation = ticket.generation;
    let response = async_service
        .service()
        .compile_with(ticket.request.clone(), || Ok(artifact(generation)));
    let poll = async_service.finish(ticket, response);

    assert_eq!(poll.state, AsyncCompileState::StaleGeneration);
    assert!(!poll.is_installable());
    let reject = async_service
        .explain_reject(&request_id)
        .expect("stale explanation");
    assert_eq!(reject.code.as_str(), "stale_generation");
    assert_eq!(
        telemetry_event_count(&async_service, AsyncCompileTelemetryEvent::StaleDrop),
        1
    );
    assert_eq!(async_service.telemetry_summary().stale, 1);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn duplicate_and_unknown_poll_are_typed_non_installable_states() {
    let mut async_service = AsyncCompileService::default();
    let request = request("duplicate", 1);
    async_service
        .submit(request.clone())
        .expect("first submit accepted");
    let reject = async_service.submit(request).expect_err("duplicate");
    assert_eq!(reject.code, AsyncSubmitRejectCode::DuplicateRequest);
    assert_eq!(reject.state, AsyncCompileState::Rejected);

    let unknown = CompileRequestId::new("missing");
    let poll = async_service.poll(&unknown);
    assert_eq!(poll.state, AsyncCompileState::NotFound);
    assert!(!poll.is_installable());
}

#[test]
fn duplicate_submit_does_not_overwrite_retained_terminal_success() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-duplicate-terminal", 1);
    let request = request("duplicate-terminal", 1).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();
    async_service.record_native_install_gate_packet(
        request_id.clone(),
        gate_packet(
            &manifest,
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::Installable,
            None,
        ),
    );
    async_service
        .submit(request.clone())
        .expect("first submit accepted");
    let poll = async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || Ok(artifact_with_manifest(generation, manifest)))
        })
        .expect("worker result");
    assert_eq!(poll.state, AsyncCompileState::CompiledInstallable);

    let reject = async_service
        .submit(request)
        .expect_err("terminal duplicate rejected");
    assert_eq!(reject.code, AsyncSubmitRejectCode::DuplicateRequest);
    assert_eq!(
        async_service.poll(&request_id).state,
        AsyncCompileState::CompiledInstallable
    );
}

#[test]
fn compiled_rejected_response_has_async_explain_reject() {
    let mut async_service = AsyncCompileService::default();
    let request = request("compiled-rejected", 7);
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    let poll = async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || Ok(rejected_artifact(generation)))
        })
        .expect("worker result");
    assert_eq!(poll.state, AsyncCompileState::Rejected);
    assert!(!poll.is_installable());

    let reject = async_service
        .explain_reject(&request_id)
        .expect("compiled rejected explanation");
    assert_eq!(reject.code.as_str(), "rejected");
    assert_eq!(reject.diagnostic_code, "compile.rejected");
    assert_eq!(async_service.telemetry_summary().reject, 1);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn failed_response_emits_failed_metadata_only_telemetry() {
    let mut async_service = AsyncCompileService::default();
    async_service
        .submit(request("failed-telemetry", 8))
        .expect("submit accepted");

    let poll = async_service
        .run_next_with(|service, request| {
            service.compile_with(request, || {
                Err(CompileDiagnostic::new(
                    "async.test_failed",
                    "test backend failure",
                ))
            })
        })
        .expect("worker result");

    assert_eq!(poll.state, AsyncCompileState::Failed);
    assert_eq!(
        telemetry_event_count(&async_service, AsyncCompileTelemetryEvent::Failed),
        1
    );
    assert_eq!(async_service.telemetry_summary().failed, 1);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn telemetry_json_is_deterministic_and_carries_join_keys() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-manifest-telemetry", 9);
    let expected_manifest_ref = format!(
        "{}:{}:{}:{}",
        manifest.schema,
        manifest.schema_version,
        manifest.artifact_id,
        manifest.checksum()
    );
    let expected_proof_ref = manifest.proof_policy.checksum().to_string();
    let request = request("json-telemetry", 9).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();
    async_service.record_native_install_gate_packet(
        request_id.clone(),
        gate_packet(
            &manifest,
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::Installable,
            None,
        ),
    );
    async_service.submit(request).expect("submit accepted");
    async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || Ok(artifact_with_manifest(generation, manifest)))
        })
        .expect("worker result");

    let packet = async_service
        .telemetry_packets()
        .iter()
        .find(|packet| packet.event == AsyncCompileTelemetryEvent::CompiledResponse)
        .expect("compiled response packet");
    let json = packet.to_json_value();

    assert_eq!(json["schema"], ASYNC_COMPILE_TELEMETRY_SCHEMA);
    assert_eq!(json["request_id"], request_id.as_str());
    assert_eq!(json["request_provenance"], request_id.as_str());
    assert_eq!(json["generation"], 9);
    assert_eq!(json["artifact_ref"], "async-test-artifact");
    assert_eq!(json["manifest_ref"], expected_manifest_ref);
    assert_eq!(json["proof_ref"], expected_proof_ref);
    assert!(json["release_ref"].is_null());
    assert_eq!(json["async_state"], "compiled_installable");
    assert_eq!(json["reason_code"], "compiled");
    assert_eq!(json["install_disposition"], "installable");
    assert_eq!(
        json["issue_refs"],
        serde_json::json!(["#695", "#707", "#681", "#721"])
    );
    assert_eq!(
        json["native_install_gate"]["disposition"].as_str(),
        Some("installable")
    );
    assert_eq!(
        json["native_install_gate"]["validation"]["proof_tv_checksum"].as_str(),
        Some("sha256:async-proof")
    );
    assert_eq!(
        json["native_install_gate"]["artifact"]["source_sha256"].as_str(),
        Some("sha256:async-source")
    );
    assert_eq!(
        json["native_install_gate"]["artifact"]["trust_ir_sha256"].as_str(),
        Some("sha256:async-trust_ir")
    );
    assert_eq!(
        json["native_install_gate"]["artifact"]["native_payload_sha256"].as_str(),
        Some("sha256:async-native")
    );
    let freshness_domains = json["native_install_gate"]["freshness"]["freshness_domains"]
        .as_array()
        .expect("freshness domains are reported");
    assert!(
        freshness_domains
            .iter()
            .any(|domain| domain["domain"].as_str() == Some("shared_artifact"))
    );
    assert!(
        freshness_domains
            .iter()
            .any(|domain| domain["domain"].as_str() == Some("ay_solver"))
    );
    assert!(
        freshness_domains
            .iter()
            .all(|domain| domain["stale"].as_bool() == Some(false))
    );
    assert_eq!(
        json["native_install_gate"]["telemetry"]["counter_scope"].as_str(),
        Some("ay:async-test:async_poll:async-manifest-telemetry")
    );
    assert_eq!(
        json["native_install_gate"]["telemetry"]["useful_native_delta"].as_u64(),
        Some(0)
    );
    assert_eq!(
        json["native_install_gate"]["replay_identity"]["replay_root_sha256"].as_str(),
        Some("sha256:async-replay")
    );
    assert_eq!(
        json["native_install_gate"]["replay_binding"]["packet_hash"].as_str(),
        json["native_install_gate"]["packet_hash"].as_str()
    );
    assert_eq!(
        json["native_install_gate"]["actions"]["expose_callable"].as_bool(),
        Some(false)
    );
    assert_eq!(
        json["native_install_gate"]["actions"]["useful_native_eligible"].as_bool(),
        Some(true)
    );
    assert!(json["native_install_gate_blocker"].is_null());
    assert_eq!(json["useful_native_eligible"], false);
    assert_eq!(packet.to_json_string(), packet.to_json_string());
    assert_eq!(
        async_service.telemetry_summary().to_json_value()["useful_native"],
        0
    );
}

#[test]
fn async_submit_and_poll_record_manifest_cache_hit_outcome() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-cache-hit", 16);
    let cache_key = manifest_cache_key(&manifest);
    record_accepted_cache_insert(&mut async_service, &manifest);
    async_service.record_manifest_cache_gate_entry_with_identity(
        &manifest,
        AsyncCacheLookupOutcome::HitInstallable,
        gate_packet(
            &manifest,
            NativeInstallGateSurface::CacheHit,
            NativeInstallGateDisposition::Installable,
            None,
        ),
        Some(ASYNC_PROOF_TV_CHECKSUM.to_owned()),
        Some(ASYNC_TELEMETRY_CHECKSUM.to_owned()),
    );

    let request = request("cache-hit-request", 16).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    let submit = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Submit,
        &request_id,
    );
    assert_eq!(submit.cache_key.as_deref(), Some(cache_key.as_str()));
    assert_eq!(
        submit.cache_lookup_outcome,
        Some(AsyncCacheLookupOutcome::HitInstallable)
    );

    let poll = async_service.poll(&request_id);
    assert_eq!(poll.state, AsyncCompileState::Queued);
    assert!(!poll.is_installable());
    let poll_packet = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Poll,
        &request_id,
    );
    assert_eq!(poll_packet.cache_key.as_deref(), Some(cache_key.as_str()));
    assert_eq!(
        poll_packet.cache_lookup_outcome,
        Some(AsyncCacheLookupOutcome::HitInstallable)
    );
    assert_eq!(
        poll_packet
            .native_install_gate
            .as_ref()
            .expect("cache gate")
            .surface,
        NativeInstallGateSurface::CacheHit
    );
    assert_eq!(poll_packet.native_install_gate_blocker, None);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn async_manifest_cache_non_authorizing_outcomes_do_not_publish_installable_polls() {
    for (artifact_id, outcome) in [
        ("async-cache-stale", AsyncCacheLookupOutcome::Stale),
        ("async-cache-corrupt", AsyncCacheLookupOutcome::Corrupt),
        (
            "async-cache-replay-only",
            AsyncCacheLookupOutcome::HitReplayOnly,
        ),
        (
            "async-cache-schema-mismatch",
            AsyncCacheLookupOutcome::SchemaMismatch,
        ),
        (
            "async-cache-unsupported-feature",
            AsyncCacheLookupOutcome::UnsupportedRequiredFeature,
        ),
    ] {
        let mut async_service = AsyncCompileService::default();
        let manifest = deterministic_manifest(artifact_id, 17);
        let cache_key = manifest_cache_key(&manifest);
        async_service.record_manifest_cache_entry(&manifest, outcome);

        let request =
            request(&format!("{artifact_id}-request"), 17).with_artifact_manifest(manifest);
        let request_id = request.request_id.clone();
        async_service.submit(request).expect("submit accepted");
        let poll = async_service.poll(&request_id);

        assert_eq!(poll.state, AsyncCompileState::Queued);
        assert!(!poll.is_installable(), "{artifact_id} became installable");
        let packet = telemetry_packet_for_request(
            &async_service,
            AsyncCompileTelemetryEvent::Poll,
            &request_id,
        );
        assert_eq!(packet.cache_key.as_deref(), Some(cache_key.as_str()));
        assert_eq!(packet.cache_lookup_outcome, Some(outcome));
        assert_metadata_only_telemetry(&async_service);
    }
}

#[test]
fn async_manifest_cache_installable_hit_without_gate_metadata_fails_closed() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-cache-missing-gate", 26);
    async_service.record_manifest_cache_entry(&manifest, AsyncCacheLookupOutcome::HitInstallable);

    let request = request("cache-missing-gate-request", 26).with_artifact_manifest(manifest);
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    let packet = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Submit,
        &request_id,
    );
    assert_eq!(
        packet.cache_lookup_outcome,
        Some(AsyncCacheLookupOutcome::GateMetadataMissing)
    );
    assert_eq!(
        packet.native_install_gate_blocker,
        Some(AsyncInstallGateBlockerCode::MissingGateMetadata)
    );
    assert!(packet.native_install_gate.is_none());
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn async_manifest_cache_insert_revalidates_gate_metadata() {
    let manifest = deterministic_manifest("async-cache-insert-gate", 29);
    let accepted_hit_gate = gate_packet(
        &manifest,
        NativeInstallGateSurface::CacheHit,
        NativeInstallGateDisposition::Installable,
        None,
    );
    let rejected_insert_gate = gate_packet(
        &manifest,
        NativeInstallGateSurface::CacheInsert,
        NativeInstallGateDisposition::Rejected,
        Some(NativeInstallGateRejectionCode::StaleInvalidation),
    );
    let mismatched_insert_gate = gate_packet(
        &deterministic_manifest("async-cache-insert-other", 29),
        NativeInstallGateSurface::CacheInsert,
        NativeInstallGateDisposition::Installable,
        None,
    );

    for (label, insert_gate, outcome, blocker, rejection_code) in [
        (
            "rejected",
            Some(rejected_insert_gate),
            AsyncCacheLookupOutcome::GateRejected,
            AsyncInstallGateBlockerCode::GateRejected,
            Some(NativeInstallGateRejectionCode::StaleInvalidation),
        ),
        (
            "mismatched",
            Some(mismatched_insert_gate),
            AsyncCacheLookupOutcome::GateMetadataMismatch,
            AsyncInstallGateBlockerCode::GateMetadataMismatch,
            None,
        ),
        (
            "missing",
            None,
            AsyncCacheLookupOutcome::GateMetadataMissing,
            AsyncInstallGateBlockerCode::MissingGateMetadata,
            None,
        ),
    ] {
        let mut async_service = AsyncCompileService::default();
        if let Some(insert_gate) = insert_gate {
            async_service.record_manifest_cache_insert_gate_entry(
                &manifest,
                AsyncCacheLookupOutcome::HitInstallable,
                insert_gate,
            );
        } else {
            async_service
                .record_manifest_cache_entry(&manifest, AsyncCacheLookupOutcome::HitInstallable);
        }
        async_service.record_manifest_cache_gate_entry_with_identity(
            &manifest,
            AsyncCacheLookupOutcome::HitInstallable,
            accepted_hit_gate.clone(),
            Some(ASYNC_PROOF_TV_CHECKSUM.to_owned()),
            Some(ASYNC_TELEMETRY_CHECKSUM.to_owned()),
        );

        let request = request(&format!("cache-insert-{label}-request"), 29)
            .with_artifact_manifest(manifest.clone());
        let request_id = request.request_id.clone();
        async_service.submit(request).expect("submit accepted");

        let packet = telemetry_packet_for_request(
            &async_service,
            AsyncCompileTelemetryEvent::Submit,
            &request_id,
        );
        assert_eq!(packet.cache_lookup_outcome, Some(outcome), "{label}");
        assert_eq!(packet.native_install_gate_blocker, Some(blocker), "{label}");
        assert_eq!(
            packet
                .native_install_gate
                .as_ref()
                .and_then(|gate| gate.rejection_code),
            rejection_code,
            "{label}"
        );
        assert_metadata_only_telemetry(&async_service);
    }
}

#[test]
fn async_manifest_cache_hit_revalidates_gate_surface_and_identity() {
    let manifest = deterministic_manifest("async-cache-identity", 28);
    let accepted_gate = gate_packet(
        &manifest,
        NativeInstallGateSurface::CacheHit,
        NativeInstallGateDisposition::Installable,
        None,
    );

    let async_poll_surface = gate_packet(
        &manifest,
        NativeInstallGateSurface::AsyncPoll,
        NativeInstallGateDisposition::Installable,
        None,
    );

    let mut stale_invalidation = accepted_gate.clone();
    stale_invalidation.artifact.invalidation_checksum =
        ArtifactChecksum::new(manifest.invalidation.checksum().get() ^ 1);

    for (label, gate, proof_tv_checksum, telemetry_checksum) in [
        (
            "async-poll-surface",
            async_poll_surface,
            ASYNC_PROOF_TV_CHECKSUM,
            ASYNC_TELEMETRY_CHECKSUM,
        ),
        (
            "proof-tv-checksum",
            accepted_gate.clone(),
            "sha256:other-proof",
            ASYNC_TELEMETRY_CHECKSUM,
        ),
        (
            "invalidation-checksum",
            stale_invalidation,
            ASYNC_PROOF_TV_CHECKSUM,
            ASYNC_TELEMETRY_CHECKSUM,
        ),
        (
            "telemetry-checksum",
            accepted_gate,
            ASYNC_PROOF_TV_CHECKSUM,
            "sha256:other-telemetry",
        ),
    ] {
        let mut async_service = AsyncCompileService::default();
        record_accepted_cache_insert(&mut async_service, &manifest);
        async_service.record_manifest_cache_gate_entry_with_identity(
            &manifest,
            AsyncCacheLookupOutcome::HitInstallable,
            gate,
            Some(proof_tv_checksum.to_owned()),
            Some(telemetry_checksum.to_owned()),
        );
        let request =
            request(&format!("cache-{label}-request"), 28).with_artifact_manifest(manifest.clone());
        let request_id = request.request_id.clone();
        async_service.submit(request).expect("submit accepted");

        let packet = telemetry_packet_for_request(
            &async_service,
            AsyncCompileTelemetryEvent::Submit,
            &request_id,
        );
        assert_eq!(
            packet.cache_lookup_outcome,
            Some(AsyncCacheLookupOutcome::GateMetadataMismatch),
            "{label}"
        );
        assert_eq!(
            packet.native_install_gate_blocker,
            Some(AsyncInstallGateBlockerCode::GateMetadataMismatch),
            "{label}"
        );
        assert_metadata_only_telemetry(&async_service);
    }
}

#[test]
fn async_manifest_cache_hit_revalidates_current_generation() {
    let manifest = deterministic_manifest("async-cache-current-generation", 29);
    let mut stale_gate = gate_packet(
        &manifest,
        NativeInstallGateSurface::CacheHit,
        NativeInstallGateDisposition::Installable,
        None,
    );
    stale_gate.freshness.current_generation += 1;
    persist_native_install_gate_packet_bindings(&mut stale_gate);

    let mut async_service = AsyncCompileService::default();
    record_accepted_cache_insert(&mut async_service, &manifest);
    async_service.record_manifest_cache_gate_entry_with_identity(
        &manifest,
        AsyncCacheLookupOutcome::HitInstallable,
        stale_gate,
        Some(ASYNC_PROOF_TV_CHECKSUM.to_owned()),
        Some(ASYNC_TELEMETRY_CHECKSUM.to_owned()),
    );
    let request =
        request("cache-current-generation-request", 29).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();
    async_service.submit(request).expect("submit accepted");

    let packet = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Submit,
        &request_id,
    );
    assert_eq!(
        packet.cache_lookup_outcome,
        Some(AsyncCacheLookupOutcome::GateRejected)
    );
    assert_eq!(
        packet.native_install_gate_blocker,
        Some(AsyncInstallGateBlockerCode::GateRejected)
    );
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn async_manifest_cache_rejects_stale_or_mismatched_gate_metadata() {
    let manifest = deterministic_manifest("async-cache-stale-gate", 27);
    let stale_gate = gate_packet(
        &manifest,
        NativeInstallGateSurface::CacheHit,
        NativeInstallGateDisposition::Rejected,
        Some(NativeInstallGateRejectionCode::StaleInvalidation),
    );
    let other_manifest = deterministic_manifest("async-cache-other-gate", 27);
    let mismatched_gate = gate_packet(
        &other_manifest,
        NativeInstallGateSurface::CacheHit,
        NativeInstallGateDisposition::Installable,
        None,
    );

    for (label, gate, outcome, blocker, rejection_code) in [
        (
            "stale",
            stale_gate,
            AsyncCacheLookupOutcome::GateRejected,
            AsyncInstallGateBlockerCode::GateRejected,
            Some(NativeInstallGateRejectionCode::StaleInvalidation),
        ),
        (
            "mismatch",
            mismatched_gate,
            AsyncCacheLookupOutcome::GateMetadataMismatch,
            AsyncInstallGateBlockerCode::GateMetadataMismatch,
            None,
        ),
    ] {
        let mut async_service = AsyncCompileService::default();
        record_accepted_cache_insert(&mut async_service, &manifest);
        async_service.record_manifest_cache_gate_entry(
            &manifest,
            AsyncCacheLookupOutcome::HitInstallable,
            gate,
        );
        let request = request(&format!("cache-{label}-gate-request"), 27)
            .with_artifact_manifest(manifest.clone());
        let request_id = request.request_id.clone();
        async_service.submit(request).expect("submit accepted");

        let packet = telemetry_packet_for_request(
            &async_service,
            AsyncCompileTelemetryEvent::Submit,
            &request_id,
        );
        assert_eq!(packet.cache_lookup_outcome, Some(outcome), "{label}");
        assert_eq!(packet.native_install_gate_blocker, Some(blocker), "{label}");
        assert_eq!(
            packet
                .native_install_gate
                .as_ref()
                .expect("gate packet")
                .rejection_code,
            rejection_code,
            "{label}"
        );
        assert_metadata_only_telemetry(&async_service);
    }
}

#[test]
fn async_manifest_cache_miss_is_recorded_for_uncached_manifest() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-cache-miss", 18);
    let cache_key = manifest_cache_key(&manifest);
    let request = request("cache-miss-request", 18).with_artifact_manifest(manifest);
    let request_id = request.request_id.clone();

    async_service.submit(request).expect("submit accepted");

    let packet = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Submit,
        &request_id,
    );
    assert_eq!(packet.cache_key.as_deref(), Some(cache_key.as_str()));
    assert_eq!(
        packet.cache_lookup_outcome,
        Some(AsyncCacheLookupOutcome::Miss)
    );
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn duplicate_in_flight_async_submit_dedupes_by_manifest_cache_key() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-cache-dedupe", 19);
    let cache_key = manifest_cache_key(&manifest);
    let first = request("cache-dedupe-first", 19).with_artifact_manifest(manifest.clone());
    let first_id = first.request_id.clone();
    let second = request("cache-dedupe-second", 20).with_artifact_manifest(manifest.clone());
    let second_id = second.request_id.clone();
    async_service.record_native_install_gate_packet(
        first_id.clone(),
        gate_packet(
            &manifest,
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::Installable,
            None,
        ),
    );

    async_service.submit(first).expect("first submit accepted");
    let reject = async_service
        .submit(second)
        .expect_err("second submit rejected by cache key");

    assert_eq!(reject.code, AsyncSubmitRejectCode::DuplicateCacheKey);
    assert_eq!(reject.state, AsyncCompileState::Rejected);
    let first_submit = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Submit,
        &first_id,
    );
    let second_submit = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Submit,
        &second_id,
    );
    assert_eq!(first_submit.cache_key.as_deref(), Some(cache_key.as_str()));
    assert_eq!(second_submit.cache_key.as_deref(), Some(cache_key.as_str()));
    assert_eq!(
        first_submit.cache_lookup_outcome,
        Some(AsyncCacheLookupOutcome::Miss)
    );
    assert_eq!(
        second_submit.cache_lookup_outcome,
        Some(AsyncCacheLookupOutcome::Miss)
    );

    let ticket = async_service.start_next().expect("first worker ticket");
    assert_eq!(ticket.request_id, first_id);
    let generation = ticket.generation;
    let response = async_service
        .service()
        .compile_with(ticket.request.clone(), || {
            Ok(artifact_with_manifest(generation, manifest))
        });
    let poll = async_service.finish(ticket, response);
    assert_eq!(poll.state, AsyncCompileState::CompiledInstallable);
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn duplicate_request_id_reject_does_not_release_manifest_cache_owner() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-cache-owner", 21);
    let cache_key = manifest_cache_key(&manifest);
    let original = request("cache-owner-original", 21).with_artifact_manifest(manifest.clone());
    let original_id = original.request_id.clone();
    let duplicate_id = request("cache-owner-original", 22).with_artifact_manifest(manifest.clone());
    let duplicate_key = request("cache-owner-key", 23).with_artifact_manifest(manifest.clone());
    let duplicate_key_id = duplicate_key.request_id.clone();
    let while_running =
        request("cache-owner-while-running", 24).with_artifact_manifest(manifest.clone());
    let after_release =
        request("cache-owner-after-release", 25).with_artifact_manifest(manifest.clone());
    async_service.record_native_install_gate_packet(
        original_id.clone(),
        gate_packet(
            &manifest,
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::Installable,
            None,
        ),
    );

    async_service
        .submit(original)
        .expect("original submit accepted");
    let duplicate_id_reject = async_service
        .submit(duplicate_id)
        .expect_err("duplicate request id rejected");

    assert_eq!(
        duplicate_id_reject.code,
        AsyncSubmitRejectCode::DuplicateRequest
    );
    assert_eq!(
        async_service.poll(&original_id).state,
        AsyncCompileState::Queued
    );

    let duplicate_key_reject = async_service
        .submit(duplicate_key)
        .expect_err("same manifest key remains owned by original");
    assert_eq!(
        duplicate_key_reject.code,
        AsyncSubmitRejectCode::DuplicateCacheKey
    );
    assert_eq!(
        async_service.poll(&duplicate_key_id).state,
        AsyncCompileState::Rejected
    );

    let ticket = async_service.start_next().expect("original worker ticket");
    assert_eq!(ticket.request_id, original_id);
    assert_eq!(
        async_service
            .submit(while_running)
            .expect_err("running owner still holds cache key")
            .code,
        AsyncSubmitRejectCode::DuplicateCacheKey
    );

    let generation = ticket.generation;
    let response = async_service
        .service()
        .compile_with(ticket.request.clone(), || {
            Ok(artifact_with_manifest(generation, manifest))
        });
    let poll = async_service.finish(ticket, response);
    assert_eq!(poll.state, AsyncCompileState::CompiledInstallable);

    let accepted = async_service
        .submit(after_release)
        .expect("cache key released after original terminal state");
    assert_eq!(accepted.state, AsyncCompileState::Queued);

    let original_submit = telemetry_packet_for_request(
        &async_service,
        AsyncCompileTelemetryEvent::Submit,
        &original_id,
    );
    assert_eq!(
        original_submit.cache_key.as_deref(),
        Some(cache_key.as_str())
    );
    assert_metadata_only_telemetry(&async_service);
}

#[test]
fn telemetry_records_async_lifecycle_events() {
    let mut async_service = AsyncCompileService::default();
    let manifest = deterministic_manifest("async-lifecycle-telemetry", 11);
    let request = request("lifecycle-telemetry", 11).with_artifact_manifest(manifest.clone());
    let request_id = request.request_id.clone();
    async_service.record_native_install_gate_packet(
        request_id.clone(),
        gate_packet(
            &manifest,
            NativeInstallGateSurface::AsyncPoll,
            NativeInstallGateDisposition::Installable,
            None,
        ),
    );

    async_service.submit(request).expect("submit accepted");
    assert_eq!(
        async_service.poll(&request_id).state,
        AsyncCompileState::Queued
    );
    let ticket = async_service.start_next().expect("worker ticket");
    assert_eq!(
        async_service.poll(&request_id).state,
        AsyncCompileState::Running
    );
    let generation = ticket.generation;
    let response = async_service
        .service()
        .compile_with(ticket.request.clone(), || {
            Ok(artifact_with_manifest(generation, manifest))
        });
    async_service.finish(ticket, response);

    for event in [
        AsyncCompileTelemetryEvent::Submit,
        AsyncCompileTelemetryEvent::Queued,
        AsyncCompileTelemetryEvent::Running,
        AsyncCompileTelemetryEvent::Poll,
        AsyncCompileTelemetryEvent::Finish,
        AsyncCompileTelemetryEvent::CompiledResponse,
    ] {
        assert!(
            telemetry_event_count(&async_service, event) > 0,
            "missing event {}",
            event.as_str()
        );
    }
}

#[test]
fn terminal_poll_reports_evicted_when_retention_is_exceeded() {
    let mut async_service = AsyncCompileService::with_default_service(AsyncCompileServiceConfig {
        max_terminal_retained: 1,
        ..AsyncCompileServiceConfig::default()
    });
    let first = request("evicted-first", 1);
    let first_id = first.request_id.clone();
    async_service.submit(first).expect("first submit");
    async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || Ok(artifact(generation)))
        })
        .expect("first result");

    async_service
        .submit(request("retained-second", 2))
        .expect("second submit");
    async_service
        .run_next_with(|service, request| {
            let generation = request.generation;
            service.compile_with(request, || Ok(artifact(generation)))
        })
        .expect("second result");

    assert_eq!(
        async_service.poll(&first_id).state,
        AsyncCompileState::Evicted
    );
}
