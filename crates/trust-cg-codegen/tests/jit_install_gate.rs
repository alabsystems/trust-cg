// trust-cg-codegen/tests/jit_install_gate.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_cg_codegen::ay_lra_proof_manifest::{
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OBSERVATIONS,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_ATTEMPTED,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED_TOTAL,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT,
    AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA, AYLraBasisEpochEvidence,
    AYLraEvidenceAvailability, AYLraKernelFamily, AYLraKernelProofConsumptionManifest,
    AYLraManifestDisposition, AYLraManifestRejectionReason, AYLraProductGateEvidence,
    AYLraProofConsumptionEvidence, AYLraReplayComparison, AYLraRequirementAvailability,
    AYLraSparseAffectedRowBatchEvidence, ay_lra_basis_update_proof_manifest,
    ay_lra_proof_fact_metadata_key, ay_lra_sparse_affected_row_batch_proof_manifest,
    ay_lra_sparse_substitute_proof_manifest, evaluate_ay_lra_sparse_affected_row_batch_evidence,
};
use trust_cg_codegen::ay_sat_helper_replacement_contract::{
    ay_sat_theory_dispatch_assignment_layout_with_text_size,
    ay_sat_theory_dispatch_assignment_manifest_for_parts,
    ay_sat_theory_dispatch_assignment_proof_policy,
    ay_sat_theory_dispatch_assignment_verified_proof_evidence,
};
use trust_cg_codegen::compile_service::ArtifactManifestReference;
use trust_cg_codegen::jit_ay_canary_allowlist::AYCanaryLraProofFactEvidence;
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, AliasPolicy, ArtifactChecksum, ArtifactManifestV1,
    ArtifactSection, ArtifactSectionKind, ArtifactSymbol, Endianness, FieldLayout,
    HOST_JIT_TARGET_FEATURE_PROFILE_CURRENT_POLICY_KEY, HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA,
    HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY, HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY,
    HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY, InvalidationKey, JitArtifactKind,
    LayoutManifest, Mutability, PointerBounds, PointerLayout, ProofEvidenceRejectionCode,
    ProofEvidenceSummary, ProofEvidenceVerdict, ProofPolicy, RecordLayout, SliceLayout,
    SymbolLayout, SymbolSignature, SymbolVisibility,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY, TargetDescriptor, TargetOperatingSystem,
    trust_ir_hardware_vector_contract_manifest_row_count,
    trust_ir_hardware_vector_contract_manifest_sha256,
};
use trust_cg_codegen::jit_install_gate::{
    NativeInstallGateAYLayoutAdapter, NativeInstallGateActions, NativeInstallGateAuthority,
    NativeInstallGateConsumerAdmissionDecision, NativeInstallGateConsumerAdmissionEvidence,
    NativeInstallGateDisposition, NativeInstallGateExpectedBindings, NativeInstallGateInput,
    NativeInstallGateLayoutEvidence, NativeInstallGatePacket, NativeInstallGatePayloadIdentity,
    NativeInstallGateProofEvidence, NativeInstallGateRejectionCode,
    NativeInstallGateRevalidationInput, NativeInstallGateRuntimeOutcome,
    NativeInstallGateSharedPrimitiveContractReason, NativeInstallGateSurface,
    NativeInstallGateTelemetryInput, NativeInstallGateTyLayoutAdapter,
    NativeInstallGateValidationPacket, native_install_gate_consumer_admission,
    native_install_gate_consumer_admission_structured_event,
    native_install_gate_consumer_allowlist_key, native_install_gate_packet_hash,
    native_install_gate_runtime_structured_event, native_install_gate_runtime_telemetry,
    native_install_gate_shadow_mismatch_event, native_install_gate_structured_event,
    persist_native_install_gate_packet_bindings, validate_native_install_gate,
    validate_native_install_gate_packet, validate_native_install_gate_packet_with_current,
    validate_native_install_gate_verdict,
};
use trust_cg_codegen::{
    AYCanaryAllowlist, AYCanaryAllowlistKey, AYCanaryCandidate, AYCanaryCandidateMode,
    AYCanaryDecisionStatus, AYCanaryEquivalenceEvidence, AYCanaryExecutionObservation,
    AYCanaryFamily, AYCanaryGenerationFence, AYCanaryInvalidationState, AYCanaryLayoutProof,
    AYCanaryManifestBinding, AYCanaryParentGateEvidence, AYCanaryProofDecision,
    AYCanaryRejectionReason, AYCanaryValidationProvenance, ControlPlaneCandidate,
    ControlPlaneConsumerAdmissionProductDecision, ControlPlaneDecision, ControlPlaneGateEvidence,
    ControlPlaneKillSwitch, ControlPlaneMode, ControlPlaneProductCallStatus, ControlPlaneReason,
    ControlPlaneRevocation, JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA,
    JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA_VERSION, JitEverywhereControlPlane,
    NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA,
    NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA,
    NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA_VERSION, NATIVE_INSTALL_GATE_EVENT_SCHEMA,
    NATIVE_INSTALL_GATE_EVENT_SCHEMA_VERSION, NATIVE_INSTALL_GATE_PACKET_SCHEMA,
    NATIVE_INSTALL_GATE_REPLAY_SCHEMA, NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA,
    NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA_VERSION, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA,
    NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION, NativeInstallGateDenyControlPlane,
    NativeInstallGateDenyReason, NativeInstallGateDenyScope, NativeInstallGateEventKind,
    NativeInstallGateEventSource, NativeInstallGateFreshnessObservation,
    NativeInstallGateReplayIdentity, NativeInstallGateStructuredEvent,
    PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR,
    ProofGuidedAdmissionEvidence, ProofOptimizationCertificateCitation,
    ProofOptimizationConsumedFactCitation, RewriteAdmissionDisposition, RewriteAdmissionRecord,
    RewriteAdmissionRejection, Target, TyCanaryAllowlist, TyCanaryAllowlistKey, TyCanaryCandidate,
    TyCanaryCandidateMode, TyCanaryDecisionStatus, TyCanaryEquivalenceEvidence,
    TyCanaryExecutionObservation, TyCanaryFamily, TyCanaryGenerationTuple,
    TyCanaryInvalidationState, TyCanaryLayoutProof, TyCanaryManifestBinding,
    TyCanaryParentGateEvidence, TyCanaryProofDecision, TyCanaryRejectionReason,
    TyCanaryValidationProvenance, consumer_admission_with_control_plane,
    evaluate_ay_canary_activation_precheck, evaluate_ay_canary_product_adapter_precheck,
    evaluate_ty_canary_activation_precheck, evaluate_ty_canary_product_adapter_precheck,
    install_gate_revalidation_with_control_plane,
};

fn manifest() -> ArtifactManifestV1 {
    let target =
        TargetDescriptor::for_trust_cg_target(Target::X86_64, TargetOperatingSystem::Linux);
    let abi = AbiDescriptor::for_trust_cg_target(Target::X86_64);
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let proof_policy = ProofPolicy::require_certificates(["trust_cg_verify"]);
    let invalidation = trust_cg_codegen::jit_contract::InvalidationKey::new(
        "source-sha",
        "compiler-sha",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        7,
    );
    ArtifactManifestV1::new(
        "artifact.installable",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    )
}

fn payload_identity() -> NativeInstallGatePayloadIdentity {
    NativeInstallGatePayloadIdentity {
        source_sha256: "source-sha256".to_owned(),
        trust_ir_sha256: "trust_ir-sha256".to_owned(),
        native_payload_sha256: "native-sha256".to_owned(),
    }
}

fn generic_layout_evidence(manifest: &ArtifactManifestV1) -> NativeInstallGateLayoutEvidence {
    let region = NativeInstallGateLayoutEvidence::region(
        "native_region",
        "native_region",
        8,
        1024,
        trust_cg_codegen::NativeInstallGateLayoutAccess::ReadWrite,
        "native-alias",
        "native_generation",
    );
    let entry = NativeInstallGateLayoutEvidence::entry_abi(
        "entry",
        manifest.abi.checksum(),
        &["native_region"],
        "native_region",
        "native_generation",
    );
    NativeInstallGateLayoutEvidence {
        layout_checksum: manifest.layout.checksum(),
        abi_checksum: manifest.abi.checksum(),
        invalidation_checksum: manifest.invalidation.checksum(),
        validation_provenance: "trust-cg.generic.layout_adapter.v1".to_owned(),
        evidence_sha256: None,
        wrapper_identity: Some("wrapper.v1".to_owned()),
        regions: vec![region],
        entry_abis: vec![entry],
    }
    .with_canonical_evidence_sha256()
}

fn verified_proof(manifest: &ArtifactManifestV1) -> NativeInstallGateProofEvidence {
    NativeInstallGateProofEvidence {
        summary: ProofEvidenceSummary::verified(
            "trust_cg_verify",
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
            manifest.invalidation.checksum(),
            manifest.proof_policy.checksum(),
        ),
        proof_report_sha256: Some("proof-report-sha256".to_owned()),
        obligation_set: Some("all-entrypoints".to_owned()),
        timeout_ms: Some(1_000),
        native_payload_sha256: Some("native-sha256".to_owned()),
    }
}

fn rejected_proof(
    manifest: &ArtifactManifestV1,
    verdict: ProofEvidenceVerdict,
    code: ProofEvidenceRejectionCode,
) -> NativeInstallGateProofEvidence {
    NativeInstallGateProofEvidence {
        summary: ProofEvidenceSummary::rejected(
            "trust_cg_verify",
            verdict,
            code,
            manifest.target.checksum(),
            manifest.abi.checksum(),
            manifest.layout.checksum(),
            manifest.invalidation.checksum(),
            manifest.proof_policy.checksum(),
        ),
        proof_report_sha256: Some("proof-report-sha256".to_owned()),
        obligation_set: Some("all-entrypoints".to_owned()),
        timeout_ms: Some(1_000),
        native_payload_sha256: Some("native-sha256".to_owned()),
    }
}

fn installable_input() -> NativeInstallGateInput {
    let manifest = manifest();
    let expected = NativeInstallGateExpectedBindings::from_manifest(&manifest);
    let payload_identity = payload_identity();
    let layout_evidence = generic_layout_evidence(&manifest);
    let proof_evidence = verified_proof(&manifest);
    let current_invalidation_checksum = expected.invalidation_checksum;
    let current_generation = expected.current_generation;

    let mut input = NativeInstallGateInput {
        consumer: "ay".to_owned(),
        consumer_mode: "solver-kernel".to_owned(),
        surface: NativeInstallGateSurface::TypedSymbolLookup,
        candidate_disposition: NativeInstallGateDisposition::Installable,
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        manifest_reference: Some(ArtifactManifestReference::from_manifest(&manifest)),
        manifest: Some(manifest),
        expected,
        payload_identity: payload_identity.clone(),
        candidate_payload_identity: payload_identity,
        layout_evidence: Some(layout_evidence),
        proof_evidence: Some(proof_evidence),
        current_invalidation_checksum,
        artifact_generation: current_generation,
        current_generation,
        revoked: false,
        deny_control: None,
        replay_identity: None,
        telemetry: None,
    };
    refresh_gate_identity(&mut input);
    input
}

fn identity_counter_scope(input: &NativeInstallGateInput) -> String {
    let consumer_mode =
        identity_counter_scope_consumer_mode(&input.consumer, &input.consumer_mode, input.surface);
    format!(
        "{}:{}:{}:{}",
        input.consumer,
        consumer_mode,
        input.surface.as_str(),
        input.expected.artifact_id
    )
}

fn identity_counter_scope_consumer_mode<'a>(
    consumer: &str,
    consumer_mode: &'a str,
    surface: NativeInstallGateSurface,
) -> &'a str {
    if consumer != "ay" || surface != NativeInstallGateSurface::AYRegistry {
        return consumer_mode;
    }

    match consumer_mode {
        mode if mode == AYLraKernelFamily::SparseSubstitute.as_str() => {
            AYLraKernelFamily::SparseSubstitute.as_str()
        }
        "lra_sparse_substitute" | "sparse_substitute" => {
            AYLraKernelFamily::SparseSubstitute.as_str()
        }
        mode if mode == AYLraKernelFamily::SparseAffectedRowBatch.as_str() => {
            AYLraKernelFamily::SparseAffectedRowBatch.as_str()
        }
        "lra_sparse_affected_row_batch" => AYLraKernelFamily::SparseAffectedRowBatch.as_str(),
        mode if mode == AYLraKernelFamily::BasisUpdate.as_str() => {
            AYLraKernelFamily::BasisUpdate.as_str()
        }
        "ay_lra_basis_row_batch" | "basis_row_batch" => AYLraKernelFamily::BasisUpdate.as_str(),
        _ => consumer_mode,
    }
}

fn replay_identity(
    input: &NativeInstallGateInput,
    replay_root_sha256: &str,
) -> NativeInstallGateReplayIdentity {
    NativeInstallGateReplayIdentity {
        schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        replay_root_sha256: replay_root_sha256.to_owned(),
        replay_consumer: input.consumer.clone(),
        replay_family: input.consumer_mode.clone(),
        artifact_id: input.expected.artifact_id.clone(),
        source_sha256: input.candidate_payload_identity.source_sha256.clone(),
        trust_ir_sha256: input.candidate_payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: input
            .candidate_payload_identity
            .native_payload_sha256
            .clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256()
}

fn refresh_gate_identity(input: &mut NativeInstallGateInput) {
    let event_id = input
        .telemetry
        .as_ref()
        .map(|telemetry| telemetry.event_id.clone())
        .unwrap_or_else(|| "install-event-1".to_owned());
    let replay_root_sha256 = input
        .replay_identity
        .as_ref()
        .map(|replay| replay.replay_root_sha256.clone())
        .unwrap_or_else(|| "sha256:install-replay-root".to_owned());
    let proof_report_sha256 = input
        .proof_evidence
        .as_ref()
        .and_then(|proof| proof.proof_report_sha256.clone());
    input.telemetry = Some(
        NativeInstallGateTelemetryInput {
            schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
            schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
            event_id,
            counter_scope: identity_counter_scope(input),
            record_sha256: String::new(),
            artifact_id: input.expected.artifact_id.clone(),
            manifest_checksum: input.expected.manifest_checksum,
            proof_report_sha256,
            layout_checksum: input.expected.layout_checksum,
            invalidation_checksum: input.expected.invalidation_checksum,
            disposition: NativeInstallGateDisposition::Installable,
            rejection_code: None,
            install_authority: input.requested_authority,
            useful_native_delta: 0,
        }
        .with_canonical_record_sha256(),
    );
    input.replay_identity = Some(replay_identity(input, &replay_root_sha256));
}

fn assert_blocked(actions: NativeInstallGateActions) {
    assert!(actions.all_install_authority_blocked());
}

fn assert_structured_event(
    event: &NativeInstallGateStructuredEvent,
    source: NativeInstallGateEventSource,
    kind: NativeInstallGateEventKind,
) {
    assert_eq!(event.schema, NATIVE_INSTALL_GATE_EVENT_SCHEMA);
    assert_eq!(
        event.schema_version,
        NATIVE_INSTALL_GATE_EVENT_SCHEMA_VERSION
    );
    assert_eq!(event.issue, 749);
    assert_eq!(event.source, source);
    assert_eq!(event.kind, kind);
    assert_eq!(event.event_sha256, event.canonical_event_sha256());
}

#[derive(Debug, Default)]
struct AYConsumerRegistry {
    registry_key: Option<String>,
    callable_handle: Option<String>,
}

impl AYConsumerRegistry {
    fn activate(&mut self, input: &NativeInstallGateInput) -> ConsumerActivationResult {
        let packet = validate_native_install_gate(input);
        let mut result = ConsumerActivationResult::from_gate(&packet);
        if packet.actions.ay_registry_insert {
            let registry_key = format!("ay:{}", packet.artifact.artifact_id);
            let handle = format!("callable:{}", packet.artifact.native_payload_sha256);
            self.registry_key = Some(registry_key.clone());
            self.callable_handle = Some(handle.clone());
            result.registry_key = Some(registry_key);
            result.callable_handle = Some(handle);
            result.callable_exposed = true;
        }
        result
    }
}

#[derive(Debug, Default)]
struct TyNativeSlot {
    native_handle: Option<String>,
}

impl TyNativeSlot {
    fn activate(&mut self, input: &NativeInstallGateInput) -> ConsumerActivationResult {
        let packet = validate_native_install_gate(input);
        let mut result = ConsumerActivationResult::from_gate(&packet);
        if packet.actions.ty_native_activate {
            let handle = format!("ty-native:{}", packet.artifact.native_payload_sha256);
            self.native_handle = Some(handle.clone());
            result.native_handle = Some(handle);
            result.callable_exposed = true;
        }
        result
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ConsumerActivationResult {
    gate_disposition: NativeInstallGateDisposition,
    gate_rejection_code: Option<NativeInstallGateRejectionCode>,
    validation: NativeInstallGateValidationPacket,
    registry_key: Option<String>,
    callable_handle: Option<String>,
    native_handle: Option<String>,
    callable_exposed: bool,
    useful_native_eligible: bool,
}

impl ConsumerActivationResult {
    fn from_gate(packet: &trust_cg_codegen::jit_install_gate::NativeInstallGatePacket) -> Self {
        Self {
            gate_disposition: packet.disposition,
            gate_rejection_code: packet.rejection_code,
            validation: packet.validation.clone(),
            registry_key: None,
            callable_handle: None,
            native_handle: None,
            callable_exposed: false,
            useful_native_eligible: packet.actions.useful_native_eligible,
        }
    }

    fn has_any_handle(&self) -> bool {
        self.registry_key.is_some()
            || self.callable_handle.is_some()
            || self.native_handle.is_some()
    }
}

#[derive(Debug, Default, PartialEq, Eq)]
struct ConsumerActivationTelemetry {
    install_accepted: u64,
    install_rejected: u64,
    install_revoked: u64,
    install_stale: u64,
    fallback_baseline: u64,
    useful_native: u64,
}

impl ConsumerActivationTelemetry {
    fn record_gate(&mut self, result: &ConsumerActivationResult) {
        if result.gate_disposition.is_installable() {
            self.install_accepted += 1;
            return;
        }

        match result.gate_rejection_code {
            Some(NativeInstallGateRejectionCode::RevokedArtifact) => {
                self.install_revoked += 1;
            }
            Some(
                NativeInstallGateRejectionCode::ProofStaleEvidence
                | NativeInstallGateRejectionCode::StaleInvalidation,
            ) => {
                self.install_stale += 1;
            }
            Some(NativeInstallGateRejectionCode::ShadowOnlyNonInstallable) => {
                self.fallback_baseline += 1;
            }
            Some(_) | None => {
                self.install_rejected += 1;
            }
        }
    }

    fn record_useful_native_execution(&mut self, result: &ConsumerActivationResult) {
        if result.callable_exposed && result.useful_native_eligible {
            self.useful_native += 1;
        }
    }
}

fn activation_input(consumer: &str, surface: NativeInstallGateSurface) -> NativeInstallGateInput {
    let mut input = installable_input();
    input.consumer = consumer.to_owned();
    input.consumer_mode = match consumer {
        "ay" => "solver-registry".to_owned(),
        "ty" => "native-fused-parent-loop".to_owned(),
        _ => "unknown".to_owned(),
    };
    input.surface = surface;
    if consumer == "ay" && surface == NativeInstallGateSurface::AYRegistry {
        input.layout_evidence = Some(NativeInstallGateLayoutEvidence::ay_solver_registry_prework(
            input.expected.layout_checksum,
            input.expected.abi_checksum,
            input.expected.invalidation_checksum,
            "ay.solver-registry.wrapper.v1",
        ));
    }
    refresh_gate_identity(&mut input);
    input
}

fn ty_prework_input() -> NativeInstallGateInput {
    let mut input = activation_input("ty", NativeInstallGateSurface::TyActivation);
    input.layout_evidence = Some(
        NativeInstallGateLayoutEvidence::ty_fused_parent_loop_prework(
            input.expected.layout_checksum,
            input.expected.abi_checksum,
            input.expected.invalidation_checksum,
            "ty.fused-parent-loop.wrapper.v1",
        ),
    );
    input
}

const AY_SAT_THEORY_DISPATCH_INSTALL_GATE_TEXT_SIZE_BYTES: u64 = 160;

fn ay_sat_theory_dispatch_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::host(), TargetOperatingSystem::host())
        .with_cpu("host")
        .with_features(["sat-helper-replacement-install-gate"])
}

fn ay_sat_theory_dispatch_abi() -> AbiDescriptor {
    let mut abi =
        AbiDescriptor::for_trust_cg_target_os(Target::host(), TargetOperatingSystem::host());
    abi.name = format!("ay-sat-theory-dispatch-{}-lp64", Target::host().name());
    abi
}

fn ay_sat_theory_dispatch_manifest(generation: u64) -> ArtifactManifestV1 {
    let layout = ay_sat_theory_dispatch_assignment_layout_with_text_size(
        Target::host().stack_alignment() as u16,
        AY_SAT_THEORY_DISPATCH_INSTALL_GATE_TEXT_SIZE_BYTES,
    );
    let mut manifest = ay_sat_theory_dispatch_assignment_manifest_for_parts(
        ay_sat_theory_dispatch_target(),
        ay_sat_theory_dispatch_abi(),
        layout,
        ay_sat_theory_dispatch_assignment_proof_policy(),
        generation,
        AY_SAT_THEORY_DISPATCH_INSTALL_GATE_TEXT_SIZE_BYTES,
    );
    manifest
        .metadata
        .insert("differential_evidence_issue".to_owned(), "803".to_owned());
    manifest.metadata.insert(
        "differential_evidence_target".to_owned(),
        "ay_sat_helper_replacement_differential".to_owned(),
    );
    manifest.metadata.insert(
        "rust_reference".to_owned(),
        "local_private_theory_dispatch_dispatch_assignment_reference".to_owned(),
    );
    manifest
        .metadata
        .insert("useful_native".to_owned(), "0".to_owned());
    manifest.metadata.insert(
        "product_promotion_scope".to_owned(),
        "does_not_unblock_665_product_promotion_or_public_ay_repin".to_owned(),
    );
    manifest
}

fn ay_sat_theory_dispatch_payload_identity() -> NativeInstallGatePayloadIdentity {
    NativeInstallGatePayloadIdentity {
        source_sha256: "sha256:ay-sat-theory-dispatch-source".to_owned(),
        trust_ir_sha256: "sha256:ay-sat-theory-dispatch-trust_ir".to_owned(),
        native_payload_sha256: "sha256:ay-sat-theory-dispatch-native".to_owned(),
    }
}

fn ay_sat_theory_dispatch_proof(manifest: &ArtifactManifestV1) -> NativeInstallGateProofEvidence {
    let mut summary =
        ay_sat_theory_dispatch_assignment_verified_proof_evidence("trust-cg-verify", manifest);
    summary.metadata.insert(
        "differential_evidence_target".to_owned(),
        "ay_sat_helper_replacement_differential".to_owned(),
    );
    summary.metadata.insert(
        "rust_reference".to_owned(),
        "local_private_theory_dispatch_dispatch_assignment_reference".to_owned(),
    );
    summary.metadata.insert(
        "non_promoting_child".to_owned(),
        "does_not_unblock_665_product_promotion_or_public_ay_repin".to_owned(),
    );

    NativeInstallGateProofEvidence {
        summary,
        proof_report_sha256: Some("sha256:ay-sat-theory-dispatch-proof-report".to_owned()),
        obligation_set: Some("ay-sat-helper-replacement-issue-803-cases".to_owned()),
        timeout_ms: Some(10_000),
        native_payload_sha256: Some(
            ay_sat_theory_dispatch_payload_identity().native_payload_sha256,
        ),
    }
}

fn ay_sat_theory_dispatch_gate_input(manifest: &ArtifactManifestV1) -> NativeInstallGateInput {
    let expected = NativeInstallGateExpectedBindings::from_manifest(manifest);
    let payload_identity = ay_sat_theory_dispatch_payload_identity();
    let proof_evidence = ay_sat_theory_dispatch_proof(manifest);
    let mut input = NativeInstallGateInput {
        consumer: "ay".to_owned(),
        consumer_mode: "sat-theory-dispatch-helper-install-gate".to_owned(),
        surface: NativeInstallGateSurface::AYRegistry,
        candidate_disposition: NativeInstallGateDisposition::Installable,
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        manifest: Some(manifest.clone()),
        manifest_reference: Some(ArtifactManifestReference::from_manifest(manifest)),
        expected,
        payload_identity: payload_identity.clone(),
        candidate_payload_identity: payload_identity,
        layout_evidence: Some(NativeInstallGateLayoutEvidence::ay_solver_registry_prework(
            manifest.layout.checksum(),
            manifest.abi.checksum(),
            manifest.invalidation.checksum(),
            "ay.sat-theory-dispatch.wrapper.v1",
        )),
        proof_evidence: Some(proof_evidence),
        current_invalidation_checksum: manifest.invalidation.checksum(),
        artifact_generation: manifest.invalidation.generation,
        current_generation: manifest.invalidation.generation,
        revoked: false,
        deny_control: None,
        replay_identity: None,
        telemetry: None,
    };
    refresh_gate_identity(&mut input);
    input
}

fn scoped_deny_control(
    input: &NativeInstallGateInput,
    scope: NativeInstallGateDenyScope,
    reason: NativeInstallGateDenyReason,
) -> NativeInstallGateDenyControlPlane {
    let mut deny = NativeInstallGateDenyControlPlane::active(scope, reason);
    match scope {
        NativeInstallGateDenyScope::Global => {}
        NativeInstallGateDenyScope::Consumer => {
            deny.consumer = Some(input.consumer.clone());
        }
        NativeInstallGateDenyScope::Family => {
            deny.family = Some(input.consumer_mode.clone());
        }
        NativeInstallGateDenyScope::Artifact => {
            deny.artifact_id = Some(input.expected.artifact_id.clone());
        }
        NativeInstallGateDenyScope::TargetProofPolicy => {
            deny.target_checksum = Some(input.expected.target_checksum);
            deny.proof_policy_checksum = Some(input.expected.proof_policy_checksum);
        }
        NativeInstallGateDenyScope::Mode => {
            deny.mode = Some(input.requested_authority);
        }
        NativeInstallGateDenyScope::Surface => {
            deny.surface = Some(input.surface);
        }
    }
    if reason == NativeInstallGateDenyReason::StaleFreshness {
        deny.freshness = vec![NativeInstallGateFreshnessObservation::new(
            "shared_artifact_generation",
            input.current_generation,
            input.current_generation + 1,
        )];
    }
    deny.with_canonical_deny_sha256()
}

fn set_rejected_proof(
    input: &mut NativeInstallGateInput,
    verdict: ProofEvidenceVerdict,
    code: ProofEvidenceRejectionCode,
) {
    let proof = {
        let manifest = input.manifest.as_ref().expect("test input has manifest");
        rejected_proof(manifest, verdict, code)
    };
    input.proof_evidence = Some(proof);
}

fn assert_no_consumer_handle(result: &ConsumerActivationResult) {
    assert!(!result.callable_exposed);
    assert!(!result.has_any_handle());
    assert!(!result.useful_native_eligible);
}

#[derive(Debug, Default)]
struct AdmissionBackedAYRegistry {
    registry_key: Option<String>,
    callable_handle: Option<String>,
}

impl AdmissionBackedAYRegistry {
    fn insert(
        &mut self,
        packet: &NativeInstallGatePacket,
        expected_packet_hash: Option<ArtifactChecksum>,
        current: &NativeInstallGateRevalidationInput,
        evidence: &NativeInstallGateConsumerAdmissionEvidence,
    ) -> ConsumerAdmissionPublicationResult {
        let decision =
            native_install_gate_consumer_admission(packet, expected_packet_hash, current, evidence);
        let mut result = ConsumerAdmissionPublicationResult::from_decision(&decision);
        if decision.actions.ay_registry_insert {
            let registry_key = format!("ay:{}", packet.artifact.artifact_id);
            let handle = format!("callable:{}", packet.artifact.native_payload_sha256);
            self.registry_key = Some(registry_key.clone());
            self.callable_handle = Some(handle.clone());
            result.registry_key = Some(registry_key);
            result.callable_handle = Some(handle);
        }
        result
    }

    fn revalidate_or_remove(
        &mut self,
        packet: &NativeInstallGatePacket,
        expected_packet_hash: Option<ArtifactChecksum>,
        current: &NativeInstallGateRevalidationInput,
        evidence: &NativeInstallGateConsumerAdmissionEvidence,
    ) -> ConsumerAdmissionPublicationResult {
        let decision =
            native_install_gate_consumer_admission(packet, expected_packet_hash, current, evidence);
        let mut result = ConsumerAdmissionPublicationResult::from_decision(&decision);
        if decision.actions.ay_registry_insert {
            let registry_key = format!("ay:{}", packet.artifact.artifact_id);
            let handle = format!("callable:{}", packet.artifact.native_payload_sha256);
            self.registry_key = Some(registry_key.clone());
            self.callable_handle = Some(handle.clone());
            result.registry_key = Some(registry_key);
            result.callable_handle = Some(handle);
        } else {
            self.registry_key = None;
            self.callable_handle = None;
        }
        result
    }
}

#[derive(Debug, Default)]
struct AdmissionBackedTySlot {
    native_handle: Option<String>,
}

impl AdmissionBackedTySlot {
    fn activate(
        &mut self,
        packet: &NativeInstallGatePacket,
        expected_packet_hash: Option<ArtifactChecksum>,
        current: &NativeInstallGateRevalidationInput,
        evidence: &NativeInstallGateConsumerAdmissionEvidence,
    ) -> ConsumerAdmissionPublicationResult {
        let decision =
            native_install_gate_consumer_admission(packet, expected_packet_hash, current, evidence);
        let mut result = ConsumerAdmissionPublicationResult::from_decision(&decision);
        if decision.actions.ty_native_activate {
            let handle = format!("ty-native:{}", packet.artifact.native_payload_sha256);
            self.native_handle = Some(handle.clone());
            result.native_handle = Some(handle);
        }
        result
    }
}

#[derive(Debug, PartialEq, Eq)]
struct ConsumerAdmissionPublicationResult {
    disposition: NativeInstallGateDisposition,
    rejection_code: Option<NativeInstallGateRejectionCode>,
    registry_key: Option<String>,
    callable_handle: Option<String>,
    native_handle: Option<String>,
    useful_native_delta: u64,
}

impl ConsumerAdmissionPublicationResult {
    fn from_decision(decision: &NativeInstallGateConsumerAdmissionDecision) -> Self {
        Self {
            disposition: decision.disposition,
            rejection_code: decision.rejection_code,
            registry_key: None,
            callable_handle: None,
            native_handle: None,
            useful_native_delta: decision.telemetry.useful_native_delta,
        }
    }

    fn has_any_handle(&self) -> bool {
        self.registry_key.is_some()
            || self.callable_handle.is_some()
            || self.native_handle.is_some()
    }
}

fn consumer_admission_evidence(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
) -> NativeInstallGateConsumerAdmissionEvidence {
    let allowlist_key = native_install_gate_consumer_allowlist_key(packet, current)
        .expect("test packet has consumer admission surface");
    NativeInstallGateConsumerAdmissionEvidence::from_packet(
        packet,
        current,
        allowlist_key,
        true,
        true,
        true,
    )
}

fn proof_guided_ay_lra_basis_rewrite_certificate() -> ProofOptimizationCertificateCitation {
    ProofOptimizationCertificateCitation {
        function_name: "ay_lra_basis_row_batch".to_owned(),
        certificate_id: "cert-ay-lra-basis-row-batch-product-adapter".to_owned(),
        proof_hash: "proof-ay-lra-basis-row-batch-product-adapter".to_owned(),
        validation_hash: "validation-ay-lra-basis-row-batch-product-adapter".to_owned(),
        source_region_hash: "trust_ir-region-ay-lra-basis-row-batch".to_owned(),
        target_region_hash: "aarch64-region-ay-lra-basis-row-batch".to_owned(),
        transform_name: "ay.lra.basis_row_batch.sub_zero".to_owned(),
        transform_version: 1,
        admission: "proof-guided-rewrite-admission".to_owned(),
        kind: "BasisUpdate".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: vec![
            ProofOptimizationConsumedFactCitation {
                name: "ay_lra_basis_prefix_rollback".to_owned(),
                payload: Some("row-batch-prefix-rollback-v1".to_owned()),
            },
            ProofOptimizationConsumedFactCitation {
                name: "ay_lra_basis_epoch_guard".to_owned(),
                payload: Some("basis-epoch-guard-v1".to_owned()),
            },
        ],
    }
}

fn proof_guided_ay_lra_basis_complete_evidence() -> ProofGuidedAdmissionEvidence {
    ProofGuidedAdmissionEvidence::new(
        "sha256:ay-lra-basis-proof-consumption-manifest",
        "ay_lra_basis_row_batch_status_abi_v1",
        "sha256:replay-root-ay-lra-basis-row-batch",
        "trust-cg.proof_guided.ay_lra_basis_row_batch.useful_native_applications",
        0,
        "trust_cg_disable_admitted_rewrite_ay_lra_basis_row_batch",
    )
}

fn proof_guided_ay_lra_basis_rewrite_record() -> RewriteAdmissionRecord {
    RewriteAdmissionRecord::from_complete_evidence(
        proof_guided_ay_lra_basis_rewrite_certificate(),
        "aarch64",
        31,
        17,
        Some("validation-ay-lra-basis-row-batch-product-adapter".to_owned()),
        proof_guided_ay_lra_basis_complete_evidence(),
    )
}

const AY_LRA_BASIS_STATUS_SYMBOL: &str = "ay_lra_basis_row_batch";
const AY_LRA_BASIS_STATUS_RECORD: &str = "AYLraBasisRowBatchStatusAbi";
const AY_LRA_BASIS_STATUS_ABI: &str = "ay_lra_basis_row_batch_status_abi_v1";
const AY_LRA_BASIS_TRUST_IR_SOURCE_IDENTITY: &str = "trust_ir:ay:lra:basis-row-batch:v1";
const AY_LRA_BASIS_TRUST_CG_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-cg:ay-lra-basis-row-batch:v1";
const AY_LRA_BASIS_TRUST_IR_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-ir:ay-lra-basis-row-batch:v1";
const AY_LRA_BASIS_WRAPPER_IDENTITY: &str = "ay::lra::BasisRowBatchKernel::lp64:v1";
const AY_LRA_BASIS_TABLEAU_ROW_LAYOUT: &str = "ptrs_to_i64_rows_len5_stride40";
const AY_LRA_BASIS_BASIS_ROW_LAYOUT: &str = "basis_epoch_pair_current_expected";
const AY_LRA_BASIS_ROW_REGION_HASH: &str = "pre_post_tableau_digest";
const AY_LRA_BASIS_INVALIDATION_ROW_REGION_HASH: &str = "runtime_tableau_digest";
const AY_LRA_BASIS_SCRATCH_ROLLBACK: &str = "row_lengths_as_commit_log_no_failed_row_rollback";
const AY_LRA_BASIS_ROLLBACK_FAILURE_DISPOSITION: &str =
    "non_promoting_deopt_failed_row_left_uncommitted";
const AY_LRA_BASIS_ALIAS_POLICY: &str = "exclusive_tableau_rows_shared_inputs";
const AY_LRA_BASIS_OUTPUT_CAPACITY: &str = "runtime_i64";
const AY_LRA_BASIS_COMMIT_POLICY: &str = "partial_row_deopt";
const AY_LRA_BASIS_STATUS_VALUE: &str = "rows_completed";
const AY_LRA_BASIS_STATUS_DETAIL: &str = "first_failed_row";
const AY_LRA_AFFECTED_ROW_BATCH_STATUS_SYMBOL: &str =
    "ay_lra_sparse_affected_row_batch_status_probe";
const AY_LRA_AFFECTED_ROW_BATCH_KERNEL: &str = "ay_lra_sparse_affected_row_batch";
const AY_LRA_AFFECTED_ROW_BATCH_STATUS_RECORD: &str = "AYLraSparseAffectedRowBatchStatusAbi";
const AY_LRA_AFFECTED_ROW_BATCH_STATUS_ABI: &str = "ay_lra_sparse_affected_row_batch_status_abi_v1";
const AY_LRA_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_IDENTITY: &str =
    "trust_ir:ay:lra:sparse-affected-row-batch:v1";
/// Native payload / proof-report digests that bind the affected-row proof
/// evidence to its artifact. `verify_proof_evidence` requires the evidence to
/// carry the artifact identity (non-empty, `sha256:`-prefixed digests), and the
/// artifact metadata must echo the same `native_payload_sha256`.
const AY_LRA_AFFECTED_ROW_BATCH_NATIVE_PAYLOAD_SHA256: &str =
    "sha256:ay-lra-sparse-affected-row-batch-native-payload";
const AY_LRA_AFFECTED_ROW_BATCH_PROOF_REPORT_SHA256: &str =
    "sha256:ay-lra-sparse-affected-row-batch-proof-report";
const AY_LRA_AFFECTED_ROW_BATCH_TRUST_CG_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-cg:ay-lra-sparse-affected-row-batch:v1";
const AY_LRA_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-ir:ay-lra-sparse-affected-row-batch:v1";
const AY_LRA_AFFECTED_ROW_BATCH_WRAPPER_IDENTITY: &str =
    "ay::lra::SparseAffectedRowBatchKernel::lp64:v1";
const AY_LRA_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS: &str = "exact_per_row_i64_lengths";
const AY_LRA_AFFECTED_ROW_BATCH_OUTPUT_CAPACITY: &str = "runtime_i64";
const AY_LRA_AFFECTED_ROW_BATCH_STATUS_VALUE: &str = "rows_committed";
const AY_LRA_AFFECTED_ROW_BATCH_STATUS_DETAIL: &str = "first_failed_row";
const AY_LRA_AARCH64_TARGET_ABI_LAYOUT: &str = "aarch64-macos-aapcs64-lp64";
const AY_LRA_SPARSE_TRUST_IR_SOURCE_IDENTITY: &str = "trust_ir:ay:lra:sparse-substitute:v1";
const AY_LRA_SPARSE_TRUST_CG_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-cg:ay-lra-sparse-substitute:v1";
const AY_LRA_SPARSE_TRUST_IR_SOURCE_LOCK: &str =
    "source-lock-sha256:trust-ir:ay-lra-sparse-substitute:v1";
const AY_LRA_CANONICAL_SHA256: &str =
    "sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef";

fn ay_lra_i64_value() -> AbiValue {
    AbiValue::new(AbiValueKind::I64)
}

fn ay_lra_ptr_value() -> AbiValue {
    AbiValue::new(AbiValueKind::Ptr)
}

fn ay_lra_basis_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            ay_lra_ptr_value(),
            ay_lra_ptr_value(),
            ay_lra_i64_value(),
            ay_lra_ptr_value(),
            ay_lra_ptr_value(),
            ay_lra_i64_value(),
            ay_lra_ptr_value(),
            ay_lra_ptr_value(),
        ],
        vec![],
    )
}

fn ay_lra_affected_row_batch_status_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            ay_lra_i64_value(),
            ay_lra_i64_value(),
            ay_lra_i64_value(),
            ay_lra_i64_value(),
            ay_lra_i64_value(),
            ay_lra_ptr_value(),
            ay_lra_ptr_value(),
        ],
        vec![],
    )
}

fn ay_lra_field_layout(
    name: &str,
    offset_bytes: u64,
    size_bytes: u64,
    alignment_bytes: u32,
) -> FieldLayout {
    FieldLayout {
        name: name.to_owned(),
        offset_bytes,
        size_bytes,
        alignment_bytes,
    }
}

fn ay_lra_basis_status_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_LRA_BASIS_STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: 24,
        alignment_bytes: 8,
        fields: vec![
            ay_lra_field_layout("status", 0, 1, 1),
            ay_lra_field_layout("deopt", 1, 1, 1),
            ay_lra_field_layout("reserved", 2, 6, 1),
            ay_lra_field_layout("rows_completed", 8, 8, 8),
            ay_lra_field_layout("first_failed_row", 16, 8, 8),
        ],
    }
}

fn ay_lra_affected_row_batch_status_record_layout() -> RecordLayout {
    RecordLayout {
        name: AY_LRA_AFFECTED_ROW_BATCH_STATUS_RECORD.to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: 24,
        alignment_bytes: 8,
        fields: vec![
            ay_lra_field_layout("status", 0, 1, 1),
            ay_lra_field_layout("deopt", 1, 1, 1),
            ay_lra_field_layout("reserved", 2, 6, 1),
            ay_lra_field_layout("rows_committed", 8, 8, 8),
            ay_lra_field_layout("first_failed_row", 16, 8, 8),
        ],
    }
}

fn ay_lra_batch_row_i64_slice(name: &str, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: 8,
        element_alignment_bytes: 8,
        stride_bytes: 8,
        length: None,
        bounds: PointerBounds::Symbol("affected_row_count".to_owned()),
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
    }
}

fn ay_lra_fixed_i64_slice(name: &str, length: u64, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: 8,
        element_alignment_bytes: 8,
        stride_bytes: 8,
        length: Some(length),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: length * 8,
        },
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
    }
}

fn ay_lra_basis_layout_metadata_pairs() -> [(&'static str, &'static str); 11] {
    [
        ("kernel", AY_LRA_BASIS_STATUS_SYMBOL),
        ("tableau_row_layout", AY_LRA_BASIS_TABLEAU_ROW_LAYOUT),
        ("basis_row_layout", AY_LRA_BASIS_BASIS_ROW_LAYOUT),
        ("row_region_hash", AY_LRA_BASIS_ROW_REGION_HASH),
        ("scratch_rollback", AY_LRA_BASIS_SCRATCH_ROLLBACK),
        (
            "rollback_failure_disposition",
            AY_LRA_BASIS_ROLLBACK_FAILURE_DISPOSITION,
        ),
        ("alias_policy", AY_LRA_BASIS_ALIAS_POLICY),
        ("output_capacity", AY_LRA_BASIS_OUTPUT_CAPACITY),
        ("commit_policy", AY_LRA_BASIS_COMMIT_POLICY),
        ("status_value", AY_LRA_BASIS_STATUS_VALUE),
        ("status_detail", AY_LRA_BASIS_STATUS_DETAIL),
    ]
}

fn ay_lra_affected_row_batch_layout_metadata_pairs() -> [(&'static str, &'static str); 5] {
    [
        ("kernel", AY_LRA_AFFECTED_ROW_BATCH_KERNEL),
        (
            "row_output_lengths",
            AY_LRA_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS,
        ),
        ("output_capacity", AY_LRA_AFFECTED_ROW_BATCH_OUTPUT_CAPACITY),
        ("status_value", AY_LRA_AFFECTED_ROW_BATCH_STATUS_VALUE),
        ("status_detail", AY_LRA_AFFECTED_ROW_BATCH_STATUS_DETAIL),
    ]
}

fn ay_lra_basis_layout() -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some(AY_LRA_BASIS_WRAPPER_IDENTITY.to_owned());
    layout.records.push(ay_lra_basis_status_record_layout());
    layout.slices.push(ay_lra_batch_row_i64_slice(
        "tableau_row_ptrs",
        Mutability::Mutable,
    ));
    layout.slices.push(ay_lra_batch_row_i64_slice(
        "row_scales",
        Mutability::Immutable,
    ));
    layout.slices.push(ay_lra_fixed_i64_slice(
        "basis_epochs",
        2,
        Mutability::Immutable,
    ));
    layout.slices.push(ay_lra_batch_row_i64_slice(
        "row_output_offsets",
        Mutability::Immutable,
    ));
    layout.slices.push(ay_lra_batch_row_i64_slice(
        "row_output_lengths",
        Mutability::Mutable,
    ));
    layout.pointers.push(PointerLayout {
        name: "batch_status_out".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 24,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.symbols.push(SymbolLayout {
        name: AY_LRA_BASIS_STATUS_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: 256,
        alignment_bytes: 16,
    });
    for (key, value) in ay_lra_basis_layout_metadata_pairs() {
        layout.metadata.insert(key.to_owned(), value.to_owned());
    }
    layout
        .metadata
        .insert("status_abi".to_owned(), AY_LRA_BASIS_STATUS_ABI.to_owned());
    layout
}

fn ay_lra_affected_row_batch_layout() -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some(AY_LRA_AFFECTED_ROW_BATCH_WRAPPER_IDENTITY.to_owned());
    layout
        .records
        .push(ay_lra_affected_row_batch_status_record_layout());
    layout.slices.push(ay_lra_batch_row_i64_slice(
        "row_output_lengths",
        Mutability::Mutable,
    ));
    layout.pointers.push(PointerLayout {
        name: "batch_status_out".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 24,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.symbols.push(SymbolLayout {
        name: AY_LRA_AFFECTED_ROW_BATCH_STATUS_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: 256,
        alignment_bytes: 16,
    });
    for (key, value) in ay_lra_affected_row_batch_layout_metadata_pairs() {
        layout.metadata.insert(key.to_owned(), value.to_owned());
    }
    layout.metadata.insert(
        "status_abi".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_STATUS_ABI.to_owned(),
    );
    layout
}

fn ay_lra_basis_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        "ay:lra:basis-row-batch:kernel-v1",
        "trust-cg:phase5:lra:o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        45,
    );
    for (key, value) in [
        ("tableau_row_ptrs", "runtime"),
        ("row_scales", "runtime"),
        ("basis_epoch", "runtime"),
        ("basis_row_layout", AY_LRA_BASIS_BASIS_ROW_LAYOUT),
        ("tableau_row_layout", AY_LRA_BASIS_TABLEAU_ROW_LAYOUT),
        ("row_region_hash", AY_LRA_BASIS_INVALIDATION_ROW_REGION_HASH),
        ("commit_policy", AY_LRA_BASIS_COMMIT_POLICY),
        ("scratch_rollback", AY_LRA_BASIS_SCRATCH_ROLLBACK),
        (
            "rollback_failure_disposition",
            AY_LRA_BASIS_ROLLBACK_FAILURE_DISPOSITION,
        ),
        ("row_output_lengths", "mutable_runtime"),
        ("row_output_offsets", "runtime"),
        ("output_capacity", AY_LRA_BASIS_OUTPUT_CAPACITY),
        ("status_abi", AY_LRA_BASIS_STATUS_ABI),
        ("status_detail", AY_LRA_BASIS_STATUS_DETAIL),
        ("status_value", AY_LRA_BASIS_STATUS_VALUE),
    ] {
        invalidation.extra.insert(key.to_owned(), value.to_owned());
    }
    invalidation
}

fn ay_lra_affected_row_batch_invalidation(
    target: &TargetDescriptor,
    abi: &AbiDescriptor,
    layout: &LayoutManifest,
    proof_policy: &ProofPolicy,
) -> InvalidationKey {
    let mut invalidation = InvalidationKey::new(
        "ay:lra:sparse-affected-row-batch:kernel-v1",
        "trust-cg:phase5:lra:o2",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        46,
    );
    for (key, value) in [
        ("basis_epoch", "runtime"),
        ("row_output_lengths", "mutable_runtime"),
        (
            "row_output_lengths_contract",
            AY_LRA_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS,
        ),
        ("output_capacity", AY_LRA_AFFECTED_ROW_BATCH_OUTPUT_CAPACITY),
        ("status_abi", AY_LRA_AFFECTED_ROW_BATCH_STATUS_ABI),
        ("status_detail", AY_LRA_AFFECTED_ROW_BATCH_STATUS_DETAIL),
        ("status_value", AY_LRA_AFFECTED_ROW_BATCH_STATUS_VALUE),
    ] {
        invalidation.extra.insert(key.to_owned(), value.to_owned());
    }
    invalidation
}

fn attach_ay_lra_basis_product_manifest_metadata(
    manifest: &mut ArtifactManifestV1,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) {
    for (key, value) in ay_lra_basis_layout_metadata_pairs() {
        manifest.metadata.insert(key.to_owned(), value.to_owned());
    }
    manifest.metadata.insert(
        "consumer".to_owned(),
        proof_manifest.product_gate.consumer.to_owned(),
    );
    manifest.metadata.insert(
        "proof_consumption_manifest_schema".to_owned(),
        proof_manifest.schema.to_owned(),
    );
    manifest.metadata.insert(
        "proof_consumption_manifest_issue".to_owned(),
        format!("#{}", proof_manifest.issue),
    );
    manifest.metadata.insert(
        "product_gate_surface".to_owned(),
        proof_manifest.product_gate.surface.to_owned(),
    );
    manifest.metadata.insert(
        "product_gate_allowlist_family".to_owned(),
        proof_manifest.product_gate.allowlist_family.to_owned(),
    );
    manifest.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        AY_LRA_BASIS_TRUST_IR_SOURCE_IDENTITY.to_owned(),
    );
    manifest.metadata.insert(
        "source_policy".to_owned(),
        "approved_private_source".to_owned(),
    );
    manifest.metadata.insert(
        "approved_private_source_policy".to_owned(),
        "issue_663_internal_source_lock_v1".to_owned(),
    );
    manifest.metadata.insert(
        "trust_cg_source_lock".to_owned(),
        AY_LRA_BASIS_TRUST_CG_SOURCE_LOCK.to_owned(),
    );
    manifest.metadata.insert(
        "trust_ir_source_lock".to_owned(),
        AY_LRA_BASIS_TRUST_IR_SOURCE_LOCK.to_owned(),
    );
    manifest.metadata.insert(
        "target_abi_layout".to_owned(),
        AY_LRA_AARCH64_TARGET_ABI_LAYOUT.to_owned(),
    );
    manifest.metadata.insert(
        "status_signature_checksum".to_owned(),
        manifest.symbols[0].signature.checksum().to_string(),
    );
    manifest.metadata.insert(
        "proof_policy_checksum".to_owned(),
        manifest.proof_policy.checksum().to_string(),
    );
    manifest.metadata.insert(
        "invalidation_checksum".to_owned(),
        manifest.invalidation.checksum().to_string(),
    );
    manifest.metadata.insert(
        "required_proof_facts".to_owned(),
        proof_manifest.required_fact_csv(),
    );
    manifest.metadata.insert(
        "required_proof_lemmas".to_owned(),
        proof_manifest.required_lemma_csv(),
    );
    manifest.metadata.insert(
        "required_certificate_dependencies".to_owned(),
        proof_manifest.required_certificate_csv(),
    );
    manifest.metadata.insert(
        "future_proof_families".to_owned(),
        proof_manifest.future_family_csv(),
    );
    manifest.metadata.insert(
        "future_proof_status".to_owned(),
        ay_lra_manifest_future_proof_status(proof_manifest),
    );
    manifest.metadata.insert(
        "replay_compare".to_owned(),
        "generic_specialized_reference_manifest_identity".to_owned(),
    );
    manifest.metadata.insert(
        "product_gate_fields".to_owned(),
        proof_manifest.product_gate.required_parent_gates.join(","),
    );
    manifest.metadata.insert(
        "baseline_authoritative_until_product_gate".to_owned(),
        proof_manifest
            .product_gate
            .baseline_authoritative_until_product_gate
            .to_string(),
    );
    manifest.metadata.insert(
        "telemetry_counter_policy".to_owned(),
        proof_manifest
            .product_gate
            .telemetry_counter_policy
            .to_owned(),
    );
    manifest.metadata.insert(
        "useful_native".to_owned(),
        proof_manifest
            .product_gate
            .useful_native_eligible
            .to_string(),
    );
    manifest
        .metadata
        .insert("status_abi".to_owned(), AY_LRA_BASIS_STATUS_ABI.to_owned());
}

fn attach_ay_lra_affected_row_batch_product_manifest_metadata(
    manifest: &mut ArtifactManifestV1,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) {
    for (key, value) in ay_lra_affected_row_batch_layout_metadata_pairs() {
        manifest.metadata.insert(key.to_owned(), value.to_owned());
    }
    manifest.metadata.insert(
        "consumer".to_owned(),
        proof_manifest.product_gate.consumer.to_owned(),
    );
    manifest.metadata.insert(
        "proof_consumption_manifest_schema".to_owned(),
        proof_manifest.schema.to_owned(),
    );
    manifest.metadata.insert(
        "proof_consumption_manifest_issue".to_owned(),
        format!("#{}", proof_manifest.issue),
    );
    manifest.metadata.insert(
        "product_gate_surface".to_owned(),
        proof_manifest.product_gate.surface.to_owned(),
    );
    manifest.metadata.insert(
        "product_gate_allowlist_family".to_owned(),
        proof_manifest.product_gate.allowlist_family.to_owned(),
    );
    manifest.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_IDENTITY.to_owned(),
    );
    manifest.metadata.insert(
        "source_policy".to_owned(),
        "approved_private_source".to_owned(),
    );
    manifest.metadata.insert(
        "approved_private_source_policy".to_owned(),
        "issue_796_internal_source_lock_v1".to_owned(),
    );
    manifest.metadata.insert(
        "trust_cg_source_lock".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_TRUST_CG_SOURCE_LOCK.to_owned(),
    );
    manifest.metadata.insert(
        "trust_ir_source_lock".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_LOCK.to_owned(),
    );
    manifest.metadata.insert(
        "target_abi_layout".to_owned(),
        AY_LRA_AARCH64_TARGET_ABI_LAYOUT.to_owned(),
    );
    manifest.metadata.insert(
        "status_signature_checksum".to_owned(),
        manifest.symbols[0].signature.checksum().to_string(),
    );
    manifest.metadata.insert(
        "proof_policy_checksum".to_owned(),
        manifest.proof_policy.checksum().to_string(),
    );
    manifest.metadata.insert(
        "invalidation_checksum".to_owned(),
        manifest.invalidation.checksum().to_string(),
    );
    manifest.metadata.insert(
        "required_proof_facts".to_owned(),
        proof_manifest.required_fact_csv(),
    );
    manifest.metadata.insert(
        "required_proof_lemmas".to_owned(),
        proof_manifest.required_lemma_csv(),
    );
    manifest.metadata.insert(
        "required_certificate_dependencies".to_owned(),
        proof_manifest.required_certificate_csv(),
    );
    manifest.metadata.insert(
        "future_proof_families".to_owned(),
        proof_manifest.future_family_csv(),
    );
    manifest.metadata.insert(
        "future_proof_status".to_owned(),
        ay_lra_manifest_future_proof_status(proof_manifest),
    );
    manifest.metadata.insert(
        "replay_compare".to_owned(),
        "generic_specialized_reference_manifest_identity".to_owned(),
    );
    manifest.metadata.insert(
        "product_gate_fields".to_owned(),
        proof_manifest.product_gate.required_parent_gates.join(","),
    );
    manifest.metadata.insert(
        "baseline_authoritative_until_product_gate".to_owned(),
        proof_manifest
            .product_gate
            .baseline_authoritative_until_product_gate
            .to_string(),
    );
    manifest.metadata.insert(
        "telemetry_counter_policy".to_owned(),
        proof_manifest
            .product_gate
            .telemetry_counter_policy
            .to_owned(),
    );
    manifest.metadata.insert(
        "useful_native".to_owned(),
        proof_manifest
            .product_gate
            .useful_native_eligible
            .to_string(),
    );
    manifest.metadata.insert(
        "status_abi".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_STATUS_ABI.to_owned(),
    );
    // Bind the native payload digest so proof evidence can prove it targets
    // this exact artifact (`verify_evidence_artifact_identity`).
    manifest.metadata.insert(
        "native_payload_sha256".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_NATIVE_PAYLOAD_SHA256.to_owned(),
    );
}

fn ay_lra_basis_product_manifest(
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> ArtifactManifestV1 {
    let target =
        TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos)
            .with_cpu("apple-m")
            .with_features(["fp", "simd"]);
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-lra-aapcs64-lp64".to_owned();
    let layout = ay_lra_basis_layout();
    let proof_policy = ProofPolicy::require_certificates(["ay-lra", "trust-cg-verify"]);
    let invalidation = ay_lra_basis_invalidation(&target, &abi, &layout, &proof_policy);
    let mut manifest = ArtifactManifestV1::new(
        "ay-lra-basis-row-batch",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: AY_LRA_BASIS_STATUS_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_lra_basis_status_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: 256,
        alignment_bytes: 16,
        checksum: None,
    });
    attach_ay_lra_basis_product_manifest_metadata(&mut manifest, proof_manifest);
    manifest
}

fn ay_lra_affected_row_batch_product_manifest(
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> ArtifactManifestV1 {
    let target =
        TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos)
            .with_cpu("apple-m")
            .with_features(["fp", "simd"]);
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ay-lra-aapcs64-lp64".to_owned();
    let layout = ay_lra_affected_row_batch_layout();
    let proof_policy = ProofPolicy::require_certificates(["ay-lra", "trust-cg-verify"]);
    let invalidation =
        ay_lra_affected_row_batch_invalidation(&target, &abi, &layout, &proof_policy);
    let mut manifest = ArtifactManifestV1::new(
        "ay-lra-sparse-affected-row-batch-status-probe",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: AY_LRA_AFFECTED_ROW_BATCH_STATUS_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: ay_lra_affected_row_batch_status_signature(),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest.sections.push(ArtifactSection {
        name: ".text".to_owned(),
        kind: ArtifactSectionKind::Text,
        size_bytes: 256,
        alignment_bytes: 16,
        checksum: None,
    });
    attach_ay_lra_affected_row_batch_product_manifest_metadata(&mut manifest, proof_manifest);
    manifest
}

fn ay_lra_basis_verified_evidence(
    artifact: &ArtifactManifestV1,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> ProofEvidenceSummary {
    let mut evidence = ProofEvidenceSummary::verified(
        "trust-cg-verify",
        artifact.target.checksum(),
        artifact.abi.checksum(),
        artifact.layout.checksum(),
        artifact.invalidation.checksum(),
        artifact.proof_policy.checksum(),
    );
    evidence.metadata.insert(
        "proof_consumption_manifest_schema".to_owned(),
        proof_manifest.schema.to_owned(),
    );
    evidence.metadata.insert(
        "proof_consumption_manifest_issue".to_owned(),
        format!("#{}", proof_manifest.issue),
    );
    evidence.metadata.insert(
        "kernel_family".to_owned(),
        proof_manifest.kernel_family.as_str().to_owned(),
    );
    evidence.metadata.insert(
        "required_proof_facts".to_owned(),
        proof_manifest.required_fact_csv(),
    );
    for requirement in &proof_manifest.required_facts {
        evidence.metadata.insert(
            ay_lra_proof_fact_metadata_key(requirement.fact),
            requirement.lemma_id.to_owned(),
        );
    }
    evidence.metadata.insert(
        "required_certificate_dependencies".to_owned(),
        proof_manifest.required_certificate_csv(),
    );
    evidence.metadata.insert(
        "future_proof_status".to_owned(),
        ay_lra_manifest_future_proof_status(proof_manifest),
    );
    evidence.metadata.insert(
        "product_gate_fields".to_owned(),
        proof_manifest.product_gate.required_parent_gates.join(","),
    );
    evidence.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        AY_LRA_BASIS_TRUST_IR_SOURCE_IDENTITY.to_owned(),
    );
    evidence.metadata.insert(
        "source_policy".to_owned(),
        "approved_private_source".to_owned(),
    );
    evidence.metadata.insert(
        "trust_cg_source_lock".to_owned(),
        AY_LRA_BASIS_TRUST_CG_SOURCE_LOCK.to_owned(),
    );
    evidence.metadata.insert(
        "trust_ir_source_lock".to_owned(),
        AY_LRA_BASIS_TRUST_IR_SOURCE_LOCK.to_owned(),
    );
    evidence
}

fn ay_lra_affected_row_batch_verified_evidence(
    artifact: &ArtifactManifestV1,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> ProofEvidenceSummary {
    // Bind the evidence to this exact artifact (artifact id, manifest /
    // symbol-manifest checksums, native payload, and proof-report digests) so
    // `verify_proof_evidence` accepts it. The native payload digest must match
    // the artifact metadata set by
    // `attach_ay_lra_affected_row_batch_product_manifest_metadata`.
    let mut evidence = ProofEvidenceSummary::verified_for_artifact(
        "trust-cg-verify",
        artifact,
        AY_LRA_AFFECTED_ROW_BATCH_NATIVE_PAYLOAD_SHA256,
        AY_LRA_AFFECTED_ROW_BATCH_PROOF_REPORT_SHA256,
    );
    evidence.metadata.insert(
        "proof_consumption_manifest_schema".to_owned(),
        proof_manifest.schema.to_owned(),
    );
    evidence.metadata.insert(
        "proof_consumption_manifest_issue".to_owned(),
        format!("#{}", proof_manifest.issue),
    );
    evidence.metadata.insert(
        "kernel_family".to_owned(),
        proof_manifest.kernel_family.as_str().to_owned(),
    );
    evidence.metadata.insert(
        "required_proof_facts".to_owned(),
        proof_manifest.required_fact_csv(),
    );
    for requirement in &proof_manifest.required_facts {
        evidence.metadata.insert(
            ay_lra_proof_fact_metadata_key(requirement.fact),
            requirement.lemma_id.to_owned(),
        );
    }
    evidence.metadata.insert(
        "required_certificate_dependencies".to_owned(),
        proof_manifest.required_certificate_csv(),
    );
    evidence.metadata.insert(
        "future_proof_status".to_owned(),
        ay_lra_manifest_future_proof_status(proof_manifest),
    );
    evidence.metadata.insert(
        "product_gate_fields".to_owned(),
        proof_manifest.product_gate.required_parent_gates.join(","),
    );
    evidence.metadata.insert(
        "trust_ir_source_identity".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_IDENTITY.to_owned(),
    );
    evidence.metadata.insert(
        "source_policy".to_owned(),
        "approved_private_source".to_owned(),
    );
    evidence.metadata.insert(
        "trust_cg_source_lock".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_TRUST_CG_SOURCE_LOCK.to_owned(),
    );
    evidence.metadata.insert(
        "trust_ir_source_lock".to_owned(),
        AY_LRA_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_LOCK.to_owned(),
    );
    evidence
}

fn ay_lra_affected_row_batch_proof_consumption_evidence(
    artifact: &ArtifactManifestV1,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
    product_gate: AYLraProductGateEvidence,
) -> AYLraProofConsumptionEvidence {
    let mut facts = BTreeMap::new();
    for requirement in &proof_manifest.required_facts {
        facts.insert(requirement.fact, AYLraEvidenceAvailability::Available);
    }
    for requirement in &proof_manifest.future_facts {
        facts.insert(requirement.fact, AYLraEvidenceAvailability::Future);
    }

    let mut certificates = BTreeMap::new();
    for dependency in &proof_manifest.certificate_dependencies {
        certificates.insert(
            dependency.id.to_owned(),
            match dependency.availability {
                AYLraRequirementAvailability::RequiredForAdmission => {
                    AYLraEvidenceAvailability::Available
                }
                AYLraRequirementAvailability::MissingFuture => AYLraEvidenceAvailability::Future,
            },
        );
    }

    AYLraProofConsumptionEvidence {
        proof_evidence: Some(ay_lra_affected_row_batch_verified_evidence(
            artifact,
            proof_manifest,
        )),
        facts,
        certificates,
        basis_epoch: AYLraBasisEpochEvidence {
            current_epoch: artifact.invalidation.generation,
            expected_epoch: artifact.invalidation.generation,
        },
        replay: AYLraReplayComparison {
            manifest_checksum: artifact.checksum(),
            replay_root_sha256: product_gate.replay_identity_sha256.clone(),
            generic_behavior_sha256: AY_LRA_CANONICAL_SHA256.to_owned(),
            specialized_behavior_sha256: AY_LRA_CANONICAL_SHA256.to_owned(),
            reference_behavior_sha256: AY_LRA_CANONICAL_SHA256.to_owned(),
        },
        product_gate,
    }
}

fn ay_lra_basis_proof_consumption_evidence(
    artifact: &ArtifactManifestV1,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
    product_gate: AYLraProductGateEvidence,
) -> AYLraProofConsumptionEvidence {
    let mut facts = BTreeMap::new();
    for requirement in &proof_manifest.required_facts {
        facts.insert(requirement.fact, AYLraEvidenceAvailability::Available);
    }
    for requirement in &proof_manifest.future_facts {
        facts.insert(requirement.fact, AYLraEvidenceAvailability::Future);
    }

    let mut certificates = BTreeMap::new();
    for dependency in &proof_manifest.certificate_dependencies {
        certificates.insert(
            dependency.id.to_owned(),
            match dependency.availability {
                AYLraRequirementAvailability::RequiredForAdmission => {
                    AYLraEvidenceAvailability::Available
                }
                AYLraRequirementAvailability::MissingFuture => AYLraEvidenceAvailability::Future,
            },
        );
    }

    AYLraProofConsumptionEvidence {
        proof_evidence: Some(ay_lra_basis_verified_evidence(artifact, proof_manifest)),
        facts,
        certificates,
        basis_epoch: AYLraBasisEpochEvidence {
            current_epoch: artifact.invalidation.generation,
            expected_epoch: artifact.invalidation.generation,
        },
        replay: AYLraReplayComparison {
            manifest_checksum: artifact.checksum(),
            replay_root_sha256: product_gate.replay_identity_sha256.clone(),
            generic_behavior_sha256: AY_LRA_CANONICAL_SHA256.to_owned(),
            specialized_behavior_sha256: AY_LRA_CANONICAL_SHA256.to_owned(),
            reference_behavior_sha256: AY_LRA_CANONICAL_SHA256.to_owned(),
        },
        product_gate,
    }
}

fn artifact_checksum_as_diagnostic_sha256(checksum: ArtifactChecksum) -> String {
    format!("sha256:{:064x}", checksum.get())
}

fn attach_rewrite_admission_metadata(
    input: &mut NativeInstallGateInput,
    record: &RewriteAdmissionRecord,
) {
    let proof = input
        .proof_evidence
        .as_mut()
        .expect("proof-guided rewrite fixture has proof evidence");
    proof.summary.metadata.insert(
        "rewrite_admission_schema".to_owned(),
        record.schema.to_owned(),
    );
    proof.summary.metadata.insert(
        "rewrite_admission_record_checksum".to_owned(),
        record.record_checksum.to_owned(),
    );
    proof.summary.metadata.insert(
        "rewrite_admission_disposition".to_owned(),
        record.disposition.as_str().to_owned(),
    );
    if let Some(rejection) = record.rejection {
        proof.summary.metadata.insert(
            "rewrite_admission_rejection".to_owned(),
            rejection.as_str().to_owned(),
        );
    }
}

fn assert_no_admission_handle(result: &ConsumerAdmissionPublicationResult) {
    assert!(!result.has_any_handle());
    assert_eq!(result.useful_native_delta, 0);
}

fn consumer_publication_attempt(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    current: &NativeInstallGateRevalidationInput,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> ConsumerAdmissionPublicationResult {
    if packet.consumer == "ty" {
        AdmissionBackedTySlot::default().activate(packet, expected_packet_hash, current, evidence)
    } else {
        AdmissionBackedAYRegistry::default().insert(packet, expected_packet_hash, current, evidence)
    }
}

fn consumer_publication_attempt_with_control_plane(
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    decision: &ControlPlaneDecision,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
) -> ConsumerAdmissionPublicationResult {
    let decision =
        consumer_admission_with_control_plane(packet, expected_packet_hash, decision, evidence);
    let mut result = ConsumerAdmissionPublicationResult::from_decision(&decision);
    if decision.actions.ay_registry_insert {
        result.registry_key = Some(format!("ay:{}", packet.artifact.artifact_id));
        result.callable_handle = Some(format!(
            "callable:{}",
            packet.artifact.native_payload_sha256
        ));
    }
    if decision.actions.ty_native_activate {
        result.native_handle = Some(format!(
            "ty-native:{}",
            packet.artifact.native_payload_sha256
        ));
    }
    result
}

fn end_to_end_input_for_consumer(consumer: &str) -> NativeInstallGateInput {
    if consumer == "ty" {
        ty_prework_input()
    } else {
        activation_input("ay", NativeInstallGateSurface::AYRegistry)
    }
}

fn assert_control_plane_bridge_non_public_fixture(
    name: &str,
    packet: &NativeInstallGatePacket,
    decision: &ControlPlaneDecision,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
    expected_disposition: NativeInstallGateDisposition,
    expected_code: NativeInstallGateRejectionCode,
    expect_runtime_rejection: bool,
) {
    if expect_runtime_rejection {
        let current = install_gate_revalidation_with_control_plane(packet, decision);
        let runtime_event =
            native_install_gate_runtime_telemetry(packet, Some(packet.packet_hash), &current, true);
        assert_eq!(runtime_event.disposition, expected_disposition, "{name}");
        assert_eq!(runtime_event.rejection_code, Some(expected_code), "{name}");
        assert_eq!(runtime_event.useful_native_delta, 0, "{name}");
        assert_blocked(runtime_event.actions);
        assert!(
            !runtime_event.actions.expose_callable
                && !runtime_event.actions.typed_symbol_lookup
                && !runtime_event.actions.insert_installable_cache
                && !runtime_event.actions.accept_installable_cache_hit
                && !runtime_event.actions.release_installable
                && !runtime_event.actions.ay_registry_insert
                && !runtime_event.actions.ty_native_activate
                && !runtime_event.actions.useful_native_eligible,
            "{name} runtime path must stay non-public"
        );
    }

    let admission =
        consumer_admission_with_control_plane(packet, Some(packet.packet_hash), decision, evidence);
    assert_eq!(admission.disposition, expected_disposition, "{name}");
    assert_eq!(admission.rejection_code, Some(expected_code), "{name}");
    assert_eq!(
        admission.install_authority,
        NativeInstallGateAuthority::None,
        "{name}"
    );
    assert_blocked(admission.actions);
    assert!(
        !admission.actions.expose_callable
            && !admission.actions.typed_symbol_lookup
            && !admission.actions.insert_installable_cache
            && !admission.actions.accept_installable_cache_hit
            && !admission.actions.release_installable
            && !admission.actions.ay_registry_insert
            && !admission.actions.ty_native_activate
            && !admission.actions.useful_native_eligible,
        "{name} admission path must stay non-public"
    );
    assert_eq!(admission.telemetry.useful_native_delta, 0, "{name}");
    assert!(
        admission
            .telemetry
            .admission_evidence_sha256
            .as_deref()
            .is_some_and(|hash| hash.starts_with("sha256:")),
        "{name}"
    );

    let publication = consumer_publication_attempt_with_control_plane(
        packet,
        Some(packet.packet_hash),
        decision,
        evidence,
    );
    assert_eq!(publication.disposition, expected_disposition, "{name}");
    assert_eq!(publication.rejection_code, Some(expected_code), "{name}");
    assert_no_admission_handle(&publication);
}

fn assert_end_to_end_non_installable_fixture(
    name: &str,
    input: NativeInstallGateInput,
    expected_disposition: NativeInstallGateDisposition,
    expected_code: NativeInstallGateRejectionCode,
) {
    let packet = validate_native_install_gate(&input);
    assert_non_installable_fixture_packet(name, &packet, expected_disposition, expected_code);

    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let runtime_event =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &current, true);
    assert_eq!(runtime_event.disposition, expected_disposition, "{name}");
    assert_eq!(runtime_event.rejection_code, Some(expected_code), "{name}");
    assert_eq!(runtime_event.useful_native_delta, 0, "{name}");
    assert_blocked(runtime_event.actions);

    let evidence = consumer_admission_evidence(&packet, &current);
    let admission = native_install_gate_consumer_admission(
        &packet,
        Some(packet.packet_hash),
        &current,
        &evidence,
    );
    assert_eq!(admission.disposition, expected_disposition, "{name}");
    assert_eq!(admission.rejection_code, Some(expected_code), "{name}");
    assert_eq!(
        admission.install_authority,
        NativeInstallGateAuthority::None,
        "{name}"
    );
    assert_blocked(admission.actions);
    assert_eq!(
        admission.telemetry.disposition, expected_disposition,
        "{name}"
    );
    assert_eq!(
        admission.telemetry.rejection_code,
        Some(expected_code),
        "{name}"
    );
    assert_eq!(admission.telemetry.useful_native_delta, 0, "{name}");
    assert!(
        admission
            .telemetry
            .admission_evidence_sha256
            .as_deref()
            .is_some_and(|hash| hash.starts_with("sha256:")),
        "{name}"
    );

    let publication =
        consumer_publication_attempt(&packet, Some(packet.packet_hash), &current, &evidence);
    assert_eq!(publication.disposition, expected_disposition, "{name}");
    assert_eq!(publication.rejection_code, Some(expected_code), "{name}");
    assert_no_admission_handle(&publication);
}

fn assert_product_adapter_bridge_non_public_fixture(
    name: &str,
    packet: &NativeInstallGatePacket,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
    control: JitEverywhereControlPlane,
    expected_disposition: NativeInstallGateDisposition,
    expected_code: NativeInstallGateRejectionCode,
) {
    let current = NativeInstallGateRevalidationInput::from_packet(packet);
    assert_product_adapter_bridge_current_non_public_fixture(
        name,
        packet,
        &current,
        evidence,
        control,
        expected_disposition,
        expected_code,
    );
}

fn assert_product_adapter_bridge_current_non_public_fixture(
    name: &str,
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
    evidence: &NativeInstallGateConsumerAdmissionEvidence,
    mut control: JitEverywhereControlPlane,
    expected_disposition: NativeInstallGateDisposition,
    expected_code: NativeInstallGateRejectionCode,
) {
    let candidate = control_plane_candidate_for_packet(packet, ControlPlaneMode::CanaryInstallable);
    control.record_existing_product_publication(&candidate);
    assert!(
        control
            .publication_state()
            .has_callable(&candidate.artifact_sha256),
        "{name}"
    );
    assert!(
        control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256),
        "{name}"
    );
    match packet.consumer.as_str() {
        "ay" => assert!(
            control
                .publication_state()
                .has_ay_registry_entry(&candidate.artifact_sha256),
            "{name}"
        ),
        "ty" => assert!(
            control
                .publication_state()
                .has_ty_native_entry(&candidate.artifact_sha256),
            "{name}"
        ),
        _ => panic!("{name}: unsupported consumer fixture"),
    }

    let bridge = control.route_consumer_admission_product_adapter_with_current(
        &candidate,
        gate_accepted(),
        packet,
        Some(packet.packet_hash),
        current,
        evidence,
    );

    assert_eq!(
        bridge.consumer_admission.disposition, expected_disposition,
        "{name}"
    );
    assert_eq!(
        bridge.consumer_admission.rejection_code,
        Some(expected_code),
        "{name}"
    );
    assert_eq!(
        bridge.consumer_admission.install_authority,
        NativeInstallGateAuthority::None,
        "{name}"
    );
    assert_blocked(bridge.consumer_admission.actions);
    assert!(!bridge.consumer_allows_ay_registry, "{name}");
    assert!(!bridge.consumer_allows_ty_activation, "{name}");
    assert!(
        bridge.publication_blocked_without_product_authority(),
        "{name}"
    );
    assert!(!bridge.publish_ay_registry_entry, "{name}");
    assert!(!bridge.activate_ty_native_handle, "{name}");
    assert!(!bridge.expose_callable_handle, "{name}");
    assert_eq!(bridge.useful_native_delta, 0, "{name}");
    assert_eq!(
        bridge.consumer_admission.telemetry.disposition, expected_disposition,
        "{name}"
    );
    assert_eq!(
        bridge.consumer_admission.telemetry.rejection_code,
        Some(expected_code),
        "{name}"
    );
    assert_eq!(
        bridge.consumer_admission.telemetry.useful_native_delta, 0,
        "{name}"
    );
    assert!(
        bridge
            .consumer_admission
            .telemetry
            .admission_evidence_sha256
            .as_deref()
            .is_some_and(|hash| hash.starts_with("sha256:")),
        "{name}"
    );
    assert_eq!(
        bridge.call_time_revalidation.useful_native_delta, 0,
        "{name}"
    );
    let expected_runtime_outcome =
        expected_product_adapter_fixture_runtime_outcome(expected_code, &bridge);
    let expected_runtime_rejection =
        expected_product_adapter_fixture_runtime_rejection(expected_code, expected_runtime_outcome);
    assert_eq!(
        bridge.call_time_revalidation.runtime_outcome, expected_runtime_outcome,
        "{name}"
    );
    assert_eq!(
        bridge.call_time_revalidation.rejection_code, expected_runtime_rejection,
        "{name}"
    );
    assert!(bridge.product_adapter.denied_without_product_authority());
    assert_eq!(bridge.product_adapter.callable_handle_id, None, "{name}");
    assert_eq!(bridge.product_adapter.native_handle_id, None, "{name}");
    assert!(
        !bridge.product_adapter.installable_cache_hit_accepted,
        "{name}"
    );
    assert_eq!(bridge.product_adapter.useful_native_delta, 0, "{name}");
    assert_eq!(
        bridge
            .product_adapter
            .retained_replay_root_sha256
            .as_deref(),
        Some(candidate.replay_root_sha256.as_str()),
        "{name}"
    );
    assert_eq!(
        bridge.product_adapter.retained_telemetry_key.as_deref(),
        Some(candidate.telemetry_key.as_str()),
        "{name}"
    );
    assert_eq!(
        bridge.product_adapter.telemetry.record_sha256,
        bridge.product_adapter.telemetry.canonical_record_sha256(),
        "{name}"
    );
    assert_eq!(
        bridge.product_adapter.telemetry.product_call_status,
        Some(bridge.call_status.status),
        "{name}"
    );
    assert_eq!(
        bridge
            .product_adapter
            .telemetry
            .product_call_status_record_sha256
            .as_deref(),
        Some(bridge.call_status.record_sha256.as_str()),
        "{name}"
    );
    assert!(
        bridge
            .product_adapter
            .telemetry
            .valid_for_product_call_status_row(&bridge.call_status),
        "{name}"
    );
    assert_product_call_status_row(
        name,
        &bridge,
        &candidate,
        expected_product_adapter_fixture_call_status(
            expected_disposition,
            expected_runtime_outcome,
        ),
        expected_disposition,
        Some(expected_code),
        expected_runtime_outcome,
        expected_runtime_rejection,
    );
    assert!(
        !control
            .publication_state()
            .has_callable(&candidate.artifact_sha256),
        "{name}"
    );
    assert!(
        !control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256),
        "{name}"
    );
    assert!(
        !control
            .publication_state()
            .has_ay_registry_entry(&candidate.artifact_sha256),
        "{name}"
    );
    assert!(
        !control
            .publication_state()
            .has_ty_native_entry(&candidate.artifact_sha256),
        "{name}"
    );
}

fn expected_product_adapter_fixture_runtime_outcome(
    expected_code: NativeInstallGateRejectionCode,
    bridge: &ControlPlaneConsumerAdmissionProductDecision,
) -> NativeInstallGateRuntimeOutcome {
    match expected_code {
        NativeInstallGateRejectionCode::StaleInvalidation
        | NativeInstallGateRejectionCode::ProofStaleEvidence => {
            NativeInstallGateRuntimeOutcome::StaleDeopt
        }
        NativeInstallGateRejectionCode::RevokedArtifact => {
            NativeInstallGateRuntimeOutcome::RevokedDeopt
        }
        NativeInstallGateRejectionCode::KillSwitchActive => {
            NativeInstallGateRuntimeOutcome::KillSwitchDeopt
        }
        NativeInstallGateRejectionCode::PacketHashMismatch
        | NativeInstallGateRejectionCode::EvidenceBindingMismatch
        | NativeInstallGateRejectionCode::ReplayIdentityMismatch
        | NativeInstallGateRejectionCode::TelemetryMismatch
        | NativeInstallGateRejectionCode::ManifestChecksumMismatch
        | NativeInstallGateRejectionCode::ArtifactIdentityMismatch
        | NativeInstallGateRejectionCode::TargetMismatch
        | NativeInstallGateRejectionCode::AbiMismatch
        | NativeInstallGateRejectionCode::LayoutMismatch => {
            NativeInstallGateRuntimeOutcome::InvalidatedDeopt
        }
        _ if bridge.call_time_revalidation.rejection_code.is_none()
            && bridge.call_time_revalidation.disposition.is_installable() =>
        {
            NativeInstallGateRuntimeOutcome::BaselineFallback
        }
        _ => NativeInstallGateRuntimeOutcome::RejectedDeopt,
    }
}

fn expected_product_adapter_fixture_runtime_rejection(
    expected_code: NativeInstallGateRejectionCode,
    expected_runtime_outcome: NativeInstallGateRuntimeOutcome,
) -> Option<NativeInstallGateRejectionCode> {
    match expected_runtime_outcome {
        NativeInstallGateRuntimeOutcome::NativeUseful
        | NativeInstallGateRuntimeOutcome::BaselineFallback
        | NativeInstallGateRuntimeOutcome::MetadataOnly => None,
        _ => Some(expected_code),
    }
}

fn expected_product_adapter_fixture_call_status(
    expected_disposition: NativeInstallGateDisposition,
    expected_runtime_outcome: NativeInstallGateRuntimeOutcome,
) -> ControlPlaneProductCallStatus {
    match expected_runtime_outcome {
        NativeInstallGateRuntimeOutcome::StaleDeopt => ControlPlaneProductCallStatus::StaleDeopt,
        NativeInstallGateRuntimeOutcome::RevokedDeopt => {
            ControlPlaneProductCallStatus::RevokedDeopt
        }
        NativeInstallGateRuntimeOutcome::KillSwitchDeopt => {
            ControlPlaneProductCallStatus::KillSwitchDeopt
        }
        NativeInstallGateRuntimeOutcome::InvalidatedDeopt => {
            ControlPlaneProductCallStatus::InvalidatedDeopt
        }
        NativeInstallGateRuntimeOutcome::RejectedDeopt if expected_disposition.is_installable() => {
            ControlPlaneProductCallStatus::RejectedDeopt
        }
        NativeInstallGateRuntimeOutcome::NativeUseful
        | NativeInstallGateRuntimeOutcome::BaselineFallback
        | NativeInstallGateRuntimeOutcome::MetadataOnly
            if expected_disposition.is_installable() =>
        {
            ControlPlaneProductCallStatus::AcceptedPendingProductGate
        }
        _ => ControlPlaneProductCallStatus::ConsumerRejected,
    }
}

#[allow(clippy::too_many_arguments)] // Assertions enumerate the complete product-gate status row.
fn assert_product_call_status_row(
    name: &str,
    bridge: &ControlPlaneConsumerAdmissionProductDecision,
    candidate: &ControlPlaneCandidate,
    expected_status: ControlPlaneProductCallStatus,
    expected_consumer_disposition: NativeInstallGateDisposition,
    expected_consumer_rejection: Option<NativeInstallGateRejectionCode>,
    expected_runtime_outcome: NativeInstallGateRuntimeOutcome,
    expected_runtime_rejection: Option<NativeInstallGateRejectionCode>,
) {
    assert_eq!(
        bridge.call_status.schema, JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA,
        "{name}"
    );
    assert_eq!(
        bridge.call_status.schema_version, JIT_EVERYWHERE_PRODUCT_CALL_STATUS_SCHEMA_VERSION,
        "{name}"
    );
    assert_eq!(bridge.call_status.issue, 748, "{name}");
    assert_eq!(
        bridge.call_status.candidate_key_sha256, candidate.candidate_key_sha256,
        "{name}"
    );
    assert_eq!(
        bridge.call_status.artifact_sha256, candidate.artifact_sha256,
        "{name}"
    );
    assert_eq!(bridge.call_status.consumer, candidate.consumer, "{name}");
    assert_eq!(bridge.call_status.family, candidate.family, "{name}");
    assert_eq!(
        bridge.call_status.route, bridge.control_plane.route,
        "{name}"
    );
    assert_eq!(
        bridge.call_status.reason, bridge.control_plane.reason,
        "{name}"
    );
    assert_eq!(bridge.call_status.status, expected_status, "{name}");
    assert_eq!(
        bridge.call_status.consumer_disposition, expected_consumer_disposition,
        "{name}"
    );
    assert_eq!(
        bridge.call_status.consumer_rejection_code, expected_consumer_rejection,
        "{name}"
    );
    assert_eq!(
        bridge.call_status.runtime_outcome, expected_runtime_outcome,
        "{name}"
    );
    assert_eq!(
        bridge.call_status.runtime_rejection_code, expected_runtime_rejection,
        "{name}"
    );
    assert!(bridge.call_status.product_publication_denied, "{name}");
    assert!(!bridge.call_status.publish_ay_registry_entry, "{name}");
    assert!(!bridge.call_status.activate_ty_native_handle, "{name}");
    assert!(!bridge.call_status.expose_callable_handle, "{name}");
    assert_eq!(bridge.call_status.useful_native_delta, 0, "{name}");
    assert!(bridge.call_status.deopt_ready, "{name}");
    assert!(bridge.call_status.fail_closed_deopt_ready(), "{name}");
    assert_eq!(
        bridge.call_status.record_sha256,
        bridge.call_status.canonical_record_sha256(),
        "{name}"
    );
}

fn assert_canary_product_precheck_call_status_row(
    name: &str,
    bridge: &ControlPlaneConsumerAdmissionProductDecision,
    candidate: &ControlPlaneCandidate,
) {
    assert_product_call_status_row(
        name,
        bridge,
        candidate,
        ControlPlaneProductCallStatus::AcceptedPendingProductGate,
        NativeInstallGateDisposition::Installable,
        None,
        NativeInstallGateRuntimeOutcome::BaselineFallback,
        None,
    );
}

fn push_end_to_end_non_installable_fixtures(
    fixtures: &mut Vec<(
        String,
        NativeInstallGateInput,
        NativeInstallGateDisposition,
        NativeInstallGateRejectionCode,
    )>,
    consumer: &str,
) {
    let mut missing_manifest = end_to_end_input_for_consumer(consumer);
    missing_manifest.manifest = None;
    fixtures.push((
        format!("{consumer}_missing_manifest"),
        missing_manifest,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingManifest,
    ));

    let mut missing_abi_checksum = end_to_end_input_for_consumer(consumer);
    missing_abi_checksum
        .manifest_reference
        .as_mut()
        .expect("test input has manifest reference")
        .abi_checksum = ArtifactChecksum::new(0);
    fixtures.push((
        format!("{consumer}_missing_abi_checksum"),
        missing_abi_checksum,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::AbiMismatch,
    ));

    let mut layout_mismatch = end_to_end_input_for_consumer(consumer);
    layout_mismatch
        .layout_evidence
        .as_mut()
        .expect("test input has layout evidence")
        .layout_checksum = ArtifactChecksum::new(99);
    fixtures.push((
        format!("{consumer}_layout_mismatch"),
        layout_mismatch,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::LayoutMismatch,
    ));

    let mut missing_proof = end_to_end_input_for_consumer(consumer);
    missing_proof.proof_evidence = None;
    fixtures.push((
        format!("{consumer}_missing_proof"),
        missing_proof,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    ));

    let mut verifier_failure = end_to_end_input_for_consumer(consumer);
    set_rejected_proof(
        &mut verifier_failure,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    );
    fixtures.push((
        format!("{consumer}_verifier_failure"),
        verifier_failure,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofVerifierFailure,
    ));

    let mut timeout = end_to_end_input_for_consumer(consumer);
    set_rejected_proof(
        &mut timeout,
        ProofEvidenceVerdict::Timeout,
        ProofEvidenceRejectionCode::Timeout,
    );
    fixtures.push((
        format!("{consumer}_proof_timeout"),
        timeout,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofTimeout,
    ));

    let mut unknown = end_to_end_input_for_consumer(consumer);
    set_rejected_proof(
        &mut unknown,
        ProofEvidenceVerdict::Unknown,
        ProofEvidenceRejectionCode::Unknown,
    );
    fixtures.push((
        format!("{consumer}_proof_unknown"),
        unknown,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofUnknown,
    ));

    let mut solver_error = end_to_end_input_for_consumer(consumer);
    set_rejected_proof(
        &mut solver_error,
        ProofEvidenceVerdict::SolverError,
        ProofEvidenceRejectionCode::SolverError,
    );
    fixtures.push((
        format!("{consumer}_proof_solver_error"),
        solver_error,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofSolverError,
    ));

    let mut unsupported_route = end_to_end_input_for_consumer(consumer);
    set_rejected_proof(
        &mut unsupported_route,
        ProofEvidenceVerdict::UnsupportedRoute,
        ProofEvidenceRejectionCode::UnsupportedRoute,
    );
    fixtures.push((
        format!("{consumer}_proof_unsupported_route"),
        unsupported_route,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofUnsupportedRoute,
    ));

    let mut malformed_report = end_to_end_input_for_consumer(consumer);
    set_rejected_proof(
        &mut malformed_report,
        ProofEvidenceVerdict::MalformedReport,
        ProofEvidenceRejectionCode::MalformedReport,
    );
    fixtures.push((
        format!("{consumer}_proof_malformed_report"),
        malformed_report,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMalformedReport,
    ));

    let mut missing_required_fields = end_to_end_input_for_consumer(consumer);
    set_rejected_proof(
        &mut missing_required_fields,
        ProofEvidenceVerdict::MissingRequiredFields,
        ProofEvidenceRejectionCode::MissingRequiredFields,
    );
    fixtures.push((
        format!("{consumer}_proof_missing_required_fields"),
        missing_required_fields,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingRequiredFields,
    ));

    let mut unknown_solver_error = end_to_end_input_for_consumer(consumer);
    set_rejected_proof(
        &mut unknown_solver_error,
        ProofEvidenceVerdict::UnknownSolverError,
        ProofEvidenceRejectionCode::UnknownSolverError,
    );
    fixtures.push((
        format!("{consumer}_proof_unknown_solver_error"),
        unknown_solver_error,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofUnknown,
    ));

    let mut stale_install = end_to_end_input_for_consumer(consumer);
    stale_install.current_generation += 1;
    fixtures.push((
        format!("{consumer}_stale_install"),
        stale_install,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::StaleInvalidation,
    ));

    let mut missing_telemetry = end_to_end_input_for_consumer(consumer);
    missing_telemetry.telemetry = None;
    fixtures.push((
        format!("{consumer}_missing_telemetry"),
        missing_telemetry,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingTelemetry,
    ));

    let mut telemetry_hash_mismatch = end_to_end_input_for_consumer(consumer);
    telemetry_hash_mismatch
        .telemetry
        .as_mut()
        .expect("test input has telemetry")
        .record_sha256 = "sha256:tampered-telemetry-record".to_owned();
    fixtures.push((
        format!("{consumer}_telemetry_hash_mismatch"),
        telemetry_hash_mismatch,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::TelemetryMismatch,
    ));

    let mut profile_only = end_to_end_input_for_consumer(consumer);
    profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;
    fixtures.push((
        format!("{consumer}_profile_only"),
        profile_only,
        NativeInstallGateDisposition::ProfileOnly,
        NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
    ));

    let mut replay_only = end_to_end_input_for_consumer(consumer);
    replay_only.candidate_disposition = NativeInstallGateDisposition::ReplayOnly;
    fixtures.push((
        format!("{consumer}_replay_only"),
        replay_only,
        NativeInstallGateDisposition::ReplayOnly,
        NativeInstallGateRejectionCode::ReplayOnlyNonInstallable,
    ));

    let mut shadow_only = end_to_end_input_for_consumer(consumer);
    shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
    fixtures.push((
        format!("{consumer}_shadow_only"),
        shadow_only,
        NativeInstallGateDisposition::ShadowOnly,
        NativeInstallGateRejectionCode::ShadowOnlyNonInstallable,
    ));

    let mut revoked = end_to_end_input_for_consumer(consumer);
    revoked.revoked = true;
    fixtures.push((
        format!("{consumer}_revoked"),
        revoked,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::RevokedArtifact,
    ));

    let mut kill_switch = end_to_end_input_for_consumer(consumer);
    kill_switch.deny_control = Some(scoped_deny_control(
        &kill_switch,
        NativeInstallGateDenyScope::Global,
        NativeInstallGateDenyReason::KillSwitch,
    ));
    fixtures.push((
        format!("{consumer}_kill_switch"),
        kill_switch,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::KillSwitchActive,
    ));
}

#[test]
fn installable_candidate_authorizes_only_the_requested_surface() {
    let packet = validate_native_install_gate(&installable_input());

    assert_eq!(packet.schema, NATIVE_INSTALL_GATE_PACKET_SCHEMA);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.is_installable());
    assert!(packet.actions.expose_callable);
    assert!(packet.actions.typed_symbol_lookup);
    assert!(!packet.actions.insert_installable_cache);
    assert!(!packet.actions.release_installable);
    assert!(!packet.actions.ay_registry_insert);
    assert!(!packet.actions.ty_native_activate);
    assert!(packet.actions.useful_native_eligible);
}

#[test]
fn complete_manifest_fields_are_bound_in_installable_packet() {
    let input = installable_input();
    let expected = input.expected.clone();
    let payload = input.payload_identity.clone();
    let packet = validate_native_install_gate(&input);

    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert_eq!(packet.artifact.artifact_id, expected.artifact_id);
    assert_eq!(
        packet.artifact.manifest_checksum,
        expected.manifest_checksum
    );
    assert_eq!(packet.artifact.source_sha256, payload.source_sha256);
    assert_eq!(packet.artifact.trust_ir_sha256, payload.trust_ir_sha256);
    assert_eq!(
        packet.artifact.native_payload_sha256,
        payload.native_payload_sha256
    );
    assert_eq!(packet.artifact.target_checksum, expected.target_checksum);
    assert_eq!(packet.artifact.abi_checksum, expected.abi_checksum);
    assert_eq!(packet.artifact.layout_checksum, expected.layout_checksum);
    assert_eq!(
        packet.artifact.proof_policy_checksum,
        expected.proof_policy_checksum
    );
    assert_eq!(
        packet.artifact.invalidation_checksum,
        expected.invalidation_checksum
    );
    assert_eq!(
        packet.validation.proof_report_sha256.as_deref(),
        Some("proof-report-sha256")
    );
    assert!(
        packet
            .validation
            .layout_evidence_sha256
            .as_deref()
            .expect("layout evidence hash is present")
            .starts_with("sha256:")
    );
    assert_eq!(
        packet.validation.layout_wrapper_identity.as_deref(),
        Some("wrapper.v1")
    );
    assert_eq!(
        packet.validation.layout_validation_provenance.as_deref(),
        Some("trust-cg.generic.layout_adapter.v1")
    );
    assert_eq!(
        packet.validation.layout_invalidation_checksum,
        Some(expected.invalidation_checksum)
    );
    assert_eq!(
        packet.validation.layout_generation_domains,
        vec!["native_generation".to_owned()]
    );
    assert!(
        packet
            .replay_binding
            .replay_root_sha256
            .starts_with("sha256:")
    );
    assert_eq!(packet.consumer_verdict.consumer, "ay");
    assert_eq!(packet.consumer_verdict.consumer_mode, "solver-kernel");
    assert!(
        packet
            .consumer_verdict
            .verdict_sha256
            .starts_with("sha256:")
    );
    assert_eq!(
        validate_native_install_gate_packet(&packet, Some(packet.packet_hash)).disposition,
        NativeInstallGateDisposition::Installable
    );
}

#[test]
fn trust_ir_hardware_vector_contract_metadata_is_bound_in_installable_packet() {
    let mut input = installable_input();
    let manifest = input.manifest.take().expect("installable manifest");
    input.expected = NativeInstallGateExpectedBindings::from_manifest(&manifest);
    input.manifest_reference = Some(ArtifactManifestReference::from_manifest(&manifest));
    input.current_invalidation_checksum = input.expected.invalidation_checksum;
    input.artifact_generation = input.expected.current_generation;
    input.current_generation = input.expected.current_generation;
    input.manifest = Some(manifest);
    refresh_gate_identity(&mut input);

    let packet = validate_native_install_gate(&input);

    assert_eq!(
        packet
            .artifact
            .manifest_metadata
            .get(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA_KEY)
            .map(String::as_str),
        Some(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SCHEMA)
    );
    assert_eq!(
        packet
            .artifact
            .manifest_metadata
            .get(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY),
        Some(&trust_ir_hardware_vector_contract_manifest_row_count().to_string())
    );
    let expected_manifest_sha256 = trust_ir_hardware_vector_contract_manifest_sha256();
    assert_eq!(
        packet
            .artifact
            .manifest_metadata
            .get(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY)
            .map(String::as_str),
        Some(expected_manifest_sha256.as_str())
    );
    assert_eq!(packet.packet_hash, native_install_gate_packet_hash(&packet));
    assert_eq!(
        validate_native_install_gate_packet(&packet, Some(packet.packet_hash)).disposition,
        NativeInstallGateDisposition::Installable
    );
}

#[test]
fn host_jit_target_feature_profile_is_bound_in_installable_packet_hash() {
    let mut input = installable_input();
    let target =
        TargetDescriptor::for_trust_cg_target(Target::X86_64, TargetOperatingSystem::host())
            .with_cpu("host")
            .with_features(["sse2", "sse4.2"]);
    let abi = AbiDescriptor::for_trust_cg_target_os(Target::X86_64, TargetOperatingSystem::host());
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let proof_policy = ProofPolicy::require_certificates(["trust_cg_verify"]);
    let invalidation = InvalidationKey::new(
        "source-sha",
        "compiler-sha",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        7,
    );
    let mut manifest = ArtifactManifestV1::new(
        "artifact.installable",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: "entry".to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: SymbolSignature::extern_c(
            vec![AbiValue::new(AbiValueKind::I64)],
            vec![AbiValue::new(AbiValueKind::I64)],
        ),
        offset_bytes: Some(0),
        checksum: None,
    });
    input.expected = NativeInstallGateExpectedBindings::from_manifest(&manifest);
    input.manifest_reference = Some(ArtifactManifestReference::from_manifest(&manifest));
    input.current_invalidation_checksum = input.expected.invalidation_checksum;
    input.artifact_generation = input.expected.current_generation;
    input.current_generation = input.expected.current_generation;
    input.layout_evidence = Some(generic_layout_evidence(&manifest));
    input.proof_evidence = Some(verified_proof(&manifest));
    input.manifest = Some(manifest);
    refresh_gate_identity(&mut input);

    let packet = validate_native_install_gate(&input);

    if cfg!(target_arch = "x86_64") {
        assert_eq!(
            packet
                .artifact
                .manifest_metadata
                .get(HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA_KEY)
                .map(String::as_str),
            Some(HOST_JIT_TARGET_FEATURE_PROFILE_SCHEMA)
        );
        assert_eq!(
            packet
                .artifact
                .manifest_metadata
                .get(HOST_JIT_TARGET_FEATURE_PROFILE_TARGET_TRIPLE_KEY)
                .map(|value| value.starts_with("x86_64-unknown-")),
            Some(true)
        );
        assert_eq!(
            packet
                .artifact
                .manifest_metadata
                .get(HOST_JIT_TARGET_FEATURE_PROFILE_CURRENT_POLICY_KEY)
                .map(String::as_str),
            Some("manifest-target-features")
        );
        assert!(
            packet
                .artifact
                .manifest_metadata
                .get(HOST_JIT_TARGET_FEATURE_PROFILE_SHA256_KEY)
                .expect("profile digest is present")
                .starts_with("sha256:")
        );
    }
    assert_eq!(packet.packet_hash, native_install_gate_packet_hash(&packet));
    assert_eq!(
        validate_native_install_gate_packet(&packet, Some(packet.packet_hash)).disposition,
        NativeInstallGateDisposition::Installable
    );
}

#[test]
fn install_authority_verdict_binds_hash_replay_consumer_and_counter_scope() {
    let input = installable_input();
    let packet = validate_native_install_gate(&input);
    let packet_hash = native_install_gate_packet_hash(&packet);
    let verdict = validate_native_install_gate_verdict(&input);

    assert_eq!(packet.packet_hash, packet_hash);
    assert_eq!(
        packet.requested_authority,
        NativeInstallGateAuthority::CanaryCallable
    );
    assert_eq!(
        verdict.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(verdict.rejection_code, None);
    assert_eq!(
        verdict.requested_authority,
        NativeInstallGateAuthority::CanaryCallable
    );
    assert_eq!(
        verdict.install_authority,
        NativeInstallGateAuthority::CanaryCallable
    );
    assert_eq!(verdict.packet_hash, packet_hash);
    assert_eq!(
        verdict.telemetry_event_id.as_deref(),
        Some("install-event-1")
    );
    assert_eq!(
        verdict.counter_scope,
        "ay:solver-kernel:typed_symbol_lookup:artifact.installable"
    );
    assert_eq!(
        packet
            .telemetry
            .as_ref()
            .expect("packet has telemetry")
            .counter_scope,
        verdict.counter_scope
    );
    assert_eq!(packet.replay_binding, verdict.replay_binding);
    assert_eq!(verdict.replay_binding.packet_hash, packet_hash);
    assert!(
        verdict
            .replay_binding
            .replay_root_sha256
            .starts_with("sha256:")
    );
    assert_eq!(packet.replay_identity, verdict.replay_identity);
    assert_eq!(
        verdict
            .replay_identity
            .as_ref()
            .expect("verdict carries replay identity")
            .replay_root_sha256,
        "sha256:install-replay-root"
    );
    assert_eq!(verdict.consumer_verdict.consumer, "ay");
    assert_eq!(verdict.consumer_verdict.consumer_mode, "solver-kernel");
    assert_eq!(
        verdict.consumer_verdict.surface,
        NativeInstallGateSurface::TypedSymbolLookup
    );
    assert!(
        verdict
            .consumer_verdict
            .verdict_sha256
            .starts_with("sha256:")
    );
    assert_eq!(packet.consumer_verdict, verdict.consumer_verdict);
    assert_eq!(
        validate_native_install_gate_packet(&packet, Some(packet_hash)),
        verdict
    );
}

#[test]
fn native_install_gate_surface_exposes_only_native_successor_shared_primitive_contract() {
    let shared_contract = PETRI_NATIVE_SUCCESSOR_TRUST_MC_CHC_SHARED_PRIMITIVE_CONTRACT_DESCRIPTOR;

    for (surface, expected_contract, expected_reason) in [
        (
            NativeInstallGateSurface::DirectCompileInstall,
            None,
            NativeInstallGateSharedPrimitiveContractReason::GenericInstallBoundary,
        ),
        (
            NativeInstallGateSurface::TypedSymbolLookup,
            None,
            NativeInstallGateSharedPrimitiveContractReason::TypedSymbolLookupBoundary,
        ),
        (
            NativeInstallGateSurface::AsyncPoll,
            None,
            NativeInstallGateSharedPrimitiveContractReason::AsyncMetadataBoundary,
        ),
        (
            NativeInstallGateSurface::CacheInsert,
            None,
            NativeInstallGateSharedPrimitiveContractReason::CacheInsertBoundary,
        ),
        (
            NativeInstallGateSurface::CacheHit,
            None,
            NativeInstallGateSharedPrimitiveContractReason::CacheHitBoundary,
        ),
        (
            NativeInstallGateSurface::ReleaseBundle,
            None,
            NativeInstallGateSharedPrimitiveContractReason::ReleaseMetadataBoundary,
        ),
        (
            NativeInstallGateSurface::AYRegistry,
            None,
            NativeInstallGateSharedPrimitiveContractReason::ProductRegistryBoundary,
        ),
        (
            NativeInstallGateSurface::TyActivation,
            None,
            NativeInstallGateSharedPrimitiveContractReason::ProductActivationBoundary,
        ),
        (
            NativeInstallGateSurface::NativeSuccessor,
            Some(shared_contract),
            NativeInstallGateSharedPrimitiveContractReason::NativeSharedPrimitive,
        ),
    ] {
        assert_eq!(
            surface.shared_primitive_contract(),
            expected_contract,
            "{surface:?} shared primitive contract"
        );
        assert_eq!(
            surface.shared_primitive_contract_reason(),
            expected_reason,
            "{surface:?} shared primitive reason"
        );
        assert!(!expected_reason.as_str().is_empty());
    }

    let packet = validate_native_install_gate(&installable_input());
    assert_eq!(packet.shared_primitive_contract(), None);
    assert_eq!(
        packet.shared_primitive_contract_reason(),
        NativeInstallGateSharedPrimitiveContractReason::TypedSymbolLookupBoundary
    );
}

#[test]
fn data_only_telemetry_replay_identity_binds_packet_without_useful_native_delta() {
    let input = installable_input();
    let packet = validate_native_install_gate(&input);
    let telemetry = packet.telemetry.as_ref().expect("packet has telemetry");
    let replay = packet
        .replay_identity
        .as_ref()
        .expect("packet has replay identity");

    assert_eq!(telemetry.schema, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA);
    assert_eq!(
        telemetry.schema_version,
        NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION
    );
    assert_eq!(
        telemetry.counter_scope,
        "ay:solver-kernel:typed_symbol_lookup:artifact.installable"
    );
    assert_eq!(telemetry.record_sha256, telemetry.canonical_record_sha256());
    assert_eq!(telemetry.useful_native_delta, 0);
    assert_eq!(replay.schema, NATIVE_INSTALL_GATE_REPLAY_SCHEMA);
    assert_eq!(
        replay.schema_version,
        NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION
    );
    assert_eq!(replay.replay_consumer, "ay");
    assert_eq!(replay.replay_family, "solver-kernel");
    assert_eq!(
        replay.replay_record_sha256,
        replay.canonical_record_sha256()
    );
    assert!(packet.actions.useful_native_eligible);

    let mut counters = ConsumerActivationTelemetry::default();
    let result = ConsumerActivationResult::from_gate(&packet);
    counters.record_gate(&result);
    assert_eq!(counters.install_accepted, 1);
    assert_eq!(
        counters.useful_native, 0,
        "data-only install identity must not publish useful-native deltas"
    );
}

#[test]
fn telemetry_replay_identity_fail_closed_on_missing_or_tampered_identity() {
    let mut missing_replay = installable_input();
    missing_replay.replay_identity = None;
    assert_reject(
        missing_replay,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingReplayIdentity,
    );

    let mut wrong_replay_schema = installable_input();
    wrong_replay_schema
        .replay_identity
        .as_mut()
        .expect("test input has replay identity")
        .schema = "trust-cg.future.replay_identity".to_owned();
    assert_reject(
        wrong_replay_schema,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ReplayIdentityMismatch,
    );

    let mut wrong_replay_root = installable_input();
    wrong_replay_root
        .replay_identity
        .as_mut()
        .expect("test input has replay identity")
        .replay_root_sha256 = "sha256:wrong-replay-root".to_owned();
    assert_reject(
        wrong_replay_root,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ReplayIdentityMismatch,
    );

    let mut tampered_replay_hash = installable_input();
    tampered_replay_hash
        .replay_identity
        .as_mut()
        .expect("test input has replay identity")
        .replay_record_sha256 = "sha256:tampered-replay-record".to_owned();
    assert_reject(
        tampered_replay_hash,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ReplayIdentityMismatch,
    );

    let mut wrong_telemetry_schema = installable_input();
    wrong_telemetry_schema
        .telemetry
        .as_mut()
        .expect("test input has telemetry")
        .schema = "trust-cg.future.telemetry".to_owned();
    assert_reject(
        wrong_telemetry_schema,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::TelemetryMismatch,
    );

    let mut tampered_telemetry_hash = installable_input();
    tampered_telemetry_hash
        .telemetry
        .as_mut()
        .expect("test input has telemetry")
        .record_sha256 = "sha256:tampered-telemetry-record".to_owned();
    assert_reject(
        tampered_telemetry_hash,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::TelemetryMismatch,
    );

    let mut premature_useful_native = installable_input();
    let telemetry = premature_useful_native
        .telemetry
        .as_mut()
        .expect("test input has telemetry");
    telemetry.useful_native_delta = 1;
    telemetry.record_sha256 = telemetry.canonical_record_sha256();
    let packet = validate_native_install_gate(&premature_useful_native);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::TelemetryMismatch)
    );
    let packet_telemetry = packet.telemetry.as_ref().expect("packet keeps telemetry");
    assert_eq!(
        packet_telemetry.useful_native_delta, 0,
        "rejected packets must neutralize premature useful-native deltas"
    );
    assert_eq!(
        packet_telemetry.record_sha256,
        packet_telemetry.canonical_record_sha256()
    );
    assert_blocked(packet.actions);
    let verdict = validate_native_install_gate_packet(&packet, Some(packet.packet_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::TelemetryMismatch)
    );
    assert_blocked(verdict.actions);
}

#[test]
fn telemetry_replay_identity_does_not_bypass_existing_gate_checks() {
    let mut missing_proof = installable_input();
    missing_proof.proof_evidence = None;
    assert_reject(
        missing_proof,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut deny = installable_input();
    deny.deny_control = Some(scoped_deny_control(
        &deny,
        NativeInstallGateDenyScope::Global,
        NativeInstallGateDenyReason::KillSwitch,
    ));
    assert_reject(
        deny,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::KillSwitchActive,
    );

    let mut missing_manifest = installable_input();
    missing_manifest.manifest = None;
    assert_reject(
        missing_manifest,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingManifest,
    );
}

#[test]
fn active_callable_authority_is_accepted_when_telemetry_matches() {
    let mut input = installable_input();
    input.requested_authority = NativeInstallGateAuthority::ActiveCallable;
    refresh_gate_identity(&mut input);

    let verdict = validate_native_install_gate_verdict(&input);

    assert_eq!(
        verdict.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(verdict.rejection_code, None);
    assert_eq!(
        verdict.requested_authority,
        NativeInstallGateAuthority::ActiveCallable
    );
    assert_eq!(
        verdict.install_authority,
        NativeInstallGateAuthority::ActiveCallable
    );
    assert!(verdict.actions.typed_symbol_lookup);
    assert!(verdict.actions.useful_native_eligible);
}

#[test]
fn non_callable_requested_authority_rejects_install() {
    let mut input = installable_input();
    input.requested_authority = NativeInstallGateAuthority::ShadowOnly;
    refresh_gate_identity(&mut input);

    let verdict = validate_native_install_gate_verdict(&input);
    let packet = validate_native_install_gate(&input);

    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::InconsistentActionAuthority)
    );
    assert_eq!(
        verdict.requested_authority,
        NativeInstallGateAuthority::ShadowOnly
    );
    assert_eq!(
        packet.requested_authority,
        NativeInstallGateAuthority::ShadowOnly
    );
    assert_eq!(verdict.install_authority, NativeInstallGateAuthority::None);
    assert_blocked(verdict.actions);
}

#[test]
fn packet_integrity_rejects_missing_or_tampered_packet_hash() {
    let packet = validate_native_install_gate(&installable_input());
    let packet_hash = native_install_gate_packet_hash(&packet);

    let missing = validate_native_install_gate_packet(&packet, None);
    assert_eq!(missing.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        missing.rejection_code,
        Some(NativeInstallGateRejectionCode::MissingPacketHash)
    );
    assert_eq!(missing.packet_hash, packet_hash);
    assert_blocked(missing.actions);

    let tampered = validate_native_install_gate_packet(
        &packet,
        Some(ArtifactChecksum::new(packet_hash.get().wrapping_add(1))),
    );
    assert_eq!(tampered.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        tampered.rejection_code,
        Some(NativeInstallGateRejectionCode::PacketHashMismatch)
    );
    assert_eq!(tampered.packet_hash, packet_hash);
    assert_blocked(tampered.actions);

    let mut persisted_hash_tampered = packet.clone();
    persisted_hash_tampered.packet_hash = ArtifactChecksum::new(packet_hash.get().wrapping_add(2));
    let verdict = validate_native_install_gate_packet(&persisted_hash_tampered, Some(packet_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::PacketHashMismatch)
    );
    assert_blocked(verdict.actions);
}

#[test]
fn packet_integrity_rejects_inconsistent_authority_actions() {
    let mut extra_action = validate_native_install_gate(&installable_input());
    extra_action.actions.release_installable = true;
    persist_native_install_gate_packet_bindings(&mut extra_action);
    let verdict =
        validate_native_install_gate_packet(&extra_action, Some(extra_action.packet_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::InconsistentActionAuthority)
    );
    assert_blocked(verdict.actions);

    let mut non_callable = validate_native_install_gate(&installable_input());
    non_callable.install_authority = NativeInstallGateAuthority::None;
    non_callable.actions = NativeInstallGateActions::none();
    persist_native_install_gate_packet_bindings(&mut non_callable);
    let verdict =
        validate_native_install_gate_packet(&non_callable, Some(non_callable.packet_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::InconsistentActionAuthority)
    );
    assert_blocked(verdict.actions);
}

#[test]
fn packet_current_revalidation_rejects_stale_generation_and_checksum() {
    let packet = validate_native_install_gate(&installable_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);

    let accepted = validate_native_install_gate_packet_with_current(
        &packet,
        Some(packet.packet_hash),
        &current,
    );
    assert_eq!(
        accepted.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(accepted.actions.typed_symbol_lookup);

    let mut stale_generation = current.clone();
    stale_generation.current_generation += 1;
    let verdict = validate_native_install_gate_packet_with_current(
        &packet,
        Some(packet.packet_hash),
        &stale_generation,
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_blocked(verdict.actions);

    let mut stale_checksum = current.clone();
    stale_checksum.current_invalidation_checksum =
        ArtifactChecksum::new(packet.artifact.invalidation_checksum.get() ^ 1);
    let verdict = validate_native_install_gate_packet_with_current(
        &packet,
        Some(packet.packet_hash),
        &stale_checksum,
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_blocked(verdict.actions);
}

#[test]
fn packet_current_revalidation_rejects_revocation_and_kill_switch() {
    let packet = validate_native_install_gate(&installable_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);

    let mut revoked = current.clone();
    revoked.revoked = true;
    let verdict = validate_native_install_gate_packet_with_current(
        &packet,
        Some(packet.packet_hash),
        &revoked,
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_blocked(verdict.actions);

    let mut kill_switch = current;
    kill_switch.deny_control = Some(
        NativeInstallGateDenyControlPlane::active(
            NativeInstallGateDenyScope::Global,
            NativeInstallGateDenyReason::KillSwitch,
        )
        .with_canonical_deny_sha256(),
    );
    let verdict = validate_native_install_gate_packet_with_current(
        &packet,
        Some(packet.packet_hash),
        &kill_switch,
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert_eq!(verdict.deny_control, kill_switch.deny_control);
    assert_blocked(verdict.actions);
}

#[test]
fn runtime_telemetry_increments_only_for_exact_accepted_native_call() {
    let packet = validate_native_install_gate(&installable_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let telemetry = packet.telemetry.as_ref().expect("packet telemetry");
    let replay = packet.replay_identity.as_ref().expect("packet replay");

    let accepted =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &current, true);
    assert_eq!(
        accepted.schema,
        NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA
    );
    assert_eq!(
        accepted.schema_version,
        NATIVE_INSTALL_GATE_RUNTIME_TELEMETRY_SCHEMA_VERSION
    );
    assert_eq!(
        accepted.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(accepted.rejection_code, None);
    assert_eq!(
        accepted.runtime_outcome,
        NativeInstallGateRuntimeOutcome::NativeUseful
    );
    assert_eq!(accepted.runtime_outcome.as_str(), "native_useful");
    assert_eq!(accepted.useful_native_delta, 1);
    assert_eq!(accepted.packet_hash, packet.packet_hash);
    assert_eq!(
        accepted.telemetry_event_id.as_deref(),
        Some(telemetry.event_id.as_str())
    );
    assert_eq!(
        accepted.telemetry_record_sha256.as_deref(),
        Some(telemetry.record_sha256.as_str())
    );
    assert_eq!(accepted.counter_scope, telemetry.counter_scope);
    assert_eq!(
        accepted.replay_root_sha256.as_deref(),
        Some(packet.replay_binding.replay_root_sha256.as_str())
    );
    assert_eq!(
        accepted.replay_record_sha256.as_deref(),
        Some(replay.replay_record_sha256.as_str())
    );
    assert_eq!(accepted.replay_binding, packet.replay_binding);
    assert_eq!(accepted.consumer_verdict, packet.consumer_verdict);

    let baseline_fallback =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &current, false);
    assert_eq!(
        baseline_fallback.runtime_outcome,
        NativeInstallGateRuntimeOutcome::BaselineFallback
    );
    assert_eq!(baseline_fallback.useful_native_delta, 0);

    let mut cache_insert = installable_input();
    cache_insert.surface = NativeInstallGateSurface::CacheInsert;
    refresh_gate_identity(&mut cache_insert);
    let cache_insert_packet = validate_native_install_gate(&cache_insert);
    let cache_insert_current =
        NativeInstallGateRevalidationInput::from_packet(&cache_insert_packet);
    let cache_insert_event = native_install_gate_runtime_telemetry(
        &cache_insert_packet,
        Some(cache_insert_packet.packet_hash),
        &cache_insert_current,
        true,
    );
    assert_eq!(
        cache_insert_event.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(
        cache_insert_event.useful_native_delta, 0,
        "cache insertion success is not a native call"
    );
    assert_eq!(
        cache_insert_event.runtime_outcome,
        NativeInstallGateRuntimeOutcome::MetadataOnly
    );

    let packet_hash_mismatch = native_install_gate_runtime_telemetry(
        &packet,
        Some(ArtifactChecksum::new(packet.packet_hash.get() ^ 1)),
        &current,
        true,
    );
    assert_eq!(
        packet_hash_mismatch.runtime_outcome,
        NativeInstallGateRuntimeOutcome::InvalidatedDeopt
    );
    assert_eq!(packet_hash_mismatch.useful_native_delta, 0);
    assert_eq!(
        packet_hash_mismatch.rejection_code,
        Some(NativeInstallGateRejectionCode::PacketHashMismatch)
    );
    assert_blocked(packet_hash_mismatch.actions);
}

#[test]
fn runtime_telemetry_keeps_stale_revoked_and_denied_deltas_zero() {
    let packet = validate_native_install_gate(&installable_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);

    let mut stale = current.clone();
    stale.current_generation += 1;
    let stale_event =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &stale, true);
    assert_eq!(
        stale_event.runtime_outcome,
        NativeInstallGateRuntimeOutcome::StaleDeopt
    );
    assert_eq!(stale_event.runtime_outcome.as_str(), "stale_deopt");
    assert_eq!(stale_event.useful_native_delta, 0);
    assert_eq!(
        stale_event.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_blocked(stale_event.actions);

    let mut revoked = current.clone();
    revoked.revoked = true;
    let revoked_event =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &revoked, true);
    assert_eq!(
        revoked_event.runtime_outcome,
        NativeInstallGateRuntimeOutcome::RevokedDeopt
    );
    assert_eq!(revoked_event.useful_native_delta, 0);
    assert_eq!(
        revoked_event.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_blocked(revoked_event.actions);

    let mut denied = current;
    denied.deny_control = Some(
        NativeInstallGateDenyControlPlane::active(
            NativeInstallGateDenyScope::Global,
            NativeInstallGateDenyReason::KillSwitch,
        )
        .with_canonical_deny_sha256(),
    );
    let denied_event =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &denied, true);
    assert_eq!(
        denied_event.runtime_outcome,
        NativeInstallGateRuntimeOutcome::KillSwitchDeopt
    );
    assert_eq!(denied_event.useful_native_delta, 0);
    assert_eq!(
        denied_event.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert_blocked(denied_event.actions);
}

#[test]
fn stale_cache_hit_and_activation_deopt_with_zero_useful_native_delta() {
    let mut cache_hit = installable_input();
    cache_hit.surface = NativeInstallGateSurface::CacheHit;
    refresh_gate_identity(&mut cache_hit);
    let cache_packet = validate_native_install_gate(&cache_hit);
    assert!(cache_packet.actions.accept_installable_cache_hit);

    let mut stale_cache_current = NativeInstallGateRevalidationInput::from_packet(&cache_packet);
    stale_cache_current.current_generation += 1;
    let cache_event = native_install_gate_runtime_telemetry(
        &cache_packet,
        Some(cache_packet.packet_hash),
        &stale_cache_current,
        true,
    );
    assert_eq!(
        cache_event.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_eq!(
        cache_event.runtime_outcome,
        NativeInstallGateRuntimeOutcome::StaleDeopt
    );
    assert_eq!(cache_event.useful_native_delta, 0);
    assert!(!cache_event.actions.accept_installable_cache_hit);
    assert!(!cache_event.actions.expose_callable);
    assert_blocked(cache_event.actions);

    let ty_packet = validate_native_install_gate(&ty_prework_input());
    assert!(ty_packet.actions.ty_native_activate);
    let current = NativeInstallGateRevalidationInput::from_packet(&ty_packet);
    let evidence = consumer_admission_evidence(&ty_packet, &current);
    let mut stale_activation_current = current;
    stale_activation_current.current_generation += 1;
    let activation = AdmissionBackedTySlot::default().activate(
        &ty_packet,
        Some(ty_packet.packet_hash),
        &stale_activation_current,
        &evidence,
    );

    assert_eq!(
        activation.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_no_admission_handle(&activation);

    let activation_event = native_install_gate_runtime_telemetry(
        &ty_packet,
        Some(ty_packet.packet_hash),
        &stale_activation_current,
        true,
    );
    assert_eq!(
        activation_event.runtime_outcome,
        NativeInstallGateRuntimeOutcome::StaleDeopt
    );
    assert_eq!(activation_event.useful_native_delta, 0);
    assert!(!activation_event.actions.ty_native_activate);
    assert_blocked(activation_event.actions);
}

#[test]
fn structured_events_bind_packet_runtime_and_consumer_admission_fields() {
    let packet = validate_native_install_gate(&installable_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let telemetry = packet.telemetry.as_ref().expect("packet telemetry");
    let replay = packet.replay_identity.as_ref().expect("packet replay");

    let install_event = native_install_gate_structured_event(&packet);
    assert_structured_event(
        &install_event,
        NativeInstallGateEventSource::InstallDecision,
        NativeInstallGateEventKind::Accepted,
    );
    assert_eq!(install_event.packet_hash, packet.packet_hash);
    assert_eq!(
        install_event.telemetry_event_id.as_deref(),
        Some(telemetry.event_id.as_str())
    );
    assert_eq!(
        install_event.telemetry_record_sha256.as_deref(),
        Some(telemetry.record_sha256.as_str())
    );
    assert_eq!(install_event.counter_scope, telemetry.counter_scope);
    assert_eq!(
        install_event.replay_root_sha256.as_deref(),
        Some(packet.replay_binding.replay_root_sha256.as_str())
    );
    assert_eq!(
        install_event.replay_record_sha256.as_deref(),
        Some(replay.replay_record_sha256.as_str())
    );
    assert_eq!(
        install_event.install_consumer_verdict_sha256.as_deref(),
        Some(packet.consumer_verdict.verdict_sha256.as_str())
    );
    assert_eq!(install_event.artifact_id, packet.artifact.artifact_id);
    assert_eq!(
        install_event.manifest_checksum,
        packet.artifact.manifest_checksum
    );
    assert_eq!(
        install_event.trust_ir_sha256,
        packet.artifact.trust_ir_sha256
    );
    assert_eq!(
        install_event.native_payload_sha256,
        packet.artifact.native_payload_sha256
    );
    assert_eq!(
        install_event.target_checksum,
        packet.artifact.target_checksum
    );
    assert_eq!(install_event.abi_checksum, packet.artifact.abi_checksum);
    assert_eq!(
        install_event.layout_checksum,
        packet.artifact.layout_checksum
    );
    assert_eq!(
        install_event.proof_policy_checksum,
        packet.artifact.proof_policy_checksum
    );
    assert_eq!(
        install_event.invalidation_checksum,
        packet.artifact.invalidation_checksum
    );
    assert_eq!(
        install_event.proof_report_sha256,
        packet.validation.proof_report_sha256
    );
    assert_eq!(
        install_event.requested_authority,
        NativeInstallGateAuthority::CanaryCallable
    );
    assert_eq!(
        install_event.install_authority,
        NativeInstallGateAuthority::CanaryCallable
    );
    assert_eq!(
        install_event.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(install_event.rejection_code, None);
    assert_eq!(install_event.actions, packet.actions);
    assert_eq!(install_event.native_call_succeeded, None);
    assert_eq!(install_event.useful_native_delta, 0);

    let runtime_event = native_install_gate_runtime_structured_event(
        &packet,
        Some(packet.packet_hash),
        &current,
        true,
    );
    assert_structured_event(
        &runtime_event,
        NativeInstallGateEventSource::RuntimeCall,
        NativeInstallGateEventKind::Accepted,
    );
    assert_eq!(runtime_event.native_call_succeeded, Some(true));
    assert_eq!(runtime_event.useful_native_delta, 1);

    let rollback_event = native_install_gate_runtime_structured_event(
        &packet,
        Some(packet.packet_hash),
        &current,
        false,
    );
    assert_structured_event(
        &rollback_event,
        NativeInstallGateEventSource::RuntimeCall,
        NativeInstallGateEventKind::RolledBack,
    );
    assert_eq!(rollback_event.native_call_succeeded, Some(false));
    assert_eq!(rollback_event.useful_native_delta, 0);

    let ay_packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let ay_current = NativeInstallGateRevalidationInput::from_packet(&ay_packet);
    let ay_evidence = consumer_admission_evidence(&ay_packet, &ay_current);
    let admission_event = native_install_gate_consumer_admission_structured_event(
        &ay_packet,
        Some(ay_packet.packet_hash),
        &ay_current,
        &ay_evidence,
    );
    assert_structured_event(
        &admission_event,
        NativeInstallGateEventSource::ConsumerAdmission,
        NativeInstallGateEventKind::Accepted,
    );
    assert!(admission_event.actions.ay_registry_insert);
    assert_eq!(admission_event.useful_native_delta, 0);
    assert_eq!(
        admission_event.diagnostic_sha256.as_deref(),
        Some(ay_evidence.evidence_sha256.as_str())
    );
}

#[test]
fn structured_events_classify_fail_closed_event_vocabulary() {
    let packet = validate_native_install_gate(&installable_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);

    let invalidated = native_install_gate_runtime_structured_event(
        &packet,
        Some(ArtifactChecksum::new(packet.packet_hash.get() ^ 1)),
        &current,
        true,
    );
    assert_structured_event(
        &invalidated,
        NativeInstallGateEventSource::RuntimeCall,
        NativeInstallGateEventKind::Invalidated,
    );
    assert_eq!(
        invalidated.rejection_code,
        Some(NativeInstallGateRejectionCode::PacketHashMismatch)
    );
    assert_eq!(invalidated.useful_native_delta, 0);
    assert_blocked(invalidated.actions);

    let mut missing_manifest = installable_input();
    missing_manifest.manifest = None;
    let missing_manifest_packet = validate_native_install_gate(&missing_manifest);
    let rejected_event = native_install_gate_structured_event(&missing_manifest_packet);
    assert_structured_event(
        &rejected_event,
        NativeInstallGateEventSource::InstallDecision,
        NativeInstallGateEventKind::Rejected,
    );
    assert_eq!(
        rejected_event.rejection_code,
        Some(NativeInstallGateRejectionCode::MissingManifest)
    );
    assert_eq!(rejected_event.useful_native_delta, 0);
    assert_blocked(rejected_event.actions);

    let mut timeout = installable_input();
    set_rejected_proof(
        &mut timeout,
        ProofEvidenceVerdict::Timeout,
        ProofEvidenceRejectionCode::Timeout,
    );
    let timeout_packet = validate_native_install_gate(&timeout);
    let timeout_event = native_install_gate_structured_event(&timeout_packet);
    assert_structured_event(
        &timeout_event,
        NativeInstallGateEventSource::InstallDecision,
        NativeInstallGateEventKind::VerifierTimeout,
    );
    assert_eq!(
        timeout_event.rejection_code,
        Some(NativeInstallGateRejectionCode::ProofTimeout)
    );
    assert_eq!(timeout_event.useful_native_delta, 0);
    assert_blocked(timeout_event.actions);

    let mut unknown = installable_input();
    set_rejected_proof(
        &mut unknown,
        ProofEvidenceVerdict::UnknownSolverError,
        ProofEvidenceRejectionCode::UnknownSolverError,
    );
    let unknown_packet = validate_native_install_gate(&unknown);
    let unknown_event = native_install_gate_structured_event(&unknown_packet);
    assert_structured_event(
        &unknown_event,
        NativeInstallGateEventSource::InstallDecision,
        NativeInstallGateEventKind::ProofUnknown,
    );
    assert_eq!(
        unknown_event.rejection_code,
        Some(NativeInstallGateRejectionCode::ProofUnknown)
    );
    assert_eq!(unknown_event.useful_native_delta, 0);
    assert_blocked(unknown_event.actions);

    let mut stale = current.clone();
    stale.current_generation += 1;
    let stale_event = native_install_gate_runtime_structured_event(
        &packet,
        Some(packet.packet_hash),
        &stale,
        true,
    );
    assert_structured_event(
        &stale_event,
        NativeInstallGateEventSource::RuntimeCall,
        NativeInstallGateEventKind::StaleGeneration,
    );
    assert_eq!(
        stale_event.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_eq!(stale_event.useful_native_delta, 0);
    assert_blocked(stale_event.actions);

    let mut revoked = current.clone();
    revoked.revoked = true;
    let revoked_event = native_install_gate_runtime_structured_event(
        &packet,
        Some(packet.packet_hash),
        &revoked,
        true,
    );
    assert_structured_event(
        &revoked_event,
        NativeInstallGateEventSource::RuntimeCall,
        NativeInstallGateEventKind::Revoked,
    );
    assert_eq!(
        revoked_event.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_eq!(revoked_event.useful_native_delta, 0);
    assert_blocked(revoked_event.actions);

    let mut denied = current;
    denied.deny_control = Some(
        NativeInstallGateDenyControlPlane::active(
            NativeInstallGateDenyScope::Global,
            NativeInstallGateDenyReason::KillSwitch,
        )
        .with_canonical_deny_sha256(),
    );
    let kill_switch_event = native_install_gate_runtime_structured_event(
        &packet,
        Some(packet.packet_hash),
        &denied,
        true,
    );
    assert_structured_event(
        &kill_switch_event,
        NativeInstallGateEventSource::RuntimeCall,
        NativeInstallGateEventKind::KillSwitch,
    );
    assert_eq!(
        kill_switch_event.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert_eq!(kill_switch_event.useful_native_delta, 0);
    assert_blocked(kill_switch_event.actions);

    let mut shadow_only = installable_input();
    shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
    let shadow_packet = validate_native_install_gate(&shadow_only);
    let shadow_event =
        native_install_gate_shadow_mismatch_event(&shadow_packet, "sha256:shadow-mismatch-report");
    assert_structured_event(
        &shadow_event,
        NativeInstallGateEventSource::ShadowReplay,
        NativeInstallGateEventKind::ShadowMismatch,
    );
    assert_eq!(
        shadow_event.rejection_code,
        Some(NativeInstallGateRejectionCode::ShadowOnlyNonInstallable)
    );
    assert_eq!(
        shadow_event.diagnostic_sha256.as_deref(),
        Some("sha256:shadow-mismatch-report")
    );
    assert_eq!(shadow_event.useful_native_delta, 0);
    assert_blocked(shadow_event.actions);
}

fn gate_accepted() -> ControlPlaneGateEvidence {
    ControlPlaneGateEvidence {
        phase6_accepted: true,
        phase9_accepted: true,
    }
}

fn control_plane_candidate_for_packet(
    packet: &NativeInstallGatePacket,
    mode: ControlPlaneMode,
) -> ControlPlaneCandidate {
    ControlPlaneCandidate::new(
        packet.consumer.clone(),
        packet.consumer_mode.clone(),
        packet.artifact.artifact_id.clone(),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        mode,
        format!(
            "{}:generation:{}",
            packet.consumer.as_str(),
            packet.freshness.current_generation
        ),
        "sha256:control-plane-replay-root",
        "telemetry:control-plane",
    )
}

fn ay_canary_generations_for_packet(packet: &NativeInstallGatePacket) -> AYCanaryGenerationFence {
    let base = packet.freshness.current_generation;
    AYCanaryGenerationFence::new(base, base + 1, base + 2, base + 3)
}

fn ay_canary_key_for_packet(packet: &NativeInstallGatePacket) -> AYCanaryAllowlistKey {
    AYCanaryAllowlistKey::new(
        packet.artifact.trust_ir_sha256.clone(),
        AYCanaryFamily::SparseSubstitute,
        ay_canary_generations_for_packet(packet),
        Target::Aarch64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    )
}

fn ay_canary_manifest_for_packet(packet: &NativeInstallGatePacket) -> AYCanaryManifestBinding {
    AYCanaryManifestBinding {
        source_sha256: packet.artifact.source_sha256.clone(),
        trust_ir_sha256: packet.artifact.trust_ir_sha256.clone(),
        native_payload_sha256: packet.artifact.native_payload_sha256.clone(),
        abi_checksum: packet.artifact.abi_checksum.to_string(),
        layout_checksum: packet.artifact.layout_checksum.to_string(),
        compiler_config_sha256: "sha256:compiler-config-ay-canary-fixture".to_owned(),
        target_facts_sha256: packet.artifact.target_checksum.to_string(),
        proof_policy: packet.artifact.proof_policy_checksum.to_string(),
        consumer_kind: "ay".to_owned(),
        wrapper_id: packet
            .validation
            .layout_wrapper_identity
            .clone()
            .unwrap_or_else(|| "ay.solver-registry.wrapper.v1".to_owned()),
        symbols: vec![
            "ay_lra_sparse_substitute".to_owned(),
            "ay_lra_basis_region".to_owned(),
        ],
        replay_root_sha256: packet.replay_binding.replay_root_sha256.clone(),
        telemetry_key: packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.event_id.clone())
            .unwrap_or_default(),
        manifest_sha256: packet.artifact.manifest_checksum.to_string(),
    }
}

fn ay_canary_layout_for_packet(packet: &NativeInstallGatePacket) -> AYCanaryLayoutProof {
    AYCanaryLayoutProof {
        pointer_inputs: true,
        bounds: true,
        mutability: true,
        aliasing: true,
        rollback_state: true,
        generation_fences: true,
        consumer_owned_memory: true,
        wrapper_id: packet
            .validation
            .layout_wrapper_identity
            .clone()
            .unwrap_or_else(|| "ay.solver-registry.wrapper.v1".to_owned()),
    }
}

fn ay_canary_provenance_for_packet(
    packet: &NativeInstallGatePacket,
) -> AYCanaryValidationProvenance {
    let key = ay_canary_key_for_packet(packet);
    let manifest = ay_canary_manifest_for_packet(packet);
    let proof_report_sha256 = AYCanaryLraProofFactEvidence::aarch64_required_for(&key, &manifest)
        .map(|evidence| evidence.canonical_report_sha256())
        .unwrap_or_else(|| "sha256:ay-canary-proof-report".to_owned());
    AYCanaryValidationProvenance {
        proof_report_sha256,
        tv_report_sha256: "sha256:ay-canary-tv-report".to_owned(),
        replay_root_sha256: packet.replay_binding.replay_root_sha256.clone(),
        consumer_equivalence_sha256: "sha256:ay-canary-equivalence".to_owned(),
        validator_id: packet
            .validation
            .layout_validation_provenance
            .clone()
            .unwrap_or_else(|| "trust-cg.ay.canary.fixture.validator".to_owned()),
        proof_policy_decision: AYCanaryProofDecision::Accepted,
    }
}

fn ay_canary_observation_for_packet(
    _packet: &NativeInstallGatePacket,
) -> AYCanaryExecutionObservation {
    AYCanaryExecutionObservation {
        result_sha256: "sha256:ay-canary-result".to_owned(),
        proof_sha256: "sha256:ay-canary-proof".to_owned(),
        witness_sha256: "sha256:ay-canary-witness".to_owned(),
        score_sha256: "sha256:ay-canary-score".to_owned(),
        status_sha256: "sha256:ay-canary-status".to_owned(),
        replay_verdict_sha256: "sha256:ay-canary-replay-verdict".to_owned(),
        wrong_answer_regressions: 0,
        proof_regressions: 0,
        witness_regressions: 0,
        score_regressions: 0,
        timeout_unknown_regressions: 0,
        crash_regressions: 0,
    }
}

fn ay_canary_equivalence_for_packet(
    packet: &NativeInstallGatePacket,
) -> AYCanaryEquivalenceEvidence {
    let observation = ay_canary_observation_for_packet(packet);
    AYCanaryEquivalenceEvidence {
        baseline: observation.clone(),
        native: observation,
    }
}

fn ay_canary_invalidation_for_packet(
    packet: &NativeInstallGatePacket,
    manifest: &AYCanaryManifestBinding,
) -> AYCanaryInvalidationState {
    AYCanaryInvalidationState {
        current_generations: ay_canary_generations_for_packet(packet),
        target_facts_sha256: packet.artifact.target_checksum.to_string(),
        proof_policy: packet.artifact.proof_policy_checksum.to_string(),
        compiler_config_sha256: manifest.compiler_config_sha256.clone(),
        manifest_sha256: manifest.manifest_sha256.clone(),
        source_sha256: manifest.source_sha256.clone(),
        trust_ir_sha256: manifest.trust_ir_sha256.clone(),
        native_payload_sha256: manifest.native_payload_sha256.clone(),
        kill_switch_active: false,
        revoked: false,
    }
}

fn ay_canary_candidate_for_packet(
    packet: &NativeInstallGatePacket,
    mode: AYCanaryCandidateMode,
) -> AYCanaryCandidate {
    let manifest = ay_canary_manifest_for_packet(packet);
    AYCanaryCandidate {
        mode,
        key: ay_canary_key_for_packet(packet),
        manifest: Some(manifest.clone()),
        layout: Some(ay_canary_layout_for_packet(packet)),
        provenance: Some(ay_canary_provenance_for_packet(packet)),
        equivalence: Some(ay_canary_equivalence_for_packet(packet)),
        invalidation: Some(ay_canary_invalidation_for_packet(packet, &manifest)),
    }
}

fn ay_canary_allowlist_for_packet(packet: &NativeInstallGatePacket) -> AYCanaryAllowlist {
    let key = ay_canary_key_for_packet(packet);
    let mut allowlist = AYCanaryAllowlist::new();
    allowlist.add_exact(&key);
    allowlist
}

fn ay_canary_parent_gates() -> AYCanaryParentGateEvidence {
    AYCanaryParentGateEvidence {
        install_gate_accepted: true,
        consumer_gate_accepted: true,
        downstream_ay_no_regression_accepted: true,
    }
}

fn ty_canary_generations_for_packet(packet: &NativeInstallGatePacket) -> TyCanaryGenerationTuple {
    let base = packet.freshness.current_generation;
    TyCanaryGenerationTuple::new(base, base + 1, base + 2, base + 3)
}

fn ty_canary_key_for_packet(packet: &NativeInstallGatePacket) -> TyCanaryAllowlistKey {
    TyCanaryAllowlistKey::new(
        packet.artifact.source_sha256.clone(),
        packet.artifact.trust_ir_sha256.clone(),
        TyCanaryFamily::ActionCluster,
        ty_canary_generations_for_packet(packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    )
}

fn ty_canary_manifest_for_packet(packet: &NativeInstallGatePacket) -> TyCanaryManifestBinding {
    TyCanaryManifestBinding {
        source_sha256: packet.artifact.source_sha256.clone(),
        trust_ir_sha256: packet.artifact.trust_ir_sha256.clone(),
        native_payload_sha256: packet.artifact.native_payload_sha256.clone(),
        abi_checksum: packet.artifact.abi_checksum.to_string(),
        layout_checksum: packet.artifact.layout_checksum.to_string(),
        compiler_config_sha256: "sha256:compiler-config-ty-canary-fixture".to_owned(),
        target_facts_sha256: packet.artifact.target_checksum.to_string(),
        proof_policy: packet.artifact.proof_policy_checksum.to_string(),
        consumer_kind: "ty".to_owned(),
        wrapper_id: packet
            .validation
            .layout_wrapper_identity
            .clone()
            .unwrap_or_else(|| "ty.fused-parent-loop.wrapper.v1".to_owned()),
        symbols: vec!["Request__1_1".to_owned(), "Fingerprint__1".to_owned()],
        replay_root_sha256: packet.replay_binding.replay_root_sha256.clone(),
        telemetry_key: packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.event_id.clone())
            .unwrap_or_default(),
        manifest_sha256: packet.artifact.manifest_checksum.to_string(),
    }
}

fn ty_canary_layout_for_packet(packet: &NativeInstallGatePacket) -> TyCanaryLayoutProof {
    TyCanaryLayoutProof {
        flat_state_buffers: true,
        parent_buffers: true,
        fingerprint_buffers: true,
        callback_runtime_symbols: true,
        return_status_buffers: true,
        generation_fences: true,
        mutability_aliasing: true,
        wrapper_id: packet
            .validation
            .layout_wrapper_identity
            .clone()
            .unwrap_or_else(|| "ty.fused-parent-loop.wrapper.v1".to_owned()),
    }
}

fn ty_canary_provenance_for_packet(
    packet: &NativeInstallGatePacket,
) -> TyCanaryValidationProvenance {
    let manifest = ty_canary_manifest_for_packet(packet);
    TyCanaryValidationProvenance {
        proof_report_sha256: packet
            .validation
            .proof_report_sha256
            .clone()
            .unwrap_or_else(|| "sha256:ty-canary-proof-report".to_owned()),
        tv_report_sha256: "sha256:ty-canary-tv-report".to_owned(),
        replay_root_sha256: packet.replay_binding.replay_root_sha256.clone(),
        consumer_equivalence_sha256: "sha256:ty-canary-equivalence".to_owned(),
        validator_id: packet
            .validation
            .layout_validation_provenance
            .clone()
            .unwrap_or_else(|| "trust-cg.ty.canary.fixture.validator".to_owned()),
        proof_policy_decision: TyCanaryProofDecision::Accepted,
    }
    .with_required_trust_ir_proof_fact_bindings(&manifest)
}

fn ty_canary_observation_for_packet(
    packet: &NativeInstallGatePacket,
) -> TyCanaryExecutionObservation {
    TyCanaryExecutionObservation {
        generated_state_count: packet.freshness.current_generation + 64,
        distinct_state_count: packet.freshness.current_generation + 19,
        parent_indexes_sha256: "sha256:ty-canary-parent-indexes".to_owned(),
        fingerprints_sha256: "sha256:ty-canary-fingerprints".to_owned(),
        final_verdict: "ok".to_owned(),
        status_codes_sha256: "sha256:ty-canary-status-codes".to_owned(),
        callback_visible_sha256: "sha256:ty-canary-callbacks".to_owned(),
        replay_verdict_sha256: "sha256:ty-canary-replay-verdict".to_owned(),
    }
}

fn ty_canary_equivalence_for_packet(
    packet: &NativeInstallGatePacket,
) -> TyCanaryEquivalenceEvidence {
    let observation = ty_canary_observation_for_packet(packet);
    TyCanaryEquivalenceEvidence {
        baseline: observation.clone(),
        native: observation,
    }
}

fn ty_canary_invalidation_for_packet(
    packet: &NativeInstallGatePacket,
    manifest: &TyCanaryManifestBinding,
) -> TyCanaryInvalidationState {
    TyCanaryInvalidationState {
        current_generations: ty_canary_generations_for_packet(packet),
        target_facts_sha256: packet.artifact.target_checksum.to_string(),
        proof_policy: packet.artifact.proof_policy_checksum.to_string(),
        compiler_config_sha256: manifest.compiler_config_sha256.clone(),
        manifest_sha256: manifest.manifest_sha256.clone(),
        source_sha256: manifest.source_sha256.clone(),
        trust_ir_sha256: manifest.trust_ir_sha256.clone(),
        native_payload_sha256: manifest.native_payload_sha256.clone(),
        kill_switch_active: false,
        revoked: false,
    }
}

fn ty_canary_candidate_for_packet(
    packet: &NativeInstallGatePacket,
    mode: TyCanaryCandidateMode,
) -> TyCanaryCandidate {
    let manifest = ty_canary_manifest_for_packet(packet);
    TyCanaryCandidate {
        mode,
        key: ty_canary_key_for_packet(packet),
        manifest: Some(manifest.clone()),
        layout: Some(ty_canary_layout_for_packet(packet)),
        provenance: Some(ty_canary_provenance_for_packet(packet)),
        equivalence: Some(ty_canary_equivalence_for_packet(packet)),
        invalidation: Some(ty_canary_invalidation_for_packet(packet, &manifest)),
    }
}

fn ty_canary_allowlist_for_packet(packet: &NativeInstallGatePacket) -> TyCanaryAllowlist {
    let key = ty_canary_key_for_packet(packet);
    let mut allowlist = TyCanaryAllowlist::new();
    allowlist.add_exact(&key);
    allowlist
}

fn ty_canary_parent_gates() -> TyCanaryParentGateEvidence {
    TyCanaryParentGateEvidence {
        install_gate_accepted: true,
        consumer_gate_accepted: true,
        three_spec_cli_accepted: true,
    }
}

#[test]
fn control_plane_kill_switch_scopes_feed_install_gate_revalidation() {
    let packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let cases = [
        (
            ControlPlaneKillSwitch::global("global native off"),
            NativeInstallGateDenyScope::Global,
        ),
        (
            ControlPlaneKillSwitch::consumer("ay", "ay native off"),
            NativeInstallGateDenyScope::Consumer,
        ),
        (
            ControlPlaneKillSwitch::family("ay", "solver-registry", "family off"),
            NativeInstallGateDenyScope::Family,
        ),
        (
            ControlPlaneKillSwitch::artifact(packet.artifact.artifact_id.clone(), "artifact off"),
            NativeInstallGateDenyScope::Artifact,
        ),
        (
            ControlPlaneKillSwitch::target_proof_policy(
                packet.artifact.target_checksum.to_string(),
                packet.artifact.proof_policy_checksum.to_string(),
                "target proof policy off",
            ),
            NativeInstallGateDenyScope::TargetProofPolicy,
        ),
        (
            ControlPlaneKillSwitch::mode(ControlPlaneMode::CanaryInstallable, "canary off"),
            NativeInstallGateDenyScope::Mode,
        ),
    ];

    for (kill_switch, expected_scope) in cases {
        let mut control = JitEverywhereControlPlane::new();
        control.add_kill_switch(kill_switch);

        let decision = control.route_new_call(&candidate, gate_accepted());
        assert_eq!(decision.reason, ControlPlaneReason::KillSwitchActive);
        assert!(decision.is_deny_or_baseline_only());
        assert_eq!(
            decision.telemetry.kill_switch_scope,
            decision.kill_switch_scope
        );

        let current = install_gate_revalidation_with_control_plane(&packet, &decision);
        let deny = current
            .deny_control
            .as_ref()
            .expect("kill switch projects to install-gate deny-control");
        assert_eq!(deny.reason, NativeInstallGateDenyReason::KillSwitch);
        assert_eq!(deny.scope, expected_scope);
        let expected_hash = deny.canonical_deny_sha256();
        assert_eq!(deny.deny_sha256.as_deref(), Some(expected_hash.as_str()));

        let verdict = validate_native_install_gate_packet_with_current(
            &packet,
            Some(packet.packet_hash),
            &current,
        );
        assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
        assert_eq!(
            verdict.rejection_code,
            Some(NativeInstallGateRejectionCode::KillSwitchActive)
        );
        assert_blocked(verdict.actions);

        let runtime = native_install_gate_runtime_telemetry(
            &packet,
            Some(packet.packet_hash),
            &current,
            true,
        );
        assert_eq!(runtime.useful_native_delta, 0);
        assert_eq!(
            runtime.rejection_code,
            Some(NativeInstallGateRejectionCode::KillSwitchActive)
        );
        assert_blocked(runtime.actions);
    }
}

#[test]
fn control_plane_revocation_feeds_install_gate_revalidation() {
    let packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let mut control = JitEverywhereControlPlane::new();
    control.revoke_artifact(ControlPlaneRevocation::active(
        candidate.artifact_sha256.clone(),
        candidate.replay_root_sha256.clone(),
        candidate.telemetry_key.clone(),
        "wrong-answer quarantine",
    ));

    let decision = control.route_new_call(&candidate, gate_accepted());
    assert_eq!(decision.reason, ControlPlaneReason::ArtifactRevoked);
    assert!(decision.is_deny_or_baseline_only());

    let current = install_gate_revalidation_with_control_plane(&packet, &decision);
    assert!(current.revoked);
    let deny = current
        .deny_control
        .as_ref()
        .expect("revocation projects to install-gate deny-control");
    assert_eq!(deny.reason, NativeInstallGateDenyReason::Revoked);
    assert_eq!(deny.scope, NativeInstallGateDenyScope::Artifact);
    assert_eq!(
        deny.artifact_id.as_deref(),
        Some(packet.artifact.artifact_id.as_str())
    );

    let verdict = validate_native_install_gate_packet_with_current(
        &packet,
        Some(packet.packet_hash),
        &current,
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_blocked(verdict.actions);

    let runtime =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &current, true);
    assert!(runtime.revoked);
    assert_eq!(runtime.useful_native_delta, 0);
    assert_eq!(
        runtime.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_blocked(runtime.actions);
}

#[test]
fn control_plane_consumer_admission_blocks_publication_before_ay_or_ty_activation() {
    let ay_packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let ay_current = NativeInstallGateRevalidationInput::from_packet(&ay_packet);
    let ay_evidence = consumer_admission_evidence(&ay_packet, &ay_current);
    let ay_candidate =
        control_plane_candidate_for_packet(&ay_packet, ControlPlaneMode::CanaryInstallable);
    let mut ay_control = JitEverywhereControlPlane::new();
    ay_control.add_kill_switch(ControlPlaneKillSwitch::consumer("ay", "ay native off"));

    let ay_decision = ay_control.route_new_call(&ay_candidate, gate_accepted());
    assert_eq!(ay_decision.reason, ControlPlaneReason::KillSwitchActive);
    let ay_admission = consumer_admission_with_control_plane(
        &ay_packet,
        Some(ay_packet.packet_hash),
        &ay_decision,
        &ay_evidence,
    );
    assert_eq!(
        ay_admission.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert_eq!(
        ay_admission.install_authority,
        NativeInstallGateAuthority::None
    );
    assert_blocked(ay_admission.actions);
    assert_eq!(ay_admission.telemetry.useful_native_delta, 0);
    let ay_deny = ay_admission
        .telemetry
        .deny_control
        .as_ref()
        .expect("consumer admission observed control-plane deny packet");
    assert_eq!(ay_deny.reason, NativeInstallGateDenyReason::KillSwitch);
    assert_eq!(ay_deny.scope, NativeInstallGateDenyScope::Consumer);
    assert_no_admission_handle(&ConsumerAdmissionPublicationResult::from_decision(
        &ay_admission,
    ));

    let ty_packet = validate_native_install_gate(&ty_prework_input());
    let ty_current = NativeInstallGateRevalidationInput::from_packet(&ty_packet);
    let ty_evidence = consumer_admission_evidence(&ty_packet, &ty_current);
    let ty_candidate =
        control_plane_candidate_for_packet(&ty_packet, ControlPlaneMode::CanaryInstallable);
    let mut ty_control = JitEverywhereControlPlane::new();
    ty_control.revoke_artifact(ControlPlaneRevocation::active(
        ty_candidate.artifact_sha256.clone(),
        ty_candidate.replay_root_sha256.clone(),
        ty_candidate.telemetry_key.clone(),
        "ty activation quarantine",
    ));

    let ty_decision = ty_control.route_new_call(&ty_candidate, gate_accepted());
    assert_eq!(ty_decision.reason, ControlPlaneReason::ArtifactRevoked);
    let ty_admission = consumer_admission_with_control_plane(
        &ty_packet,
        Some(ty_packet.packet_hash),
        &ty_decision,
        &ty_evidence,
    );
    assert_eq!(
        ty_admission.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_eq!(
        ty_admission.install_authority,
        NativeInstallGateAuthority::None
    );
    assert_blocked(ty_admission.actions);
    assert_eq!(ty_admission.telemetry.useful_native_delta, 0);
    assert!(ty_admission.telemetry.revoked);
    let ty_deny = ty_admission
        .telemetry
        .deny_control
        .as_ref()
        .expect("consumer admission observed revocation deny packet");
    assert_eq!(ty_deny.reason, NativeInstallGateDenyReason::Revoked);
    assert_eq!(ty_deny.scope, NativeInstallGateDenyScope::Artifact);
    assert_no_admission_handle(&ConsumerAdmissionPublicationResult::from_decision(
        &ty_admission,
    ));
}

#[test]
fn product_adapter_bridge_records_consumer_admission_without_product_publication() {
    for (name, packet) in [
        (
            "ay",
            validate_native_install_gate(&activation_input(
                "ay",
                NativeInstallGateSurface::AYRegistry,
            )),
        ),
        ("ty", validate_native_install_gate(&ty_prework_input())),
    ] {
        let current = NativeInstallGateRevalidationInput::from_packet(&packet);
        let evidence = consumer_admission_evidence(&packet, &current);
        let candidate =
            control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
        let mut control = JitEverywhereControlPlane::new();
        control.record_existing_product_publication(&candidate);

        let bridge = control.route_consumer_admission_product_adapter(
            &candidate,
            gate_accepted(),
            &packet,
            Some(packet.packet_hash),
            &evidence,
        );

        assert_eq!(
            bridge.control_plane.reason,
            ControlPlaneReason::ProductActivationRequired,
            "{name}"
        );
        assert_eq!(
            bridge.consumer_admission.disposition,
            NativeInstallGateDisposition::Installable,
            "{name}"
        );
        assert_eq!(bridge.consumer_admission.rejection_code, None, "{name}");
        assert_eq!(
            bridge.product_adapter.reason,
            ControlPlaneReason::ProductActivationRequired,
            "{name}"
        );
        assert!(bridge.product_adapter.denied_without_product_authority());
        assert!(
            bridge.publication_blocked_without_product_authority(),
            "{name}"
        );
        assert_eq!(bridge.consumer_allows_ay_registry, name == "ay", "{name}");
        assert_eq!(bridge.consumer_allows_ty_activation, name == "ty", "{name}");
        assert!(!bridge.publish_ay_registry_entry, "{name}");
        assert!(!bridge.activate_ty_native_handle, "{name}");
        assert!(!bridge.expose_callable_handle, "{name}");
        assert_eq!(bridge.useful_native_delta, 0, "{name}");
        assert_eq!(
            bridge.consumer_admission.telemetry.useful_native_delta, 0,
            "{name}"
        );
        assert_eq!(
            bridge.product_adapter.telemetry.useful_native_delta, 0,
            "{name}"
        );
        assert_product_call_status_row(
            name,
            &bridge,
            &candidate,
            ControlPlaneProductCallStatus::AcceptedPendingProductGate,
            NativeInstallGateDisposition::Installable,
            None,
            NativeInstallGateRuntimeOutcome::BaselineFallback,
            None,
        );
        assert!(
            !control
                .publication_state()
                .has_callable(&candidate.artifact_sha256),
            "{name}"
        );
        assert!(
            !control
                .publication_state()
                .has_installable_cache_entry(&candidate.artifact_sha256),
            "{name}"
        );
        if name == "ay" {
            assert!(
                !control
                    .publication_state()
                    .has_ay_registry_entry(&candidate.artifact_sha256)
            );
        } else {
            assert!(
                !control
                    .publication_state()
                    .has_ty_native_entry(&candidate.artifact_sha256)
            );
        }
    }
}

#[test]
fn ay_sat_theory_dispatch_product_adapter_fixture_stays_non_promoting() {
    let manifest = ay_sat_theory_dispatch_manifest(803);
    let input = ay_sat_theory_dispatch_gate_input(&manifest);
    assert!(!manifest.proof_policy.requires_evidence());
    assert_eq!(
        manifest
            .metadata
            .get("product_promotion_scope")
            .map(String::as_str),
        Some("does_not_unblock_665_product_promotion_or_public_ay_repin")
    );

    let packet = validate_native_install_gate(&input);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(!packet.actions.expose_callable);
    assert!(packet.actions.ay_registry_insert);
    assert!(!packet.actions.ty_native_activate);
    assert!(!packet.actions.insert_installable_cache);
    assert!(!packet.actions.accept_installable_cache_hit);
    assert!(!packet.actions.release_installable);
    assert_eq!(
        packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.useful_native_delta),
        Some(0)
    );

    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);
    let candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&candidate);

    let bridge = control.route_consumer_admission_product_adapter_with_current(
        &candidate,
        gate_accepted(),
        &packet,
        Some(packet.packet_hash),
        &current,
        &evidence,
    );

    assert_eq!(
        bridge.consumer_admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(bridge.consumer_admission.rejection_code, None);
    assert!(bridge.product_adapter.denied_without_product_authority());
    assert!(bridge.publication_blocked_without_product_authority());
    assert!(bridge.consumer_allows_ay_registry);
    assert!(!bridge.consumer_allows_ty_activation);
    assert!(!bridge.publish_ay_registry_entry);
    assert!(!bridge.activate_ty_native_handle);
    assert!(!bridge.expose_callable_handle);
    assert!(!bridge.product_adapter.installable_cache_hit_accepted);
    assert_eq!(bridge.product_adapter.callable_handle_id, None);
    assert_eq!(bridge.product_adapter.native_handle_id, None);
    assert_eq!(bridge.useful_native_delta, 0);
    assert_eq!(bridge.consumer_admission.telemetry.useful_native_delta, 0);
    assert_eq!(bridge.product_adapter.telemetry.useful_native_delta, 0);
    assert_eq!(bridge.call_time_revalidation.useful_native_delta, 0);
    assert_product_call_status_row(
        "ay_sat_theory_dispatch_non_promoting_product_adapter",
        &bridge,
        &candidate,
        ControlPlaneProductCallStatus::AcceptedPendingProductGate,
        NativeInstallGateDisposition::Installable,
        None,
        NativeInstallGateRuntimeOutcome::BaselineFallback,
        None,
    );
    assert!(
        !control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_ay_registry_entry(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_ty_native_entry(&candidate.artifact_sha256)
    );

    let mut missing_proof = input.clone();
    missing_proof.proof_evidence = None;
    refresh_gate_identity(&mut missing_proof);
    let missing_packet = validate_native_install_gate(&missing_proof);
    assert_non_installable_fixture_packet(
        "ay_sat_theory_dispatch_missing_proof_evidence",
        &missing_packet,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );
    let missing_current = NativeInstallGateRevalidationInput::from_packet(&missing_packet);
    let missing_evidence = consumer_admission_evidence(&missing_packet, &missing_current);
    assert_product_adapter_bridge_non_public_fixture(
        "ay_sat_theory_dispatch_missing_proof_evidence",
        &missing_packet,
        &missing_evidence,
        JitEverywhereControlPlane::new(),
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut proof_policy_mismatch = input;
    proof_policy_mismatch
        .proof_evidence
        .as_mut()
        .expect("theory-dispatch input has proof evidence")
        .summary
        .proof_policy_checksum = ArtifactChecksum::new(0x803);
    let mismatch_packet = validate_native_install_gate(&proof_policy_mismatch);
    assert_non_installable_fixture_packet(
        "ay_sat_theory_dispatch_proof_policy_mismatch",
        &mismatch_packet,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );
    let mismatch_current = NativeInstallGateRevalidationInput::from_packet(&mismatch_packet);
    let mismatch_evidence = consumer_admission_evidence(&mismatch_packet, &mismatch_current);
    assert_product_adapter_bridge_non_public_fixture(
        "ay_sat_theory_dispatch_proof_policy_mismatch",
        &mismatch_packet,
        &mismatch_evidence,
        JitEverywhereControlPlane::new(),
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );
}

#[test]
fn sparse_affected_row_product_adapter_keeps_batch_tuple_diagnostic_only() {
    let input = ay_lra_registry_input_with_layout(
        AYLraKernelFamily::SparseAffectedRowBatch.as_str(),
        ay_lra_base_layout(),
    );
    let packet = validate_native_install_gate(&input);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);
    assert!(!packet.actions.expose_callable);
    assert!(!packet.actions.insert_installable_cache);
    assert!(!packet.actions.accept_installable_cache_hit);
    assert!(!packet.actions.release_installable);

    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);
    let candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&candidate);
    let bridge = control.route_consumer_admission_product_adapter_with_current(
        &candidate,
        gate_accepted(),
        &packet,
        Some(packet.packet_hash),
        &current,
        &evidence,
    );

    assert_eq!(
        bridge.consumer_admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(bridge.consumer_admission.rejection_code, None);
    assert!(bridge.consumer_allows_ay_registry);
    assert!(!bridge.consumer_allows_ty_activation);
    assert!(bridge.publication_blocked_without_product_authority());
    assert!(!bridge.publish_ay_registry_entry);
    assert!(!bridge.activate_ty_native_handle);
    assert!(!bridge.expose_callable_handle);
    assert_eq!(bridge.useful_native_delta, 0);
    assert!(bridge.product_adapter.denied_without_product_authority());
    assert!(bridge.product_adapter.callable_registry_removed);
    assert!(bridge.product_adapter.installable_cache_removed);
    assert!(bridge.product_adapter.ay_registry_removed);
    assert!(!bridge.product_adapter.ty_native_removed);
    assert_eq!(bridge.product_adapter.callable_handle_id, None);
    assert_eq!(bridge.product_adapter.native_handle_id, None);
    assert!(!bridge.product_adapter.installable_cache_hit_accepted);
    assert_eq!(bridge.product_adapter.useful_native_delta, 0);
    assert_eq!(bridge.product_adapter.telemetry.issue, 749);
    assert_eq!(
        bridge.product_adapter.telemetry.product_call_status,
        Some(bridge.call_status.status)
    );
    assert_eq!(
        bridge
            .product_adapter
            .telemetry
            .product_call_status_record_sha256
            .as_deref(),
        Some(bridge.call_status.record_sha256.as_str())
    );
    assert!(
        bridge
            .product_adapter
            .telemetry
            .valid_for_product_call_status_row(&bridge.call_status)
    );
    assert_eq!(bridge.consumer_admission.telemetry.useful_native_delta, 0);
    assert_eq!(bridge.product_adapter.telemetry.useful_native_delta, 0);
    assert_eq!(bridge.call_time_revalidation.useful_native_delta, 0);
    assert_product_call_status_row(
        "ay_sparse_affected_row_product_adapter_diagnostic_only",
        &bridge,
        &candidate,
        ControlPlaneProductCallStatus::AcceptedPendingProductGate,
        NativeInstallGateDisposition::Installable,
        None,
        NativeInstallGateRuntimeOutcome::BaselineFallback,
        None,
    );
    assert!(
        !control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_ay_registry_entry(&candidate.artifact_sha256)
    );

    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let artifact = ay_lra_affected_row_batch_product_manifest(&proof_manifest);
    let product_gate = AYLraProductGateEvidence {
        install_gate_packet_sha256: artifact_checksum_as_diagnostic_sha256(packet.packet_hash),
        consumer_admission_sha256: bridge
            .consumer_admission
            .telemetry
            .admission_evidence_sha256
            .clone()
            .expect("consumer admission binds diagnostic evidence hash"),
        replay_identity_sha256: packet
            .replay_identity
            .as_ref()
            .expect("packet has replay identity")
            .replay_record_sha256
            .clone(),
        telemetry_record_sha256: bridge.product_adapter.telemetry.record_sha256.clone(),
    };
    let proof_consumption = ay_lra_affected_row_batch_proof_consumption_evidence(
        &artifact,
        &proof_manifest,
        product_gate,
    );
    let affected_row_evidence = AYLraSparseAffectedRowBatchEvidence::private_local()
        .with_canonical_hashes(&artifact, &proof_manifest, &proof_consumption);

    assert_eq!(
        affected_row_evidence.counters.row_output_lengths.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS
    );
    assert_eq!(
        affected_row_evidence.counters.rows_attempted(),
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_ATTEMPTED
    );
    assert_eq!(
        affected_row_evidence.counters.rows_committed.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED
    );
    assert_eq!(
        affected_row_evidence.counters.total_rows_committed(),
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED_TOTAL
    );
    assert_eq!(
        affected_row_evidence.counters.first_failed_rows.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS
    );
    assert_eq!(
        affected_row_evidence.counters.ok_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.overflow_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.bounds_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.stale_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.ok_statuses
            + affected_row_evidence.counters.overflow_statuses
            + affected_row_evidence.counters.bounds_statuses
            + affected_row_evidence.counters.stale_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OBSERVATIONS
    );
    assert_eq!(
        affected_row_evidence.useful_native_delta,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA
    );
    assert!(!affected_row_evidence.production_activation);
    assert!(!affected_row_evidence.publication_claim);
    assert_eq!(
        affected_row_evidence.hashes,
        affected_row_evidence.canonical_hashes(&artifact, &proof_manifest, &proof_consumption)
    );

    let sparse_affected_row_admission = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &artifact,
        &proof_manifest,
        &proof_consumption,
        &affected_row_evidence,
    );
    assert!(
        sparse_affected_row_admission.reasons.is_empty(),
        "sparse affected-row manifest fixture should admit: {:?}",
        sparse_affected_row_admission.reasons
    );
    assert_eq!(
        sparse_affected_row_admission.disposition,
        AYLraManifestDisposition::EmitManifest
    );
    assert!(sparse_affected_row_admission.non_promoting);
    assert_eq!(sparse_affected_row_admission.useful_native_delta, 0);
    assert_eq!(
        sparse_affected_row_admission.manifest_checksum,
        artifact.checksum()
    );
}

#[test]
fn sparse_affected_row_product_adapter_rejects_basis_tuple_diagnostic_only() {
    let input = ay_lra_registry_input_with_layout("ay_lra_basis_row_batch", ay_lra_base_layout());
    let packet = validate_native_install_gate(&input);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);
    assert!(!packet.actions.expose_callable);
    assert!(!packet.actions.insert_installable_cache);
    assert!(!packet.actions.accept_installable_cache_hit);
    assert!(!packet.actions.release_installable);

    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);
    let candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&candidate);
    let bridge = control.route_consumer_admission_product_adapter_with_current(
        &candidate,
        gate_accepted(),
        &packet,
        Some(packet.packet_hash),
        &current,
        &evidence,
    );

    assert_eq!(
        bridge.consumer_admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(bridge.consumer_admission.rejection_code, None);
    assert!(bridge.consumer_allows_ay_registry);
    assert!(!bridge.consumer_allows_ty_activation);
    assert!(bridge.publication_blocked_without_product_authority());
    assert!(!bridge.publish_ay_registry_entry);
    assert!(!bridge.activate_ty_native_handle);
    assert!(!bridge.expose_callable_handle);
    assert_eq!(bridge.useful_native_delta, 0);
    assert!(bridge.product_adapter.denied_without_product_authority());
    assert!(bridge.product_adapter.callable_registry_removed);
    assert!(bridge.product_adapter.installable_cache_removed);
    assert!(bridge.product_adapter.ay_registry_removed);
    assert!(!bridge.product_adapter.ty_native_removed);
    assert_eq!(bridge.product_adapter.callable_handle_id, None);
    assert_eq!(bridge.product_adapter.native_handle_id, None);
    assert!(!bridge.product_adapter.installable_cache_hit_accepted);
    assert_eq!(bridge.product_adapter.useful_native_delta, 0);
    assert_eq!(bridge.product_adapter.telemetry.issue, 749);
    assert_eq!(
        bridge.product_adapter.telemetry.product_call_status,
        Some(bridge.call_status.status)
    );
    assert_eq!(
        bridge
            .product_adapter
            .telemetry
            .product_call_status_record_sha256
            .as_deref(),
        Some(bridge.call_status.record_sha256.as_str())
    );
    assert!(
        bridge
            .product_adapter
            .telemetry
            .valid_for_product_call_status_row(&bridge.call_status)
    );
    assert_eq!(bridge.consumer_admission.telemetry.useful_native_delta, 0);
    assert_eq!(bridge.product_adapter.telemetry.useful_native_delta, 0);
    assert_eq!(bridge.call_time_revalidation.useful_native_delta, 0);
    assert_product_call_status_row(
        "ay_sparse_affected_row_product_adapter_diagnostic_only",
        &bridge,
        &candidate,
        ControlPlaneProductCallStatus::AcceptedPendingProductGate,
        NativeInstallGateDisposition::Installable,
        None,
        NativeInstallGateRuntimeOutcome::BaselineFallback,
        None,
    );
    assert!(
        !control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_ay_registry_entry(&candidate.artifact_sha256)
    );

    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let artifact = ay_lra_basis_product_manifest(&proof_manifest);
    let product_gate = AYLraProductGateEvidence {
        install_gate_packet_sha256: artifact_checksum_as_diagnostic_sha256(packet.packet_hash),
        consumer_admission_sha256: bridge
            .consumer_admission
            .telemetry
            .admission_evidence_sha256
            .clone()
            .expect("consumer admission binds diagnostic evidence hash"),
        replay_identity_sha256: packet
            .replay_identity
            .as_ref()
            .expect("packet has replay identity")
            .replay_record_sha256
            .clone(),
        telemetry_record_sha256: bridge.product_adapter.telemetry.record_sha256.clone(),
    };
    let proof_consumption =
        ay_lra_basis_proof_consumption_evidence(&artifact, &proof_manifest, product_gate);
    let affected_row_evidence = AYLraSparseAffectedRowBatchEvidence::private_local()
        .with_canonical_hashes(&artifact, &proof_manifest, &proof_consumption);

    assert_eq!(
        affected_row_evidence.counters.row_output_lengths.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROW_OUTPUT_LENGTHS
    );
    assert_eq!(
        affected_row_evidence.counters.rows_committed.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_ROWS_COMMITTED
    );
    assert_eq!(
        affected_row_evidence.counters.first_failed_rows.as_slice(),
        &AY_LRA_SPARSE_AFFECTED_ROW_BATCH_FIRST_FAILED_ROWS
    );
    assert_eq!(
        affected_row_evidence.counters.ok_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OK_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.overflow_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_OVERFLOW_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.bounds_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_BOUNDS_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.counters.stale_statuses,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_STALE_STATUS_COUNT
    );
    assert_eq!(
        affected_row_evidence.useful_native_delta,
        AY_LRA_SPARSE_AFFECTED_ROW_BATCH_USEFUL_NATIVE_DELTA
    );
    assert!(!affected_row_evidence.production_activation);
    assert!(!affected_row_evidence.publication_claim);
    assert_eq!(
        affected_row_evidence.hashes,
        affected_row_evidence.canonical_hashes(&artifact, &proof_manifest, &proof_consumption)
    );

    let sparse_affected_row_admission = evaluate_ay_lra_sparse_affected_row_batch_evidence(
        &artifact,
        &proof_manifest,
        &proof_consumption,
        &affected_row_evidence,
    );
    assert_eq!(
        sparse_affected_row_admission.disposition,
        AYLraManifestDisposition::RejectNonPromoting
    );
    assert!(
        sparse_affected_row_admission
            .reasons
            .contains(&AYLraManifestRejectionReason::UnsupportedKernelFamily),
        "sparse affected-row evidence must reject basis-row manifest family: {:?}",
        sparse_affected_row_admission.reasons
    );
    assert!(
        sparse_affected_row_admission
            .reasons
            .contains(&AYLraManifestRejectionReason::ManifestIdentityMetadataMismatch),
        "sparse affected-row evidence must reject basis-row manifest identity: {:?}",
        sparse_affected_row_admission.reasons
    );
    assert!(sparse_affected_row_admission.non_promoting);
    assert_eq!(sparse_affected_row_admission.useful_native_delta, 0);
    assert_eq!(
        sparse_affected_row_admission.manifest_checksum,
        artifact.checksum()
    );
}

#[test]
fn proof_guided_rewrite_admission_product_adapter_keeps_missing_or_failed_verdicts_non_installable()
{
    let admitted_record = proof_guided_ay_lra_basis_rewrite_record();
    assert_eq!(
        admitted_record.disposition,
        RewriteAdmissionDisposition::AdmitNonPromoting
    );
    assert_eq!(admitted_record.rejection, None);
    admitted_record
        .validate()
        .expect("complete #800 proof-guided rewrite evidence admits as non-promoting metadata");
    assert!(!admitted_record.product_install_authority);
    assert!(!admitted_record.grants_product_install_authority());

    let mut admitted_input =
        ay_lra_registry_input_with_layout("ay_lra_basis_row_batch", ay_lra_base_layout());
    attach_rewrite_admission_metadata(&mut admitted_input, &admitted_record);
    let admitted_packet = validate_native_install_gate(&admitted_input);
    assert_eq!(
        admitted_packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(admitted_packet.rejection_code, None);
    assert!(admitted_packet.actions.ay_registry_insert);
    assert!(!admitted_packet.actions.release_installable);

    let admitted_current = NativeInstallGateRevalidationInput::from_packet(&admitted_packet);
    let admitted_evidence = consumer_admission_evidence(&admitted_packet, &admitted_current);
    let admitted_candidate =
        control_plane_candidate_for_packet(&admitted_packet, ControlPlaneMode::CanaryInstallable);
    let mut admitted_control = JitEverywhereControlPlane::new();
    admitted_control.record_existing_product_publication(&admitted_candidate);
    let admitted_bridge = admitted_control.route_consumer_admission_product_adapter_with_current(
        &admitted_candidate,
        gate_accepted(),
        &admitted_packet,
        Some(admitted_packet.packet_hash),
        &admitted_current,
        &admitted_evidence,
    );

    assert_eq!(
        admitted_bridge.consumer_admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(admitted_bridge.consumer_admission.rejection_code, None);
    assert!(admitted_bridge.consumer_allows_ay_registry);
    assert!(!admitted_bridge.consumer_allows_ty_activation);
    assert!(admitted_bridge.publication_blocked_without_product_authority());
    assert!(
        admitted_bridge
            .product_adapter
            .denied_without_product_authority()
    );
    assert!(!admitted_bridge.publish_ay_registry_entry);
    assert!(!admitted_bridge.activate_ty_native_handle);
    assert!(!admitted_bridge.expose_callable_handle);
    assert!(
        !admitted_bridge
            .product_adapter
            .installable_cache_hit_accepted
    );
    assert_eq!(admitted_bridge.useful_native_delta, 0);
    assert_eq!(admitted_bridge.product_adapter.useful_native_delta, 0);
    assert_product_call_status_row(
        "ay_lra_basis_rewrite_admitted_non_promoting",
        &admitted_bridge,
        &admitted_candidate,
        ControlPlaneProductCallStatus::AcceptedPendingProductGate,
        NativeInstallGateDisposition::Installable,
        None,
        NativeInstallGateRuntimeOutcome::BaselineFallback,
        None,
    );
    assert!(
        !admitted_control
            .publication_state()
            .has_callable(&admitted_candidate.artifact_sha256)
    );
    assert!(
        !admitted_control
            .publication_state()
            .has_installable_cache_entry(&admitted_candidate.artifact_sha256)
    );
    assert!(
        !admitted_control
            .publication_state()
            .has_ay_registry_entry(&admitted_candidate.artifact_sha256)
    );

    let missing_record = RewriteAdmissionRecord::from_certificate_citation(
        proof_guided_ay_lra_basis_rewrite_certificate(),
        "aarch64",
        31,
        17,
        Some("validation-ay-lra-basis-row-batch-product-adapter".to_owned()),
    );
    assert_eq!(
        missing_record.disposition,
        RewriteAdmissionDisposition::Reject
    );
    assert_eq!(
        missing_record.rejection,
        Some(RewriteAdmissionRejection::MissingManifestHash)
    );
    assert_eq!(
        missing_record.validate(),
        Err(RewriteAdmissionRejection::MissingManifestHash)
    );
    assert!(!missing_record.product_install_authority);
    assert!(!missing_record.grants_product_install_authority());
    let mut missing_input =
        ay_lra_registry_input_with_layout("ay_lra_basis_row_batch", ay_lra_base_layout());
    missing_input.proof_evidence = None;
    let missing_packet = validate_native_install_gate(&missing_input);
    assert_non_installable_fixture_packet(
        "ay_lra_basis_rewrite_missing_proof_guided_verdict",
        &missing_packet,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );
    let missing_current = NativeInstallGateRevalidationInput::from_packet(&missing_packet);
    let missing_evidence = consumer_admission_evidence(&missing_packet, &missing_current);
    assert_product_adapter_bridge_non_public_fixture(
        "ay_lra_basis_rewrite_missing_proof_guided_verdict",
        &missing_packet,
        &missing_evidence,
        JitEverywhereControlPlane::new(),
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut failed_certificate = proof_guided_ay_lra_basis_rewrite_certificate();
    failed_certificate.status = "rejected".to_owned();
    failed_certificate.rejection_code = Some("proof_guided_verdict_rejected".to_owned());
    failed_certificate.rejection_detail =
        Some("ay rejected equivalence for product-adapter fixture".to_owned());
    let failed_record = RewriteAdmissionRecord::from_complete_evidence(
        failed_certificate,
        "aarch64",
        31,
        17,
        Some("validation-ay-lra-basis-row-batch-product-adapter".to_owned()),
        proof_guided_ay_lra_basis_complete_evidence(),
    );
    assert_eq!(
        failed_record.disposition,
        RewriteAdmissionDisposition::Reject
    );
    assert_eq!(
        failed_record.rejection,
        Some(RewriteAdmissionRejection::RejectedCertificateEvidence)
    );
    assert_eq!(
        failed_record.validate(),
        Err(RewriteAdmissionRejection::RejectedCertificateEvidence)
    );
    assert!(!failed_record.product_install_authority);
    assert!(!failed_record.grants_product_install_authority());
    let mut failed_input =
        ay_lra_registry_input_with_layout("ay_lra_basis_row_batch", ay_lra_base_layout());
    set_rejected_proof(
        &mut failed_input,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    );
    attach_rewrite_admission_metadata(&mut failed_input, &failed_record);
    let failed_packet = validate_native_install_gate(&failed_input);
    assert_non_installable_fixture_packet(
        "ay_lra_basis_rewrite_failed_proof_guided_verdict",
        &failed_packet,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofVerifierFailure,
    );
    let failed_current = NativeInstallGateRevalidationInput::from_packet(&failed_packet);
    let failed_evidence = consumer_admission_evidence(&failed_packet, &failed_current);
    assert_product_adapter_bridge_non_public_fixture(
        "ay_lra_basis_rewrite_failed_proof_guided_verdict",
        &failed_packet,
        &failed_evidence,
        JitEverywhereControlPlane::new(),
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofVerifierFailure,
    );
}

#[test]
fn product_adapter_bridge_fail_closed_for_invalid_consumer_admission_inputs() {
    let mut fixtures = Vec::new();
    push_end_to_end_non_installable_fixtures(&mut fixtures, "ay");
    push_end_to_end_non_installable_fixtures(&mut fixtures, "ty");

    for (name, input, expected_disposition, expected_code) in fixtures {
        let packet = validate_native_install_gate(&input);
        let current = NativeInstallGateRevalidationInput::from_packet(&packet);
        let evidence = consumer_admission_evidence(&packet, &current);
        let candidate =
            control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
        let mut control = JitEverywhereControlPlane::new();
        control.record_existing_product_publication(&candidate);

        let bridge = control.route_consumer_admission_product_adapter(
            &candidate,
            gate_accepted(),
            &packet,
            Some(packet.packet_hash),
            &evidence,
        );

        assert_eq!(
            bridge.consumer_admission.disposition, expected_disposition,
            "{name}"
        );
        assert_eq!(
            bridge.consumer_admission.rejection_code,
            Some(expected_code),
            "{name}"
        );
        assert_eq!(
            bridge.consumer_admission.install_authority,
            NativeInstallGateAuthority::None,
            "{name}"
        );
        assert_blocked(bridge.consumer_admission.actions);
        assert!(!bridge.consumer_allows_ay_registry, "{name}");
        assert!(!bridge.consumer_allows_ty_activation, "{name}");
        assert!(
            bridge.publication_blocked_without_product_authority(),
            "{name}"
        );
        assert!(!bridge.publish_ay_registry_entry, "{name}");
        assert!(!bridge.activate_ty_native_handle, "{name}");
        assert!(!bridge.expose_callable_handle, "{name}");
        assert_eq!(bridge.useful_native_delta, 0, "{name}");
        assert_eq!(
            bridge.consumer_admission.telemetry.useful_native_delta, 0,
            "{name}"
        );
        assert_eq!(
            bridge.product_adapter.telemetry.useful_native_delta, 0,
            "{name}"
        );
        assert!(
            !control
                .publication_state()
                .has_callable(&candidate.artifact_sha256),
            "{name}"
        );
        assert!(
            !control
                .publication_state()
                .has_installable_cache_entry(&candidate.artifact_sha256),
            "{name}"
        );
        assert!(
            !control
                .publication_state()
                .has_ay_registry_entry(&candidate.artifact_sha256),
            "{name}"
        );
        assert!(
            !control
                .publication_state()
                .has_ty_native_entry(&candidate.artifact_sha256),
            "{name}"
        );
    }
}

#[test]
fn product_adapter_bridge_call_time_current_revalidation_blocks_publication() {
    for consumer in ["ay", "ty"] {
        let input = end_to_end_input_for_consumer(consumer);
        let packet = validate_native_install_gate(&input);
        let base_current = NativeInstallGateRevalidationInput::from_packet(&packet);
        let evidence = consumer_admission_evidence(&packet, &base_current);

        let mut cases: Vec<(
            String,
            NativeInstallGateRevalidationInput,
            NativeInstallGateRejectionCode,
            NativeInstallGateRuntimeOutcome,
        )> = Vec::new();

        let mut stale_generation = base_current.clone();
        stale_generation.current_generation += 1;
        cases.push((
            format!("{consumer}_product_adapter_stale_call_generation"),
            stale_generation,
            NativeInstallGateRejectionCode::StaleInvalidation,
            NativeInstallGateRuntimeOutcome::StaleDeopt,
        ));

        let mut stale_domain = base_current.clone();
        stale_domain
            .freshness_domains
            .first_mut()
            .expect("installable packet has freshness domains")
            .current_generation += 1;
        cases.push((
            format!("{consumer}_product_adapter_stale_call_domain"),
            stale_domain,
            NativeInstallGateRejectionCode::StaleInvalidation,
            NativeInstallGateRuntimeOutcome::StaleDeopt,
        ));

        let mut revoked = base_current.clone();
        revoked.revoked = true;
        cases.push((
            format!("{consumer}_product_adapter_call_revoked"),
            revoked,
            NativeInstallGateRejectionCode::RevokedArtifact,
            NativeInstallGateRuntimeOutcome::RevokedDeopt,
        ));

        let mut kill_switch = base_current.clone();
        kill_switch.deny_control = Some(scoped_deny_control(
            &input,
            NativeInstallGateDenyScope::Consumer,
            NativeInstallGateDenyReason::KillSwitch,
        ));
        cases.push((
            format!("{consumer}_product_adapter_call_kill_switch"),
            kill_switch,
            NativeInstallGateRejectionCode::KillSwitchActive,
            NativeInstallGateRuntimeOutcome::KillSwitchDeopt,
        ));

        for (name, current, expected_code, expected_outcome) in cases {
            let candidate =
                control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
            let mut control = JitEverywhereControlPlane::new();
            control.record_existing_product_publication(&candidate);

            let bridge = control.route_consumer_admission_product_adapter_with_current(
                &candidate,
                gate_accepted(),
                &packet,
                Some(packet.packet_hash),
                &current,
                &evidence,
            );

            assert_eq!(
                bridge.consumer_admission.disposition,
                NativeInstallGateDisposition::Rejected,
                "{name}"
            );
            assert_eq!(
                bridge.consumer_admission.rejection_code,
                Some(expected_code),
                "{name}"
            );
            assert_eq!(
                bridge.consumer_admission.install_authority,
                NativeInstallGateAuthority::None,
                "{name}"
            );
            assert_blocked(bridge.consumer_admission.actions);
            assert_eq!(
                bridge.consumer_admission.telemetry.useful_native_delta, 0,
                "{name}"
            );
            assert_eq!(
                bridge.call_time_revalidation.rejection_code,
                Some(expected_code),
                "{name}"
            );
            assert_eq!(
                bridge.call_time_revalidation.runtime_outcome, expected_outcome,
                "{name}"
            );
            assert_eq!(
                bridge.call_time_revalidation.useful_native_delta, 0,
                "{name}"
            );
            let expected_status = match expected_outcome {
                NativeInstallGateRuntimeOutcome::StaleDeopt => {
                    ControlPlaneProductCallStatus::StaleDeopt
                }
                NativeInstallGateRuntimeOutcome::RevokedDeopt => {
                    ControlPlaneProductCallStatus::RevokedDeopt
                }
                NativeInstallGateRuntimeOutcome::KillSwitchDeopt => {
                    ControlPlaneProductCallStatus::KillSwitchDeopt
                }
                NativeInstallGateRuntimeOutcome::InvalidatedDeopt => {
                    ControlPlaneProductCallStatus::InvalidatedDeopt
                }
                _ => panic!("{name}: unexpected call-time outcome"),
            };
            assert_product_call_status_row(
                &name,
                &bridge,
                &candidate,
                expected_status,
                NativeInstallGateDisposition::Rejected,
                Some(expected_code),
                expected_outcome,
                Some(expected_code),
            );
            assert_blocked(bridge.call_time_revalidation.actions);
            assert!(
                bridge.publication_blocked_without_product_authority(),
                "{name}"
            );
            assert!(bridge.product_adapter.denied_without_product_authority());
            assert!(!bridge.publish_ay_registry_entry, "{name}");
            assert!(!bridge.activate_ty_native_handle, "{name}");
            assert!(!bridge.expose_callable_handle, "{name}");
            assert!(
                !control
                    .publication_state()
                    .has_callable(&candidate.artifact_sha256),
                "{name}"
            );
            assert!(
                !control
                    .publication_state()
                    .has_installable_cache_entry(&candidate.artifact_sha256),
                "{name}"
            );
            assert!(
                !control
                    .publication_state()
                    .has_ay_registry_entry(&candidate.artifact_sha256),
                "{name}"
            );
            assert!(
                !control
                    .publication_state()
                    .has_ty_native_entry(&candidate.artifact_sha256),
                "{name}"
            );
        }
    }
}

#[test]
fn product_adapter_bridge_exports_consumer_rejected_call_status_row() {
    let mut input = end_to_end_input_for_consumer("ay");
    input.manifest = None;
    let packet = validate_native_install_gate(&input);
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);
    let candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&candidate);

    let bridge = control.route_consumer_admission_product_adapter_with_current(
        &candidate,
        gate_accepted(),
        &packet,
        Some(packet.packet_hash),
        &current,
        &evidence,
    );

    assert_eq!(
        bridge.consumer_admission.disposition,
        NativeInstallGateDisposition::Rejected
    );
    assert_eq!(
        bridge.consumer_admission.rejection_code,
        Some(NativeInstallGateRejectionCode::MissingManifest)
    );
    assert_blocked(bridge.consumer_admission.actions);
    assert_product_call_status_row(
        "ay_product_adapter_missing_manifest_call_status",
        &bridge,
        &candidate,
        ControlPlaneProductCallStatus::ConsumerRejected,
        NativeInstallGateDisposition::Rejected,
        Some(NativeInstallGateRejectionCode::MissingManifest),
        NativeInstallGateRuntimeOutcome::RejectedDeopt,
        Some(NativeInstallGateRejectionCode::MissingManifest),
    );
    assert!(bridge.publication_blocked_without_product_authority());
    assert!(
        !control
            .publication_state()
            .has_callable(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_installable_cache_entry(&candidate.artifact_sha256)
    );
    assert!(
        !control
            .publication_state()
            .has_ay_registry_entry(&candidate.artifact_sha256)
    );
}

#[test]
fn ay_canary_allowlist_fixture_composes_admission_without_registry_publication() {
    let packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let consumer_evidence = consumer_admission_evidence(&packet, &current);
    let allowlist = ay_canary_allowlist_for_packet(&packet);
    let control = JitEverywhereControlPlane::new();
    let control_candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let control_decision = control.route_new_call(&control_candidate, gate_accepted());
    let candidate =
        ay_canary_candidate_for_packet(&packet, AYCanaryCandidateMode::CanaryInstallable);

    let precheck = evaluate_ay_canary_activation_precheck(
        &allowlist,
        &candidate,
        ay_canary_parent_gates(),
        &packet,
        Some(packet.packet_hash),
        &control_decision,
        &consumer_evidence,
    );
    assert_eq!(
        precheck.allowlist.status,
        AYCanaryDecisionStatus::AllowlistedRequiresProductGate
    );
    assert_eq!(
        precheck.allowlist.reason,
        AYCanaryRejectionReason::ProductActivationRequired
    );
    assert_eq!(
        precheck.consumer_admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(precheck.consumer_admission.actions.ay_registry_insert);
    assert!(precheck.is_pre_activation_only());
    assert!(!precheck.publish_ay_registry_entry);
    assert!(!precheck.publish_callable_handle);
    assert_eq!(precheck.useful_native_delta, 0);
    assert!(precheck.side_effects.all_blocked());

    let mut non_allowlisted_family = candidate.clone();
    non_allowlisted_family.key = AYCanaryAllowlistKey::new(
        packet.artifact.trust_ir_sha256.clone(),
        AYCanaryFamily::BasisRegionScanner,
        ay_canary_generations_for_packet(&packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    );
    let precheck = evaluate_ay_canary_activation_precheck(
        &allowlist,
        &non_allowlisted_family,
        ay_canary_parent_gates(),
        &packet,
        Some(packet.packet_hash),
        &control_decision,
        &consumer_evidence,
    );
    assert_eq!(precheck.allowlist.status, AYCanaryDecisionStatus::Rejected);
    assert_eq!(
        precheck.allowlist.reason,
        AYCanaryRejectionReason::NonAllowlisted
    );
    assert!(precheck.is_pre_activation_only());
    assert!(!precheck.publish_ay_registry_entry);
    assert!(!precheck.publish_callable_handle);
    assert_eq!(precheck.useful_native_delta, 0);

    let mut cases: Vec<(String, AYCanaryCandidate, AYCanaryRejectionReason)> = Vec::new();

    let mut invalid_manifest = candidate.clone();
    invalid_manifest.manifest.as_mut().unwrap().manifest_sha256 =
        "sha256:wrong-ay-canary-manifest".to_owned();
    cases.push((
        "invalid_manifest".to_owned(),
        invalid_manifest,
        AYCanaryRejectionReason::MissingManifest,
    ));

    let mut layout_mismatch = candidate.clone();
    layout_mismatch.layout.as_mut().unwrap().bounds = false;
    cases.push((
        "layout_mismatch".to_owned(),
        layout_mismatch,
        AYCanaryRejectionReason::LayoutMismatch,
    ));

    let mut failed_validation = candidate.clone();
    failed_validation
        .provenance
        .as_mut()
        .unwrap()
        .proof_policy_decision = AYCanaryProofDecision::Rejected;
    cases.push((
        "failed_validation".to_owned(),
        failed_validation,
        AYCanaryRejectionReason::FailedProof,
    ));

    let mut stale_invalidation = candidate.clone();
    stale_invalidation
        .invalidation
        .as_mut()
        .unwrap()
        .current_generations = AYCanaryGenerationFence::new(
        packet.freshness.current_generation,
        packet.freshness.current_generation + 1,
        packet.freshness.current_generation + 2,
        packet.freshness.current_generation + 4,
    );
    cases.push((
        "stale_invalidation".to_owned(),
        stale_invalidation,
        AYCanaryRejectionReason::StaleGeneration,
    ));

    let mut missing_telemetry = candidate.clone();
    missing_telemetry
        .manifest
        .as_mut()
        .unwrap()
        .telemetry_key
        .clear();
    cases.push((
        "missing_telemetry".to_owned(),
        missing_telemetry,
        AYCanaryRejectionReason::MissingTelemetry,
    ));

    let mut regression_mismatch = candidate.clone();
    regression_mismatch
        .equivalence
        .as_mut()
        .unwrap()
        .native
        .wrong_answer_regressions = 1;
    cases.push((
        "regression_mismatch".to_owned(),
        regression_mismatch,
        AYCanaryRejectionReason::AYRegressionEvidenceMismatch,
    ));

    for (name, candidate, expected_reason) in cases {
        let precheck = evaluate_ay_canary_activation_precheck(
            &allowlist,
            &candidate,
            ay_canary_parent_gates(),
            &packet,
            Some(packet.packet_hash),
            &control_decision,
            &consumer_evidence,
        );
        assert_eq!(
            precheck.allowlist.status,
            AYCanaryDecisionStatus::Rejected,
            "{name}"
        );
        assert_eq!(precheck.allowlist.reason, expected_reason, "{name}");
        assert!(precheck.is_pre_activation_only(), "{name}");
        assert!(!precheck.publish_ay_registry_entry, "{name}");
        assert!(!precheck.publish_callable_handle, "{name}");
        assert_eq!(precheck.useful_native_delta, 0, "{name}");
        assert!(precheck.side_effects.all_blocked(), "{name}");
    }

    let mut kill_switch_control = JitEverywhereControlPlane::new();
    kill_switch_control.add_kill_switch(ControlPlaneKillSwitch::consumer("ay", "ay canary off"));
    let kill_switch_decision =
        kill_switch_control.route_new_call(&control_candidate, gate_accepted());
    let precheck = evaluate_ay_canary_activation_precheck(
        &allowlist,
        &candidate,
        ay_canary_parent_gates(),
        &packet,
        Some(packet.packet_hash),
        &kill_switch_decision,
        &consumer_evidence,
    );
    assert_eq!(
        precheck.consumer_admission.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert_blocked(precheck.consumer_admission.actions);
    assert!(precheck.is_pre_activation_only());

    let mut revocation_control = JitEverywhereControlPlane::new();
    revocation_control.revoke_artifact(ControlPlaneRevocation::active(
        control_candidate.artifact_sha256.clone(),
        control_candidate.replay_root_sha256.clone(),
        control_candidate.telemetry_key.clone(),
        "ay canary revoked",
    ));
    let revocation_decision =
        revocation_control.route_new_call(&control_candidate, gate_accepted());
    let precheck = evaluate_ay_canary_activation_precheck(
        &allowlist,
        &candidate,
        ay_canary_parent_gates(),
        &packet,
        Some(packet.packet_hash),
        &revocation_decision,
        &consumer_evidence,
    );
    assert_eq!(
        precheck.consumer_admission.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_blocked(precheck.consumer_admission.actions);
    assert!(precheck.is_pre_activation_only());
}

#[test]
fn ay_canary_product_adapter_precheck_keeps_exact_family_fail_closed() {
    let packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let consumer_evidence = consumer_admission_evidence(&packet, &current);
    let allowlist = ay_canary_allowlist_for_packet(&packet);
    let control_candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let candidate =
        ay_canary_candidate_for_packet(&packet, AYCanaryCandidateMode::CanaryInstallable);

    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&control_candidate);
    let exact = evaluate_ay_canary_product_adapter_precheck(
        &allowlist,
        &candidate,
        ay_canary_parent_gates(),
        &mut control,
        &control_candidate,
        gate_accepted(),
        &packet,
        Some(packet.packet_hash),
        &current,
        &consumer_evidence,
    );
    assert_eq!(
        exact.allowlist.status,
        AYCanaryDecisionStatus::AllowlistedRequiresProductGate
    );
    assert_eq!(
        exact.allowlist.reason,
        AYCanaryRejectionReason::ProductActivationRequired
    );
    assert_eq!(
        exact.product_admission.consumer_admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(
        exact
            .product_admission
            .consumer_admission
            .actions
            .ay_registry_insert
    );
    assert!(exact.product_admission.consumer_allows_ay_registry);
    assert!(exact.is_pre_activation_only());
    assert!(!exact.publish_ay_registry_entry);
    assert!(!exact.publish_callable_handle);
    assert_eq!(exact.useful_native_delta, 0);
    assert_eq!(
        exact.product_admission.product_adapter.useful_native_delta,
        0
    );
    assert_canary_product_precheck_call_status_row(
        "ay_exact",
        &exact.product_admission,
        &control_candidate,
    );
    assert!(
        !control
            .publication_state()
            .has_ay_registry_entry(&control_candidate.artifact_sha256)
    );

    let mut non_exact_cases: Vec<(String, AYCanaryCandidate)> = Vec::new();

    let mut wrong_family = candidate.clone();
    wrong_family.key = AYCanaryAllowlistKey::new(
        packet.artifact.trust_ir_sha256.clone(),
        AYCanaryFamily::BasisRegionScanner,
        ay_canary_generations_for_packet(&packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    );
    non_exact_cases.push(("wrong_family".to_owned(), wrong_family));

    let mut wrong_solver = candidate.clone();
    wrong_solver.key = AYCanaryAllowlistKey::new(
        "sha256:other-ay-solver-program",
        AYCanaryFamily::SparseSubstitute,
        ay_canary_generations_for_packet(&packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    );
    non_exact_cases.push(("wrong_solver".to_owned(), wrong_solver));

    let mut wrong_generation = candidate.clone();
    wrong_generation.key = AYCanaryAllowlistKey::new(
        packet.artifact.trust_ir_sha256.clone(),
        AYCanaryFamily::SparseSubstitute,
        AYCanaryGenerationFence::new(
            packet.freshness.current_generation,
            packet.freshness.current_generation + 1,
            packet.freshness.current_generation + 2,
            packet.freshness.current_generation + 4,
        ),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    );
    non_exact_cases.push(("wrong_generation".to_owned(), wrong_generation));

    let mut wrong_manifest = candidate.clone();
    wrong_manifest.key = AYCanaryAllowlistKey::new(
        packet.artifact.trust_ir_sha256.clone(),
        AYCanaryFamily::SparseSubstitute,
        ay_canary_generations_for_packet(&packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        "sha256:other-ay-manifest",
    );
    non_exact_cases.push(("wrong_manifest".to_owned(), wrong_manifest));

    for (name, candidate) in non_exact_cases {
        let mut control = JitEverywhereControlPlane::new();
        control.record_existing_product_publication(&control_candidate);
        let precheck = evaluate_ay_canary_product_adapter_precheck(
            &allowlist,
            &candidate,
            ay_canary_parent_gates(),
            &mut control,
            &control_candidate,
            gate_accepted(),
            &packet,
            Some(packet.packet_hash),
            &current,
            &consumer_evidence,
        );
        assert_eq!(
            precheck.allowlist.status,
            AYCanaryDecisionStatus::Rejected,
            "{name}"
        );
        assert_eq!(
            precheck.allowlist.reason,
            AYCanaryRejectionReason::NonAllowlisted,
            "{name}"
        );
        assert!(precheck.is_pre_activation_only(), "{name}");
        assert!(!precheck.publish_ay_registry_entry, "{name}");
        assert!(!precheck.publish_callable_handle, "{name}");
        assert_eq!(precheck.useful_native_delta, 0, "{name}");
        assert!(
            precheck
                .product_admission
                .publication_blocked_without_product_authority(),
            "{name}"
        );
        assert_canary_product_precheck_call_status_row(
            &name,
            &precheck.product_admission,
            &control_candidate,
        );
        assert!(
            !control
                .publication_state()
                .has_ay_registry_entry(&control_candidate.artifact_sha256),
            "{name}"
        );
    }
}

#[test]
fn ay_canary_product_adapter_precheck_negative_evidence_stays_non_callable() {
    let packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let consumer_evidence = consumer_admission_evidence(&packet, &current);
    let allowlist = ay_canary_allowlist_for_packet(&packet);
    let control_candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let candidate =
        ay_canary_candidate_for_packet(&packet, AYCanaryCandidateMode::CanaryInstallable);

    let mut cases: Vec<(String, AYCanaryCandidate, AYCanaryRejectionReason)> = Vec::new();

    let mut missing_manifest = candidate.clone();
    missing_manifest.manifest = None;
    cases.push((
        "missing_manifest".to_owned(),
        missing_manifest,
        AYCanaryRejectionReason::MissingManifest,
    ));

    let mut layout_mismatch = candidate.clone();
    layout_mismatch.layout.as_mut().unwrap().bounds = false;
    cases.push((
        "layout_mismatch".to_owned(),
        layout_mismatch,
        AYCanaryRejectionReason::LayoutMismatch,
    ));

    let mut failed_validation = candidate.clone();
    failed_validation
        .provenance
        .as_mut()
        .unwrap()
        .proof_policy_decision = AYCanaryProofDecision::Rejected;
    cases.push((
        "failed_validation".to_owned(),
        failed_validation,
        AYCanaryRejectionReason::FailedProof,
    ));

    let mut stale_invalidation = candidate.clone();
    stale_invalidation
        .invalidation
        .as_mut()
        .unwrap()
        .current_generations = AYCanaryGenerationFence::new(
        packet.freshness.current_generation,
        packet.freshness.current_generation + 1,
        packet.freshness.current_generation + 2,
        packet.freshness.current_generation + 4,
    );
    cases.push((
        "stale_invalidation".to_owned(),
        stale_invalidation,
        AYCanaryRejectionReason::StaleGeneration,
    ));

    let mut missing_telemetry = candidate.clone();
    missing_telemetry
        .manifest
        .as_mut()
        .unwrap()
        .telemetry_key
        .clear();
    cases.push((
        "missing_telemetry".to_owned(),
        missing_telemetry,
        AYCanaryRejectionReason::MissingTelemetry,
    ));

    let mut regression_mismatch = candidate.clone();
    regression_mismatch
        .equivalence
        .as_mut()
        .unwrap()
        .native
        .wrong_answer_regressions = 1;
    cases.push((
        "regression_mismatch".to_owned(),
        regression_mismatch,
        AYCanaryRejectionReason::AYRegressionEvidenceMismatch,
    ));

    for (name, candidate, expected_reason) in cases {
        let mut control = JitEverywhereControlPlane::new();
        control.record_existing_product_publication(&control_candidate);
        let precheck = evaluate_ay_canary_product_adapter_precheck(
            &allowlist,
            &candidate,
            ay_canary_parent_gates(),
            &mut control,
            &control_candidate,
            gate_accepted(),
            &packet,
            Some(packet.packet_hash),
            &current,
            &consumer_evidence,
        );
        assert_eq!(
            precheck.allowlist.status,
            AYCanaryDecisionStatus::Rejected,
            "{name}"
        );
        assert_eq!(precheck.allowlist.reason, expected_reason, "{name}");
        assert!(precheck.is_pre_activation_only(), "{name}");
        assert!(precheck.side_effects.all_blocked(), "{name}");
        assert!(!precheck.publish_ay_registry_entry, "{name}");
        assert!(!precheck.publish_callable_handle, "{name}");
        assert_eq!(precheck.useful_native_delta, 0, "{name}");
        assert!(
            !precheck.product_admission.publish_ay_registry_entry,
            "{name}"
        );
        assert!(!precheck.product_admission.expose_callable_handle, "{name}");
        assert!(
            !precheck.product_admission.activate_ty_native_handle,
            "{name}"
        );
        assert_eq!(
            precheck
                .product_admission
                .product_adapter
                .callable_handle_id,
            None,
            "{name}"
        );
        assert_eq!(
            precheck.product_admission.product_adapter.native_handle_id, None,
            "{name}"
        );
        assert!(
            !precheck
                .product_admission
                .product_adapter
                .installable_cache_hit_accepted,
            "{name}"
        );
        assert_eq!(
            precheck
                .product_admission
                .product_adapter
                .useful_native_delta,
            0,
            "{name}"
        );
        assert_canary_product_precheck_call_status_row(
            &name,
            &precheck.product_admission,
            &control_candidate,
        );
        assert!(
            !control
                .publication_state()
                .has_ay_registry_entry(&control_candidate.artifact_sha256),
            "{name}"
        );
    }
}

#[test]
fn ty_canary_allowlist_fixture_composes_admission_without_activation() {
    let packet = validate_native_install_gate(&ty_prework_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let consumer_evidence = consumer_admission_evidence(&packet, &current);
    let allowlist = ty_canary_allowlist_for_packet(&packet);
    let control = JitEverywhereControlPlane::new();
    let control_candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let control_decision = control.route_new_call(&control_candidate, gate_accepted());
    let candidate =
        ty_canary_candidate_for_packet(&packet, TyCanaryCandidateMode::CanaryInstallable);

    let precheck = evaluate_ty_canary_activation_precheck(
        &allowlist,
        &candidate,
        ty_canary_parent_gates(),
        &packet,
        Some(packet.packet_hash),
        &control_decision,
        &consumer_evidence,
    );
    assert_eq!(
        precheck.allowlist.status,
        TyCanaryDecisionStatus::AllowlistedRequiresProductGate
    );
    assert_eq!(
        precheck.allowlist.reason,
        TyCanaryRejectionReason::ProductActivationRequired
    );
    assert_eq!(
        precheck.consumer_admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(precheck.consumer_admission.actions.ty_native_activate);
    assert!(precheck.is_pre_activation_only());
    assert!(!precheck.publish_ty_native_handle);
    assert_eq!(precheck.useful_native_delta, 0);
    assert!(precheck.side_effects.all_blocked());

    let mut non_allowlisted_family = candidate.clone();
    non_allowlisted_family.key = TyCanaryAllowlistKey::new(
        packet.artifact.source_sha256.clone(),
        packet.artifact.trust_ir_sha256.clone(),
        TyCanaryFamily::FingerprintHelper,
        ty_canary_generations_for_packet(&packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    );
    let precheck = evaluate_ty_canary_activation_precheck(
        &allowlist,
        &non_allowlisted_family,
        ty_canary_parent_gates(),
        &packet,
        Some(packet.packet_hash),
        &control_decision,
        &consumer_evidence,
    );
    assert_eq!(precheck.allowlist.status, TyCanaryDecisionStatus::Rejected);
    assert_eq!(
        precheck.allowlist.reason,
        TyCanaryRejectionReason::NonAllowlisted
    );
    assert!(precheck.is_pre_activation_only());
    assert!(!precheck.publish_ty_native_handle);
    assert_eq!(precheck.useful_native_delta, 0);

    let mut cases: Vec<(String, TyCanaryCandidate, TyCanaryRejectionReason)> = Vec::new();

    let mut missing_manifest = candidate.clone();
    missing_manifest.manifest = None;
    cases.push((
        "missing_manifest".to_owned(),
        missing_manifest,
        TyCanaryRejectionReason::MissingManifest,
    ));

    let mut layout_mismatch = candidate.clone();
    layout_mismatch.layout.as_mut().unwrap().parent_buffers = false;
    cases.push((
        "layout_mismatch".to_owned(),
        layout_mismatch,
        TyCanaryRejectionReason::LayoutMismatch,
    ));

    let mut failed_validation = candidate.clone();
    failed_validation
        .provenance
        .as_mut()
        .unwrap()
        .proof_policy_decision = TyCanaryProofDecision::Rejected;
    cases.push((
        "failed_validation".to_owned(),
        failed_validation,
        TyCanaryRejectionReason::FailedProof,
    ));

    let mut stale_invalidation = candidate.clone();
    stale_invalidation
        .invalidation
        .as_mut()
        .unwrap()
        .current_generations = TyCanaryGenerationTuple::new(
        packet.freshness.current_generation,
        packet.freshness.current_generation + 1,
        packet.freshness.current_generation + 2,
        packet.freshness.current_generation + 4,
    );
    cases.push((
        "stale_invalidation".to_owned(),
        stale_invalidation,
        TyCanaryRejectionReason::StaleGeneration,
    ));

    let mut missing_telemetry = candidate.clone();
    missing_telemetry
        .manifest
        .as_mut()
        .unwrap()
        .telemetry_key
        .clear();
    cases.push((
        "missing_telemetry".to_owned(),
        missing_telemetry,
        TyCanaryRejectionReason::MissingTelemetry,
    ));

    for (name, candidate, expected_reason) in cases {
        let precheck = evaluate_ty_canary_activation_precheck(
            &allowlist,
            &candidate,
            ty_canary_parent_gates(),
            &packet,
            Some(packet.packet_hash),
            &control_decision,
            &consumer_evidence,
        );
        assert_eq!(
            precheck.allowlist.status,
            TyCanaryDecisionStatus::Rejected,
            "{name}"
        );
        assert_eq!(precheck.allowlist.reason, expected_reason, "{name}");
        assert!(precheck.is_pre_activation_only(), "{name}");
        assert!(!precheck.publish_ty_native_handle, "{name}");
        assert_eq!(precheck.useful_native_delta, 0, "{name}");
        assert!(precheck.side_effects.all_blocked(), "{name}");
    }

    let mut kill_switch_control = JitEverywhereControlPlane::new();
    kill_switch_control.add_kill_switch(ControlPlaneKillSwitch::consumer("ty", "ty canary off"));
    let kill_switch_decision =
        kill_switch_control.route_new_call(&control_candidate, gate_accepted());
    let precheck = evaluate_ty_canary_activation_precheck(
        &allowlist,
        &candidate,
        ty_canary_parent_gates(),
        &packet,
        Some(packet.packet_hash),
        &kill_switch_decision,
        &consumer_evidence,
    );
    assert_eq!(
        precheck.consumer_admission.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert_blocked(precheck.consumer_admission.actions);
    assert!(precheck.is_pre_activation_only());

    let mut revocation_control = JitEverywhereControlPlane::new();
    revocation_control.revoke_artifact(ControlPlaneRevocation::active(
        control_candidate.artifact_sha256.clone(),
        control_candidate.replay_root_sha256.clone(),
        control_candidate.telemetry_key.clone(),
        "ty canary revoked",
    ));
    let revocation_decision =
        revocation_control.route_new_call(&control_candidate, gate_accepted());
    let precheck = evaluate_ty_canary_activation_precheck(
        &allowlist,
        &candidate,
        ty_canary_parent_gates(),
        &packet,
        Some(packet.packet_hash),
        &revocation_decision,
        &consumer_evidence,
    );
    assert_eq!(
        precheck.consumer_admission.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_blocked(precheck.consumer_admission.actions);
    assert!(precheck.is_pre_activation_only());
}

#[test]
fn ty_canary_product_adapter_precheck_keeps_exact_family_fail_closed() {
    let packet = validate_native_install_gate(&ty_prework_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let consumer_evidence = consumer_admission_evidence(&packet, &current);
    let allowlist = ty_canary_allowlist_for_packet(&packet);
    let control_candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let candidate =
        ty_canary_candidate_for_packet(&packet, TyCanaryCandidateMode::CanaryInstallable);

    let mut control = JitEverywhereControlPlane::new();
    control.record_existing_product_publication(&control_candidate);
    let exact = evaluate_ty_canary_product_adapter_precheck(
        &allowlist,
        &candidate,
        ty_canary_parent_gates(),
        &mut control,
        &control_candidate,
        gate_accepted(),
        &packet,
        Some(packet.packet_hash),
        &current,
        &consumer_evidence,
    );
    assert_eq!(
        exact.allowlist.status,
        TyCanaryDecisionStatus::AllowlistedRequiresProductGate
    );
    assert_eq!(
        exact.allowlist.reason,
        TyCanaryRejectionReason::ProductActivationRequired
    );
    assert_eq!(
        exact.product_admission.consumer_admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(
        exact
            .product_admission
            .consumer_admission
            .actions
            .ty_native_activate
    );
    assert!(exact.product_admission.consumer_allows_ty_activation);
    assert!(exact.is_pre_activation_only());
    assert!(!exact.publish_ty_native_handle);
    assert_eq!(exact.useful_native_delta, 0);
    assert_eq!(
        exact.product_admission.product_adapter.useful_native_delta,
        0
    );
    assert_canary_product_precheck_call_status_row(
        "ty_exact",
        &exact.product_admission,
        &control_candidate,
    );
    assert!(
        !control
            .publication_state()
            .has_ty_native_entry(&control_candidate.artifact_sha256)
    );

    let mut non_exact_cases: Vec<(String, TyCanaryCandidate)> = Vec::new();

    let mut wrong_family = candidate.clone();
    wrong_family.key = TyCanaryAllowlistKey::new(
        packet.artifact.source_sha256.clone(),
        packet.artifact.trust_ir_sha256.clone(),
        TyCanaryFamily::FingerprintHelper,
        ty_canary_generations_for_packet(&packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    );
    non_exact_cases.push(("wrong_family".to_owned(), wrong_family));

    let mut wrong_spec = candidate.clone();
    wrong_spec.key = TyCanaryAllowlistKey::new(
        "sha256:other-ty-spec",
        packet.artifact.trust_ir_sha256.clone(),
        TyCanaryFamily::ActionCluster,
        ty_canary_generations_for_packet(&packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    );
    non_exact_cases.push(("wrong_spec".to_owned(), wrong_spec));

    let mut wrong_generation = candidate.clone();
    wrong_generation.key = TyCanaryAllowlistKey::new(
        packet.artifact.source_sha256.clone(),
        packet.artifact.trust_ir_sha256.clone(),
        TyCanaryFamily::ActionCluster,
        TyCanaryGenerationTuple::new(
            packet.freshness.current_generation,
            packet.freshness.current_generation + 1,
            packet.freshness.current_generation + 2,
            packet.freshness.current_generation + 4,
        ),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        packet.artifact.manifest_checksum.to_string(),
    );
    non_exact_cases.push(("wrong_generation".to_owned(), wrong_generation));

    let mut wrong_manifest = candidate.clone();
    wrong_manifest.key = TyCanaryAllowlistKey::new(
        packet.artifact.source_sha256.clone(),
        packet.artifact.trust_ir_sha256.clone(),
        TyCanaryFamily::ActionCluster,
        ty_canary_generations_for_packet(&packet),
        Target::X86_64,
        packet.artifact.target_checksum.to_string(),
        packet.artifact.proof_policy_checksum.to_string(),
        packet.artifact.layout_checksum.to_string(),
        "sha256:other-ty-manifest",
    );
    non_exact_cases.push(("wrong_manifest".to_owned(), wrong_manifest));

    for (name, candidate) in non_exact_cases {
        let mut control = JitEverywhereControlPlane::new();
        control.record_existing_product_publication(&control_candidate);
        let precheck = evaluate_ty_canary_product_adapter_precheck(
            &allowlist,
            &candidate,
            ty_canary_parent_gates(),
            &mut control,
            &control_candidate,
            gate_accepted(),
            &packet,
            Some(packet.packet_hash),
            &current,
            &consumer_evidence,
        );
        assert_eq!(
            precheck.allowlist.status,
            TyCanaryDecisionStatus::Rejected,
            "{name}"
        );
        assert_eq!(
            precheck.allowlist.reason,
            TyCanaryRejectionReason::NonAllowlisted,
            "{name}"
        );
        assert!(precheck.is_pre_activation_only(), "{name}");
        assert!(!precheck.publish_ty_native_handle, "{name}");
        assert_eq!(precheck.useful_native_delta, 0, "{name}");
        assert!(
            precheck
                .product_admission
                .publication_blocked_without_product_authority(),
            "{name}"
        );
        assert_canary_product_precheck_call_status_row(
            &name,
            &precheck.product_admission,
            &control_candidate,
        );
        assert!(
            !control
                .publication_state()
                .has_ty_native_entry(&control_candidate.artifact_sha256),
            "{name}"
        );
    }
}

#[test]
fn ty_canary_product_adapter_precheck_negative_evidence_stays_non_callable() {
    let packet = validate_native_install_gate(&ty_prework_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let consumer_evidence = consumer_admission_evidence(&packet, &current);
    let allowlist = ty_canary_allowlist_for_packet(&packet);
    let control_candidate =
        control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
    let candidate =
        ty_canary_candidate_for_packet(&packet, TyCanaryCandidateMode::CanaryInstallable);

    let mut cases: Vec<(String, TyCanaryCandidate, TyCanaryRejectionReason)> = Vec::new();

    let mut missing_manifest = candidate.clone();
    missing_manifest.manifest = None;
    cases.push((
        "missing_manifest".to_owned(),
        missing_manifest,
        TyCanaryRejectionReason::MissingManifest,
    ));

    let mut layout_mismatch = candidate.clone();
    layout_mismatch.layout.as_mut().unwrap().parent_buffers = false;
    cases.push((
        "layout_mismatch".to_owned(),
        layout_mismatch,
        TyCanaryRejectionReason::LayoutMismatch,
    ));

    let mut failed_validation = candidate.clone();
    failed_validation
        .provenance
        .as_mut()
        .unwrap()
        .proof_policy_decision = TyCanaryProofDecision::Rejected;
    cases.push((
        "failed_validation".to_owned(),
        failed_validation,
        TyCanaryRejectionReason::FailedProof,
    ));

    let mut stale_invalidation = candidate.clone();
    stale_invalidation
        .invalidation
        .as_mut()
        .unwrap()
        .current_generations = TyCanaryGenerationTuple::new(
        packet.freshness.current_generation,
        packet.freshness.current_generation + 1,
        packet.freshness.current_generation + 2,
        packet.freshness.current_generation + 4,
    );
    cases.push((
        "stale_invalidation".to_owned(),
        stale_invalidation,
        TyCanaryRejectionReason::StaleGeneration,
    ));

    let mut missing_telemetry = candidate.clone();
    missing_telemetry
        .manifest
        .as_mut()
        .unwrap()
        .telemetry_key
        .clear();
    cases.push((
        "missing_telemetry".to_owned(),
        missing_telemetry,
        TyCanaryRejectionReason::MissingTelemetry,
    ));

    for (name, candidate, expected_reason) in cases {
        let mut control = JitEverywhereControlPlane::new();
        control.record_existing_product_publication(&control_candidate);
        let precheck = evaluate_ty_canary_product_adapter_precheck(
            &allowlist,
            &candidate,
            ty_canary_parent_gates(),
            &mut control,
            &control_candidate,
            gate_accepted(),
            &packet,
            Some(packet.packet_hash),
            &current,
            &consumer_evidence,
        );
        assert_eq!(
            precheck.allowlist.status,
            TyCanaryDecisionStatus::Rejected,
            "{name}"
        );
        assert_eq!(precheck.allowlist.reason, expected_reason, "{name}");
        assert!(precheck.is_pre_activation_only(), "{name}");
        assert!(precheck.side_effects.all_blocked(), "{name}");
        assert!(!precheck.publish_ty_native_handle, "{name}");
        assert_eq!(precheck.useful_native_delta, 0, "{name}");
        assert!(
            !precheck.product_admission.activate_ty_native_handle,
            "{name}"
        );
        assert!(!precheck.product_admission.expose_callable_handle, "{name}");
        assert_eq!(
            precheck
                .product_admission
                .product_adapter
                .callable_handle_id,
            None,
            "{name}"
        );
        assert_eq!(
            precheck.product_admission.product_adapter.native_handle_id, None,
            "{name}"
        );
        assert!(
            !precheck
                .product_admission
                .product_adapter
                .installable_cache_hit_accepted,
            "{name}"
        );
        assert_eq!(
            precheck
                .product_admission
                .product_adapter
                .useful_native_delta,
            0,
            "{name}"
        );
        assert_canary_product_precheck_call_status_row(
            &name,
            &precheck.product_admission,
            &control_candidate,
        );
        assert!(
            !control
                .publication_state()
                .has_ty_native_entry(&control_candidate.artifact_sha256),
            "{name}"
        );
    }
}

#[test]
fn control_plane_telemetry_emits_revocation_and_kill_switch_state() {
    let input = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    let packet = validate_native_install_gate(&input);
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);

    let mut revoked_current = current.clone();
    revoked_current.revoked = true;
    let runtime_revoked = native_install_gate_runtime_telemetry(
        &packet,
        Some(packet.packet_hash),
        &revoked_current,
        true,
    );
    assert_eq!(
        runtime_revoked.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert!(runtime_revoked.revoked);
    assert_eq!(runtime_revoked.deny_control, None);
    assert_eq!(runtime_revoked.useful_native_delta, 0);
    assert_blocked(runtime_revoked.actions);

    let admission_revoked = native_install_gate_consumer_admission(
        &packet,
        Some(packet.packet_hash),
        &revoked_current,
        &evidence,
    );
    assert_eq!(
        admission_revoked.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert!(admission_revoked.telemetry.revoked);
    assert_eq!(admission_revoked.telemetry.deny_control, None);
    assert_eq!(admission_revoked.telemetry.useful_native_delta, 0);
    assert_blocked(admission_revoked.actions);

    let kill_switch = scoped_deny_control(
        &input,
        NativeInstallGateDenyScope::Consumer,
        NativeInstallGateDenyReason::KillSwitch,
    );
    let mut denied_current = current;
    denied_current.deny_control = Some(kill_switch.clone());
    let runtime_denied = native_install_gate_runtime_telemetry(
        &packet,
        Some(packet.packet_hash),
        &denied_current,
        true,
    );
    assert_eq!(
        runtime_denied.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert!(!runtime_denied.revoked);
    assert_eq!(runtime_denied.deny_control, Some(kill_switch.clone()));
    assert_eq!(runtime_denied.useful_native_delta, 0);
    assert_blocked(runtime_denied.actions);

    let admission_denied = native_install_gate_consumer_admission(
        &packet,
        Some(packet.packet_hash),
        &denied_current,
        &evidence,
    );
    assert_eq!(
        admission_denied.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert!(!admission_denied.telemetry.revoked);
    assert_eq!(admission_denied.telemetry.deny_control, Some(kill_switch));
    assert_eq!(admission_denied.telemetry.useful_native_delta, 0);
    assert_blocked(admission_denied.actions);
}

#[test]
fn revocation_removes_publication_and_cache_authority_but_retains_replay_evidence() {
    let packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);
    let mut registry = AdmissionBackedAYRegistry::default();

    let accepted = registry.insert(&packet, Some(packet.packet_hash), &current, &evidence);
    assert_eq!(
        accepted.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(registry.registry_key.is_some());
    assert!(registry.callable_handle.is_some());

    let accepted_event =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &current, true);
    assert_eq!(accepted_event.useful_native_delta, 1);

    let mut revoked_current = current;
    revoked_current.revoked = true;
    let revoked_publication = registry.revalidate_or_remove(
        &packet,
        Some(packet.packet_hash),
        &revoked_current,
        &evidence,
    );
    assert_eq!(
        revoked_publication.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert_no_admission_handle(&revoked_publication);
    assert_eq!(registry.registry_key, None);
    assert_eq!(registry.callable_handle, None);

    let revoked_event = native_install_gate_runtime_telemetry(
        &packet,
        Some(packet.packet_hash),
        &revoked_current,
        true,
    );
    assert!(revoked_event.revoked);
    assert_eq!(revoked_event.useful_native_delta, 0);
    assert!(
        revoked_event
            .replay_root_sha256
            .as_deref()
            .is_some_and(|root| root.starts_with("sha256:"))
    );
    assert!(
        revoked_event
            .telemetry_record_sha256
            .as_deref()
            .is_some_and(|record| record.starts_with("sha256:"))
    );

    let mut cache_hit = installable_input();
    cache_hit.surface = NativeInstallGateSurface::CacheHit;
    refresh_gate_identity(&mut cache_hit);
    let cache_packet = validate_native_install_gate(&cache_hit);
    let mut cache_current = NativeInstallGateRevalidationInput::from_packet(&cache_packet);
    cache_current.revoked = true;
    let cache_verdict = validate_native_install_gate_packet_with_current(
        &cache_packet,
        Some(cache_packet.packet_hash),
        &cache_current,
    );
    assert_eq!(
        cache_verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::RevokedArtifact)
    );
    assert!(!cache_verdict.actions.accept_installable_cache_hit);
    assert_blocked(cache_verdict.actions);
}

fn assert_runtime_rejects_tampered_layout_packet(
    mut packet: NativeInstallGatePacket,
    expected_code: NativeInstallGateRejectionCode,
) {
    persist_native_install_gate_packet_bindings(&mut packet);
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let verdict = validate_native_install_gate_packet_with_current(
        &packet,
        Some(packet.packet_hash),
        &current,
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(verdict.rejection_code, Some(expected_code));
    assert_blocked(verdict.actions);

    let event =
        native_install_gate_runtime_telemetry(&packet, Some(packet.packet_hash), &current, true);
    assert_eq!(event.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(event.rejection_code, Some(expected_code));
    assert_eq!(event.useful_native_delta, 0);
    assert_blocked(event.actions);
}

fn freshness_domain_names(packet: &NativeInstallGatePacket) -> BTreeSet<&str> {
    packet
        .freshness
        .freshness_domains
        .iter()
        .map(|observation| observation.domain.as_str())
        .collect()
}

fn assert_bound_freshness_domains(packet: &NativeInstallGatePacket, expected_domains: &[&str]) {
    let names = freshness_domain_names(packet);
    for expected_domain in expected_domains {
        assert!(
            names.contains(expected_domain),
            "missing freshness domain {expected_domain}"
        );
    }
    for observation in &packet.freshness.freshness_domains {
        assert_eq!(
            observation.observed_generation, packet.freshness.artifact_generation,
            "{} observed generation binds packet artifact generation",
            observation.domain
        );
        assert_eq!(
            observation.current_generation, packet.freshness.current_generation,
            "{} current generation binds packet current generation",
            observation.domain
        );
        assert!(!observation.is_stale(), "{} is current", observation.domain);
    }
}

fn assert_runtime_rejects_freshness_packet(
    packet: &NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
    expected_code: NativeInstallGateRejectionCode,
) {
    let verdict =
        validate_native_install_gate_packet_with_current(packet, Some(packet.packet_hash), current);
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(verdict.rejection_code, Some(expected_code));
    assert_blocked(verdict.actions);

    let event =
        native_install_gate_runtime_telemetry(packet, Some(packet.packet_hash), current, true);
    assert_eq!(event.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(event.rejection_code, Some(expected_code));
    assert_eq!(event.useful_native_delta, 0);
    assert_blocked(event.actions);
}

#[test]
fn install_packets_bind_shared_and_product_freshness_domains() {
    let shared_domains = [
        "shared_artifact",
        "shared_proof_policy",
        "shared_target_abi",
        "shared_release_bundle",
        "shared_revocation",
        "shared_kill_switch",
    ];
    let ay_domains = [
        "ay_solver",
        "ay_sparse",
        "ay_basis",
        "ay_watch_list",
        "ay_proof_witness",
        "ay_rollback",
        "ay_registry",
    ];
    let ty_domains = [
        "ty_runtime",
        "ty_action",
        "ty_invariant",
        "ty_liveness",
        "ty_fingerprint",
        "ty_flat_state",
        "ty_helper_abi",
        "ty_library_publication",
    ];

    let direct_packet = validate_native_install_gate(&installable_input());
    assert_bound_freshness_domains(&direct_packet, &shared_domains);
    assert_bound_freshness_domains(&direct_packet, &ay_domains);
    let direct_names = freshness_domain_names(&direct_packet);
    assert!(!direct_names.contains("ty_runtime"));

    let ay_packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    assert_bound_freshness_domains(&ay_packet, &shared_domains);
    assert_bound_freshness_domains(&ay_packet, &ay_domains);

    let ty_packet = validate_native_install_gate(&ty_prework_input());
    assert_bound_freshness_domains(&ty_packet, &shared_domains);
    assert_bound_freshness_domains(&ty_packet, &ty_domains);
}

#[test]
fn packet_current_revalidation_requires_freshness_domains() {
    let packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );

    let mut missing_domain = packet.clone();
    missing_domain
        .freshness
        .freshness_domains
        .retain(|observation| observation.domain != "ay_solver");
    persist_native_install_gate_packet_bindings(&mut missing_domain);
    let missing_domain_current = NativeInstallGateRevalidationInput::from_packet(&missing_domain);
    assert_runtime_rejects_freshness_packet(
        &missing_domain,
        &missing_domain_current,
        NativeInstallGateRejectionCode::EvidenceBindingMismatch,
    );

    let mut self_consistent_wrong_generation = packet.clone();
    let wrong_generation = self_consistent_wrong_generation
        .freshness
        .current_generation
        + 100;
    {
        let observation = self_consistent_wrong_generation
            .freshness
            .freshness_domains
            .iter_mut()
            .find(|observation| observation.domain == "ay_solver")
            .expect("ay freshness domain is bound");
        observation.observed_generation = wrong_generation;
        observation.current_generation = wrong_generation;
    }
    persist_native_install_gate_packet_bindings(&mut self_consistent_wrong_generation);
    let wrong_generation_current =
        NativeInstallGateRevalidationInput::from_packet(&self_consistent_wrong_generation);
    assert_runtime_rejects_freshness_packet(
        &self_consistent_wrong_generation,
        &wrong_generation_current,
        NativeInstallGateRejectionCode::EvidenceBindingMismatch,
    );

    let mut stale_current = NativeInstallGateRevalidationInput::from_packet(&packet);
    stale_current
        .freshness_domains
        .iter_mut()
        .find(|observation| observation.domain == "ay_solver")
        .expect("ay freshness domain is bound")
        .current_generation += 1;
    assert_runtime_rejects_freshness_packet(
        &packet,
        &stale_current,
        NativeInstallGateRejectionCode::StaleInvalidation,
    );

    let mut stale_packet_domain = packet.clone();
    stale_packet_domain
        .freshness
        .freshness_domains
        .iter_mut()
        .find(|observation| observation.domain == "ay_solver")
        .expect("ay freshness domain is bound")
        .current_generation += 1;
    persist_native_install_gate_packet_bindings(&mut stale_packet_domain);
    let stale_packet_current =
        NativeInstallGateRevalidationInput::from_packet(&stale_packet_domain);
    assert_runtime_rejects_freshness_packet(
        &stale_packet_domain,
        &stale_packet_current,
        NativeInstallGateRejectionCode::StaleInvalidation,
    );
}

#[test]
fn runtime_revalidation_requires_persisted_layout_adapter_bindings() {
    let ay_packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let ty_packet = validate_native_install_gate(&ty_prework_input());

    let mut missing_hash = ay_packet.clone();
    missing_hash.validation.layout_evidence_sha256 = None;
    assert_runtime_rejects_tampered_layout_packet(
        missing_hash,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let mut mismatched_status = ay_packet.clone();
    mismatched_status.validation.layout_status = "mismatch";
    assert_runtime_rejects_tampered_layout_packet(
        mismatched_status,
        NativeInstallGateRejectionCode::LayoutMismatch,
    );

    let mut missing_provenance = ay_packet.clone();
    missing_provenance.validation.layout_validation_provenance = None;
    assert_runtime_rejects_tampered_layout_packet(
        missing_provenance,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let mut stale_layout_invalidation = ay_packet.clone();
    let stale_layout_invalidation_checksum =
        ArtifactChecksum::new(ay_packet.artifact.invalidation_checksum.get() ^ 0x748);
    stale_layout_invalidation
        .validation
        .layout_invalidation_checksum = Some(stale_layout_invalidation_checksum);
    assert_runtime_rejects_tampered_layout_packet(
        stale_layout_invalidation,
        NativeInstallGateRejectionCode::StaleInvalidation,
    );

    let mut missing_ay_domain = ay_packet;
    missing_ay_domain
        .validation
        .layout_generation_domains
        .retain(|domain| domain != "ay_watch_list");
    assert_runtime_rejects_tampered_layout_packet(
        missing_ay_domain,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let mut missing_ty_domain = ty_packet;
    missing_ty_domain
        .validation
        .layout_generation_domains
        .retain(|domain| domain != "ty_fingerprint");
    assert_runtime_rejects_tampered_layout_packet(
        missing_ty_domain,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );
}

#[test]
fn runtime_revalidation_keeps_adapter_backed_non_callable_modes_non_callable() {
    let mut cases = Vec::new();

    for (consumer, surface) in [
        ("ay", NativeInstallGateSurface::AYRegistry),
        ("ty", NativeInstallGateSurface::TyActivation),
    ] {
        let base = if consumer == "ty" {
            ty_prework_input()
        } else {
            activation_input(consumer, surface)
        };

        let mut profile_only = base.clone();
        profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;
        cases.push((
            profile_only,
            NativeInstallGateDisposition::ProfileOnly,
            NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
        ));

        let mut replay_only = base.clone();
        replay_only.candidate_disposition = NativeInstallGateDisposition::ReplayOnly;
        cases.push((
            replay_only,
            NativeInstallGateDisposition::ReplayOnly,
            NativeInstallGateRejectionCode::ReplayOnlyNonInstallable,
        ));

        let mut shadow_only = base;
        shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
        cases.push((
            shadow_only,
            NativeInstallGateDisposition::ShadowOnly,
            NativeInstallGateRejectionCode::ShadowOnlyNonInstallable,
        ));
    }

    for (input, expected_disposition, expected_code) in cases {
        let packet = validate_native_install_gate(&input);
        assert_eq!(packet.disposition, expected_disposition);
        assert_eq!(packet.rejection_code, Some(expected_code));
        assert_eq!(
            packet.validation.layout_status, "accepted",
            "adapter evidence remains valid but non-callable"
        );

        let current = NativeInstallGateRevalidationInput::from_packet(&packet);
        let event = native_install_gate_runtime_telemetry(
            &packet,
            Some(packet.packet_hash),
            &current,
            true,
        );
        assert_eq!(event.disposition, expected_disposition);
        assert_eq!(event.rejection_code, Some(expected_code));
        assert_eq!(event.useful_native_delta, 0);
        assert_blocked(event.actions);
    }
}

#[test]
fn consumer_admission_gates_ay_registry_on_packet_hash_verdict_and_allowlist() {
    let packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);
    let mut registry = AdmissionBackedAYRegistry::default();

    let accepted = registry.insert(&packet, Some(packet.packet_hash), &current, &evidence);
    assert_eq!(
        accepted.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(accepted.rejection_code, None);
    assert_eq!(
        accepted.registry_key.as_deref(),
        Some("ay:artifact.installable")
    );
    assert!(accepted.callable_handle.is_some());
    assert_eq!(accepted.native_handle, None);
    assert_eq!(accepted.useful_native_delta, 0);
    assert_eq!(registry.registry_key, accepted.registry_key);

    let decision = native_install_gate_consumer_admission(
        &packet,
        Some(packet.packet_hash),
        &current,
        &evidence,
    );
    assert_eq!(
        decision.telemetry.schema,
        NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA
    );
    assert_eq!(
        decision.telemetry.schema_version,
        NATIVE_INSTALL_GATE_CONSUMER_ADMISSION_SCHEMA_VERSION
    );
    assert_eq!(decision.telemetry.packet_hash, packet.packet_hash);
    assert_eq!(
        decision.telemetry.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(decision.telemetry.rejection_code, None);
    assert_eq!(decision.telemetry.useful_native_delta, 0);
    assert_eq!(
        decision
            .telemetry
            .install_consumer_verdict_sha256
            .as_deref(),
        Some(packet.consumer_verdict.verdict_sha256.as_str())
    );

    let missing_hash =
        AdmissionBackedAYRegistry::default().insert(&packet, None, &current, &evidence);
    assert_eq!(
        missing_hash.rejection_code,
        Some(NativeInstallGateRejectionCode::MissingPacketHash)
    );
    assert_no_admission_handle(&missing_hash);

    let mut bad_consumer_verdict = packet.clone();
    bad_consumer_verdict.consumer_verdict.verdict_sha256 =
        "sha256:tampered-consumer-verdict".to_owned();
    let bad_verdict_result = AdmissionBackedAYRegistry::default().insert(
        &bad_consumer_verdict,
        Some(bad_consumer_verdict.packet_hash),
        &current,
        &evidence,
    );
    assert_eq!(
        bad_verdict_result.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_no_admission_handle(&bad_verdict_result);

    let mut non_allowlisted = evidence.clone();
    non_allowlisted.allowlist_key = "ay:non-allowlisted-family".to_owned();
    non_allowlisted = non_allowlisted.with_canonical_evidence_sha256();
    let non_allowlisted_result = AdmissionBackedAYRegistry::default().insert(
        &packet,
        Some(packet.packet_hash),
        &current,
        &non_allowlisted,
    );
    assert_eq!(
        non_allowlisted_result.rejection_code,
        Some(NativeInstallGateRejectionCode::UnsupportedConsumer)
    );
    assert_no_admission_handle(&non_allowlisted_result);

    let mut bad_evidence_hash = evidence.clone();
    bad_evidence_hash.evidence_sha256 = "sha256:tampered-admission-evidence".to_owned();
    let bad_evidence_result = AdmissionBackedAYRegistry::default().insert(
        &packet,
        Some(packet.packet_hash),
        &current,
        &bad_evidence_hash,
    );
    assert_eq!(
        bad_evidence_result.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_no_admission_handle(&bad_evidence_result);

    let mut missing_rollback = evidence;
    missing_rollback.rollback_ready = false;
    missing_rollback = missing_rollback.with_canonical_evidence_sha256();
    let missing_rollback_result = AdmissionBackedAYRegistry::default().insert(
        &packet,
        Some(packet.packet_hash),
        &current,
        &missing_rollback,
    );
    assert_eq!(
        missing_rollback_result.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_no_admission_handle(&missing_rollback_result);
}

#[test]
fn consumer_admission_gates_ty_activation_on_runtime_tuple_and_status_readiness() {
    let packet = validate_native_install_gate(&ty_prework_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);
    let mut slot = AdmissionBackedTySlot::default();

    let accepted = slot.activate(&packet, Some(packet.packet_hash), &current, &evidence);
    assert_eq!(
        accepted.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(accepted.rejection_code, None);
    assert_eq!(accepted.registry_key, None);
    assert_eq!(accepted.callable_handle, None);
    assert_eq!(
        accepted.native_handle.as_deref(),
        Some("ty-native:native-sha256")
    );
    assert_eq!(accepted.useful_native_delta, 0);
    assert_eq!(slot.native_handle, accepted.native_handle);

    let mut stale_current = current.clone();
    stale_current.current_generation += 1;
    let stale = AdmissionBackedTySlot::default().activate(
        &packet,
        Some(packet.packet_hash),
        &stale_current,
        &evidence,
    );
    assert_eq!(
        stale.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_no_admission_handle(&stale);

    let mut wrong_generation = evidence.clone();
    wrong_generation.runtime_generation += 1;
    wrong_generation = wrong_generation.with_canonical_evidence_sha256();
    let wrong_generation_result = AdmissionBackedTySlot::default().activate(
        &packet,
        Some(packet.packet_hash),
        &current,
        &wrong_generation,
    );
    assert_eq!(
        wrong_generation_result.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_no_admission_handle(&wrong_generation_result);

    let mut missing_status = evidence.clone();
    missing_status.status_ready = false;
    missing_status = missing_status.with_canonical_evidence_sha256();
    let missing_status_result = AdmissionBackedTySlot::default().activate(
        &packet,
        Some(packet.packet_hash),
        &current,
        &missing_status,
    );
    assert_eq!(
        missing_status_result.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_no_admission_handle(&missing_status_result);

    let mut telemetry_mismatch = evidence;
    telemetry_mismatch.telemetry_record_sha256 = "sha256:wrong-telemetry".to_owned();
    telemetry_mismatch = telemetry_mismatch.with_canonical_evidence_sha256();
    let telemetry_mismatch_result = AdmissionBackedTySlot::default().activate(
        &packet,
        Some(packet.packet_hash),
        &current,
        &telemetry_mismatch,
    );
    assert_eq!(
        telemetry_mismatch_result.rejection_code,
        Some(NativeInstallGateRejectionCode::TelemetryMismatch)
    );
    assert_no_admission_handle(&telemetry_mismatch_result);
}

#[test]
fn consumer_admission_summary_exports_artifact_digests_and_reason_codes() {
    let packet = validate_native_install_gate(&ty_prework_input());
    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = consumer_admission_evidence(&packet, &current);

    let accepted = native_install_gate_consumer_admission(
        &packet,
        Some(packet.packet_hash),
        &current,
        &evidence,
    );
    assert_eq!(accepted.reason_code(), None);
    assert_eq!(accepted.telemetry.reason_code(), None);

    let accepted_summary = accepted.admission_summary(&packet);
    assert_eq!(
        accepted_summary.schema,
        NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA
    );
    assert_eq!(
        accepted_summary.schema_version,
        NATIVE_INSTALL_GATE_ADMISSION_SUMMARY_SCHEMA_VERSION
    );
    assert_eq!(accepted_summary.packet_hash, accepted.packet_hash);
    assert_eq!(accepted_summary.persisted_packet_hash, packet.packet_hash);
    assert_eq!(accepted_summary.consumer, "ty");
    assert_eq!(accepted_summary.consumer_mode, packet.consumer_mode);
    assert_eq!(accepted_summary.surface, "ty_activation");
    assert_eq!(accepted_summary.artifact_id, packet.artifact.artifact_id);
    assert_eq!(
        accepted_summary.trust_ir_sha256,
        packet.artifact.trust_ir_sha256
    );
    assert_eq!(
        accepted_summary.native_payload_sha256,
        packet.artifact.native_payload_sha256
    );
    assert_eq!(accepted_summary.abi_checksum, packet.artifact.abi_checksum);
    assert_eq!(
        accepted_summary.target_checksum,
        packet.artifact.target_checksum
    );
    assert_eq!(accepted_summary.disposition, "installable");
    assert_eq!(accepted_summary.reason_code, None);
    assert_eq!(
        accepted_summary.requested_authority,
        packet.requested_authority.as_str()
    );
    assert_eq!(
        accepted_summary.install_authority,
        accepted.install_authority.as_str()
    );
    assert_eq!(
        accepted_summary.admission_evidence_sha256.as_deref(),
        Some(evidence.evidence_sha256.as_str())
    );
    assert_eq!(accepted_summary.useful_native_delta, 0);

    let packet_summary = packet.admission_summary();
    assert_eq!(packet_summary.reason_code, None);
    assert_eq!(packet_summary.abi_checksum, packet.artifact.abi_checksum);

    let missing_hash = native_install_gate_consumer_admission(&packet, None, &current, &evidence);
    assert_eq!(missing_hash.reason_code(), Some("missing_packet_hash"));
    assert_eq!(
        missing_hash.telemetry.reason_code(),
        Some("missing_packet_hash")
    );
    let rejected_summary = missing_hash.admission_summary(&packet);
    assert_eq!(rejected_summary.disposition, "rejected");
    assert_eq!(rejected_summary.reason_code, Some("missing_packet_hash"));
    assert_eq!(rejected_summary.install_authority, "none");
    assert_eq!(rejected_summary.actions, NativeInstallGateActions::none());
}

#[test]
fn consumer_admission_keeps_non_callable_and_denied_packets_non_callable() {
    let mut cases = Vec::new();

    for (consumer, surface) in [
        ("ay", NativeInstallGateSurface::AYRegistry),
        ("ty", NativeInstallGateSurface::TyActivation),
    ] {
        let base = if consumer == "ty" {
            ty_prework_input()
        } else {
            activation_input(consumer, surface)
        };

        let mut profile_only = base.clone();
        profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;
        cases.push((
            format!("{consumer}_profile_only"),
            profile_only,
            NativeInstallGateDisposition::ProfileOnly,
            NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
        ));

        let mut replay_only = base.clone();
        replay_only.candidate_disposition = NativeInstallGateDisposition::ReplayOnly;
        cases.push((
            format!("{consumer}_replay_only"),
            replay_only,
            NativeInstallGateDisposition::ReplayOnly,
            NativeInstallGateRejectionCode::ReplayOnlyNonInstallable,
        ));

        let mut shadow_only = base.clone();
        shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
        cases.push((
            format!("{consumer}_shadow_only"),
            shadow_only,
            NativeInstallGateDisposition::ShadowOnly,
            NativeInstallGateRejectionCode::ShadowOnlyNonInstallable,
        ));

        let mut revoked = base.clone();
        revoked.revoked = true;
        cases.push((
            format!("{consumer}_revoked"),
            revoked,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::RevokedArtifact,
        ));

        let mut stale = base.clone();
        stale.current_generation += 1;
        cases.push((
            format!("{consumer}_stale"),
            stale,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::StaleInvalidation,
        ));

        let mut kill_switch = base;
        kill_switch.deny_control = Some(scoped_deny_control(
            &kill_switch,
            NativeInstallGateDenyScope::Consumer,
            NativeInstallGateDenyReason::KillSwitch,
        ));
        cases.push((
            format!("{consumer}_kill_switch"),
            kill_switch,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::KillSwitchActive,
        ));
    }

    for (name, input, expected_disposition, expected_code) in cases {
        let packet = validate_native_install_gate(&input);
        let current = NativeInstallGateRevalidationInput::from_packet(&packet);
        let evidence = consumer_admission_evidence(&packet, &current);
        let result = if packet.consumer == "ty" {
            AdmissionBackedTySlot::default().activate(
                &packet,
                Some(packet.packet_hash),
                &current,
                &evidence,
            )
        } else {
            AdmissionBackedAYRegistry::default().insert(
                &packet,
                Some(packet.packet_hash),
                &current,
                &evidence,
            )
        };
        assert_eq!(result.disposition, expected_disposition, "{name}");
        assert_eq!(result.rejection_code, Some(expected_code), "{name}");
        assert_no_admission_handle(&result);
    }
}

#[test]
fn packet_integrity_rejects_schema_version_and_binding_mismatch() {
    let packet = validate_native_install_gate(&installable_input());

    let mut bad_schema = packet.clone();
    bad_schema.schema = "trust-cg.phase6.native_install_gate.future";
    let bad_schema_hash = native_install_gate_packet_hash(&bad_schema);
    bad_schema.packet_hash = bad_schema_hash;
    let verdict = validate_native_install_gate_packet(&bad_schema, Some(bad_schema_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::UnsupportedSchema)
    );
    assert_blocked(verdict.actions);

    let mut bad_version = packet.clone();
    bad_version.schema_version += 1;
    let bad_version_hash = native_install_gate_packet_hash(&bad_version);
    bad_version.packet_hash = bad_version_hash;
    let verdict = validate_native_install_gate_packet(&bad_version, Some(bad_version_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::UnsupportedSchema)
    );
    assert_blocked(verdict.actions);

    let mut bad_replay = packet.clone();
    bad_replay.replay_binding.replay_root_sha256 = "sha256:wrong-replay-root".to_owned();
    let verdict = validate_native_install_gate_packet(&bad_replay, Some(bad_replay.packet_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_blocked(verdict.actions);

    let mut missing_replay = packet.clone();
    missing_replay.replay_binding.replay_root_sha256.clear();
    let verdict =
        validate_native_install_gate_packet(&missing_replay, Some(missing_replay.packet_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_blocked(verdict.actions);

    let mut bad_consumer_verdict = packet.clone();
    bad_consumer_verdict.consumer_verdict.verdict_sha256 = "sha256:wrong-verdict".to_owned();
    let verdict = validate_native_install_gate_packet(
        &bad_consumer_verdict,
        Some(bad_consumer_verdict.packet_hash),
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_blocked(verdict.actions);

    let mut missing_consumer_verdict = packet.clone();
    missing_consumer_verdict.consumer_verdict.verdict_id.clear();
    let verdict = validate_native_install_gate_packet(
        &missing_consumer_verdict,
        Some(missing_consumer_verdict.packet_hash),
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_blocked(verdict.actions);

    let mut missing_telemetry = packet.clone();
    missing_telemetry.telemetry = None;
    persist_native_install_gate_packet_bindings(&mut missing_telemetry);
    let verdict = validate_native_install_gate_packet(
        &missing_telemetry,
        Some(missing_telemetry.packet_hash),
    );
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::MissingTelemetry)
    );
    assert_blocked(verdict.actions);
}

#[test]
fn unknown_rejection_code_ingestion_fails_closed() {
    assert_eq!(
        NativeInstallGateRejectionCode::parse_stable("proof_timeout"),
        NativeInstallGateRejectionCode::ProofTimeout
    );
    assert_eq!(
        NativeInstallGateRejectionCode::parse_stable("future_new_rejection_code"),
        NativeInstallGateRejectionCode::UnknownRejectionCode
    );
    assert_eq!(
        NativeInstallGateRejectionCode::UnknownRejectionCode.as_str(),
        "unknown_rejection_code"
    );
}

#[test]
fn ay_registry_activation_requires_accepted_install_gate_verdict() {
    let mut registry = AYConsumerRegistry::default();
    let accepted_input = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    let accepted_packet = validate_native_install_gate(&accepted_input);

    assert_eq!(
        accepted_packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(accepted_packet.rejection_code, None);
    assert!(accepted_packet.actions.ay_registry_insert);
    assert!(!accepted_packet.actions.ty_native_activate);
    assert!(!accepted_packet.actions.typed_symbol_lookup);

    let accepted = registry.activate(&accepted_input);
    assert_eq!(
        accepted.gate_disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(accepted.gate_rejection_code, None);
    assert!(accepted.callable_exposed);
    assert_eq!(
        accepted.registry_key.as_deref(),
        Some("ay:artifact.installable")
    );
    assert!(accepted.callable_handle.is_some());
    assert_eq!(accepted.native_handle, None);
    assert_eq!(registry.registry_key, accepted.registry_key);

    let mut negative_cases: Vec<(
        &'static str,
        NativeInstallGateInput,
        NativeInstallGateRejectionCode,
    )> = Vec::new();

    let mut profile_only = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;
    negative_cases.push((
        "profile_only",
        profile_only,
        NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
    ));

    let mut verifier_failure = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    set_rejected_proof(
        &mut verifier_failure,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    );
    negative_cases.push((
        "rejected_verifier_failure",
        verifier_failure,
        NativeInstallGateRejectionCode::ProofVerifierFailure,
    ));

    let mut stale = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    set_rejected_proof(
        &mut stale,
        ProofEvidenceVerdict::StaleEvidence,
        ProofEvidenceRejectionCode::StaleEvidence,
    );
    negative_cases.push((
        "stale_evidence",
        stale,
        NativeInstallGateRejectionCode::ProofStaleEvidence,
    ));

    let mut timeout = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    set_rejected_proof(
        &mut timeout,
        ProofEvidenceVerdict::Timeout,
        ProofEvidenceRejectionCode::Timeout,
    );
    negative_cases.push((
        "timeout",
        timeout,
        NativeInstallGateRejectionCode::ProofTimeout,
    ));

    let mut unknown = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    set_rejected_proof(
        &mut unknown,
        ProofEvidenceVerdict::UnknownSolverError,
        ProofEvidenceRejectionCode::UnknownSolverError,
    );
    negative_cases.push((
        "unknown_solver_error",
        unknown,
        NativeInstallGateRejectionCode::ProofUnknown,
    ));

    let mut missing = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    missing.proof_evidence = None;
    negative_cases.push((
        "missing_evidence",
        missing,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    ));

    for (name, input, expected_code) in negative_cases {
        let mut local_registry = AYConsumerRegistry::default();
        let result = local_registry.activate(&input);
        assert_ne!(
            result.gate_disposition,
            NativeInstallGateDisposition::Installable,
            "{name} must not be installable"
        );
        assert_eq!(result.gate_rejection_code, Some(expected_code), "{name}");
        assert_no_consumer_handle(&result);
        assert_eq!(local_registry.registry_key, None, "{name}");
        assert_eq!(local_registry.callable_handle, None, "{name}");
    }
}

#[test]
fn ty_native_activation_requires_accepted_install_gate_verdict() {
    let mut slot = TyNativeSlot::default();
    let accepted_input = ty_prework_input();
    let accepted_packet = validate_native_install_gate(&accepted_input);

    assert_eq!(
        accepted_packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(accepted_packet.rejection_code, None);
    assert!(accepted_packet.actions.ty_native_activate);
    assert!(!accepted_packet.actions.ay_registry_insert);
    assert!(!accepted_packet.actions.typed_symbol_lookup);

    let accepted = slot.activate(&accepted_input);
    assert_eq!(
        accepted.gate_disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(accepted.callable_exposed);
    assert_eq!(accepted.registry_key, None);
    assert_eq!(accepted.callable_handle, None);
    assert_eq!(
        accepted.native_handle.as_deref(),
        Some("ty-native:native-sha256")
    );
    assert_eq!(slot.native_handle, accepted.native_handle);

    let mut rejected = ty_prework_input();
    set_rejected_proof(
        &mut rejected,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    );

    let mut profile_only = ty_prework_input();
    profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;

    let mut replay_only = ty_prework_input();
    replay_only.candidate_disposition = NativeInstallGateDisposition::ReplayOnly;

    let mut shadow_only = ty_prework_input();
    shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;

    let negative_cases = [
        (
            "rejected",
            rejected,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::ProofVerifierFailure,
        ),
        (
            "profile_only",
            profile_only,
            NativeInstallGateDisposition::ProfileOnly,
            NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
        ),
        (
            "replay_only",
            replay_only,
            NativeInstallGateDisposition::ReplayOnly,
            NativeInstallGateRejectionCode::ReplayOnlyNonInstallable,
        ),
        (
            "shadow_only",
            shadow_only,
            NativeInstallGateDisposition::ShadowOnly,
            NativeInstallGateRejectionCode::ShadowOnlyNonInstallable,
        ),
    ];

    for (name, input, expected_disposition, expected_code) in negative_cases {
        let mut local_slot = TyNativeSlot::default();
        let result = local_slot.activate(&input);
        assert_eq!(result.gate_disposition, expected_disposition, "{name}");
        assert_eq!(result.gate_rejection_code, Some(expected_code), "{name}");
        assert_no_consumer_handle(&result);
        assert_eq!(local_slot.native_handle, None, "{name}");
    }
}

#[test]
fn consumer_activation_telemetry_separates_install_and_useful_native_events() {
    let mut telemetry = ConsumerActivationTelemetry::default();
    let mut registry = AYConsumerRegistry::default();

    let accepted = registry.activate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    telemetry.record_gate(&accepted);
    assert_eq!(telemetry.install_accepted, 1);
    assert_eq!(
        telemetry.useful_native, 0,
        "install acceptance is not a useful-native execution"
    );

    telemetry.record_useful_native_execution(&accepted);
    assert_eq!(telemetry.useful_native, 1);

    let mut rejected = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    set_rejected_proof(
        &mut rejected,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    );
    telemetry.record_gate(&AYConsumerRegistry::default().activate(&rejected));

    let mut revoked = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    revoked.revoked = true;
    telemetry.record_gate(&AYConsumerRegistry::default().activate(&revoked));

    let mut stale = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    stale.current_generation += 1;
    telemetry.record_gate(&AYConsumerRegistry::default().activate(&stale));

    let mut fallback = activation_input("ty", NativeInstallGateSurface::TyActivation);
    fallback.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
    telemetry.record_gate(&TyNativeSlot::default().activate(&fallback));

    assert_eq!(
        telemetry,
        ConsumerActivationTelemetry {
            install_accepted: 1,
            install_rejected: 1,
            install_revoked: 1,
            install_stale: 1,
            fallback_baseline: 1,
            useful_native: 1,
        }
    );
}

#[test]
fn deny_only_control_plane_scopes_reject_without_install_actions() {
    let mut cases: Vec<(
        &'static str,
        NativeInstallGateInput,
        NativeInstallGateDenyScope,
        NativeInstallGateDenyReason,
        NativeInstallGateRejectionCode,
    )> = vec![
        (
            "global_kill_switch",
            installable_input(),
            NativeInstallGateDenyScope::Global,
            NativeInstallGateDenyReason::KillSwitch,
            NativeInstallGateRejectionCode::KillSwitchActive,
        ),
        (
            "consumer_kill_switch",
            activation_input("ay", NativeInstallGateSurface::AYRegistry),
            NativeInstallGateDenyScope::Consumer,
            NativeInstallGateDenyReason::KillSwitch,
            NativeInstallGateRejectionCode::KillSwitchActive,
        ),
        (
            "family_mode_disablement",
            ty_prework_input(),
            NativeInstallGateDenyScope::Family,
            NativeInstallGateDenyReason::KillSwitch,
            NativeInstallGateRejectionCode::KillSwitchActive,
        ),
        (
            "artifact_revocation",
            activation_input("ay", NativeInstallGateSurface::CacheHit),
            NativeInstallGateDenyScope::Artifact,
            NativeInstallGateDenyReason::Revoked,
            NativeInstallGateRejectionCode::RevokedArtifact,
        ),
        (
            "target_proof_policy_revocation",
            activation_input("ay", NativeInstallGateSurface::ReleaseBundle),
            NativeInstallGateDenyScope::TargetProofPolicy,
            NativeInstallGateDenyReason::Revoked,
            NativeInstallGateRejectionCode::RevokedArtifact,
        ),
        (
            "requested_mode_kill_switch",
            installable_input(),
            NativeInstallGateDenyScope::Mode,
            NativeInstallGateDenyReason::KillSwitch,
            NativeInstallGateRejectionCode::KillSwitchActive,
        ),
        (
            "surface_stale_generation",
            activation_input("ay", NativeInstallGateSurface::CacheHit),
            NativeInstallGateDenyScope::Surface,
            NativeInstallGateDenyReason::StaleFreshness,
            NativeInstallGateRejectionCode::StaleInvalidation,
        ),
    ];

    for (name, mut input, scope, reason, expected_code) in cases.drain(..) {
        input.deny_control = Some(scoped_deny_control(&input, scope, reason));

        let packet = validate_native_install_gate(&input);
        let verdict = validate_native_install_gate_packet(&packet, Some(packet.packet_hash));

        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "{name}"
        );
        assert_eq!(packet.rejection_code, Some(expected_code), "{name}");
        assert_eq!(packet.install_authority, NativeInstallGateAuthority::None);
        assert_blocked(packet.actions);
        assert!(
            !packet.actions.expose_callable
                && !packet.actions.ay_registry_insert
                && !packet.actions.ty_native_activate
                && !packet.actions.accept_installable_cache_hit
                && !packet.actions.release_installable
                && !packet.actions.useful_native_eligible,
            "{name} must remain deny-only"
        );
        assert!(packet.freshness.deny_control.is_some(), "{name}");
        assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
        assert_eq!(verdict.rejection_code, Some(expected_code), "{name}");
        assert_eq!(verdict.deny_control, packet.freshness.deny_control);
        assert_blocked(verdict.actions);
    }
}

#[test]
fn deny_only_control_plane_rejects_tampered_or_incomplete_packets() {
    let mut tampered = installable_input();
    let mut tampered_deny = scoped_deny_control(
        &tampered,
        NativeInstallGateDenyScope::Global,
        NativeInstallGateDenyReason::KillSwitch,
    );
    tampered_deny.deny_sha256 = Some("sha256:tampered-deny-control".to_owned());
    tampered.deny_control = Some(tampered_deny);
    let packet = validate_native_install_gate(&tampered);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_blocked(packet.actions);

    let mut missing_hash = installable_input();
    let mut missing_hash_deny = scoped_deny_control(
        &missing_hash,
        NativeInstallGateDenyScope::Global,
        NativeInstallGateDenyReason::KillSwitch,
    );
    missing_hash_deny.deny_sha256 = None;
    missing_hash.deny_control = Some(missing_hash_deny);
    let packet = validate_native_install_gate(&missing_hash);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_blocked(packet.actions);

    let mut stale_without_stale_domain = installable_input();
    let mut stale_deny = scoped_deny_control(
        &stale_without_stale_domain,
        NativeInstallGateDenyScope::Global,
        NativeInstallGateDenyReason::StaleFreshness,
    );
    stale_deny.freshness = vec![NativeInstallGateFreshnessObservation::new(
        "shared_artifact_generation",
        stale_without_stale_domain.current_generation,
        stale_without_stale_domain.current_generation,
    )];
    stale_deny = stale_deny.with_canonical_deny_sha256();
    stale_without_stale_domain.deny_control = Some(stale_deny);
    let packet = validate_native_install_gate(&stale_without_stale_domain);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::EvidenceBindingMismatch)
    );
    assert_blocked(packet.actions);
}

#[test]
fn inactive_or_non_matching_deny_control_does_not_bypass_existing_gate_checks() {
    let mut inactive = installable_input();
    inactive.deny_control = Some(
        NativeInstallGateDenyControlPlane::inactive(
            NativeInstallGateDenyScope::Global,
            NativeInstallGateDenyReason::KillSwitch,
        )
        .with_canonical_deny_sha256(),
    );
    let packet = validate_native_install_gate(&inactive);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(packet.actions.expose_callable);
    assert!(packet.actions.useful_native_eligible);
    assert!(packet.freshness.deny_control.is_some());

    let mut non_matching = installable_input();
    let mut consumer_deny = NativeInstallGateDenyControlPlane::active(
        NativeInstallGateDenyScope::Consumer,
        NativeInstallGateDenyReason::KillSwitch,
    );
    consumer_deny.consumer = Some("ty".to_owned());
    non_matching.deny_control = Some(consumer_deny.with_canonical_deny_sha256());
    let packet = validate_native_install_gate(&non_matching);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(packet.actions.expose_callable);

    let mut still_requires_proof = installable_input();
    still_requires_proof.proof_evidence = None;
    still_requires_proof.deny_control = Some(
        NativeInstallGateDenyControlPlane::inactive(
            NativeInstallGateDenyScope::Global,
            NativeInstallGateDenyReason::KillSwitch,
        )
        .with_canonical_deny_sha256(),
    );
    let packet = validate_native_install_gate(&still_requires_proof);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::ProofMissingEvidence)
    );
    assert_blocked(packet.actions);
}

fn assert_reject(
    mut input: NativeInstallGateInput,
    expected_disposition: NativeInstallGateDisposition,
    expected_code: NativeInstallGateRejectionCode,
) {
    let packet = validate_native_install_gate(&input);
    assert_eq!(packet.disposition, expected_disposition);
    assert_eq!(packet.rejection_code, Some(expected_code));
    assert_eq!(packet.requested_authority, input.requested_authority);
    assert!(!packet.is_installable());
    assert_blocked(packet.actions);
    let verdict = validate_native_install_gate_packet(&packet, Some(packet.packet_hash));
    assert_eq!(verdict.disposition, expected_disposition);
    assert_eq!(verdict.rejection_code, Some(expected_code));
    assert_eq!(verdict.requested_authority, input.requested_authority);
    assert_blocked(verdict.actions);

    input.surface = NativeInstallGateSurface::CacheInsert;
    let packet = validate_native_install_gate(&input);
    assert_eq!(packet.rejection_code, Some(expected_code));
    assert_eq!(packet.requested_authority, input.requested_authority);
    assert_blocked(packet.actions);
}

fn assert_non_installable_fixture_packet(
    name: &str,
    packet: &NativeInstallGatePacket,
    expected_disposition: NativeInstallGateDisposition,
    expected_code: NativeInstallGateRejectionCode,
) {
    assert_eq!(packet.disposition, expected_disposition, "{name}");
    assert_eq!(packet.rejection_code, Some(expected_code), "{name}");
    assert_eq!(
        packet.install_authority,
        NativeInstallGateAuthority::None,
        "{name}"
    );
    assert_blocked(packet.actions);
    assert!(
        !packet.actions.expose_callable
            && !packet.actions.typed_symbol_lookup
            && !packet.actions.insert_installable_cache
            && !packet.actions.accept_installable_cache_hit
            && !packet.actions.release_installable
            && !packet.actions.ay_registry_insert
            && !packet.actions.ty_native_activate
            && !packet.actions.useful_native_eligible,
        "{name} must expose no install-authorizing action"
    );
    assert_ne!(packet.packet_hash, ArtifactChecksum::new(0), "{name}");
    assert_ne!(
        packet.replay_binding.packet_hash,
        ArtifactChecksum::new(0),
        "{name}"
    );
    assert!(
        packet
            .replay_binding
            .replay_root_sha256
            .starts_with("sha256:"),
        "{name}"
    );
    assert!(
        packet
            .consumer_verdict
            .verdict_sha256
            .starts_with("sha256:"),
        "{name}"
    );
    if let Some(telemetry) = &packet.telemetry {
        assert_eq!(
            telemetry.useful_native_delta, 0,
            "{name} rejected telemetry must not carry useful-native deltas"
        );
        assert!(telemetry.record_sha256.starts_with("sha256:"), "{name}");
    }
}

fn assert_non_installable_input_fixture(
    name: &str,
    input: NativeInstallGateInput,
    expected_disposition: NativeInstallGateDisposition,
    expected_code: NativeInstallGateRejectionCode,
) {
    let packet = validate_native_install_gate(&input);
    assert_non_installable_fixture_packet(name, &packet, expected_disposition, expected_code);
    let verdict = validate_native_install_gate_packet(&packet, Some(packet.packet_hash));
    assert_eq!(verdict.disposition, expected_disposition, "{name}");
    assert_eq!(verdict.rejection_code, Some(expected_code), "{name}");
    assert_eq!(
        verdict.install_authority,
        NativeInstallGateAuthority::None,
        "{name}"
    );
    assert_blocked(verdict.actions);
}

fn assert_non_installable_persisted_packet_fixture(
    name: &str,
    packet: &NativeInstallGatePacket,
    expected_packet_hash: Option<ArtifactChecksum>,
    expected_code: NativeInstallGateRejectionCode,
) {
    let verdict = validate_native_install_gate_packet(packet, expected_packet_hash);
    assert_eq!(
        verdict.disposition,
        NativeInstallGateDisposition::Rejected,
        "{name}"
    );
    assert_eq!(verdict.rejection_code, Some(expected_code), "{name}");
    assert_eq!(
        verdict.install_authority,
        NativeInstallGateAuthority::None,
        "{name}"
    );
    assert_blocked(verdict.actions);
    if let Some(telemetry) = &packet.telemetry {
        assert_eq!(
            telemetry.useful_native_delta, 0,
            "{name} persisted packet telemetry must not carry useful-native deltas"
        );
    }
}

#[test]
fn data_only_non_installable_fixture_suite_covers_gate_rejections() {
    let mut fixtures: Vec<(
        &'static str,
        NativeInstallGateInput,
        NativeInstallGateDisposition,
        NativeInstallGateRejectionCode,
    )> = Vec::new();

    let mut missing_manifest = installable_input();
    missing_manifest.manifest = None;
    fixtures.push((
        "missing_manifest",
        missing_manifest,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingManifest,
    ));

    let mut missing_manifest_reference = installable_input();
    missing_manifest_reference.manifest_reference = None;
    fixtures.push((
        "missing_manifest_reference",
        missing_manifest_reference,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingManifest,
    ));

    let mut artifact_identity = installable_input();
    artifact_identity
        .candidate_payload_identity
        .native_payload_sha256 = "sha256:wrong-native-payload".to_owned();
    fixtures.push((
        "artifact_identity_mismatch",
        artifact_identity,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ArtifactIdentityMismatch,
    ));

    let mut abi_checksum = installable_input();
    abi_checksum
        .manifest_reference
        .as_mut()
        .expect("test input has manifest reference")
        .abi_checksum = ArtifactChecksum::new(0);
    fixtures.push((
        "missing_abi_checksum",
        abi_checksum,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::AbiMismatch,
    ));

    let mut layout_mismatch = installable_input();
    layout_mismatch
        .layout_evidence
        .as_mut()
        .expect("test input has layout evidence")
        .layout_checksum = ArtifactChecksum::new(99);
    fixtures.push((
        "layout_mismatch",
        layout_mismatch,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::LayoutMismatch,
    ));

    let mut missing_layout_evidence = installable_input();
    missing_layout_evidence.layout_evidence = None;
    fixtures.push((
        "missing_layout_evidence",
        missing_layout_evidence,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    ));

    let mut generic_ty_layout = activation_input("ty", NativeInstallGateSurface::TyActivation);
    generic_ty_layout.layout_evidence = Some(generic_layout_evidence(
        generic_ty_layout
            .manifest
            .as_ref()
            .expect("generic input has manifest"),
    ));
    fixtures.push((
        "generic_ty_layout",
        generic_ty_layout,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    ));

    let mut missing_proof = installable_input();
    missing_proof.proof_evidence = None;
    fixtures.push((
        "missing_proof",
        missing_proof,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    ));

    let mut verifier_failure = installable_input();
    set_rejected_proof(
        &mut verifier_failure,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    );
    fixtures.push((
        "verifier_failure",
        verifier_failure,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofVerifierFailure,
    ));

    let mut timeout = installable_input();
    set_rejected_proof(
        &mut timeout,
        ProofEvidenceVerdict::Timeout,
        ProofEvidenceRejectionCode::Timeout,
    );
    fixtures.push((
        "proof_timeout",
        timeout,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofTimeout,
    ));

    let mut unknown = installable_input();
    set_rejected_proof(
        &mut unknown,
        ProofEvidenceVerdict::UnknownSolverError,
        ProofEvidenceRejectionCode::UnknownSolverError,
    );
    fixtures.push((
        "proof_unknown",
        unknown,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofUnknown,
    ));

    let mut stale_proof = installable_input();
    set_rejected_proof(
        &mut stale_proof,
        ProofEvidenceVerdict::StaleEvidence,
        ProofEvidenceRejectionCode::StaleEvidence,
    );
    fixtures.push((
        "stale_proof",
        stale_proof,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofStaleEvidence,
    ));

    let mut stale_invalidation = installable_input();
    stale_invalidation.current_generation += 1;
    fixtures.push((
        "stale_invalidation",
        stale_invalidation,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::StaleInvalidation,
    ));

    let mut missing_telemetry = installable_input();
    missing_telemetry.telemetry = None;
    fixtures.push((
        "missing_telemetry",
        missing_telemetry,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingTelemetry,
    ));

    let mut telemetry_hash = installable_input();
    telemetry_hash
        .telemetry
        .as_mut()
        .expect("test input has telemetry")
        .record_sha256 = "sha256:tampered-telemetry-record".to_owned();
    fixtures.push((
        "telemetry_hash_mismatch",
        telemetry_hash,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::TelemetryMismatch,
    ));

    let mut missing_replay_identity = installable_input();
    missing_replay_identity.replay_identity = None;
    fixtures.push((
        "missing_replay_identity",
        missing_replay_identity,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingReplayIdentity,
    ));

    let mut replay_root = installable_input();
    replay_root
        .replay_identity
        .as_mut()
        .expect("test input has replay identity")
        .replay_root_sha256 = "sha256:wrong-replay-root".to_owned();
    fixtures.push((
        "replay_root_mismatch",
        replay_root,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ReplayIdentityMismatch,
    ));

    let mut profile_only = installable_input();
    profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;
    fixtures.push((
        "profile_only",
        profile_only,
        NativeInstallGateDisposition::ProfileOnly,
        NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
    ));

    let mut replay_only = installable_input();
    replay_only.candidate_disposition = NativeInstallGateDisposition::ReplayOnly;
    fixtures.push((
        "replay_only",
        replay_only,
        NativeInstallGateDisposition::ReplayOnly,
        NativeInstallGateRejectionCode::ReplayOnlyNonInstallable,
    ));

    let mut shadow_only = installable_input();
    shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
    fixtures.push((
        "shadow_only",
        shadow_only,
        NativeInstallGateDisposition::ShadowOnly,
        NativeInstallGateRejectionCode::ShadowOnlyNonInstallable,
    ));

    let mut revoked = installable_input();
    revoked.revoked = true;
    fixtures.push((
        "revoked",
        revoked,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::RevokedArtifact,
    ));

    let mut kill_switch = installable_input();
    kill_switch.deny_control = Some(scoped_deny_control(
        &kill_switch,
        NativeInstallGateDenyScope::Global,
        NativeInstallGateDenyReason::KillSwitch,
    ));
    fixtures.push((
        "kill_switch",
        kill_switch,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::KillSwitchActive,
    ));

    let mut unsupported_consumer = installable_input();
    unsupported_consumer.consumer = "other-consumer".to_owned();
    fixtures.push((
        "unsupported_consumer",
        unsupported_consumer,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::UnsupportedConsumer,
    ));

    for (name, input, expected_disposition, expected_code) in fixtures {
        assert_non_installable_input_fixture(name, input, expected_disposition, expected_code);
    }
}

#[test]
fn data_only_non_installable_fixture_suite_covers_persisted_packet_rejections() {
    let base = validate_native_install_gate(&installable_input());

    let mut bad_schema = base.clone();
    bad_schema.schema = "trust-cg.phase6.native_install_gate.future";
    let bad_schema_hash = native_install_gate_packet_hash(&bad_schema);
    bad_schema.packet_hash = bad_schema_hash;
    assert_non_installable_persisted_packet_fixture(
        "bad_schema",
        &bad_schema,
        Some(bad_schema_hash),
        NativeInstallGateRejectionCode::UnsupportedSchema,
    );

    let mut bad_schema_version = base.clone();
    bad_schema_version.schema_version += 1;
    let bad_schema_version_hash = native_install_gate_packet_hash(&bad_schema_version);
    bad_schema_version.packet_hash = bad_schema_version_hash;
    assert_non_installable_persisted_packet_fixture(
        "bad_schema_version",
        &bad_schema_version,
        Some(bad_schema_version_hash),
        NativeInstallGateRejectionCode::UnsupportedSchema,
    );

    assert_non_installable_persisted_packet_fixture(
        "packet_hash_mismatch",
        &base,
        Some(ArtifactChecksum::new(
            base.packet_hash.get().wrapping_add(1),
        )),
        NativeInstallGateRejectionCode::PacketHashMismatch,
    );

    let mut bad_replay = base.clone();
    bad_replay.replay_binding.replay_root_sha256 = "sha256:wrong-replay-root".to_owned();
    assert_non_installable_persisted_packet_fixture(
        "bad_replay_binding",
        &bad_replay,
        Some(bad_replay.packet_hash),
        NativeInstallGateRejectionCode::EvidenceBindingMismatch,
    );

    let mut bad_consumer_verdict = base.clone();
    bad_consumer_verdict.consumer_verdict.verdict_sha256 = "sha256:wrong-verdict".to_owned();
    assert_non_installable_persisted_packet_fixture(
        "bad_consumer_verdict",
        &bad_consumer_verdict,
        Some(bad_consumer_verdict.packet_hash),
        NativeInstallGateRejectionCode::EvidenceBindingMismatch,
    );

    let mut extra_action = base.clone();
    extra_action.actions.release_installable = true;
    persist_native_install_gate_packet_bindings(&mut extra_action);
    assert_non_installable_persisted_packet_fixture(
        "inconsistent_actions",
        &extra_action,
        Some(extra_action.packet_hash),
        NativeInstallGateRejectionCode::InconsistentActionAuthority,
    );
}

#[test]
fn end_to_end_non_installable_fixture_suite_blocks_consumer_publication_paths() {
    let mut fixtures: Vec<(
        String,
        NativeInstallGateInput,
        NativeInstallGateDisposition,
        NativeInstallGateRejectionCode,
    )> = Vec::new();
    push_end_to_end_non_installable_fixtures(&mut fixtures, "ay");
    push_end_to_end_non_installable_fixtures(&mut fixtures, "ty");

    for (name, input, expected_disposition, expected_code) in fixtures {
        assert_end_to_end_non_installable_fixture(
            &name,
            input,
            expected_disposition,
            expected_code,
        );
    }
}

#[test]
fn end_to_end_fixture_suite_blocks_stale_call_and_non_allowlisted_admission() {
    let ay_packet = validate_native_install_gate(&activation_input(
        "ay",
        NativeInstallGateSurface::AYRegistry,
    ));
    let ay_current = NativeInstallGateRevalidationInput::from_packet(&ay_packet);
    let ay_evidence = consumer_admission_evidence(&ay_packet, &ay_current);

    let mut stale_call_current = ay_current.clone();
    stale_call_current.current_generation += 1;
    let stale_event = native_install_gate_runtime_telemetry(
        &ay_packet,
        Some(ay_packet.packet_hash),
        &stale_call_current,
        true,
    );
    assert_eq!(
        stale_event.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_eq!(stale_event.useful_native_delta, 0);
    assert_blocked(stale_event.actions);

    let stale_publication = consumer_publication_attempt(
        &ay_packet,
        Some(ay_packet.packet_hash),
        &stale_call_current,
        &ay_evidence,
    );
    assert_eq!(
        stale_publication.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert_no_admission_handle(&stale_publication);

    let mut non_allowlisted_ay = ay_evidence.clone();
    non_allowlisted_ay.allowlist_key = "ay:non-allowlisted-family".to_owned();
    non_allowlisted_ay = non_allowlisted_ay.with_canonical_evidence_sha256();
    let non_allowlisted_ay_publication = consumer_publication_attempt(
        &ay_packet,
        Some(ay_packet.packet_hash),
        &ay_current,
        &non_allowlisted_ay,
    );
    assert_eq!(
        non_allowlisted_ay_publication.rejection_code,
        Some(NativeInstallGateRejectionCode::UnsupportedConsumer)
    );
    assert_no_admission_handle(&non_allowlisted_ay_publication);

    let ty_packet = validate_native_install_gate(&ty_prework_input());
    let ty_current = NativeInstallGateRevalidationInput::from_packet(&ty_packet);
    let mut non_allowlisted_ty = consumer_admission_evidence(&ty_packet, &ty_current);
    non_allowlisted_ty.allowlist_key = "ty:non-allowlisted-spec-action".to_owned();
    non_allowlisted_ty = non_allowlisted_ty.with_canonical_evidence_sha256();
    let non_allowlisted_ty_publication = consumer_publication_attempt(
        &ty_packet,
        Some(ty_packet.packet_hash),
        &ty_current,
        &non_allowlisted_ty,
    );
    assert_eq!(
        non_allowlisted_ty_publication.rejection_code,
        Some(NativeInstallGateRejectionCode::UnsupportedConsumer)
    );
    assert_no_admission_handle(&non_allowlisted_ty_publication);
}

#[test]
fn end_to_end_control_plane_bridge_suite_keeps_non_installable_artifacts_non_public() {
    for consumer in ["ay", "ty"] {
        let base_input = end_to_end_input_for_consumer(consumer);
        let mut fixtures: Vec<(
            String,
            NativeInstallGateInput,
            NativeInstallGateDisposition,
            NativeInstallGateRejectionCode,
        )> = Vec::new();

        let mut missing_manifest = base_input.clone();
        missing_manifest.manifest = None;
        fixtures.push((
            format!("{consumer}_bridge_missing_manifest"),
            missing_manifest,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::MissingManifest,
        ));

        let mut layout_mismatch = base_input.clone();
        layout_mismatch
            .layout_evidence
            .as_mut()
            .expect("test input has layout evidence")
            .layout_checksum = ArtifactChecksum::new(99);
        fixtures.push((
            format!("{consumer}_bridge_layout_mismatch"),
            layout_mismatch,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::LayoutMismatch,
        ));

        let mut verifier_failure = base_input.clone();
        set_rejected_proof(
            &mut verifier_failure,
            ProofEvidenceVerdict::VerifierFailure,
            ProofEvidenceRejectionCode::VerifierFailure,
        );
        fixtures.push((
            format!("{consumer}_bridge_verifier_failure"),
            verifier_failure,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::ProofVerifierFailure,
        ));

        let mut stale_install = base_input.clone();
        stale_install.current_generation += 1;
        fixtures.push((
            format!("{consumer}_bridge_stale_install"),
            stale_install,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::StaleInvalidation,
        ));

        let mut missing_telemetry = base_input.clone();
        missing_telemetry.telemetry = None;
        fixtures.push((
            format!("{consumer}_bridge_missing_telemetry"),
            missing_telemetry,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::MissingTelemetry,
        ));

        let mut telemetry_hash_mismatch = base_input.clone();
        telemetry_hash_mismatch
            .telemetry
            .as_mut()
            .expect("test input has telemetry")
            .record_sha256 = "sha256:tampered-telemetry-record".to_owned();
        fixtures.push((
            format!("{consumer}_bridge_telemetry_hash_mismatch"),
            telemetry_hash_mismatch,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::TelemetryMismatch,
        ));

        for (name, input, expected_disposition, expected_code) in fixtures {
            let packet = validate_native_install_gate(&input);
            let current = NativeInstallGateRevalidationInput::from_packet(&packet);
            let evidence = consumer_admission_evidence(&packet, &current);
            let control = JitEverywhereControlPlane::new();
            let candidate =
                control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
            let decision = control.route_new_call(&candidate, gate_accepted());

            assert_control_plane_bridge_non_public_fixture(
                &name,
                &packet,
                &decision,
                &evidence,
                expected_disposition,
                expected_code,
                true,
            );
        }

        let accepted_packet = validate_native_install_gate(&base_input);
        let accepted_current = NativeInstallGateRevalidationInput::from_packet(&accepted_packet);
        let accepted_evidence = consumer_admission_evidence(&accepted_packet, &accepted_current);
        let candidate = control_plane_candidate_for_packet(
            &accepted_packet,
            ControlPlaneMode::CanaryInstallable,
        );

        let mut kill_switch_control = JitEverywhereControlPlane::new();
        kill_switch_control.add_kill_switch(ControlPlaneKillSwitch::consumer(
            consumer,
            "product admission off",
        ));
        let kill_switch_decision = kill_switch_control.route_new_call(&candidate, gate_accepted());
        assert_control_plane_bridge_non_public_fixture(
            &format!("{consumer}_bridge_control_plane_kill_switch"),
            &accepted_packet,
            &kill_switch_decision,
            &accepted_evidence,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::KillSwitchActive,
            true,
        );

        let mut revocation_control = JitEverywhereControlPlane::new();
        revocation_control.revoke_artifact(ControlPlaneRevocation::active(
            candidate.artifact_sha256.clone(),
            candidate.replay_root_sha256.clone(),
            candidate.telemetry_key.clone(),
            "product admission revoked",
        ));
        let revocation_decision = revocation_control.route_new_call(&candidate, gate_accepted());
        assert_control_plane_bridge_non_public_fixture(
            &format!("{consumer}_bridge_control_plane_revocation"),
            &accepted_packet,
            &revocation_decision,
            &accepted_evidence,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::RevokedArtifact,
            true,
        );

        let mut non_allowlisted_evidence = accepted_evidence;
        non_allowlisted_evidence.allowlist_key = format!("{consumer}:non-allowlisted-family");
        non_allowlisted_evidence = non_allowlisted_evidence.with_canonical_evidence_sha256();
        let control = JitEverywhereControlPlane::new();
        let allowlist_decision = control.route_new_call(&candidate, gate_accepted());
        assert_control_plane_bridge_non_public_fixture(
            &format!("{consumer}_bridge_non_allowlisted_family"),
            &accepted_packet,
            &allowlist_decision,
            &non_allowlisted_evidence,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::UnsupportedConsumer,
            false,
        );
    }
}

#[test]
fn end_to_end_product_adapter_bridge_suite_keeps_non_installable_artifacts_non_public() {
    let mut fixtures: Vec<(
        String,
        NativeInstallGateInput,
        NativeInstallGateDisposition,
        NativeInstallGateRejectionCode,
    )> = Vec::new();
    push_end_to_end_non_installable_fixtures(&mut fixtures, "ay");
    push_end_to_end_non_installable_fixtures(&mut fixtures, "ty");

    for (name, input, expected_disposition, expected_code) in fixtures {
        let packet = validate_native_install_gate(&input);
        assert_non_installable_fixture_packet(&name, &packet, expected_disposition, expected_code);

        let current = NativeInstallGateRevalidationInput::from_packet(&packet);
        let runtime_event = native_install_gate_runtime_telemetry(
            &packet,
            Some(packet.packet_hash),
            &current,
            true,
        );
        assert_eq!(runtime_event.disposition, expected_disposition, "{name}");
        assert_eq!(runtime_event.rejection_code, Some(expected_code), "{name}");
        assert_eq!(runtime_event.useful_native_delta, 0, "{name}");
        assert_blocked(runtime_event.actions);

        let evidence = consumer_admission_evidence(&packet, &current);
        assert_product_adapter_bridge_non_public_fixture(
            &name,
            &packet,
            &evidence,
            JitEverywhereControlPlane::new(),
            expected_disposition,
            expected_code,
        );
    }

    for consumer in ["ay", "ty"] {
        let packet = validate_native_install_gate(&end_to_end_input_for_consumer(consumer));
        let current = NativeInstallGateRevalidationInput::from_packet(&packet);
        let evidence = consumer_admission_evidence(&packet, &current);
        let candidate =
            control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);

        let mut non_allowlisted = evidence.clone();
        non_allowlisted.allowlist_key = format!("{consumer}:non-allowlisted-family");
        non_allowlisted = non_allowlisted.with_canonical_evidence_sha256();
        assert_product_adapter_bridge_non_public_fixture(
            &format!("{consumer}_product_adapter_non_allowlisted_family"),
            &packet,
            &non_allowlisted,
            JitEverywhereControlPlane::new(),
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::UnsupportedConsumer,
        );

        let mut kill_switch_control = JitEverywhereControlPlane::new();
        kill_switch_control.add_kill_switch(ControlPlaneKillSwitch::consumer(
            consumer,
            "product adapter bridge off",
        ));
        assert_product_adapter_bridge_non_public_fixture(
            &format!("{consumer}_product_adapter_control_plane_kill_switch"),
            &packet,
            &evidence,
            kill_switch_control,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::KillSwitchActive,
        );

        let mut revocation_control = JitEverywhereControlPlane::new();
        revocation_control.revoke_artifact(ControlPlaneRevocation::active(
            candidate.artifact_sha256.clone(),
            candidate.replay_root_sha256.clone(),
            candidate.telemetry_key.clone(),
            "product adapter bridge revoked",
        ));
        assert_product_adapter_bridge_non_public_fixture(
            &format!("{consumer}_product_adapter_control_plane_revocation"),
            &packet,
            &evidence,
            revocation_control,
            NativeInstallGateDisposition::Rejected,
            NativeInstallGateRejectionCode::RevokedArtifact,
        );
    }
}

#[test]
fn product_adapter_bridge_binds_call_status_identity_without_product_promotion() {
    for consumer in ["ay", "ty"] {
        let packet = validate_native_install_gate(&end_to_end_input_for_consumer(consumer));
        let current = NativeInstallGateRevalidationInput::from_packet(&packet);
        let evidence = consumer_admission_evidence(&packet, &current);
        let candidate =
            control_plane_candidate_for_packet(&packet, ControlPlaneMode::CanaryInstallable);
        let mut control = JitEverywhereControlPlane::new();
        control.record_existing_product_publication(&candidate);

        let bridge = control.route_consumer_admission_product_adapter_with_current(
            &candidate,
            gate_accepted(),
            &packet,
            Some(packet.packet_hash),
            &current,
            &evidence,
        );

        assert_eq!(
            bridge.consumer_admission.disposition,
            NativeInstallGateDisposition::Installable,
            "{consumer}"
        );
        assert_eq!(bridge.consumer_admission.rejection_code, None, "{consumer}");
        assert!(bridge.product_adapter.denied_without_product_authority());
        assert!(
            bridge.publication_blocked_without_product_authority(),
            "{consumer}"
        );
        assert_eq!(
            bridge.product_adapter.callable_handle_id, None,
            "{consumer}"
        );
        assert_eq!(bridge.product_adapter.native_handle_id, None, "{consumer}");
        assert!(
            !bridge.product_adapter.installable_cache_hit_accepted,
            "{consumer}"
        );
        assert_eq!(bridge.product_adapter.useful_native_delta, 0, "{consumer}");
        assert_eq!(
            bridge.product_adapter.telemetry.callable_handle_id, None,
            "{consumer}"
        );
        assert_eq!(
            bridge.product_adapter.telemetry.native_handle_id, None,
            "{consumer}"
        );
        assert_eq!(
            bridge.product_adapter.telemetry.useful_native_delta, 0,
            "{consumer}"
        );
        assert_eq!(
            bridge.call_time_revalidation.useful_native_delta, 0,
            "{consumer}"
        );
        assert_eq!(bridge.call_status.useful_native_delta, 0, "{consumer}");
        assert_eq!(bridge.useful_native_delta, 0, "{consumer}");
        assert!(!bridge.publish_ay_registry_entry, "{consumer}");
        assert!(!bridge.activate_ty_native_handle, "{consumer}");
        assert!(!bridge.expose_callable_handle, "{consumer}");
        match consumer {
            "ay" => {
                assert!(bridge.consumer_allows_ay_registry, "{consumer}");
                assert!(!bridge.consumer_allows_ty_activation, "{consumer}");
            }
            "ty" => {
                assert!(!bridge.consumer_allows_ay_registry, "{consumer}");
                assert!(bridge.consumer_allows_ty_activation, "{consumer}");
            }
            _ => unreachable!(),
        }
        assert_eq!(
            bridge.product_adapter.telemetry.product_call_status,
            Some(bridge.call_status.status),
            "{consumer}"
        );
        assert_eq!(
            bridge
                .product_adapter
                .telemetry
                .product_call_status_record_sha256
                .as_deref(),
            Some(bridge.call_status.record_sha256.as_str()),
            "{consumer}"
        );
        assert!(
            bridge
                .product_adapter
                .telemetry
                .valid_for_product_call_status_row(&bridge.call_status),
            "{consumer}"
        );

        let mut hash_tampered = bridge.clone();
        hash_tampered.call_status.record_sha256 =
            "sha256:tampered-product-call-status-row".to_owned();
        assert!(
            hash_tampered
                .product_adapter
                .denied_without_product_authority()
        );
        assert!(
            !hash_tampered
                .product_adapter
                .telemetry
                .valid_for_product_call_status_row(&hash_tampered.call_status),
            "{consumer}"
        );
        assert!(
            !hash_tampered.publication_blocked_without_product_authority(),
            "{consumer}"
        );

        let mut status_tampered = bridge.clone();
        let tampered_status = match bridge.call_status.status {
            ControlPlaneProductCallStatus::InvalidatedDeopt => {
                ControlPlaneProductCallStatus::RejectedDeopt
            }
            _ => ControlPlaneProductCallStatus::InvalidatedDeopt,
        };
        status_tampered.call_status.status = tampered_status;
        status_tampered.call_status.record_sha256 =
            status_tampered.call_status.canonical_record_sha256();
        assert!(status_tampered.call_status.fail_closed_deopt_ready());
        assert!(
            status_tampered
                .product_adapter
                .denied_without_product_authority()
        );
        assert!(
            !status_tampered
                .product_adapter
                .telemetry
                .valid_for_product_call_status_row(&status_tampered.call_status),
            "{consumer}"
        );
        assert!(
            !status_tampered.publication_blocked_without_product_authority(),
            "{consumer}"
        );
    }
}

#[test]
fn fail_closed_missing_manifest_and_reference() {
    let mut input = installable_input();
    input.manifest = None;
    assert_reject(
        input,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingManifest,
    );

    let mut missing_reference = installable_input();
    missing_reference.manifest_reference = None;
    assert_reject(
        missing_reference,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingManifest,
    );
}

#[test]
fn fail_closed_manifest_field_and_checksum_mismatches() {
    let mut source = installable_input();
    source.payload_identity.source_sha256.clear();
    assert_reject(
        source,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ArtifactIdentityMismatch,
    );

    let mut trust_ir = installable_input();
    trust_ir.candidate_payload_identity.trust_ir_sha256.clear();
    assert_reject(
        trust_ir,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ArtifactIdentityMismatch,
    );

    let mut native = installable_input();
    native.candidate_payload_identity.native_payload_sha256 = "other-native".to_owned();
    assert_reject(
        native,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ArtifactIdentityMismatch,
    );

    let mut compiler = installable_input();
    compiler
        .manifest
        .as_mut()
        .expect("test input has manifest")
        .invalidation
        .compiler_fingerprint
        .clear();
    assert_reject(
        compiler,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::StaleInvalidation,
    );

    let mut manifest_checksum = installable_input();
    manifest_checksum
        .manifest_reference
        .as_mut()
        .expect("test input has manifest reference")
        .manifest_checksum = ArtifactChecksum::new(0);
    assert_reject(
        manifest_checksum,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ManifestChecksumMismatch,
    );

    let mut target = installable_input();
    target
        .manifest_reference
        .as_mut()
        .expect("test input has manifest reference")
        .target_checksum = ArtifactChecksum::new(0);
    assert_reject(
        target,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::TargetMismatch,
    );

    let mut abi = installable_input();
    abi.manifest_reference
        .as_mut()
        .expect("test input has manifest reference")
        .abi_checksum = ArtifactChecksum::new(0);
    assert_reject(
        abi,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::AbiMismatch,
    );

    let mut layout = installable_input();
    layout
        .manifest_reference
        .as_mut()
        .expect("test input has manifest reference")
        .layout_checksum = ArtifactChecksum::new(0);
    assert_reject(
        layout,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::LayoutMismatch,
    );

    let mut proof_policy = installable_input();
    proof_policy
        .manifest_reference
        .as_mut()
        .expect("test input has manifest reference")
        .proof_policy_checksum = ArtifactChecksum::new(0);
    assert_reject(
        proof_policy,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut invalidation = installable_input();
    invalidation
        .manifest_reference
        .as_mut()
        .expect("test input has manifest reference")
        .invalidation_checksum = ArtifactChecksum::new(0);
    assert_reject(
        invalidation,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::StaleInvalidation,
    );
}

#[test]
fn fail_closed_layout_mismatch_and_missing_layout_evidence() {
    let mut mismatch = installable_input();
    mismatch.layout_evidence.as_mut().unwrap().layout_checksum = ArtifactChecksum::new(99);
    assert_reject(
        mismatch,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::LayoutMismatch,
    );

    let mut missing = installable_input();
    missing.layout_evidence = None;
    assert_reject(
        missing,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let mut missing_report = installable_input();
    missing_report
        .layout_evidence
        .as_mut()
        .expect("test input has layout evidence")
        .evidence_sha256 = None;
    assert_reject(
        missing_report,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let mut missing_wrapper = installable_input();
    missing_wrapper
        .layout_evidence
        .as_mut()
        .expect("test input has layout evidence")
        .wrapper_identity = None;
    assert_reject(
        missing_wrapper,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let mut missing_access = installable_input();
    missing_access
        .layout_evidence
        .as_mut()
        .expect("test input has layout evidence")
        .regions[0]
        .access = None;
    assert_reject(
        missing_access,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );
}

#[test]
fn ty_shared_layout_adapter_prework_authorizes_activation_packet() {
    let input = ty_prework_input();
    let evidence = input
        .layout_evidence
        .as_ref()
        .expect("prework input has layout evidence");

    assert_eq!(evidence.regions.len(), 6);
    assert_eq!(evidence.entry_abis.len(), 5);
    assert_eq!(
        NativeInstallGateTyLayoutAdapter::fused_parent_loop(
            input.expected.layout_checksum,
            input.expected.abi_checksum,
            input.expected.invalidation_checksum,
            "ty.fused-parent-loop.wrapper.v1",
        )
        .into_layout_evidence(),
        evidence.clone()
    );
    assert!(
        evidence
            .evidence_sha256
            .as_deref()
            .expect("adapter computes evidence hash")
            .starts_with("sha256:")
    );

    let packet = validate_native_install_gate(&input);

    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ty_native_activate);
    assert_eq!(packet.validation.layout_status, "accepted");
    assert_eq!(
        packet.validation.layout_wrapper_identity.as_deref(),
        Some("ty.fused-parent-loop.wrapper.v1")
    );
    assert_eq!(
        packet.validation.layout_validation_provenance.as_deref(),
        Some("trust-cg.ty.fused_parent_loop.layout_adapter.v1")
    );
    assert_eq!(
        packet.validation.layout_invalidation_checksum,
        Some(input.expected.invalidation_checksum)
    );
    assert_eq!(
        packet.validation.layout_generation_domains,
        vec![
            "ty_action".to_owned(),
            "ty_arena".to_owned(),
            "ty_fingerprint".to_owned(),
            "ty_runtime".to_owned()
        ]
    );
    assert_eq!(
        packet.validation.layout_evidence_sha256.as_deref(),
        evidence.evidence_sha256.as_deref()
    );
}

#[test]
fn ty_shared_layout_adapter_prework_fails_closed_on_missing_or_mismatched_coverage() {
    let base = ty_prework_input()
        .layout_evidence
        .expect("prework input has layout evidence");

    let mut generic = activation_input("ty", NativeInstallGateSurface::TyActivation);
    generic.layout_evidence = Some(generic_layout_evidence(
        generic
            .manifest
            .as_ref()
            .expect("generic input has manifest"),
    ));
    let generic_packet = validate_native_install_gate(&generic);
    assert_eq!(
        generic_packet.disposition,
        NativeInstallGateDisposition::Rejected
    );
    assert_eq!(
        generic_packet.rejection_code,
        Some(NativeInstallGateRejectionCode::MissingLayoutEvidence)
    );
    assert_blocked(generic_packet.actions);

    let mut missing_region = base.clone();
    missing_region
        .regions
        .retain(|region| region.name != "fingerprint_buffer");
    let mut input = ty_prework_input();
    input.layout_evidence = Some(missing_region);
    assert_reject(
        input,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let cases = [
        (
            "missing_bounds",
            {
                let mut evidence = base.clone();
                evidence.regions[0].byte_len = 0;
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "missing_mutability",
            {
                let mut evidence = base.clone();
                evidence.regions[0].access = None;
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "missing_alias",
            {
                let mut evidence = base.clone();
                evidence.regions[0].alias_group.clear();
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "missing_generation_domain",
            {
                let mut evidence = base.clone();
                evidence.regions[0].generation_domain.clear();
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "missing_entry_abi",
            {
                let mut evidence = base.clone();
                evidence
                    .entry_abis
                    .retain(|entry| entry.name != "fingerprint");
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "dropped_callback_status_region",
            {
                let mut evidence = base.clone();
                evidence.entry_abis[0].status_region = None;
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "dropped_callback_status_buffer_region",
            {
                let mut evidence = base.clone();
                evidence
                    .regions
                    .retain(|region| region.name != "callback_status_buffer");
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "wrong_required_region_role",
            {
                let mut evidence = base.clone();
                evidence.regions[0].role = "wrong_runtime_role".to_owned();
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "wrong_required_region_name",
            {
                let mut evidence = base.clone();
                evidence.regions[0].name = "wrong_runtime_arena".to_owned();
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "incomplete_entry_argument_coverage",
            {
                let mut evidence = base.clone();
                evidence.entry_abis[3]
                    .argument_regions
                    .retain(|region| region != "fingerprint_buffer");
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "abi_mismatch",
            {
                let mut evidence = base.clone();
                evidence.entry_abis[0].abi_checksum = ArtifactChecksum::new(123);
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::AbiMismatch,
        ),
        (
            "layout_mismatch",
            {
                let mut evidence = base.clone();
                evidence.layout_checksum = ArtifactChecksum::new(123);
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::LayoutMismatch,
        ),
        (
            "invalidation_mismatch",
            {
                let mut evidence = base.clone();
                evidence.invalidation_checksum =
                    ArtifactChecksum::new(evidence.invalidation_checksum.get() ^ 0x747);
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::StaleInvalidation,
        ),
        (
            "missing_validation_provenance",
            {
                let mut evidence = base.clone();
                evidence.validation_provenance.clear();
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "tampered_layout_evidence_hash",
            {
                let mut evidence = base.clone();
                evidence.evidence_sha256 = Some("sha256:tampered-layout-evidence".to_owned());
                evidence
            },
            NativeInstallGateRejectionCode::LayoutMismatch,
        ),
        (
            "missing_wrapper_identity",
            {
                let mut evidence = base.clone();
                evidence.wrapper_identity = None;
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "missing_evidence_hash",
            {
                let mut evidence = base.clone();
                evidence.evidence_sha256 = None;
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
    ];

    for (name, evidence, expected_code) in cases {
        let mut input = ty_prework_input();
        input.layout_evidence = Some(evidence);
        let packet = validate_native_install_gate(&input);
        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "{name}"
        );
        assert_eq!(packet.rejection_code, Some(expected_code), "{name}");
        assert_blocked(packet.actions);
    }
}

#[test]
fn ay_layout_adapter_prework_authorizes_registry_packet() {
    let input = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    let evidence = input
        .layout_evidence
        .as_ref()
        .expect("ay registry input has layout evidence");

    assert_eq!(evidence.regions.len(), 7);
    assert_eq!(evidence.entry_abis.len(), 6);
    assert_eq!(
        NativeInstallGateAYLayoutAdapter::solver_registry(
            input.expected.layout_checksum,
            input.expected.abi_checksum,
            input.expected.invalidation_checksum,
            "ay.solver-registry.wrapper.v1",
        )
        .into_layout_evidence(),
        evidence.clone()
    );
    assert_eq!(
        evidence.validation_provenance,
        "trust-cg.ay.solver_registry.layout_adapter.v1"
    );
    assert_eq!(
        evidence.invalidation_checksum,
        input.expected.invalidation_checksum
    );
    assert!(
        evidence
            .evidence_sha256
            .as_deref()
            .expect("adapter computes evidence hash")
            .starts_with("sha256:")
    );

    let packet = validate_native_install_gate(&input);

    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);
    assert!(!packet.actions.ty_native_activate);
    assert_eq!(packet.validation.layout_status, "accepted");
    assert_eq!(
        packet.validation.layout_wrapper_identity.as_deref(),
        Some("ay.solver-registry.wrapper.v1")
    );
    assert_eq!(
        packet.validation.layout_validation_provenance.as_deref(),
        Some("trust-cg.ay.solver_registry.layout_adapter.v1")
    );
    assert_eq!(
        packet.validation.layout_invalidation_checksum,
        Some(input.expected.invalidation_checksum)
    );
    assert_eq!(
        packet.validation.layout_generation_domains,
        vec![
            "ay_basis".to_owned(),
            "ay_proof_witness".to_owned(),
            "ay_rollback".to_owned(),
            "ay_solver".to_owned(),
            "ay_sparse_substitute".to_owned(),
            "ay_watch_list".to_owned(),
        ]
    );
    assert_eq!(
        packet.validation.layout_evidence_sha256.as_deref(),
        evidence.evidence_sha256.as_deref()
    );
}

#[test]
fn ay_layout_adapter_prework_fails_closed_on_missing_or_mismatched_coverage() {
    let base = activation_input("ay", NativeInstallGateSurface::AYRegistry)
        .layout_evidence
        .expect("ay registry input has layout evidence");

    let mut generic = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    generic.layout_evidence = Some(generic_layout_evidence(
        generic
            .manifest
            .as_ref()
            .expect("generic input has manifest"),
    ));
    let generic_packet = validate_native_install_gate(&generic);
    assert_eq!(
        generic_packet.disposition,
        NativeInstallGateDisposition::Rejected
    );
    assert_eq!(
        generic_packet.rejection_code,
        Some(NativeInstallGateRejectionCode::MissingLayoutEvidence)
    );
    assert_blocked(generic_packet.actions);

    let cases = [
        (
            "missing_sparse_substitute_rows",
            {
                let mut evidence = base.clone();
                evidence
                    .regions
                    .retain(|region| region.name != "sparse_substitute_rows");
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "wrong_solver_access",
            {
                let mut evidence = base.clone();
                evidence.regions[0].access =
                    Some(trust_cg_codegen::NativeInstallGateLayoutAccess::ReadWrite);
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "missing_watch_list_entry",
            {
                let mut evidence = base.clone();
                evidence
                    .entry_abis
                    .retain(|entry| entry.name != "watch_list_bcp");
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "incomplete_basis_argument_coverage",
            {
                let mut evidence = base.clone();
                evidence.entry_abis[2]
                    .argument_regions
                    .retain(|region| region != "basis_region_state");
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "wrong_status_region",
            {
                let mut evidence = base.clone();
                evidence.entry_abis[0].status_region = Some("proof_witness_buffer".to_owned());
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "abi_mismatch",
            {
                let mut evidence = base.clone();
                evidence.entry_abis[0].abi_checksum = ArtifactChecksum::new(123);
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::AbiMismatch,
        ),
        (
            "layout_mismatch",
            {
                let mut evidence = base.clone();
                evidence.layout_checksum = ArtifactChecksum::new(123);
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::LayoutMismatch,
        ),
        (
            "invalidation_mismatch",
            {
                let mut evidence = base.clone();
                evidence.invalidation_checksum =
                    ArtifactChecksum::new(evidence.invalidation_checksum.get() ^ 0x747);
                evidence.evidence_sha256 = Some(evidence.canonical_evidence_sha256());
                evidence
            },
            NativeInstallGateRejectionCode::StaleInvalidation,
        ),
        (
            "missing_validation_provenance",
            {
                let mut evidence = base.clone();
                evidence.validation_provenance.clear();
                evidence
            },
            NativeInstallGateRejectionCode::MissingLayoutEvidence,
        ),
        (
            "tampered_layout_evidence_hash",
            {
                let mut evidence = base.clone();
                evidence.evidence_sha256 = Some("sha256:tampered-ay-layout-evidence".to_owned());
                evidence
            },
            NativeInstallGateRejectionCode::LayoutMismatch,
        ),
    ];

    for (name, evidence, expected_code) in cases {
        let mut input = activation_input("ay", NativeInstallGateSurface::AYRegistry);
        input.layout_evidence = Some(evidence);
        let packet = validate_native_install_gate(&input);
        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "{name}"
        );
        assert_eq!(packet.rejection_code, Some(expected_code), "{name}");
        assert_blocked(packet.actions);
    }
}

fn ay_lra_registry_input_with_layout(
    consumer_mode: &str,
    mut layout_evidence: NativeInstallGateLayoutEvidence,
) -> NativeInstallGateInput {
    layout_evidence.evidence_sha256 = Some(layout_evidence.canonical_evidence_sha256());
    let mut input = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    input.consumer_mode = consumer_mode.to_owned();
    input.layout_evidence = Some(layout_evidence);
    if let Some(proof_manifest) = ay_lra_test_proof_manifest(consumer_mode) {
        attach_ay_lra_proof_metadata(&mut input, &proof_manifest);
    }
    refresh_manifest_bindings(&mut input);
    input
}

fn ay_lra_test_proof_manifest(consumer_mode: &str) -> Option<AYLraKernelProofConsumptionManifest> {
    match consumer_mode {
        mode if mode == AYLraKernelFamily::SparseSubstitute.as_str() => {
            Some(ay_lra_sparse_substitute_proof_manifest())
        }
        "sparse_substitute" | "ay_sparse_substitute" | "lra_sparse_substitute" => {
            Some(ay_lra_sparse_substitute_proof_manifest())
        }
        mode if mode == AYLraKernelFamily::SparseAffectedRowBatch.as_str() => {
            Some(ay_lra_sparse_affected_row_batch_proof_manifest())
        }
        "lra_sparse_affected_row_batch" => Some(ay_lra_sparse_affected_row_batch_proof_manifest()),
        mode if mode == AYLraKernelFamily::BasisUpdate.as_str() => {
            Some(ay_lra_basis_update_proof_manifest())
        }
        "basis_region"
        | "basis_row_batch"
        | "ay_basis"
        | "ay_lra_basis_row_batch"
        | "ay_lra_basis_update" => Some(ay_lra_basis_update_proof_manifest()),
        _ => None,
    }
}

fn ay_lra_manifest_proof_metadata(
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> Vec<(&'static str, String)> {
    vec![
        (
            "proof_consumption_manifest_schema",
            proof_manifest.schema.to_owned(),
        ),
        (
            "proof_consumption_manifest_issue",
            format!("#{}", proof_manifest.issue),
        ),
        (
            "kernel_family",
            proof_manifest.kernel_family.as_str().to_owned(),
        ),
        ("required_proof_facts", proof_manifest.required_fact_csv()),
        (
            "required_certificate_dependencies",
            proof_manifest.required_certificate_csv(),
        ),
        (
            "future_proof_status",
            ay_lra_manifest_future_proof_status(proof_manifest),
        ),
        (
            "product_gate_fields",
            proof_manifest.product_gate.required_parent_gates.join(","),
        ),
    ]
}

fn ay_lra_manifest_future_proof_status(
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> String {
    let mut statuses: Vec<_> = proof_manifest
        .future_facts
        .iter()
        .map(|requirement| requirement.availability.as_str())
        .collect();
    statuses.sort_unstable();
    statuses.dedup();
    statuses.join(",")
}

fn attach_ay_lra_proof_metadata(
    input: &mut NativeInstallGateInput,
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) {
    let source_metadata = ay_lra_source_metadata(proof_manifest);
    if let Some(manifest) = input.manifest.as_mut() {
        for (key, value) in source_metadata {
            manifest.metadata.insert(key.to_owned(), value.to_owned());
        }
    }

    let proof = input
        .proof_evidence
        .as_mut()
        .expect("ay LRA registry input has proof evidence");
    for (key, value) in ay_lra_manifest_proof_metadata(proof_manifest) {
        proof.summary.metadata.insert(key.to_owned(), value);
    }
    for (key, value) in ay_lra_source_metadata(proof_manifest) {
        proof
            .summary
            .metadata
            .insert(key.to_owned(), value.to_owned());
    }
    for requirement in &proof_manifest.required_facts {
        proof.summary.metadata.insert(
            ay_lra_proof_fact_metadata_key(requirement.fact),
            requirement.lemma_id.to_owned(),
        );
    }
}

fn ay_lra_source_metadata(
    proof_manifest: &AYLraKernelProofConsumptionManifest,
) -> [(&'static str, &'static str); 4] {
    let (trust_ir_source_identity, trust_cg_source_lock, trust_ir_source_lock) =
        match proof_manifest.kernel_family {
            AYLraKernelFamily::SparseAffectedRowBatch => (
                AY_LRA_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_IDENTITY,
                AY_LRA_AFFECTED_ROW_BATCH_TRUST_CG_SOURCE_LOCK,
                AY_LRA_AFFECTED_ROW_BATCH_TRUST_IR_SOURCE_LOCK,
            ),
            AYLraKernelFamily::BasisUpdate => (
                AY_LRA_BASIS_TRUST_IR_SOURCE_IDENTITY,
                AY_LRA_BASIS_TRUST_CG_SOURCE_LOCK,
                AY_LRA_BASIS_TRUST_IR_SOURCE_LOCK,
            ),
            _ => (
                AY_LRA_SPARSE_TRUST_IR_SOURCE_IDENTITY,
                AY_LRA_SPARSE_TRUST_CG_SOURCE_LOCK,
                AY_LRA_SPARSE_TRUST_IR_SOURCE_LOCK,
            ),
        };

    [
        ("source_policy", "approved_private_source"),
        ("trust_ir_source_identity", trust_ir_source_identity),
        ("trust_cg_source_lock", trust_cg_source_lock),
        ("trust_ir_source_lock", trust_ir_source_lock),
    ]
}

fn ay_lra_base_layout() -> NativeInstallGateLayoutEvidence {
    activation_input("ay", NativeInstallGateSurface::AYRegistry)
        .layout_evidence
        .expect("ay registry input has layout evidence")
}

fn assert_ay_lra_packet_validates_end_to_end(packet: &NativeInstallGatePacket) {
    let persisted = validate_native_install_gate_packet(packet, Some(packet.packet_hash));
    assert_eq!(
        persisted.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(persisted.rejection_code, None);
    let current = NativeInstallGateRevalidationInput::from_packet(packet);
    let current_verdict = validate_native_install_gate_packet_with_current(
        packet,
        Some(packet.packet_hash),
        &current,
    );
    assert_eq!(
        current_verdict.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(current_verdict.rejection_code, None);
}

fn assert_ay_lra_rejects_missing_proof_metadata(input: &NativeInstallGateInput, name: &str) {
    let packet = validate_native_install_gate(input);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Rejected,
        "{name}"
    );
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::ProofMissingEvidence),
        "{name}"
    );
    assert!(!packet.actions.ay_registry_insert, "{name}");
    assert_blocked(packet.actions);
}

fn assert_ay_lra_manifest_metadata_is_required(accepted: &NativeInstallGateInput, key: &str) {
    let expected = accepted
        .proof_evidence
        .as_ref()
        .expect("accepted input has proof evidence")
        .summary
        .metadata
        .get(key)
        .cloned()
        .expect("accepted input has ay LRA manifest metadata");

    let mut missing = accepted.clone();
    missing
        .proof_evidence
        .as_mut()
        .expect("accepted input has proof evidence")
        .summary
        .metadata
        .remove(key);
    assert_ay_lra_rejects_missing_proof_metadata(&missing, &format!("missing {key}"));

    let mut spoofed = accepted.clone();
    spoofed
        .proof_evidence
        .as_mut()
        .expect("accepted input has proof evidence")
        .summary
        .metadata
        .insert(key.to_owned(), format!("{expected}.spoof"));
    assert_ay_lra_rejects_missing_proof_metadata(&spoofed, &format!("spoofed {key}"));
}

fn assert_ay_lra_source_metadata_is_required(accepted: &NativeInstallGateInput, key: &str) {
    assert_ay_lra_manifest_metadata_is_required(accepted, key);

    let mut missing_manifest = accepted.clone();
    missing_manifest
        .manifest
        .as_mut()
        .expect("accepted input has manifest")
        .metadata
        .remove(key);
    refresh_manifest_bindings(&mut missing_manifest);
    assert_ay_lra_rejects_missing_proof_metadata(
        &missing_manifest,
        &format!("manifest missing {key}"),
    );

    let mut spoofed_manifest = accepted.clone();
    let manifest_value = spoofed_manifest
        .manifest
        .as_mut()
        .expect("accepted input has manifest")
        .metadata
        .get_mut(key)
        .expect("accepted manifest has source metadata");
    manifest_value.push_str(".spoof");
    refresh_manifest_bindings(&mut spoofed_manifest);
    assert_ay_lra_rejects_missing_proof_metadata(
        &spoofed_manifest,
        &format!("manifest spoofed {key}"),
    );
}

fn refresh_manifest_bindings(input: &mut NativeInstallGateInput) {
    if let Some(manifest) = input.manifest.as_ref() {
        input.expected = NativeInstallGateExpectedBindings::from_manifest(manifest);
        input.manifest_reference = Some(ArtifactManifestReference::from_manifest(manifest));
        input.current_invalidation_checksum = manifest.invalidation.checksum();
        input.current_generation = manifest.invalidation.generation;
        input.artifact_generation = manifest.invalidation.generation;
    }
    refresh_gate_identity(input);
}

#[test]
fn ay_lra_registry_allowlisted_modes_keep_current_behavior() {
    for consumer_mode in [
        AYLraKernelFamily::SparseSubstitute.as_str(),
        "lra_sparse_substitute",
        AYLraKernelFamily::SparseAffectedRowBatch.as_str(),
        "lra_sparse_affected_row_batch",
        AYLraKernelFamily::BasisUpdate.as_str(),
        "ay_lra_basis_row_batch",
        "ay_lra_basis_update",
        "ay_lra_watch_list_bcp",
    ] {
        let input = ay_lra_registry_input_with_layout(consumer_mode, ay_lra_base_layout());
        let packet = validate_native_install_gate(&input);

        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Installable,
            "{consumer_mode}"
        );
        assert_eq!(packet.rejection_code, None, "{consumer_mode}");
        assert!(packet.actions.ay_registry_insert, "{consumer_mode}");
        assert_ay_lra_packet_validates_end_to_end(&packet);
    }

    let input = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    let packet = validate_native_install_gate(&input);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable,
        "solver-registry"
    );
    assert_eq!(packet.rejection_code, None, "solver-registry");
    assert!(packet.actions.ay_registry_insert, "solver-registry");
    assert_ay_lra_packet_validates_end_to_end(&packet);
}

#[test]
fn ay_lra_registry_alias_counter_scopes_use_canonical_family_names() {
    for (consumer_mode, canonical_mode) in [
        (
            AYLraKernelFamily::SparseSubstitute.as_str(),
            AYLraKernelFamily::SparseSubstitute.as_str(),
        ),
        (
            "lra_sparse_substitute",
            AYLraKernelFamily::SparseSubstitute.as_str(),
        ),
        (
            "sparse_substitute",
            AYLraKernelFamily::SparseSubstitute.as_str(),
        ),
        (
            AYLraKernelFamily::SparseAffectedRowBatch.as_str(),
            AYLraKernelFamily::SparseAffectedRowBatch.as_str(),
        ),
        (
            "lra_sparse_affected_row_batch",
            AYLraKernelFamily::SparseAffectedRowBatch.as_str(),
        ),
        (
            AYLraKernelFamily::BasisUpdate.as_str(),
            AYLraKernelFamily::BasisUpdate.as_str(),
        ),
        (
            "ay_lra_basis_row_batch",
            AYLraKernelFamily::BasisUpdate.as_str(),
        ),
        ("basis_row_batch", AYLraKernelFamily::BasisUpdate.as_str()),
    ] {
        let input = ay_lra_registry_input_with_layout(consumer_mode, ay_lra_base_layout());
        let packet = validate_native_install_gate(&input);
        let telemetry = packet.telemetry.as_ref().expect("packet has telemetry");
        let expected_scope = format!("ay:{canonical_mode}:ay_registry:artifact.installable");

        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Installable,
            "{consumer_mode}"
        );
        assert_eq!(packet.rejection_code, None, "{consumer_mode}");
        assert_eq!(telemetry.counter_scope, expected_scope, "{consumer_mode}");
        assert_eq!(
            telemetry.record_sha256,
            telemetry.canonical_record_sha256(),
            "{consumer_mode}"
        );
        assert_ay_lra_packet_validates_end_to_end(&packet);
    }
}

#[test]
fn ay_lra_counter_scope_canonicalization_is_limited_to_registry_aliases() {
    let mut non_registry = installable_input();
    non_registry.consumer_mode = "lra_sparse_substitute".to_owned();
    refresh_gate_identity(&mut non_registry);
    let packet = validate_native_install_gate(&non_registry);
    let telemetry = packet.telemetry.as_ref().expect("packet has telemetry");
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(
        telemetry.counter_scope,
        "ay:lra_sparse_substitute:typed_symbol_lookup:artifact.installable"
    );

    for consumer_mode in [
        "solver-registry",
        "ay_sparse_substitute",
        "basis_region",
        "ay_basis",
    ] {
        let input = if consumer_mode == "solver-registry" {
            activation_input("ay", NativeInstallGateSurface::AYRegistry)
        } else {
            ay_lra_registry_input_with_layout(consumer_mode, ay_lra_base_layout())
        };
        let packet = validate_native_install_gate(&input);
        let telemetry = packet.telemetry.as_ref().expect("packet has telemetry");
        let expected_scope = format!("ay:{consumer_mode}:ay_registry:artifact.installable");

        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Installable,
            "{consumer_mode}"
        );
        assert_eq!(telemetry.counter_scope, expected_scope, "{consumer_mode}");
        assert_ay_lra_packet_validates_end_to_end(&packet);
    }
}

#[test]
fn ay_lra_registry_unknown_lra_namespaced_modes_fail_closed() {
    for consumer_mode in ["ay_lra_future_registry", "lra_future_registry"] {
        let input = ay_lra_registry_input_with_layout(consumer_mode, ay_lra_base_layout());
        let packet = validate_native_install_gate(&input);

        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "{consumer_mode}"
        );
        assert_eq!(
            packet.rejection_code,
            Some(NativeInstallGateRejectionCode::UnsupportedConsumer),
            "{consumer_mode}"
        );
        assert!(!packet.actions.ay_registry_insert, "{consumer_mode}");
        assert_blocked(packet.actions);
    }
}

#[test]
fn ay_lra_registry_persisted_packet_rejects_unknown_lra_namespaced_mode_after_rehash() {
    let input = activation_input("ay", NativeInstallGateSurface::AYRegistry);
    let mut packet = validate_native_install_gate(&input);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert!(packet.actions.ay_registry_insert);

    packet.consumer_mode = "ay_lra_future_registry".to_owned();
    persist_native_install_gate_packet_bindings(&mut packet);

    let verdict = validate_native_install_gate_packet(&packet, Some(packet.packet_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::UnsupportedConsumer)
    );
    assert!(!verdict.actions.ay_registry_insert);
    assert_blocked(verdict.actions);
}

#[test]
fn ay_lra_sparse_layout_admission_allows_family_specific_regions() {
    let mut evidence = ay_lra_base_layout();
    evidence.regions.retain(|region| {
        !matches!(
            region.name.as_str(),
            "watch_list_bcp_state" | "proof_witness_buffer"
        )
    });
    evidence
        .entry_abis
        .retain(|entry| entry.name == "sparse_substitute");
    evidence.entry_abis[0]
        .argument_regions
        .retain(|region| region != "proof_witness_buffer");

    let input =
        ay_lra_registry_input_with_layout(AYLraKernelFamily::SparseSubstitute.as_str(), evidence);
    let packet = validate_native_install_gate(&input);

    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);
    assert_eq!(packet.validation.layout_status, "accepted");
    assert_ay_lra_packet_validates_end_to_end(&packet);
    assert!(
        !packet
            .validation
            .layout_generation_domains
            .contains(&"ay_watch_list".to_owned())
    );
    assert!(
        !packet
            .validation
            .layout_generation_domains
            .contains(&"ay_proof_witness".to_owned())
    );
}

#[test]
fn ay_lra_registry_sparse_requires_complete_proof_manifest_metadata() {
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let accepted = ay_lra_registry_input_with_layout(
        AYLraKernelFamily::SparseSubstitute.as_str(),
        ay_lra_base_layout(),
    );
    let packet = validate_native_install_gate(&accepted);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);

    for (key, _) in ay_lra_manifest_proof_metadata(&proof_manifest) {
        assert_ay_lra_manifest_metadata_is_required(&accepted, key);
    }
    for (key, _) in ay_lra_source_metadata(&proof_manifest) {
        assert_ay_lra_source_metadata_is_required(&accepted, key);
    }
}

#[test]
fn ay_lra_registry_affected_row_batch_requires_complete_proof_manifest_metadata() {
    let proof_manifest = ay_lra_sparse_affected_row_batch_proof_manifest();
    let accepted = ay_lra_registry_input_with_layout(
        AYLraKernelFamily::SparseAffectedRowBatch.as_str(),
        ay_lra_base_layout(),
    );
    let packet = validate_native_install_gate(&accepted);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);

    for (key, _) in ay_lra_manifest_proof_metadata(&proof_manifest) {
        assert_ay_lra_manifest_metadata_is_required(&accepted, key);
    }
    for (key, _) in ay_lra_source_metadata(&proof_manifest) {
        assert_ay_lra_source_metadata_is_required(&accepted, key);
    }
}

#[test]
fn ay_lra_registry_sparse_requires_matched_per_fact_proof_metadata() {
    let proof_manifest = ay_lra_sparse_substitute_proof_manifest();
    let requirement = proof_manifest
        .required_facts
        .first()
        .expect("sparse proof manifest has required facts");
    let key = ay_lra_proof_fact_metadata_key(requirement.fact);

    let accepted = ay_lra_registry_input_with_layout(
        AYLraKernelFamily::SparseSubstitute.as_str(),
        ay_lra_base_layout(),
    );
    let packet = validate_native_install_gate(&accepted);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);

    let mut missing = accepted.clone();
    missing
        .proof_evidence
        .as_mut()
        .expect("accepted input has proof evidence")
        .summary
        .metadata
        .remove(&key);
    let packet = validate_native_install_gate(&missing);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::ProofMissingEvidence)
    );
    assert!(!packet.actions.ay_registry_insert);
    assert_blocked(packet.actions);

    let mut spoofed = accepted;
    spoofed
        .proof_evidence
        .as_mut()
        .expect("accepted input has proof evidence")
        .summary
        .metadata
        .insert(key, format!("{}.spoof", requirement.lemma_id));
    let packet = validate_native_install_gate(&spoofed);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::ProofMissingEvidence)
    );
    assert!(!packet.actions.ay_registry_insert);
    assert_blocked(packet.actions);
}

#[test]
fn ay_lra_basis_layout_admission_allows_family_specific_regions() {
    let mut evidence = ay_lra_base_layout();
    evidence.regions.retain(|region| {
        !matches!(
            region.name.as_str(),
            "sparse_substitute_rows" | "watch_list_bcp_state" | "proof_witness_buffer"
        )
    });
    evidence
        .entry_abis
        .retain(|entry| entry.name == "basis_region");

    let input =
        ay_lra_registry_input_with_layout(AYLraKernelFamily::BasisUpdate.as_str(), evidence);
    let packet = validate_native_install_gate(&input);

    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);
    assert_eq!(packet.validation.layout_status, "accepted");
    assert_ay_lra_packet_validates_end_to_end(&packet);
    assert!(
        !packet
            .validation
            .layout_generation_domains
            .contains(&"ay_sparse_substitute".to_owned())
    );
    assert!(
        !packet
            .validation
            .layout_generation_domains
            .contains(&"ay_watch_list".to_owned())
    );
    assert!(
        !packet
            .validation
            .layout_generation_domains
            .contains(&"ay_proof_witness".to_owned())
    );
}

#[test]
fn ay_lra_registry_basis_requires_complete_proof_manifest_metadata() {
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let accepted = ay_lra_registry_input_with_layout("ay_basis", ay_lra_base_layout());
    let packet = validate_native_install_gate(&accepted);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);

    for (key, _) in ay_lra_manifest_proof_metadata(&proof_manifest) {
        assert_ay_lra_manifest_metadata_is_required(&accepted, key);
    }
    for (key, _) in ay_lra_source_metadata(&proof_manifest) {
        assert_ay_lra_source_metadata_is_required(&accepted, key);
    }
}

#[test]
fn ay_lra_registry_basis_requires_matched_per_fact_proof_metadata() {
    let proof_manifest = ay_lra_basis_update_proof_manifest();
    let requirement = proof_manifest
        .required_facts
        .last()
        .expect("basis proof manifest has required facts");
    let key = ay_lra_proof_fact_metadata_key(requirement.fact);

    let accepted = ay_lra_registry_input_with_layout("ay_basis", ay_lra_base_layout());
    let packet = validate_native_install_gate(&accepted);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ay_registry_insert);

    let mut missing = accepted.clone();
    missing
        .proof_evidence
        .as_mut()
        .expect("accepted input has proof evidence")
        .summary
        .metadata
        .remove(&key);
    let packet = validate_native_install_gate(&missing);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::ProofMissingEvidence)
    );
    assert!(!packet.actions.ay_registry_insert);
    assert_blocked(packet.actions);

    let mut spoofed = accepted;
    spoofed
        .proof_evidence
        .as_mut()
        .expect("accepted input has proof evidence")
        .summary
        .metadata
        .insert(key, format!("{}.spoof", requirement.lemma_id));
    let packet = validate_native_install_gate(&spoofed);
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        packet.rejection_code,
        Some(NativeInstallGateRejectionCode::ProofMissingEvidence)
    );
    assert!(!packet.actions.ay_registry_insert);
    assert_blocked(packet.actions);
}

#[test]
fn ay_lra_watch_list_layout_admission_keeps_bcp_and_witness_requirements() {
    let base = ay_lra_base_layout();

    for (name, evidence) in [
        ("missing_watch_list_bcp_state", {
            let mut evidence = base.clone();
            evidence
                .regions
                .retain(|region| region.name != "watch_list_bcp_state");
            evidence
        }),
        ("missing_proof_witness_buffer", {
            let mut evidence = base.clone();
            evidence
                .regions
                .retain(|region| region.name != "proof_witness_buffer");
            evidence
                .entry_abis
                .iter_mut()
                .find(|entry| entry.name == "watch_list_bcp")
                .expect("base layout has watch-list entry")
                .argument_regions
                .retain(|region| region != "proof_witness_buffer");
            evidence
        }),
        ("missing_watch_list_status_region", {
            let mut evidence = base.clone();
            evidence
                .entry_abis
                .iter_mut()
                .find(|entry| entry.name == "watch_list_bcp")
                .expect("base layout has watch-list entry")
                .status_region = None;
            evidence
        }),
    ] {
        let input = ay_lra_registry_input_with_layout("watch_list_bcp", evidence);
        let packet = validate_native_install_gate(&input);
        assert_eq!(
            packet.disposition,
            NativeInstallGateDisposition::Rejected,
            "{name}"
        );
        assert_eq!(
            packet.rejection_code,
            Some(NativeInstallGateRejectionCode::MissingLayoutEvidence),
            "{name}"
        );
        assert_blocked(packet.actions);
    }
}

#[test]
fn layout_adapters_do_not_make_non_callable_modes_callable() {
    let mut cases = Vec::new();

    for (consumer, surface) in [
        ("ay", NativeInstallGateSurface::AYRegistry),
        ("ty", NativeInstallGateSurface::TyActivation),
    ] {
        let base = if consumer == "ty" {
            ty_prework_input()
        } else {
            activation_input(consumer, surface)
        };

        let mut profile_only = base.clone();
        profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;
        cases.push((
            format!("{consumer}_profile_only"),
            profile_only,
            NativeInstallGateDisposition::ProfileOnly,
            NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
        ));

        let mut replay_only = base.clone();
        replay_only.candidate_disposition = NativeInstallGateDisposition::ReplayOnly;
        cases.push((
            format!("{consumer}_replay_only"),
            replay_only,
            NativeInstallGateDisposition::ReplayOnly,
            NativeInstallGateRejectionCode::ReplayOnlyNonInstallable,
        ));

        let mut shadow_only = base;
        shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
        cases.push((
            format!("{consumer}_shadow_only"),
            shadow_only,
            NativeInstallGateDisposition::ShadowOnly,
            NativeInstallGateRejectionCode::ShadowOnlyNonInstallable,
        ));
    }

    for (name, input, expected_disposition, expected_code) in cases {
        let packet = validate_native_install_gate(&input);
        assert_eq!(packet.disposition, expected_disposition, "{name}");
        assert_eq!(packet.rejection_code, Some(expected_code), "{name}");
        assert_eq!(
            packet.validation.layout_status, "accepted",
            "{name} still has valid adapter evidence"
        );
        assert_blocked(packet.actions);
    }
}

#[test]
fn fail_closed_proof_missing_rejected_timeout_unknown_and_stale() {
    let mut missing = installable_input();
    missing.proof_evidence = None;
    assert_reject(
        missing,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let manifest = manifest();
    let cases = [
        (
            ProofEvidenceVerdict::VerifierFailure,
            ProofEvidenceRejectionCode::VerifierFailure,
            NativeInstallGateRejectionCode::ProofVerifierFailure,
        ),
        (
            ProofEvidenceVerdict::Timeout,
            ProofEvidenceRejectionCode::Timeout,
            NativeInstallGateRejectionCode::ProofTimeout,
        ),
        (
            ProofEvidenceVerdict::UnknownSolverError,
            ProofEvidenceRejectionCode::UnknownSolverError,
            NativeInstallGateRejectionCode::ProofUnknown,
        ),
        (
            ProofEvidenceVerdict::UnsupportedTarget,
            ProofEvidenceRejectionCode::UnsupportedTarget,
            NativeInstallGateRejectionCode::ProofUnsupportedTarget,
        ),
        (
            ProofEvidenceVerdict::StaleEvidence,
            ProofEvidenceRejectionCode::StaleEvidence,
            NativeInstallGateRejectionCode::ProofStaleEvidence,
        ),
    ];

    for (verdict, proof_code, gate_code) in cases {
        let mut input = installable_input();
        input.proof_evidence = Some(rejected_proof(&manifest, verdict, proof_code));
        assert_reject(input, NativeInstallGateDisposition::Rejected, gate_code);
    }
}

#[test]
fn fail_closed_missing_required_proof_fields() {
    let mut missing_report = installable_input();
    missing_report
        .proof_evidence
        .as_mut()
        .expect("test input has proof evidence")
        .proof_report_sha256 = None;
    assert_reject(
        missing_report,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut missing_obligation = installable_input();
    missing_obligation
        .proof_evidence
        .as_mut()
        .expect("test input has proof evidence")
        .obligation_set = None;
    assert_reject(
        missing_obligation,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut missing_timeout = installable_input();
    missing_timeout
        .proof_evidence
        .as_mut()
        .expect("test input has proof evidence")
        .timeout_ms = None;
    assert_reject(
        missing_timeout,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut missing_native_hash = installable_input();
    missing_native_hash
        .proof_evidence
        .as_mut()
        .expect("test input has proof evidence")
        .native_payload_sha256 = None;
    assert_reject(
        missing_native_hash,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut missing_verifier = installable_input();
    missing_verifier
        .proof_evidence
        .as_mut()
        .expect("test input has proof evidence")
        .summary
        .verifier
        .clear();
    assert_reject(
        missing_verifier,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );
}

#[test]
fn fail_closed_stale_invalidation() {
    let mut input = installable_input();
    input.current_generation += 1;
    assert_reject(
        input,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::StaleInvalidation,
    );
}

#[test]
fn fail_closed_missing_and_mismatched_telemetry() {
    let mut missing = installable_input();
    missing.telemetry = None;
    assert_reject(
        missing,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::MissingTelemetry,
    );

    let mut mismatch = installable_input();
    mismatch.telemetry.as_mut().unwrap().manifest_checksum = ArtifactChecksum::new(123);
    assert_reject(
        mismatch,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::TelemetryMismatch,
    );
}

#[test]
fn fail_closed_unsupported_schema_and_consumer() {
    let mut schema = installable_input();
    schema.manifest.as_mut().unwrap().schema_version += 1;
    assert_reject(
        schema,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::UnsupportedSchema,
    );

    let mut consumer = installable_input();
    consumer.consumer = "other".to_owned();
    assert_reject(
        consumer,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::UnsupportedConsumer,
    );
}

#[test]
fn fail_closed_non_callable_modes_and_policy_blocks() {
    let mut profile_only = installable_input();
    profile_only.candidate_disposition = NativeInstallGateDisposition::ProfileOnly;
    assert_reject(
        profile_only,
        NativeInstallGateDisposition::ProfileOnly,
        NativeInstallGateRejectionCode::ProfileOnlyNonInstallable,
    );

    let mut replay_only = installable_input();
    replay_only.candidate_disposition = NativeInstallGateDisposition::ReplayOnly;
    assert_reject(
        replay_only,
        NativeInstallGateDisposition::ReplayOnly,
        NativeInstallGateRejectionCode::ReplayOnlyNonInstallable,
    );

    let mut shadow_only = installable_input();
    shadow_only.candidate_disposition = NativeInstallGateDisposition::ShadowOnly;
    assert_reject(
        shadow_only,
        NativeInstallGateDisposition::ShadowOnly,
        NativeInstallGateRejectionCode::ShadowOnlyNonInstallable,
    );

    let mut rejected = installable_input();
    rejected.candidate_disposition = NativeInstallGateDisposition::Rejected;
    assert_reject(
        rejected,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::ArtifactIdentityMismatch,
    );

    let mut invalidated = installable_input();
    invalidated.current_generation += 1;
    assert_reject(
        invalidated,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::StaleInvalidation,
    );

    let mut revoked = installable_input();
    revoked.revoked = true;
    assert_reject(
        revoked,
        NativeInstallGateDisposition::Rejected,
        NativeInstallGateRejectionCode::RevokedArtifact,
    );

    let mut kill_switch = validate_native_install_gate(&installable_input());
    kill_switch.disposition = NativeInstallGateDisposition::Rejected;
    kill_switch.rejection_code = Some(NativeInstallGateRejectionCode::KillSwitchActive);
    kill_switch.install_authority = NativeInstallGateAuthority::None;
    kill_switch.actions = NativeInstallGateActions::none();
    persist_native_install_gate_packet_bindings(&mut kill_switch);
    let verdict = validate_native_install_gate_packet(&kill_switch, Some(kill_switch.packet_hash));
    assert_eq!(verdict.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(
        verdict.rejection_code,
        Some(NativeInstallGateRejectionCode::KillSwitchActive)
    );
    assert_blocked(verdict.actions);
}
