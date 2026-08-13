// trust-cg-codegen/tests/ty_runtime_value_replay_contract.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::compile_service::ArtifactManifestReference;
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiValue, AbiValueKind, AliasPolicy, ArtifactManifestV1, ArtifactSection,
    ArtifactSectionKind, ArtifactSymbol, Endianness, FieldLayout, InvalidationKey, JitArtifactKind,
    LayoutManifest, Mutability, PointerBounds, PointerLayout, ProofEvidenceSummary, ProofMode,
    ProofPolicy, RecordLayout, SliceLayout, SymbolLayout, SymbolSignature, SymbolVisibility,
    TargetDescriptor, TargetOperatingSystem,
};
use trust_cg_codegen::jit_diagnostics::sha256_hex;
use trust_cg_codegen::jit_install_gate::{
    NATIVE_INSTALL_GATE_REPLAY_SCHEMA, NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
    NativeInstallGateAuthority, NativeInstallGateConsumerAdmissionEvidence,
    NativeInstallGateDisposition, NativeInstallGateExpectedBindings, NativeInstallGateInput,
    NativeInstallGateLayoutEvidence, NativeInstallGatePayloadIdentity,
    NativeInstallGateProductPromotionRejectionReason, NativeInstallGateProofEvidence,
    NativeInstallGateRejectionCode, NativeInstallGateReplayIdentity,
    NativeInstallGateRevalidationInput, NativeInstallGateSurface, NativeInstallGateTelemetryInput,
    TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY, TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_MANIFEST_IDENTITY_KEY, TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY,
    TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY, TY_NATIVE_FUSED_EVIDENCE_VALIDATION_HASH_KEY,
    TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION, TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
    TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA, TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT,
    TY_NATIVE_FUSED_PROOF_FACT_VERIFIED, TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA,
    TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY, native_install_gate_consumer_admission,
    native_install_gate_consumer_allowlist_key,
    native_install_gate_non_promoting_product_promotion_packet as native_install_gate_non_promoting_product_promotion_packet_impl,
    validate_native_install_gate,
};
use trust_cg_codegen::jit_shadow_replay::{
    ShadowReplayTyNativeFusedSmokeRejection,
    TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256,
    ty_native_fused_three_spec_smoke_fixture,
};
use trust_cg_codegen::ty_reducer_evidence::TyReducerEvidenceCoverageSummary;
use trust_cg_codegen::{
    ProofOptimizationCertificateCitation, ProofOptimizationConsumedFactCitation, Target,
    TyCanaryAllowlist, TyCanaryAllowlistDecision, TyCanaryAllowlistKey, TyCanaryCandidate,
    TyCanaryCandidateMode, TyCanaryDecisionStatus, TyCanaryEquivalenceEvidence,
    TyCanaryExecutionObservation, TyCanaryFamily, TyCanaryGenerationTuple,
    TyCanaryInvalidationState, TyCanaryLayoutProof, TyCanaryManifestBinding,
    TyCanaryParentGateEvidence, TyCanaryProofDecision, TyCanaryRejectionReason,
    TyCanaryValidationProvenance, TyReducerEvidencePacket, TyReducerEvidenceRow,
    TyReducerEvidenceStatus,
};

const ENTRY_SYMBOL: &str = "ty_runtime_value_replay_parent_loop";
const WRAPPER_ID: &str = "ty.fused-parent-loop.wrapper.v1";
const CERTIFICATE_ID: &str =
    "ty-native-fused-parent-loop:ty_runtime_value_replay_parent_loop:cert-v1";
const PROOF_VALIDATION_SHA256: &str = "sha256:ty-runtime-value-proof-validation";

fn transition_cluster_descriptor_identity() -> String {
    format!("ty-native-fused-transition-cluster:{ENTRY_SYMBOL}:descriptor-v1")
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct RuntimeCallbackValues {
    runtime_generation: u64,
    callback_budget: u64,
    callback_epoch: u64,
    status_code: u32,
    generated_state_count: u64,
    distinct_state_count: u64,
    helper_dispatch_count: u64,
}

impl RuntimeCallbackValues {
    fn for_generation(runtime_generation: u64) -> Self {
        Self {
            runtime_generation,
            callback_budget: 32,
            callback_epoch: runtime_generation + 7,
            status_code: 0,
            generated_state_count: 64,
            distinct_state_count: 19,
            helper_dispatch_count: 11,
        }
    }

    fn callback_digest(self) -> String {
        stable_sha256(&format!(
            "ty-runtime-callback-values:v1:generation={}:budget={}:epoch={}:status={}:generated={}:distinct={}:dispatch={}",
            self.runtime_generation,
            self.callback_budget,
            self.callback_epoch,
            self.status_code,
            self.generated_state_count,
            self.distinct_state_count,
            self.helper_dispatch_count
        ))
    }

    fn status_digest(self) -> String {
        stable_sha256(&format!(
            "ty-runtime-status:v1:generation={}:status={}:dispatch={}",
            self.runtime_generation, self.status_code, self.helper_dispatch_count
        ))
    }

    fn replay_verdict_digest(self) -> String {
        stable_sha256(&format!(
            "ty-runtime-replay-verdict:v1:{}:{}",
            self.callback_digest(),
            self.status_digest()
        ))
    }

    fn replay_root(self, manifest: &ArtifactManifestV1) -> String {
        let facts = manifest_required_fact_digest(manifest);
        stable_sha256(&format!(
            "ty-native-fused-runtime-replay-root:v1:manifest={}:generation={}:callback={}:facts={}",
            manifest.checksum(),
            manifest.invalidation.generation,
            self.callback_digest(),
            facts
        ))
    }

    fn proof_payload(self) -> String {
        format!(
            "runtime_generation={},callback_budget={},callback_epoch={},status_code={},generated_state_count={},distinct_state_count={},helper_dispatch_count={}",
            self.runtime_generation,
            self.callback_budget,
            self.callback_epoch,
            self.status_code,
            self.generated_state_count,
            self.distinct_state_count,
            self.helper_dispatch_count
        )
    }
}

#[derive(Debug, Clone)]
struct RuntimeReplayFixture {
    manifest: ArtifactManifestV1,
    values: RuntimeCallbackValues,
    replay_root_sha256: String,
    telemetry_event_id: String,
    telemetry_record_sha256: String,
    payload_identity: NativeInstallGatePayloadIdentity,
}

fn stable_sha256(value: &str) -> String {
    format!("sha256:{}", sha256_hex(value.as_bytes()))
}

fn runtime_reducer_evidence_summary() -> TyReducerEvidenceCoverageSummary {
    TyReducerEvidencePacket::phase4_local([
        runtime_reducer_evidence_row("minimal_parent_loop"),
        runtime_reducer_evidence_row("no_action_body_parent_loop"),
        runtime_reducer_evidence_row("mcl_shaped_native_fused_parent_loop"),
        runtime_reducer_evidence_row("callback_abi_call_clobber"),
        runtime_reducer_evidence_row("edge_copy_block_arg"),
        runtime_reducer_evidence_row("o3_materialized_helper_return"),
    ])
    .coverage_summary()
    .expect("runtime replay fixture covers required reducer families")
}

fn runtime_reducer_evidence_row(reducer_family: &str) -> TyReducerEvidenceRow {
    TyReducerEvidenceRow {
        command: format!("cargo test -p trust-cg-codegen --test {reducer_family}"),
        target_tuple: "aarch64-apple-darwin".to_owned(),
        trust_cg_revision: "trust-cg-test-revision".to_owned(),
        opt_level: "O1/O3".to_owned(),
        reducer_family: reducer_family.to_owned(),
        case_name: "green_local_reducer_evidence".to_owned(),
        parent_digest: format!("trust-cg-stable128:{reducer_family}:parent"),
        state_count: 1,
        generated_count: 1,
        fingerprint_digest: Some(format!("trust-cg-stable128:{reducer_family}:fingerprint")),
        callback_observations: vec![],
        status: TyReducerEvidenceStatus::GreenReducerEvidence,
        issue_refs: vec!["#667".to_owned()],
    }
}

fn bind_runtime_reducer_evidence(
    manifest: &mut ArtifactManifestV1,
    summary: &TyReducerEvidenceCoverageSummary,
) {
    for (key, value) in summary.metadata_bindings() {
        manifest.metadata.insert(key, value);
    }
}

fn abi_i64() -> AbiValue {
    AbiValue::new(AbiValueKind::I64)
}

fn abi_ptr() -> AbiValue {
    AbiValue::new(AbiValueKind::Ptr)
}

fn entry_signature() -> SymbolSignature {
    SymbolSignature::extern_c(
        vec![
            abi_ptr(),
            abi_ptr(),
            abi_ptr(),
            abi_ptr(),
            abi_ptr(),
            abi_ptr(),
            abi_i64(),
            abi_i64(),
        ],
        vec![],
    )
}

fn native_fused_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target(Target::Aarch64, TargetOperatingSystem::Macos)
        .with_cpu("apple-m")
        .with_features(["fp", "simd"])
}

fn native_fused_abi() -> AbiDescriptor {
    let mut abi = AbiDescriptor::for_trust_cg_target(Target::Aarch64);
    abi.name = "ty-native-fused-parent-loop-aapcs64-lp64".to_owned();
    abi
}

fn native_fused_replay_policy() -> ProofPolicy {
    let mut policy =
        ProofPolicy::require_certificates(["trust-cg-verify", "ty-native-fused-parent-loop"]);
    policy.mode = ProofMode::RequireReplay;
    policy.max_replay_age_generations = Some(0);
    policy
}

fn status_record_layout() -> RecordLayout {
    RecordLayout {
        name: "TyNativeFusedParentLoopStatusAbi".to_owned(),
        representation: "repr(C)".to_owned(),
        size_bytes: 32,
        alignment_bytes: 8,
        fields: vec![
            FieldLayout {
                name: "status".to_owned(),
                offset_bytes: 0,
                size_bytes: 1,
                alignment_bytes: 1,
            },
            FieldLayout {
                name: "deopt".to_owned(),
                offset_bytes: 1,
                size_bytes: 1,
                alignment_bytes: 1,
            },
            FieldLayout {
                name: "panic_code".to_owned(),
                offset_bytes: 2,
                size_bytes: 2,
                alignment_bytes: 2,
            },
            FieldLayout {
                name: "reserved".to_owned(),
                offset_bytes: 4,
                size_bytes: 4,
                alignment_bytes: 1,
            },
            FieldLayout {
                name: "generated_count".to_owned(),
                offset_bytes: 8,
                size_bytes: 8,
                alignment_bytes: 8,
            },
            FieldLayout {
                name: "first_failed_parent".to_owned(),
                offset_bytes: 16,
                size_bytes: 8,
                alignment_bytes: 8,
            },
            FieldLayout {
                name: "rollback_epoch".to_owned(),
                offset_bytes: 24,
                size_bytes: 8,
                alignment_bytes: 8,
            },
        ],
    }
}

fn native_fused_slice(name: &str, bounds_symbol: &str, mutability: Mutability) -> SliceLayout {
    SliceLayout {
        name: name.to_owned(),
        element_size_bytes: 8,
        element_alignment_bytes: 8,
        stride_bytes: 8,
        length: None,
        bounds: PointerBounds::Symbol(bounds_symbol.to_owned()),
        mutability,
        alias_policy: match mutability {
            Mutability::Immutable => AliasPolicy::SharedReadOnly,
            Mutability::Mutable => AliasPolicy::Exclusive,
        },
    }
}

fn native_fused_layout() -> LayoutManifest {
    let mut layout = LayoutManifest::lp64(Endianness::Little, 16);
    layout.wrapper_identity = Some(WRAPPER_ID.to_owned());
    layout.records.push(status_record_layout());
    layout.slices.push(native_fused_slice(
        "flat_state_buffer",
        "state_count",
        Mutability::Immutable,
    ));
    layout.slices.push(native_fused_slice(
        "parent_buffer",
        "parent_capacity",
        Mutability::Mutable,
    ));
    layout.slices.push(native_fused_slice(
        "successor_buffer",
        "successor_capacity",
        Mutability::Mutable,
    ));
    layout.slices.push(native_fused_slice(
        "fingerprint_buffer",
        "successor_capacity",
        Mutability::Mutable,
    ));
    layout.slices.push(SliceLayout {
        name: "callback_status_buffer".to_owned(),
        element_size_bytes: 4,
        element_alignment_bytes: 4,
        stride_bytes: 4,
        length: None,
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 256,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.pointers.push(PointerLayout {
        name: "runtime_arena".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 4096,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.pointers.push(PointerLayout {
        name: "status_out".to_owned(),
        bounds: PointerBounds::ByteRange {
            start_bytes: 0,
            length_bytes: 32,
        },
        mutability: Mutability::Mutable,
        alias_policy: AliasPolicy::Exclusive,
    });
    layout.symbols.push(SymbolLayout {
        name: ENTRY_SYMBOL.to_owned(),
        section: ".text".to_owned(),
        offset_bytes: Some(0),
        size_bytes: 256,
        alignment_bytes: 16,
    });
    layout
        .metadata
        .insert("consumer".to_owned(), "ty".to_owned());
    layout.metadata.insert(
        "status_deopt_contract".to_owned(),
        TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT.to_owned(),
    );
    layout.metadata.insert(
        "native_fused_kernel_identity".to_owned(),
        ENTRY_SYMBOL.to_owned(),
    );
    layout.metadata.insert(
        TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY.to_owned(),
        transition_cluster_descriptor_identity(),
    );
    layout.metadata.insert(
        "state_layout_stability".to_owned(),
        "flat_state_parent_successor_fingerprint_status_v1".to_owned(),
    );
    layout.metadata.insert(
        "helper_purity_readonly".to_owned(),
        "runtime_callbacks_status_only_no_state_mutation".to_owned(),
    );
    layout.metadata.insert(
        "fused_step_invariants".to_owned(),
        "parent_index_fingerprint_generated_count_preserved".to_owned(),
    );
    layout.metadata.insert(
        "bounds_pointer_facts".to_owned(),
        "state_count_parent_capacity_successor_capacity_runtime_checked".to_owned(),
    );
    layout.metadata.insert(
        "dispatch_panic_deopt_safety".to_owned(),
        "panic_or_status_error_deopts_before_useful_native_credit".to_owned(),
    );
    layout
}

fn native_fused_manifest() -> ArtifactManifestV1 {
    let target = native_fused_target();
    let abi = native_fused_abi();
    let layout = native_fused_layout();
    let proof_policy = native_fused_replay_policy();
    let source_sha256 = stable_sha256("ty-runtime-value-replay-spec-lock");
    let compiler_sha256 = stable_sha256("trust-cg-aarch64-ty-runtime-value-replay");
    let trust_ir_sha256 = stable_sha256("ty-runtime-value-replay-trust_ir");
    let native_payload_sha256 = stable_sha256("ty-runtime-value-replay-native-payload");
    let mut invalidation = InvalidationKey::new(
        source_sha256.clone(),
        compiler_sha256.clone(),
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        proof_policy.checksum(),
        41,
    );
    invalidation
        .extra
        .insert("trust_ir_sha256".to_owned(), trust_ir_sha256.clone());
    invalidation.extra.insert(
        "native_payload_sha256".to_owned(),
        native_payload_sha256.clone(),
    );
    invalidation.extra.insert(
        "status_deopt_contract".to_owned(),
        TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT.to_owned(),
    );
    invalidation.extra.insert(
        "native_fused_kernel_identity".to_owned(),
        ENTRY_SYMBOL.to_owned(),
    );
    invalidation.extra.insert(
        TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY.to_owned(),
        transition_cluster_descriptor_identity(),
    );
    invalidation.extra.insert(
        "missing_proof_disposition".to_owned(),
        TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION.to_owned(),
    );
    for (evidence_key, fact) in TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA {
        invalidation
            .extra
            .insert(format!("required_fact.{fact}"), (*evidence_key).to_owned());
    }

    let mut manifest = ArtifactManifestV1::new(
        "ty-native-fused-runtime-value-replay",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        proof_policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: ENTRY_SYMBOL.to_owned(),
        visibility: SymbolVisibility::Exported,
        signature: entry_signature(),
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
    manifest
        .metadata
        .insert("consumer".to_owned(), "ty".to_owned());
    manifest.metadata.insert(
        "ty_manifest_schema".to_owned(),
        TY_NATIVE_FUSED_PARENT_LOOP_MANIFEST_SCHEMA.to_owned(),
    );
    manifest.metadata.insert(
        "classification".to_owned(),
        "product-native-fused-parent-loop".to_owned(),
    );
    manifest.metadata.insert(
        "native_fused_kernel_identity".to_owned(),
        ENTRY_SYMBOL.to_owned(),
    );
    manifest.metadata.insert(
        TY_NATIVE_FUSED_TRANSITION_CLUSTER_DESCRIPTOR_KEY.to_owned(),
        transition_cluster_descriptor_identity(),
    );
    manifest
        .metadata
        .insert("spec_source_lock_sha256".to_owned(), source_sha256);
    manifest
        .metadata
        .insert("trust_ir_sha256".to_owned(), trust_ir_sha256);
    manifest
        .metadata
        .insert("native_payload_sha256".to_owned(), native_payload_sha256);
    manifest
        .metadata
        .insert("trust_cg_source_lock_sha256".to_owned(), compiler_sha256);
    manifest.metadata.insert(
        "proof_policy_checksum".to_owned(),
        manifest.proof_policy.checksum().to_string(),
    );
    manifest.metadata.insert(
        "invalidation_checksum".to_owned(),
        manifest.invalidation.checksum().to_string(),
    );
    manifest.metadata.insert(
        "status_deopt_contract".to_owned(),
        TY_NATIVE_FUSED_PARENT_LOOP_STATUS_DEOPT_CONTRACT.to_owned(),
    );
    manifest.metadata.insert(
        "deopt_rollback_condition".to_owned(),
        "status_deopt_or_dispatch_panic_before_successor_commit".to_owned(),
    );
    manifest.metadata.insert(
        "missing_proof_disposition".to_owned(),
        TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION.to_owned(),
    );
    manifest.metadata.insert(
        "useful_native".to_owned(),
        "false_until_gate_accepts".to_owned(),
    );
    manifest.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY.to_owned(),
        CERTIFICATE_ID.to_owned(),
    );
    for (evidence_key, fact) in TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA {
        manifest
            .metadata
            .insert(format!("required_fact.{fact}"), (*evidence_key).to_owned());
    }
    bind_runtime_reducer_evidence(&mut manifest, &runtime_reducer_evidence_summary());
    manifest
}

fn manifest_required_fact_bindings(
    manifest: &ArtifactManifestV1,
) -> Vec<(String, &'static str, String)> {
    TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA
        .iter()
        .map(|(evidence_key, fact)| {
            let manifest_key = format!("required_fact.{fact}");
            let manifest_value = manifest
                .metadata
                .get(&manifest_key)
                .unwrap_or_else(|| panic!("manifest missing {manifest_key}"))
                .clone();
            let invalidation_value = manifest
                .invalidation
                .extra
                .get(&manifest_key)
                .unwrap_or_else(|| panic!("invalidation missing {manifest_key}"));
            assert_eq!(
                manifest_value, *evidence_key,
                "proof fact {fact} must be sourced from manifest metadata"
            );
            assert_eq!(
                invalidation_value, evidence_key,
                "proof fact {fact} must be sourced from invalidation metadata"
            );
            (manifest_value, *fact, manifest_key)
        })
        .collect()
}

fn manifest_required_fact_digest(manifest: &ArtifactManifestV1) -> String {
    let facts = manifest_required_fact_bindings(manifest)
        .into_iter()
        .map(|(metadata_key, fact, manifest_key)| format!("{manifest_key}={metadata_key}:{fact}"))
        .collect::<Vec<_>>()
        .join("|");
    stable_sha256(&facts)
}

fn manifest_sha256(manifest: &ArtifactManifestV1) -> String {
    format!("sha256:{}", sha256_hex(&manifest.canonical_bytes()))
}

fn payload_identity_from_manifest(
    manifest: &ArtifactManifestV1,
) -> NativeInstallGatePayloadIdentity {
    NativeInstallGatePayloadIdentity {
        source_sha256: manifest
            .metadata
            .get("spec_source_lock_sha256")
            .expect("manifest has spec source digest")
            .clone(),
        trust_ir_sha256: manifest
            .metadata
            .get("trust_ir_sha256")
            .expect("manifest has trust_ir digest")
            .clone(),
        native_payload_sha256: manifest
            .metadata
            .get("native_payload_sha256")
            .expect("manifest has native payload digest")
            .clone(),
    }
}

fn fixture() -> RuntimeReplayFixture {
    let manifest = native_fused_manifest();
    let values = RuntimeCallbackValues::for_generation(manifest.invalidation.generation);
    let replay_root_sha256 = values.replay_root(&manifest);
    let telemetry_event_id = format!(
        "ty-runtime-value-replay:{}:install",
        manifest.invalidation.generation
    );
    let payload_identity = payload_identity_from_manifest(&manifest);
    let telemetry_record_sha256 = stable_sha256(&format!(
        "ty-runtime-value-replay-telemetry:v1:{}:{}",
        telemetry_event_id, replay_root_sha256
    ));
    RuntimeReplayFixture {
        manifest,
        values,
        replay_root_sha256,
        telemetry_event_id,
        telemetry_record_sha256,
        payload_identity,
    }
}

fn replay_identity(
    fixture: &RuntimeReplayFixture,
    expected: &NativeInstallGateExpectedBindings,
) -> NativeInstallGateReplayIdentity {
    NativeInstallGateReplayIdentity {
        schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        replay_root_sha256: fixture.replay_root_sha256.clone(),
        replay_consumer: "ty".to_owned(),
        replay_family: TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE.to_owned(),
        artifact_id: expected.artifact_id.clone(),
        source_sha256: fixture.payload_identity.source_sha256.clone(),
        trust_ir_sha256: fixture.payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: fixture.payload_identity.native_payload_sha256.clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256()
}

fn telemetry(
    fixture: &RuntimeReplayFixture,
    expected: &NativeInstallGateExpectedBindings,
) -> NativeInstallGateTelemetryInput {
    NativeInstallGateTelemetryInput {
        schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        event_id: fixture.telemetry_event_id.clone(),
        counter_scope: format!(
            "ty:{}:{}:{}",
            TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE,
            NativeInstallGateSurface::TyActivation.as_str(),
            expected.artifact_id
        ),
        record_sha256: String::new(),
        artifact_id: expected.artifact_id.clone(),
        manifest_checksum: expected.manifest_checksum,
        proof_report_sha256: Some(PROOF_VALIDATION_SHA256.to_owned()),
        layout_checksum: expected.layout_checksum,
        invalidation_checksum: expected.invalidation_checksum,
        disposition: NativeInstallGateDisposition::Installable,
        rejection_code: None,
        install_authority: NativeInstallGateAuthority::CanaryCallable,
        useful_native_delta: 0,
    }
    .with_canonical_record_sha256()
}

fn proof_summary(
    fixture: &RuntimeReplayFixture,
    telemetry_record_sha256: &str,
) -> ProofEvidenceSummary {
    let manifest = &fixture.manifest;
    let mut evidence = ProofEvidenceSummary::verified(
        "trust-cg-verify",
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
        manifest.invalidation.checksum(),
        manifest.proof_policy.checksum(),
    );
    for (metadata_key, _fact, _manifest_key) in manifest_required_fact_bindings(manifest) {
        evidence
            .metadata
            .insert(metadata_key, TY_NATIVE_FUSED_PROOF_FACT_VERIFIED.to_owned());
    }
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_MANIFEST_IDENTITY_KEY.to_owned(),
        manifest.checksum().to_string(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_CERTIFICATE_IDENTITY_KEY.to_owned(),
        CERTIFICATE_ID.to_owned(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY.to_owned(),
        fixture.replay_root_sha256.clone(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_TELEMETRY_EVENT_KEY.to_owned(),
        fixture.telemetry_event_id.clone(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_GATE_RESULT_KEY.to_owned(),
        telemetry_record_sha256.to_owned(),
    );
    evidence.metadata.insert(
        TY_NATIVE_FUSED_EVIDENCE_VALIDATION_HASH_KEY.to_owned(),
        PROOF_VALIDATION_SHA256.to_owned(),
    );
    evidence.metadata.insert(
        "ty.native_fused.runtime_callback_values".to_owned(),
        fixture.values.proof_payload(),
    );
    evidence.metadata.insert(
        "ty.native_fused.runtime_callback_digest".to_owned(),
        fixture.values.callback_digest(),
    );
    evidence.metadata.insert(
        "ty.native_fused.runtime_status_digest".to_owned(),
        fixture.values.status_digest(),
    );
    evidence
}

fn gate_input(fixture: &RuntimeReplayFixture) -> NativeInstallGateInput {
    let expected = NativeInstallGateExpectedBindings::from_manifest(&fixture.manifest);
    let layout_evidence = NativeInstallGateLayoutEvidence::ty_fused_parent_loop_prework(
        expected.layout_checksum,
        expected.abi_checksum,
        expected.invalidation_checksum,
        WRAPPER_ID,
    );
    let replay_identity = replay_identity(fixture, &expected);
    let telemetry = telemetry(fixture, &expected);
    let proof_evidence = NativeInstallGateProofEvidence {
        summary: proof_summary(fixture, &telemetry.record_sha256),
        proof_report_sha256: Some(PROOF_VALIDATION_SHA256.to_owned()),
        obligation_set: Some("ty-native-fused-runtime-value-replay-required-facts".to_owned()),
        timeout_ms: Some(1_000),
        native_payload_sha256: Some(fixture.payload_identity.native_payload_sha256.clone()),
    };
    let current_invalidation_checksum = expected.invalidation_checksum;
    let current_generation = expected.current_generation;
    NativeInstallGateInput {
        consumer: "ty".to_owned(),
        consumer_mode: TY_NATIVE_FUSED_PARENT_LOOP_CONSUMER_MODE.to_owned(),
        surface: NativeInstallGateSurface::TyActivation,
        candidate_disposition: NativeInstallGateDisposition::Installable,
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        manifest: Some(fixture.manifest.clone()),
        manifest_reference: Some(ArtifactManifestReference::from_manifest(&fixture.manifest)),
        expected,
        payload_identity: fixture.payload_identity.clone(),
        candidate_payload_identity: fixture.payload_identity.clone(),
        layout_evidence: Some(layout_evidence),
        proof_evidence: Some(proof_evidence),
        current_invalidation_checksum,
        artifact_generation: current_generation,
        current_generation,
        revoked: false,
        deny_control: None,
        replay_identity: Some(replay_identity),
        telemetry: Some(telemetry),
    }
}

fn proof_optimization_citation(
    manifest: &ArtifactManifestV1,
) -> ProofOptimizationCertificateCitation {
    ProofOptimizationCertificateCitation {
        function_name: ENTRY_SYMBOL.to_owned(),
        certificate_id: CERTIFICATE_ID.to_owned(),
        proof_hash: stable_sha256("ty-runtime-value-replay-proof"),
        validation_hash: PROOF_VALIDATION_SHA256.to_owned(),
        source_region_hash: stable_sha256("ty-runtime-value-source-region"),
        target_region_hash: stable_sha256("ty-runtime-value-target-region"),
        transform_name: "ty-native-fused-parent-loop".to_owned(),
        transform_version: 1,
        admission: "proof-annotation+proof-facts".to_owned(),
        kind: "TyNativeFusedParentLoop".to_owned(),
        status: "applied".to_owned(),
        rejection_code: None,
        rejection_fact: None,
        rejection_detail: None,
        consumed_facts: manifest_required_fact_bindings(manifest)
            .into_iter()
            .map(
                |(metadata_key, fact, _manifest_key)| ProofOptimizationConsumedFactCitation {
                    name: fact.to_owned(),
                    payload: Some(metadata_key),
                },
            )
            .collect(),
    }
}

fn canary_generations(values: RuntimeCallbackValues) -> TyCanaryGenerationTuple {
    TyCanaryGenerationTuple::new(
        values.runtime_generation,
        values.runtime_generation + 1,
        values.runtime_generation + 2,
        values.runtime_generation,
    )
}

fn canary_key(fixture: &RuntimeReplayFixture) -> TyCanaryAllowlistKey {
    TyCanaryAllowlistKey::new(
        fixture.payload_identity.source_sha256.clone(),
        fixture.values.callback_digest(),
        TyCanaryFamily::ActionCluster,
        canary_generations(fixture.values),
        Target::Aarch64,
        stable_sha256(&fixture.manifest.target.checksum().to_string()),
        fixture.manifest.proof_policy.checksum().to_string(),
        fixture.manifest.layout.checksum().to_string(),
        manifest_sha256(&fixture.manifest),
    )
}

fn canary_manifest(
    fixture: &RuntimeReplayFixture,
    key: &TyCanaryAllowlistKey,
) -> TyCanaryManifestBinding {
    TyCanaryManifestBinding {
        source_sha256: fixture.payload_identity.source_sha256.clone(),
        trust_ir_sha256: fixture.payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: fixture.payload_identity.native_payload_sha256.clone(),
        abi_checksum: fixture.manifest.abi.checksum().to_string(),
        layout_checksum: key.layout_checksum.clone(),
        compiler_config_sha256: fixture.manifest.invalidation.compiler_fingerprint.clone(),
        target_facts_sha256: key.target_facts_sha256.clone(),
        proof_policy: key.proof_policy.clone(),
        consumer_kind: "ty".to_owned(),
        wrapper_id: WRAPPER_ID.to_owned(),
        symbols: fixture
            .manifest
            .symbols
            .iter()
            .map(|symbol| symbol.name.clone())
            .collect(),
        replay_root_sha256: fixture.replay_root_sha256.clone(),
        telemetry_key: fixture.telemetry_record_sha256.clone(),
        manifest_sha256: key.manifest_sha256.clone(),
    }
}

fn canary_layout() -> TyCanaryLayoutProof {
    TyCanaryLayoutProof {
        flat_state_buffers: true,
        parent_buffers: true,
        fingerprint_buffers: true,
        callback_runtime_symbols: true,
        return_status_buffers: true,
        generation_fences: true,
        mutability_aliasing: true,
        wrapper_id: WRAPPER_ID.to_owned(),
    }
}

fn canary_observation(values: RuntimeCallbackValues) -> TyCanaryExecutionObservation {
    TyCanaryExecutionObservation {
        generated_state_count: values.generated_state_count,
        distinct_state_count: values.distinct_state_count,
        parent_indexes_sha256: stable_sha256(&format!(
            "ty-runtime-parents:v1:{}:{}",
            values.runtime_generation, values.generated_state_count
        )),
        fingerprints_sha256: stable_sha256(&format!(
            "ty-runtime-fingerprints:v1:{}:{}",
            values.runtime_generation, values.distinct_state_count
        )),
        final_verdict: "ok".to_owned(),
        status_codes_sha256: values.status_digest(),
        callback_visible_sha256: values.callback_digest(),
        replay_verdict_sha256: values.replay_verdict_digest(),
    }
}

fn canary_candidate(fixture: &RuntimeReplayFixture) -> TyCanaryCandidate {
    let key = canary_key(fixture);
    let manifest = canary_manifest(fixture, &key);
    let observation = canary_observation(fixture.values);
    let provenance = TyCanaryValidationProvenance {
        proof_report_sha256: PROOF_VALIDATION_SHA256.to_owned(),
        tv_report_sha256: stable_sha256("ty-runtime-value-tv-report"),
        replay_root_sha256: fixture.replay_root_sha256.clone(),
        consumer_equivalence_sha256: stable_sha256(&format!(
            "ty-runtime-value-equivalence:v1:{}:{}",
            observation.callback_visible_sha256, observation.replay_verdict_sha256
        )),
        validator_id: "trust-cg-tv:ty-runtime-value-replay:v1".to_owned(),
        proof_policy_decision: TyCanaryProofDecision::Accepted,
    }
    .with_required_trust_ir_proof_fact_bindings(&manifest);
    TyCanaryCandidate {
        mode: TyCanaryCandidateMode::CanaryInstallable,
        key: key.clone(),
        manifest: Some(manifest.clone()),
        layout: Some(canary_layout()),
        provenance: Some(provenance),
        equivalence: Some(TyCanaryEquivalenceEvidence {
            baseline: observation.clone(),
            native: observation,
        }),
        invalidation: Some(TyCanaryInvalidationState {
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
        }),
    }
}

fn canary_allowlist(fixture: &RuntimeReplayFixture) -> TyCanaryAllowlist {
    let mut allowlist = TyCanaryAllowlist::new();
    allowlist.add_exact(&canary_key(fixture));
    allowlist
}

fn accepted_parent_gates() -> TyCanaryParentGateEvidence {
    TyCanaryParentGateEvidence {
        install_gate_accepted: true,
        consumer_gate_accepted: true,
        three_spec_cli_accepted: true,
    }
}

fn assert_canary_no_authority(
    decision: &TyCanaryAllowlistDecision,
    status: TyCanaryDecisionStatus,
    reason: TyCanaryRejectionReason,
) {
    assert_eq!(decision.status, status);
    assert_eq!(decision.reason, reason);
    assert!(decision.baseline_authoritative);
    assert!(!decision.native_authoritative);
    assert!(decision.is_pre_activation_only());
    assert!(decision.side_effects.all_blocked());
    assert_eq!(decision.side_effects.useful_native_delta, 0);
}

fn admission_evidence(
    packet: &trust_cg_codegen::jit_install_gate::NativeInstallGatePacket,
    current: &NativeInstallGateRevalidationInput,
) -> NativeInstallGateConsumerAdmissionEvidence {
    NativeInstallGateConsumerAdmissionEvidence::from_packet(
        packet,
        current,
        native_install_gate_consumer_allowlist_key(packet, current)
            .expect("TY activation packet has allowlist key"),
        true,
        true,
        true,
    )
}

#[test]
fn ty_native_fused_runtime_callback_values_bind_replay_and_non_promoting_identity() {
    let fixture = fixture();
    let input = gate_input(&fixture);
    let packet = validate_native_install_gate(&input);

    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable,
        "packet rejected with {:?}",
        packet.rejection_code
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.ty_native_activate);
    assert!(packet.actions.useful_native_eligible);
    assert_eq!(
        packet
            .replay_identity
            .as_ref()
            .expect("install packet carries replay identity")
            .replay_root_sha256,
        fixture.replay_root_sha256
    );

    let proof = input
        .proof_evidence
        .as_ref()
        .expect("gate input carries proof evidence");
    assert_eq!(
        proof
            .summary
            .metadata
            .get("ty.native_fused.runtime_callback_values")
            .map(String::as_str),
        Some(fixture.values.proof_payload().as_str())
    );
    assert_eq!(
        proof
            .summary
            .metadata
            .get("ty.native_fused.runtime_callback_digest")
            .map(String::as_str),
        Some(fixture.values.callback_digest().as_str())
    );
    for (metadata_key, fact, _manifest_key) in manifest_required_fact_bindings(&fixture.manifest) {
        assert_eq!(
            proof
                .summary
                .metadata
                .get(&metadata_key)
                .map(String::as_str),
            Some(TY_NATIVE_FUSED_PROOF_FACT_VERIFIED),
            "proof fact {fact} must be verified through manifest metadata"
        );
    }

    let product_packet = native_install_gate_non_promoting_product_promotion_packet_impl(
        &fixture.manifest,
        &packet,
        &proof_optimization_citation(&fixture.manifest),
        &runtime_reducer_evidence_summary(),
    )
    .expect("complete runtime replay evidence should emit the non-promoting product packet");
    assert!(!product_packet.product_promotion_allowed);
    assert_eq!(
        product_packet.product_promotion_disposition,
        TY_NATIVE_FUSED_NON_PROMOTING_DISPOSITION
    );
    assert!(!product_packet.promotion_useful_native_credit_allowed);
    assert_eq!(
        product_packet.replay_root_sha256,
        fixture.replay_root_sha256
    );
    assert_eq!(
        product_packet.required_fact_bindings.len(),
        TY_NATIVE_FUSED_REQUIRED_PROOF_FACT_METADATA.len()
    );

    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let admission = native_install_gate_consumer_admission(
        &packet,
        Some(packet.packet_hash),
        &current,
        &admission_evidence(&packet, &current),
    );
    assert_eq!(
        admission.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(admission.rejection_code, None);
    assert!(admission.actions.ty_native_activate);
    assert_eq!(admission.telemetry.useful_native_delta, 0);

    let allowlist = canary_allowlist(&fixture);
    let candidate = canary_candidate(&fixture);
    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());
    assert_canary_no_authority(
        &decision,
        TyCanaryDecisionStatus::AllowlistedRequiresProductGate,
        TyCanaryRejectionReason::ProductActivationRequired,
    );
    let observation = canary_observation(fixture.values);
    assert_eq!(
        candidate
            .equivalence
            .as_ref()
            .expect("candidate carries equivalence")
            .native
            .callback_visible_sha256,
        observation.callback_visible_sha256
    );
    assert_eq!(
        decision.telemetry.replay_root_sha256.as_deref(),
        Some(fixture.replay_root_sha256.as_str())
    );
}

#[test]
fn ty_native_fused_runtime_callback_replay_mutations_reject_non_promoting() {
    let fixture = fixture();
    let input = gate_input(&fixture);
    let packet = validate_native_install_gate(&input);
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable,
        "packet rejected with {:?}",
        packet.rejection_code
    );

    let mut changed_values = fixture.values;
    changed_values.callback_budget += 1;
    assert_ne!(
        changed_values.callback_digest(),
        fixture.values.callback_digest()
    );

    let allowlist = canary_allowlist(&fixture);
    let mut callback_mismatch = canary_candidate(&fixture);
    callback_mismatch
        .equivalence
        .as_mut()
        .expect("candidate carries equivalence")
        .native
        .callback_visible_sha256 = changed_values.callback_digest();
    let decision = allowlist.evaluate(&callback_mismatch, accepted_parent_gates());
    assert_canary_no_authority(
        &decision,
        TyCanaryDecisionStatus::Rejected,
        TyCanaryRejectionReason::MissingEquivalence,
    );

    let mut replay_root_mismatch = canary_candidate(&fixture);
    replay_root_mismatch
        .provenance
        .as_mut()
        .expect("candidate carries provenance")
        .replay_root_sha256 = changed_values.replay_root(&fixture.manifest);
    let decision = allowlist.evaluate(&replay_root_mismatch, accepted_parent_gates());
    assert_canary_no_authority(
        &decision,
        TyCanaryDecisionStatus::Rejected,
        TyCanaryRejectionReason::FailedProof,
    );

    let mut proof_replay_root = gate_input(&fixture);
    proof_replay_root
        .proof_evidence
        .as_mut()
        .expect("gate input carries proof evidence")
        .summary
        .metadata
        .insert(
            TY_NATIVE_FUSED_EVIDENCE_REPLAY_ROOT_KEY.to_owned(),
            changed_values.replay_root(&fixture.manifest),
        );
    let rejected_packet = validate_native_install_gate(&proof_replay_root);
    assert_eq!(
        rejected_packet.disposition,
        NativeInstallGateDisposition::Rejected
    );
    assert_eq!(
        rejected_packet.rejection_code,
        Some(NativeInstallGateRejectionCode::ReplayIdentityMismatch)
    );
    assert!(rejected_packet.actions.all_install_authority_blocked());

    let mut tampered_product_packet = packet.clone();
    tampered_product_packet
        .replay_identity
        .as_mut()
        .expect("packet carries replay identity")
        .replay_root_sha256 = changed_values.replay_root(&fixture.manifest);
    let err = native_install_gate_non_promoting_product_promotion_packet_impl(
        &fixture.manifest,
        &tampered_product_packet,
        &proof_optimization_citation(&fixture.manifest),
        &runtime_reducer_evidence_summary(),
    )
    .expect_err("product packet must reject replay roots not bound to the install packet");
    assert_eq!(
        err,
        NativeInstallGateProductPromotionRejectionReason::ReplayIdentityMismatch
    );

    let current = NativeInstallGateRevalidationInput::from_packet(&packet);
    let evidence = admission_evidence(&packet, &current);
    let mut stale_current = current.clone();
    stale_current.current_generation += 1;
    let stale_admission = native_install_gate_consumer_admission(
        &packet,
        Some(packet.packet_hash),
        &stale_current,
        &evidence,
    );
    assert_eq!(
        stale_admission.disposition,
        NativeInstallGateDisposition::Rejected
    );
    assert_eq!(
        stale_admission.rejection_code,
        Some(NativeInstallGateRejectionCode::StaleInvalidation)
    );
    assert!(stale_admission.actions.all_install_authority_blocked());
    assert_eq!(stale_admission.telemetry.useful_native_delta, 0);
}

#[test]
fn ty_three_spec_native_fused_smoke_replay_stays_shadow_only_non_promoting() {
    let smoke_fixture = ty_native_fused_three_spec_smoke_fixture();
    assert!(smoke_fixture.is_shadow_only_non_promoting());
    assert!(!smoke_fixture.product_promotion_allowed);
    assert!(!smoke_fixture.useful_native_credit_allowed);
    assert_eq!(
        smoke_fixture.canonical_fixture_sha256(),
        TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256
    );

    for spec in &smoke_fixture.specs {
        smoke_fixture
            .validate_spec_observation(spec)
            .expect("three-spec smoke fixture row should validate");
    }

    let mut status_mismatch = smoke_fixture.specs[0].clone();
    status_mismatch.status_sha256 = "sha256:changed-three-spec-status".to_owned();
    let err = smoke_fixture
        .validate_spec_observation(&status_mismatch)
        .expect_err("changed status digest must reject shadow replay evidence");
    assert_eq!(
        err,
        ShadowReplayTyNativeFusedSmokeRejection::StatusDigestMismatch
    );

    let row_under_test = smoke_fixture.specs[0].clone();
    let mut unrelated_row_mutation = smoke_fixture.clone();
    unrelated_row_mutation.specs[1].generated_count += 1;
    assert_ne!(
        unrelated_row_mutation.canonical_fixture_sha256(),
        TY_NATIVE_FUSED_THREE_SPEC_SMOKE_CANONICAL_FIXTURE_SHA256
    );
    let err = unrelated_row_mutation
        .validate_spec_observation(&row_under_test)
        .expect_err("unrelated row mutation must reject row replay through fixture hash");
    assert_eq!(
        err,
        ShadowReplayTyNativeFusedSmokeRejection::CanonicalFixtureHashMismatch
    );

    let runtime_fixture = fixture();
    let allowlist = canary_allowlist(&runtime_fixture);
    let mut candidate = canary_candidate(&runtime_fixture);
    candidate.mode = TyCanaryCandidateMode::ShadowOnly;
    let decision = allowlist.evaluate(&candidate, accepted_parent_gates());
    assert_canary_no_authority(
        &decision,
        TyCanaryDecisionStatus::Rejected,
        TyCanaryRejectionReason::ShadowOnlyNonCallable,
    );
}
