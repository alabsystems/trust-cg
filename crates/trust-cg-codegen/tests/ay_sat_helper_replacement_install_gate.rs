// trust-cg-codegen/tests/ay_sat_helper_replacement_install_gate.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::sync::OnceLock;

use trust_cg_codegen::ay_sat_helper_replacement_contract::{
    AY_SAT_CONTAINS4_MASKED_SYMBOL, AY_SAT_MINIMIZE_CLASSIFY_CHECK, AY_SAT_MINIMIZE_CLASSIFY_DROP,
    AY_SAT_MINIMIZE_CLASSIFY_KEEP, AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL, AY_SAT_MINIMIZE_MIN_KEEP_FLAG,
    AY_SAT_MINIMIZE_MIN_POISON_FLAG, AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG, AY_SAT_MINIMIZE_NO_REASON,
    AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL, AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED,
    AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE, AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED,
    AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH, AY_SAT_THEORY_DISPATCH_RESULT_STATUS_MASK,
    AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT, AY_SAT_THEORY_DISPATCH_RESULT_VALUE_BIT,
    AY_SAT_THEORY_DISPATCH_STATUS_ASSERT, AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE,
    AY_SAT_THEORY_DISPATCH_STATUS_SKIP, ay_sat_contains4_masked_manifest_for_parts,
    ay_sat_contains4_masked_proof_policy, ay_sat_contains4_masked_signature,
    ay_sat_contains4_masked_symbol_lookup_contract,
    ay_sat_contains4_masked_verified_proof_evidence, ay_sat_minimize_keep_drop_manifest_for_parts,
    ay_sat_minimize_keep_drop_proof_policy, ay_sat_minimize_keep_drop_signature,
    ay_sat_minimize_keep_drop_symbol_lookup_contract,
    ay_sat_minimize_keep_drop_verified_proof_evidence,
    ay_sat_theory_dispatch_assignment_manifest_for_parts,
    ay_sat_theory_dispatch_assignment_proof_policy, ay_sat_theory_dispatch_assignment_signature,
    ay_sat_theory_dispatch_assignment_symbol_lookup_contract,
    ay_sat_theory_dispatch_assignment_verified_proof_evidence,
};
use trust_cg_codegen::compile_service::{
    ArtifactInstallDisposition, ArtifactManifestReference, ProofTvEvidenceOutcome, ProofTvVerdict,
};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, ArtifactManifestV1, Endianness, LayoutManifest, ProofEvidenceRejectionCode,
    ProofEvidenceSummary, ProofEvidenceVerdict, ProofPolicy, SymbolLookupContract,
    TargetDescriptor, TargetOperatingSystem,
};
use trust_cg_codegen::{
    ArtifactKind, ArtifactPayload, CompileGeneration, CompileRequest, CompileService,
    CompileStatus, NATIVE_INSTALL_GATE_REPLAY_SCHEMA, NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
    NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA, NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
    NativeInstallGateActions, NativeInstallGateAuthority, NativeInstallGateDisposition,
    NativeInstallGateExpectedBindings, NativeInstallGateInput, NativeInstallGateLayoutAccess,
    NativeInstallGateLayoutEvidence, NativeInstallGatePayloadIdentity,
    NativeInstallGateProofEvidence, NativeInstallGateRejectionCode,
    NativeInstallGateReplayIdentity, NativeInstallGateSurface, NativeInstallGateTelemetryInput,
    SourceKind, Target,
};
use trust_ir::{
    BinOp, Block as TrustIrBlock, BlockId, CastOp, Constant, FuncId, FuncTy,
    Function as TrustIrFunction, ICmpOp, Inst, InstrNode, Module as TrustIrModule, Ty, ValueId,
};

type AYSatContains4MaskedFn = unsafe extern "C" fn(i32, i32, i32, i32, i32, i32) -> i32;
type AYSatMinimizeKeepDropFn = unsafe extern "C" fn(i32, i32, i32, i32, i32, i32, i32) -> i32;
type AYSatTheoryDispatchAssignmentFn =
    unsafe extern "C" fn(i32, i32, i32, i32, i32, i32, i32) -> i64;

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}

fn ay_sat_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target_spec(
        trust_cg_codegen::target::TargetSpec::default_for_architecture(Target::host()),
    )
}

fn ay_sat_abi() -> AbiDescriptor {
    AbiDescriptor::for_trust_cg_target_os(Target::host(), TargetOperatingSystem::host())
}

fn ay_sat_minimize_abi() -> AbiDescriptor {
    AbiDescriptor::for_trust_cg_target_os(Target::host(), TargetOperatingSystem::host())
}

fn ay_sat_theory_dispatch_abi() -> AbiDescriptor {
    AbiDescriptor::for_trust_cg_target_os(Target::host(), TargetOperatingSystem::host())
}

fn ay_sat_contains4_manifest(generation: u64) -> ArtifactManifestV1 {
    let (text_size_bytes, native_payload_sha256) = observed_contains4_payload_contract();
    let layout = LayoutManifest::lp64(Endianness::Little, Target::host().stack_alignment() as u16);
    let mut manifest = ay_sat_contains4_masked_manifest_for_parts(
        ay_sat_target(),
        ay_sat_abi(),
        layout,
        ay_sat_contains4_masked_proof_policy(),
        generation,
        text_size_bytes,
    );
    manifest
        .metadata
        .insert("native_payload_sha256".to_owned(), native_payload_sha256);
    manifest
        .metadata
        .insert("differential_evidence_issue".to_owned(), "801".to_owned());
    manifest.metadata.insert(
        "differential_evidence_target".to_owned(),
        "ay_sat_helper_replacement_differential".to_owned(),
    );
    manifest.metadata.insert(
        "rust_reference".to_owned(),
        "contains4_masked_and_contains_literal_reference".to_owned(),
    );
    manifest
        .metadata
        .insert("useful_native".to_owned(), "0".to_owned());
    manifest
}

fn ay_sat_minimize_manifest(generation: u64) -> ArtifactManifestV1 {
    let (text_size_bytes, native_payload_sha256) = observed_minimize_payload_contract();
    let layout = LayoutManifest::lp64(Endianness::Little, Target::host().stack_alignment() as u16);
    let mut manifest = ay_sat_minimize_keep_drop_manifest_for_parts(
        ay_sat_target(),
        ay_sat_minimize_abi(),
        layout,
        ay_sat_minimize_keep_drop_proof_policy(),
        generation,
        text_size_bytes,
    );
    manifest
        .metadata
        .insert("native_payload_sha256".to_owned(), native_payload_sha256);
    manifest
        .metadata
        .insert("differential_evidence_issue".to_owned(), "802".to_owned());
    manifest.metadata.insert(
        "differential_evidence_target".to_owned(),
        "ay_sat_helper_replacement_differential".to_owned(),
    );
    manifest.metadata.insert(
        "rust_reference".to_owned(),
        "minimize_keep_drop_classification_reference".to_owned(),
    );
    manifest
        .metadata
        .insert("useful_native".to_owned(), "0".to_owned());
    manifest
}

fn ay_sat_theory_dispatch_manifest(generation: u64) -> ArtifactManifestV1 {
    let (text_size_bytes, native_payload_sha256) = observed_theory_dispatch_payload_contract();
    let layout = LayoutManifest::lp64(Endianness::Little, Target::host().stack_alignment() as u16);
    let mut manifest = ay_sat_theory_dispatch_assignment_manifest_for_parts(
        ay_sat_target(),
        ay_sat_theory_dispatch_abi(),
        layout,
        ay_sat_theory_dispatch_assignment_proof_policy(),
        generation,
        text_size_bytes,
    );
    manifest
        .metadata
        .insert("native_payload_sha256".to_owned(), native_payload_sha256);
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
    manifest
}

fn sat_helper_payload_identity() -> NativeInstallGatePayloadIdentity {
    NativeInstallGatePayloadIdentity {
        source_sha256: "sha256:ay-sat-contains4-source".to_owned(),
        trust_ir_sha256: "sha256:ay-sat-contains4-trust_ir".to_owned(),
        native_payload_sha256: observed_contains4_payload_contract().1,
    }
}

fn minimize_helper_payload_identity() -> NativeInstallGatePayloadIdentity {
    NativeInstallGatePayloadIdentity {
        source_sha256: "sha256:ay-sat-minimize-source".to_owned(),
        trust_ir_sha256: "sha256:ay-sat-minimize-trust_ir".to_owned(),
        native_payload_sha256: observed_minimize_payload_contract().1,
    }
}

fn theory_dispatch_payload_identity() -> NativeInstallGatePayloadIdentity {
    NativeInstallGatePayloadIdentity {
        source_sha256: "sha256:ay-sat-theory-dispatch-source".to_owned(),
        trust_ir_sha256: "sha256:ay-sat-theory-dispatch-trust_ir".to_owned(),
        native_payload_sha256: observed_theory_dispatch_payload_contract().1,
    }
}

fn observe_payload_contract(request_id: &'static str, module: TrustIrModule) -> (u64, String) {
    // This compile-only observation carries neither a manifest nor install
    // authority. The manifest-bearing compile in each test independently
    // rechecks these portable fixture claims against a fresh live payload.
    let mut request = CompileRequest::new(request_id, CompileGeneration::new(0));
    request.install_intent = trust_cg_codegen::InstallIntent::CompileOnly;
    request.provenance.source_kind = SourceKind::TrustIrModule;
    let response = CompileService::default().compile(request, &module);
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "compile-only SAT helper observation diagnostics: {:?}",
        response.diagnostics
    );
    let binding = response
        .artifact
        .as_ref()
        .and_then(|artifact| artifact.install.installed_payload_binding.as_ref())
        .expect("compile-only SAT helper observation seals a live payload binding");
    (
        binding.code_size_bytes,
        binding.native_payload_sha256.clone(),
    )
}

fn observed_contains4_payload_contract() -> (u64, String) {
    static CONTRACT: OnceLock<(u64, String)> = OnceLock::new();
    CONTRACT
        .get_or_init(|| {
            observe_payload_contract(
                "sat-contains4-observe-live-payload",
                contains4_masked_module(),
            )
        })
        .clone()
}

fn observed_minimize_payload_contract() -> (u64, String) {
    static CONTRACT: OnceLock<(u64, String)> = OnceLock::new();
    CONTRACT
        .get_or_init(|| {
            observe_payload_contract(
                "sat-minimize-observe-live-payload",
                minimize_keep_drop_module(),
            )
        })
        .clone()
}

fn observed_theory_dispatch_payload_contract() -> (u64, String) {
    static CONTRACT: OnceLock<(u64, String)> = OnceLock::new();
    CONTRACT
        .get_or_init(|| {
            observe_payload_contract(
                "sat-theory-dispatch-observe-live-payload",
                theory_dispatch_assignment_module(),
            )
        })
        .clone()
}

fn sat_helper_verified_proof(manifest: &ArtifactManifestV1) -> NativeInstallGateProofEvidence {
    let mut summary = ay_sat_contains4_masked_verified_proof_evidence("trust-cg-verify", manifest);
    summary.native_payload_sha256 = sat_helper_payload_identity().native_payload_sha256;
    summary.metadata.insert(
        "differential_evidence_target".to_owned(),
        "ay_sat_helper_replacement_differential".to_owned(),
    );
    summary.metadata.insert(
        "rust_reference".to_owned(),
        "contains4_masked_and_contains_literal_reference".to_owned(),
    );

    NativeInstallGateProofEvidence {
        summary,
        proof_report_sha256: Some("sha256:ay-sat-contains4-proof-report".to_owned()),
        obligation_set: Some("ay-sat-helper-replacement-issue-801-cases".to_owned()),
        timeout_ms: Some(10_000),
        native_payload_sha256: Some(sat_helper_payload_identity().native_payload_sha256),
    }
}

fn minimize_helper_verified_proof(manifest: &ArtifactManifestV1) -> NativeInstallGateProofEvidence {
    let mut summary =
        ay_sat_minimize_keep_drop_verified_proof_evidence("trust-cg-verify", manifest);
    summary.native_payload_sha256 = minimize_helper_payload_identity().native_payload_sha256;
    summary.metadata.insert(
        "differential_evidence_target".to_owned(),
        "ay_sat_helper_replacement_differential".to_owned(),
    );
    summary.metadata.insert(
        "rust_reference".to_owned(),
        "minimize_keep_drop_classification_reference".to_owned(),
    );

    NativeInstallGateProofEvidence {
        summary,
        proof_report_sha256: Some("sha256:ay-sat-minimize-proof-report".to_owned()),
        obligation_set: Some("ay-sat-helper-replacement-issue-802-cases".to_owned()),
        timeout_ms: Some(10_000),
        native_payload_sha256: Some(minimize_helper_payload_identity().native_payload_sha256),
    }
}

fn theory_dispatch_verified_proof(manifest: &ArtifactManifestV1) -> NativeInstallGateProofEvidence {
    let mut summary =
        ay_sat_theory_dispatch_assignment_verified_proof_evidence("trust-cg-verify", manifest);
    summary.native_payload_sha256 = theory_dispatch_payload_identity().native_payload_sha256;
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
        native_payload_sha256: Some(theory_dispatch_payload_identity().native_payload_sha256),
    }
}

fn sat_helper_gate_input(manifest: &ArtifactManifestV1) -> NativeInstallGateInput {
    let expected = NativeInstallGateExpectedBindings::from_manifest(manifest);
    let payload_identity = sat_helper_payload_identity();
    let proof_evidence = sat_helper_verified_proof(manifest);
    let counter_scope = format!(
        "{}:{}:{}:{}",
        "ay",
        "sat-helper-replacement-install-gate",
        NativeInstallGateSurface::DirectCompileInstall.as_str(),
        expected.artifact_id
    );
    let telemetry = NativeInstallGateTelemetryInput {
        schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        event_id: "ay-sat-helper-replacement-install-gate".to_owned(),
        counter_scope,
        record_sha256: String::new(),
        artifact_id: expected.artifact_id.clone(),
        manifest_checksum: expected.manifest_checksum,
        proof_report_sha256: proof_evidence.proof_report_sha256.clone(),
        layout_checksum: expected.layout_checksum,
        invalidation_checksum: expected.invalidation_checksum,
        disposition: NativeInstallGateDisposition::Installable,
        rejection_code: None,
        install_authority: NativeInstallGateAuthority::CanaryCallable,
        useful_native_delta: 0,
    }
    .with_canonical_record_sha256();
    let replay_identity = NativeInstallGateReplayIdentity {
        schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        replay_root_sha256: "sha256:ay-sat-helper-replacement-replay".to_owned(),
        replay_consumer: "ay".to_owned(),
        replay_family: "sat-helper-replacement-install-gate".to_owned(),
        artifact_id: expected.artifact_id.clone(),
        source_sha256: payload_identity.source_sha256.clone(),
        trust_ir_sha256: payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: payload_identity.native_payload_sha256.clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256();

    NativeInstallGateInput {
        consumer: "ay".to_owned(),
        consumer_mode: "sat-helper-replacement-install-gate".to_owned(),
        surface: NativeInstallGateSurface::DirectCompileInstall,
        candidate_disposition: NativeInstallGateDisposition::Installable,
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        manifest: Some(manifest.clone()),
        manifest_reference: Some(ArtifactManifestReference::from_manifest(manifest)),
        expected: expected.clone(),
        payload_identity: payload_identity.clone(),
        candidate_payload_identity: payload_identity,
        layout_evidence: Some(
            NativeInstallGateLayoutEvidence {
                layout_checksum: expected.layout_checksum,
                abi_checksum: expected.abi_checksum,
                invalidation_checksum: expected.invalidation_checksum,
                validation_provenance: "trust-cg.ay.sat_contains4.layout_adapter.v1".to_owned(),
                evidence_sha256: None,
                wrapper_identity: manifest.layout.wrapper_identity.clone(),
                regions: vec![
                    NativeInstallGateLayoutEvidence::region(
                        "contains4_args",
                        "contains4_args",
                        4,
                        24,
                        NativeInstallGateLayoutAccess::ReadOnly,
                        "ay-sat-helper",
                        "ay_sat_helper",
                    ),
                    NativeInstallGateLayoutEvidence::region(
                        "contains4_result",
                        "contains4_result",
                        4,
                        4,
                        NativeInstallGateLayoutAccess::WriteOnly,
                        "ay-sat-helper",
                        "ay_sat_helper",
                    ),
                ],
                entry_abis: vec![NativeInstallGateLayoutEvidence::entry_abi(
                    "ay_sat_contains4_masked",
                    expected.abi_checksum,
                    &["contains4_args"],
                    "contains4_result",
                    "ay_sat_helper",
                )],
            }
            .with_canonical_evidence_sha256(),
        ),
        proof_evidence: Some(proof_evidence.clone()),
        current_invalidation_checksum: expected.invalidation_checksum,
        artifact_generation: expected.current_generation,
        current_generation: expected.current_generation,
        revoked: false,
        deny_control: None,
        replay_identity: Some(replay_identity),
        telemetry: Some(telemetry),
    }
}

fn minimize_helper_gate_input(manifest: &ArtifactManifestV1) -> NativeInstallGateInput {
    let expected = NativeInstallGateExpectedBindings::from_manifest(manifest);
    let payload_identity = minimize_helper_payload_identity();
    let proof_evidence = minimize_helper_verified_proof(manifest);
    let counter_scope = format!(
        "{}:{}:{}:{}",
        "ay",
        "sat-minimize-helper-install-gate",
        NativeInstallGateSurface::DirectCompileInstall.as_str(),
        expected.artifact_id
    );
    let telemetry = NativeInstallGateTelemetryInput {
        schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        event_id: "ay-sat-minimize-helper-install-gate".to_owned(),
        counter_scope,
        record_sha256: String::new(),
        artifact_id: expected.artifact_id.clone(),
        manifest_checksum: expected.manifest_checksum,
        proof_report_sha256: proof_evidence.proof_report_sha256.clone(),
        layout_checksum: expected.layout_checksum,
        invalidation_checksum: expected.invalidation_checksum,
        disposition: NativeInstallGateDisposition::Installable,
        rejection_code: None,
        install_authority: NativeInstallGateAuthority::CanaryCallable,
        useful_native_delta: 0,
    }
    .with_canonical_record_sha256();
    let replay_identity = NativeInstallGateReplayIdentity {
        schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        replay_root_sha256: "sha256:ay-sat-minimize-helper-replay".to_owned(),
        replay_consumer: "ay".to_owned(),
        replay_family: "sat-minimize-helper-install-gate".to_owned(),
        artifact_id: expected.artifact_id.clone(),
        source_sha256: payload_identity.source_sha256.clone(),
        trust_ir_sha256: payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: payload_identity.native_payload_sha256.clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256();

    NativeInstallGateInput {
        consumer: "ay".to_owned(),
        consumer_mode: "sat-minimize-helper-install-gate".to_owned(),
        surface: NativeInstallGateSurface::DirectCompileInstall,
        candidate_disposition: NativeInstallGateDisposition::Installable,
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        manifest: Some(manifest.clone()),
        manifest_reference: Some(ArtifactManifestReference::from_manifest(manifest)),
        expected: expected.clone(),
        payload_identity: payload_identity.clone(),
        candidate_payload_identity: payload_identity,
        layout_evidence: Some(
            NativeInstallGateLayoutEvidence {
                layout_checksum: expected.layout_checksum,
                abi_checksum: expected.abi_checksum,
                invalidation_checksum: expected.invalidation_checksum,
                validation_provenance: "trust-cg.ay.sat_minimize.layout_adapter.v1".to_owned(),
                evidence_sha256: None,
                wrapper_identity: manifest.layout.wrapper_identity.clone(),
                regions: vec![
                    NativeInstallGateLayoutEvidence::region(
                        "minimize_args",
                        "minimize_args",
                        4,
                        28,
                        NativeInstallGateLayoutAccess::ReadOnly,
                        "ay-sat-helper",
                        "ay_sat_helper",
                    ),
                    NativeInstallGateLayoutEvidence::region(
                        "minimize_result",
                        "minimize_result",
                        4,
                        4,
                        NativeInstallGateLayoutAccess::WriteOnly,
                        "ay-sat-helper",
                        "ay_sat_helper",
                    ),
                ],
                entry_abis: vec![NativeInstallGateLayoutEvidence::entry_abi(
                    "ay_sat_minimize_keep_drop_classify",
                    expected.abi_checksum,
                    &["minimize_args"],
                    "minimize_result",
                    "ay_sat_helper",
                )],
            }
            .with_canonical_evidence_sha256(),
        ),
        proof_evidence: Some(proof_evidence.clone()),
        current_invalidation_checksum: expected.invalidation_checksum,
        artifact_generation: expected.current_generation,
        current_generation: expected.current_generation,
        revoked: false,
        deny_control: None,
        replay_identity: Some(replay_identity),
        telemetry: Some(telemetry),
    }
}

fn theory_dispatch_gate_input(manifest: &ArtifactManifestV1) -> NativeInstallGateInput {
    let expected = NativeInstallGateExpectedBindings::from_manifest(manifest);
    let payload_identity = theory_dispatch_payload_identity();
    let proof_evidence = theory_dispatch_verified_proof(manifest);
    let counter_scope = format!(
        "{}:{}:{}:{}",
        "ay",
        "sat-theory-dispatch-helper-install-gate",
        NativeInstallGateSurface::DirectCompileInstall.as_str(),
        expected.artifact_id
    );
    let telemetry = NativeInstallGateTelemetryInput {
        schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        event_id: "ay-sat-theory-dispatch-helper-install-gate".to_owned(),
        counter_scope,
        record_sha256: String::new(),
        artifact_id: expected.artifact_id.clone(),
        manifest_checksum: expected.manifest_checksum,
        proof_report_sha256: proof_evidence.proof_report_sha256.clone(),
        layout_checksum: expected.layout_checksum,
        invalidation_checksum: expected.invalidation_checksum,
        disposition: NativeInstallGateDisposition::Installable,
        rejection_code: None,
        install_authority: NativeInstallGateAuthority::CanaryCallable,
        useful_native_delta: 0,
    }
    .with_canonical_record_sha256();
    let replay_identity = NativeInstallGateReplayIdentity {
        schema: NATIVE_INSTALL_GATE_REPLAY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_REPLAY_SCHEMA_VERSION,
        replay_root_sha256: "sha256:ay-sat-theory-dispatch-helper-replay".to_owned(),
        replay_consumer: "ay".to_owned(),
        replay_family: "sat-theory-dispatch-helper-install-gate".to_owned(),
        artifact_id: expected.artifact_id.clone(),
        source_sha256: payload_identity.source_sha256.clone(),
        trust_ir_sha256: payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: payload_identity.native_payload_sha256.clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256();

    NativeInstallGateInput {
        consumer: "ay".to_owned(),
        consumer_mode: "sat-theory-dispatch-helper-install-gate".to_owned(),
        surface: NativeInstallGateSurface::DirectCompileInstall,
        candidate_disposition: NativeInstallGateDisposition::Installable,
        requested_authority: NativeInstallGateAuthority::CanaryCallable,
        manifest: Some(manifest.clone()),
        manifest_reference: Some(ArtifactManifestReference::from_manifest(manifest)),
        expected: expected.clone(),
        payload_identity: payload_identity.clone(),
        candidate_payload_identity: payload_identity,
        layout_evidence: Some(
            NativeInstallGateLayoutEvidence {
                layout_checksum: expected.layout_checksum,
                abi_checksum: expected.abi_checksum,
                invalidation_checksum: expected.invalidation_checksum,
                validation_provenance: "trust-cg.ay.sat_theory_dispatch.layout_adapter.v1"
                    .to_owned(),
                evidence_sha256: None,
                wrapper_identity: manifest.layout.wrapper_identity.clone(),
                regions: vec![
                    NativeInstallGateLayoutEvidence::region(
                        "theory_dispatch_args",
                        "theory_dispatch_args",
                        4,
                        28,
                        NativeInstallGateLayoutAccess::ReadOnly,
                        "ay-sat-helper",
                        "ay_sat_helper",
                    ),
                    NativeInstallGateLayoutEvidence::region(
                        "theory_dispatch_result",
                        "theory_dispatch_result",
                        8,
                        8,
                        NativeInstallGateLayoutAccess::WriteOnly,
                        "ay-sat-helper",
                        "ay_sat_helper",
                    ),
                ],
                entry_abis: vec![NativeInstallGateLayoutEvidence::entry_abi(
                    "ay_sat_theory_dispatch_assignment",
                    expected.abi_checksum,
                    &["theory_dispatch_args"],
                    "theory_dispatch_result",
                    "ay_sat_helper",
                )],
            }
            .with_canonical_evidence_sha256(),
        ),
        proof_evidence: Some(proof_evidence.clone()),
        current_invalidation_checksum: expected.invalidation_checksum,
        artifact_generation: expected.current_generation,
        current_generation: expected.current_generation,
        revoked: false,
        deny_control: None,
        replay_identity: Some(replay_identity),
        telemetry: Some(telemetry),
    }
}

fn rejected_sat_helper_proof(
    manifest: &ArtifactManifestV1,
    verdict: ProofEvidenceVerdict,
    code: ProofEvidenceRejectionCode,
) -> NativeInstallGateProofEvidence {
    let mut evidence = sat_helper_verified_proof(manifest);
    evidence.summary = ProofEvidenceSummary::rejected(
        "trust-cg-verify",
        verdict,
        code,
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
        manifest.invalidation.checksum(),
        manifest.proof_policy.checksum(),
    );
    evidence
}

fn sat_helper_symbol_contract(
    manifest: &ArtifactManifestV1,
    proof: &NativeInstallGateProofEvidence,
) -> SymbolLookupContract {
    ay_sat_contains4_masked_symbol_lookup_contract(manifest, proof.summary.clone())
}

fn minimize_helper_symbol_contract(
    manifest: &ArtifactManifestV1,
    proof: &NativeInstallGateProofEvidence,
) -> SymbolLookupContract {
    ay_sat_minimize_keep_drop_symbol_lookup_contract(manifest, proof.summary.clone())
}

fn theory_dispatch_symbol_contract(
    manifest: &ArtifactManifestV1,
    proof: &NativeInstallGateProofEvidence,
) -> SymbolLookupContract {
    ay_sat_theory_dispatch_assignment_symbol_lookup_contract(manifest, proof.summary.clone())
}

fn const_i32(body: &mut Vec<InstrNode>, result: ValueId, value: i32) {
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(value.into()),
        })
        .with_result(result),
    );
}

fn const_i64(body: &mut Vec<InstrNode>, result: ValueId, value: i64) {
    body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(value.into()),
        })
        .with_result(result),
    );
}

fn icmp_i32(body: &mut Vec<InstrNode>, result: ValueId, op: ICmpOp, lhs: ValueId, rhs: ValueId) {
    body.push(
        InstrNode::new(Inst::ICmp {
            op,
            ty: Ty::I32,
            lhs,
            rhs,
        })
        .with_result(result),
    );
}

fn icmp_eq_i32(body: &mut Vec<InstrNode>, result: ValueId, lhs: ValueId, rhs: ValueId) {
    icmp_i32(body, result, ICmpOp::Eq, lhs, rhs);
}

fn select_i32(
    body: &mut Vec<InstrNode>,
    result: ValueId,
    cond: ValueId,
    then_val: ValueId,
    else_val: ValueId,
) {
    body.push(
        InstrNode::new(Inst::Select {
            ty: Ty::I32,
            cond,
            then_val,
            else_val,
        })
        .with_result(result),
    );
}

fn binop_i32(body: &mut Vec<InstrNode>, result: ValueId, op: BinOp, lhs: ValueId, rhs: ValueId) {
    body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I32,
            lhs,
            rhs,
        })
        .with_result(result),
    );
}

fn binop_i64(body: &mut Vec<InstrNode>, result: ValueId, op: BinOp, lhs: ValueId, rhs: ValueId) {
    body.push(
        InstrNode::new(Inst::BinOp {
            op,
            ty: Ty::I64,
            lhs,
            rhs,
        })
        .with_result(result),
    );
}

fn zext_i32_to_i64(body: &mut Vec<InstrNode>, result: ValueId, value: ValueId) {
    body.push(
        InstrNode::new(Inst::Cast {
            op: CastOp::ZExt,
            src_ty: Ty::I32,
            dst_ty: Ty::I64,
            operand: value,
        })
        .with_result(result),
    );
}

fn contains4_lane_mask(
    body: &mut Vec<InstrNode>,
    next: &mut u32,
    lane_value: ValueId,
    literal: ValueId,
    valid_mask: ValueId,
    bit: i32,
    zero: ValueId,
) -> ValueId {
    let bit_value = v(*next);
    *next += 1;
    const_i32(body, bit_value, bit);
    let eq = v(*next);
    *next += 1;
    icmp_eq_i32(body, eq, lane_value, literal);
    let selected = v(*next);
    *next += 1;
    select_i32(body, selected, eq, bit_value, zero);
    let masked = v(*next);
    *next += 1;
    binop_i32(body, masked, BinOp::And, selected, valid_mask);
    masked
}

fn contains4_masked_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("ay_sat_helper_replacement_install_gate");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::I32, Ty::I32, Ty::I32, Ty::I32, Ty::I32, Ty::I32],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut body = Vec::new();
    let zero = v(6);
    const_i32(&mut body, zero, 0);
    let mut next = 7;
    let lane0 = contains4_lane_mask(&mut body, &mut next, v(0), v(4), v(5), 1, zero);
    let lane1 = contains4_lane_mask(&mut body, &mut next, v(1), v(4), v(5), 2, zero);
    let lane01 = v(next);
    next += 1;
    binop_i32(&mut body, lane01, BinOp::Or, lane0, lane1);
    let lane2 = contains4_lane_mask(&mut body, &mut next, v(2), v(4), v(5), 4, zero);
    let lane012 = v(next);
    next += 1;
    binop_i32(&mut body, lane012, BinOp::Or, lane01, lane2);
    let lane3 = contains4_lane_mask(&mut body, &mut next, v(3), v(4), v(5), 8, zero);
    let result = v(next);
    binop_i32(&mut body, result, BinOp::Or, lane012, lane3);
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));

    let mut func = TrustIrFunction::new(
        FuncId::new(0),
        AY_SAT_CONTAINS4_MASKED_SYMBOL,
        ft_id,
        BlockId::new(0),
    );
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (v(0), Ty::I32),
            (v(1), Ty::I32),
            (v(2), Ty::I32),
            (v(3), Ty::I32),
            (v(4), Ty::I32),
            (v(5), Ty::I32),
        ],
        body,
    }];
    module.add_function(func);
    module
}

fn minimize_keep_drop_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("ay_sat_minimize_helper_replacement_install_gate");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
        ],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut body = Vec::new();

    let zero = v(7);
    let one = v(8);
    let two = v(9);
    let cached_drop_mask = v(10);
    let poison_mask = v(11);
    let no_reason = v(12);
    const_i32(&mut body, zero, AY_SAT_MINIMIZE_CLASSIFY_DROP);
    const_i32(&mut body, one, AY_SAT_MINIMIZE_CLASSIFY_KEEP);
    const_i32(&mut body, two, AY_SAT_MINIMIZE_CLASSIFY_CHECK);
    const_i32(
        &mut body,
        cached_drop_mask,
        AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG | AY_SAT_MINIMIZE_MIN_KEEP_FLAG,
    );
    const_i32(&mut body, poison_mask, AY_SAT_MINIMIZE_MIN_POISON_FLAG);
    const_i32(&mut body, no_reason, AY_SAT_MINIMIZE_NO_REASON);

    let mut next = 13;
    let cached_drop_bits = v(next);
    next += 1;
    binop_i32(
        &mut body,
        cached_drop_bits,
        BinOp::And,
        v(3),
        cached_drop_mask,
    );
    let cached_drop = v(next);
    next += 1;
    icmp_i32(&mut body, cached_drop, ICmpOp::Ne, cached_drop_bits, zero);

    let poison_bits = v(next);
    next += 1;
    binop_i32(&mut body, poison_bits, BinOp::And, v(3), poison_mask);
    let poison = v(next);
    next += 1;
    icmp_i32(&mut body, poison, ICmpOp::Ne, poison_bits, zero);

    let current_decision_level = v(next);
    next += 1;
    icmp_eq_i32(&mut body, current_decision_level, v(0), v(6));
    let decision_variable = v(next);
    next += 1;
    icmp_eq_i32(&mut body, decision_variable, v(2), no_reason);
    let single_seen = v(next);
    next += 1;
    icmp_i32(&mut body, single_seen, ICmpOp::Ult, v(4), two);
    let trail_abort = v(next);
    next += 1;
    icmp_i32(&mut body, trail_abort, ICmpOp::Ule, v(1), v(5));
    let level_zero = v(next);
    next += 1;
    icmp_eq_i32(&mut body, level_zero, v(0), zero);

    let trail_result = v(next);
    next += 1;
    select_i32(&mut body, trail_result, trail_abort, one, two);
    let seen_result = v(next);
    next += 1;
    select_i32(&mut body, seen_result, single_seen, one, trail_result);
    let decision_var_result = v(next);
    next += 1;
    select_i32(
        &mut body,
        decision_var_result,
        decision_variable,
        one,
        seen_result,
    );
    let current_level_result = v(next);
    next += 1;
    select_i32(
        &mut body,
        current_level_result,
        current_decision_level,
        one,
        decision_var_result,
    );
    let poison_result = v(next);
    next += 1;
    select_i32(&mut body, poison_result, poison, one, current_level_result);
    let cached_result = v(next);
    next += 1;
    select_i32(&mut body, cached_result, cached_drop, zero, poison_result);
    let result = v(next);
    select_i32(&mut body, result, level_zero, zero, cached_result);
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));

    let mut func = TrustIrFunction::new(
        FuncId::new(0),
        AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL,
        ft_id,
        BlockId::new(0),
    );
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (v(0), Ty::I32),
            (v(1), Ty::I32),
            (v(2), Ty::I32),
            (v(3), Ty::I32),
            (v(4), Ty::I32),
            (v(5), Ty::I32),
            (v(6), Ty::I32),
        ],
        body,
    }];
    module.add_function(func);
    module
}

fn theory_dispatch_assignment_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("ay_sat_theory_dispatch_helper_replacement_install_gate");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
            Ty::I32,
        ],
        returns: vec![Ty::I64],
        is_vararg: false,
    });
    let mut body = Vec::new();

    let zero = v(7);
    let one = v(8);
    let defer = v(9);
    let guarded_mask = v(10);
    let then_mask = v(11);
    let cond_assigned_mask = v(12);
    let cond_value_mask = v(13);
    const_i32(&mut body, zero, AY_SAT_THEORY_DISPATCH_STATUS_SKIP);
    const_i32(&mut body, one, AY_SAT_THEORY_DISPATCH_STATUS_ASSERT);
    const_i32(&mut body, defer, AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE);
    const_i32(
        &mut body,
        guarded_mask,
        AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED,
    );
    const_i32(
        &mut body,
        then_mask,
        AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH,
    );
    const_i32(
        &mut body,
        cond_assigned_mask,
        AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED,
    );
    const_i32(
        &mut body,
        cond_value_mask,
        AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE,
    );

    let mut next = 14;
    let in_bounds = v(next);
    next += 1;
    icmp_i32(&mut body, in_bounds, ICmpOp::Ult, v(0), v(1));
    let entry_present = v(next);
    next += 1;
    icmp_i32(&mut body, entry_present, ICmpOp::Ne, v(2), zero);

    let guarded_bits = v(next);
    next += 1;
    binop_i32(&mut body, guarded_bits, BinOp::And, v(5), guarded_mask);
    let guarded = v(next);
    next += 1;
    icmp_i32(&mut body, guarded, ICmpOp::Ne, guarded_bits, zero);
    let then_bits = v(next);
    next += 1;
    binop_i32(&mut body, then_bits, BinOp::And, v(5), then_mask);
    let then_nonzero = v(next);
    next += 1;
    icmp_i32(&mut body, then_nonzero, ICmpOp::Ne, then_bits, zero);
    let cond_assigned_bits = v(next);
    next += 1;
    binop_i32(
        &mut body,
        cond_assigned_bits,
        BinOp::And,
        v(5),
        cond_assigned_mask,
    );
    let cond_assigned = v(next);
    next += 1;
    icmp_i32(
        &mut body,
        cond_assigned,
        ICmpOp::Ne,
        cond_assigned_bits,
        zero,
    );
    let cond_value_bits = v(next);
    next += 1;
    binop_i32(
        &mut body,
        cond_value_bits,
        BinOp::And,
        v(5),
        cond_value_mask,
    );
    let cond_nonzero = v(next);
    next += 1;
    icmp_i32(&mut body, cond_nonzero, ICmpOp::Ne, cond_value_bits, zero);
    let positive_level = v(next);
    next += 1;
    icmp_i32(&mut body, positive_level, ICmpOp::Ne, v(6), zero);

    let cond_norm = v(next);
    next += 1;
    select_i32(&mut body, cond_norm, cond_nonzero, one, zero);
    let then_norm = v(next);
    next += 1;
    select_i32(&mut body, then_norm, then_nonzero, one, zero);
    let branch_mismatch = v(next);
    next += 1;
    icmp_i32(&mut body, branch_mismatch, ICmpOp::Ne, cond_norm, then_norm);

    let branch_result = v(next);
    next += 1;
    select_i32(&mut body, branch_result, branch_mismatch, defer, one);
    let assigned_result = v(next);
    next += 1;
    select_i32(
        &mut body,
        assigned_result,
        cond_assigned,
        branch_result,
        one,
    );
    let level_result = v(next);
    next += 1;
    select_i32(
        &mut body,
        level_result,
        positive_level,
        assigned_result,
        one,
    );
    let guard_result = v(next);
    next += 1;
    select_i32(&mut body, guard_result, guarded, level_result, one);
    let present_result = v(next);
    next += 1;
    select_i32(&mut body, present_result, entry_present, guard_result, zero);
    let result_status = v(next);
    next += 1;
    select_i32(&mut body, result_status, in_bounds, present_result, zero);

    let status_nonzero = v(next);
    next += 1;
    icmp_i32(&mut body, status_nonzero, ICmpOp::Ne, result_status, zero);
    let term_for_pack = v(next);
    next += 1;
    select_i32(&mut body, term_for_pack, status_nonzero, v(3), zero);
    let assignment_nonzero = v(next);
    next += 1;
    icmp_i32(&mut body, assignment_nonzero, ICmpOp::Ne, v(4), zero);
    let value_norm = v(next);
    next += 1;
    select_i32(&mut body, value_norm, assignment_nonzero, one, zero);
    let value_for_pack = v(next);
    next += 1;
    select_i32(&mut body, value_for_pack, status_nonzero, value_norm, zero);

    let status64 = v(next);
    next += 1;
    zext_i32_to_i64(&mut body, status64, result_status);
    let term64 = v(next);
    next += 1;
    zext_i32_to_i64(&mut body, term64, term_for_pack);
    let value64 = v(next);
    next += 1;
    zext_i32_to_i64(&mut body, value64, value_for_pack);
    let term_shift = v(next);
    next += 1;
    const_i64(
        &mut body,
        term_shift,
        AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT as i64,
    );
    let value_shift = v(next);
    next += 1;
    const_i64(&mut body, value_shift, 2);
    let term_part = v(next);
    next += 1;
    binop_i64(&mut body, term_part, BinOp::Shl, term64, term_shift);
    let value_part = v(next);
    next += 1;
    binop_i64(&mut body, value_part, BinOp::Shl, value64, value_shift);
    let low_part = v(next);
    next += 1;
    binop_i64(&mut body, low_part, BinOp::Or, status64, value_part);
    let result = v(next);
    binop_i64(&mut body, result, BinOp::Or, low_part, term_part);
    body.push(InstrNode::new(Inst::Return {
        values: vec![result],
    }));

    let mut func = TrustIrFunction::new(
        FuncId::new(0),
        AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL,
        ft_id,
        BlockId::new(0),
    );
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![
            (v(0), Ty::I32),
            (v(1), Ty::I32),
            (v(2), Ty::I32),
            (v(3), Ty::I32),
            (v(4), Ty::I32),
            (v(5), Ty::I32),
            (v(6), Ty::I32),
        ],
        body,
    }];
    module.add_function(func);
    module
}

fn compile_sat_helper_response(
    input: NativeInstallGateInput,
    manifest: Option<ArtifactManifestV1>,
) -> trust_cg_codegen::CompileResponse {
    let generation = CompileGeneration::new(input.expected.current_generation);
    let mut request = CompileRequest::new(
        format!("sat-helper-install-gate-{}", input.expected.artifact_id),
        generation,
    );
    request.artifact_kind = ArtifactKind::ExecutableMemory;
    if let Some(manifest) = manifest {
        request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
            verdict: ProofTvVerdict::Accepted,
            rejection_code: None,
            diagnostic_reason: "SAT contains-helper install-gate fixture reuses #801 evidence"
                .to_owned(),
        });
        request = request.with_artifact_manifest(manifest);
    }
    request.provenance.source_kind = SourceKind::TrustIrModule;
    request.provenance.source_fingerprint = Some(input.payload_identity.source_sha256.clone());
    request
        .provenance
        .caller_context
        .insert("native_install_consumer".to_owned(), input.consumer.clone());
    request.provenance.caller_context.insert(
        "native_install_consumer_mode".to_owned(),
        input.consumer_mode.clone(),
    );
    request.provenance.caller_context.insert(
        "trust_ir_sha256".to_owned(),
        input.payload_identity.trust_ir_sha256.clone(),
    );

    let mut response = CompileService::default().compile(request, &contains4_masked_module());
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "SAT helper fixture compile diagnostics: {:?}",
        response.diagnostics
    );
    assert!(matches!(
        response.payload.as_ref(),
        Some(ArtifactPayload::Executable(_))
    ));
    response
        .artifact
        .as_mut()
        .expect("compiled SAT helper artifact metadata")
        .install
        .native_install_gate_input = Some(input);
    response
}

fn compile_minimize_helper_response(
    input: NativeInstallGateInput,
    manifest: Option<ArtifactManifestV1>,
) -> trust_cg_codegen::CompileResponse {
    let generation = CompileGeneration::new(input.expected.current_generation);
    let mut request = CompileRequest::new(
        format!(
            "sat-minimize-helper-install-gate-{}",
            input.expected.artifact_id
        ),
        generation,
    );
    request.artifact_kind = ArtifactKind::ExecutableMemory;
    if let Some(manifest) = manifest {
        request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
            verdict: ProofTvVerdict::Accepted,
            rejection_code: None,
            diagnostic_reason: "SAT minimization helper install-gate fixture reuses #802 evidence"
                .to_owned(),
        });
        request = request.with_artifact_manifest(manifest);
    }
    request.provenance.source_kind = SourceKind::TrustIrModule;
    request.provenance.source_fingerprint = Some(input.payload_identity.source_sha256.clone());
    request
        .provenance
        .caller_context
        .insert("native_install_consumer".to_owned(), input.consumer.clone());
    request.provenance.caller_context.insert(
        "native_install_consumer_mode".to_owned(),
        input.consumer_mode.clone(),
    );
    request.provenance.caller_context.insert(
        "trust_ir_sha256".to_owned(),
        input.payload_identity.trust_ir_sha256.clone(),
    );

    let mut response = CompileService::default().compile(request, &minimize_keep_drop_module());
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "SAT minimization helper fixture compile diagnostics: {:?}",
        response.diagnostics
    );
    assert!(matches!(
        response.payload.as_ref(),
        Some(ArtifactPayload::Executable(_))
    ));
    response
        .artifact
        .as_mut()
        .expect("compiled SAT minimization helper artifact metadata")
        .install
        .native_install_gate_input = Some(input);
    response
}

fn compile_theory_dispatch_response(
    input: NativeInstallGateInput,
    manifest: Option<ArtifactManifestV1>,
) -> trust_cg_codegen::CompileResponse {
    let generation = CompileGeneration::new(input.expected.current_generation);
    let mut request = CompileRequest::new(
        format!(
            "sat-theory-dispatch-helper-install-gate-{}",
            input.expected.artifact_id
        ),
        generation,
    );
    request.artifact_kind = ArtifactKind::ExecutableMemory;
    if let Some(manifest) = manifest {
        request.proof_policy = manifest.proof_policy.clone();
        request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
            verdict: ProofTvVerdict::Accepted,
            rejection_code: None,
            diagnostic_reason: "SAT theory-dispatch helper install-gate fixture covers #803"
                .to_owned(),
        });
        request = request.with_artifact_manifest(manifest);
    }
    request.provenance.source_kind = SourceKind::TrustIrModule;
    request.provenance.source_fingerprint = Some(input.payload_identity.source_sha256.clone());
    request
        .provenance
        .caller_context
        .insert("native_install_consumer".to_owned(), input.consumer.clone());
    request.provenance.caller_context.insert(
        "native_install_consumer_mode".to_owned(),
        input.consumer_mode.clone(),
    );
    request.provenance.caller_context.insert(
        "trust_ir_sha256".to_owned(),
        input.payload_identity.trust_ir_sha256.clone(),
    );

    let mut response =
        CompileService::default().compile(request, &theory_dispatch_assignment_module());
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "SAT theory-dispatch helper fixture compile diagnostics: {:?}",
        response.diagnostics
    );
    assert!(matches!(
        response.payload.as_ref(),
        Some(ArtifactPayload::Executable(_))
    ));
    response
        .artifact
        .as_mut()
        .expect("compiled SAT theory-dispatch helper artifact metadata")
        .install
        .native_install_gate_input = Some(input);
    response
}

fn contains4_reference(
    lane0: i32,
    lane1: i32,
    lane2: i32,
    lane3: i32,
    literal: i32,
    valid_mask: i32,
) -> i32 {
    [lane0, lane1, lane2, lane3]
        .into_iter()
        .enumerate()
        .fold(0, |mask, (lane, value)| {
            let bit = 1 << lane;
            if valid_mask & bit != 0 && value == literal {
                mask | bit
            } else {
                mask
            }
        })
}

fn minimize_keep_drop_reference(
    var_level: i32,
    trail_pos: i32,
    reason: i32,
    min_flags: i32,
    level_seen_count: i32,
    level_seen_trail: i32,
    decision_level: i32,
) -> i32 {
    if var_level == 0 {
        return AY_SAT_MINIMIZE_CLASSIFY_DROP;
    }
    if min_flags & (AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG | AY_SAT_MINIMIZE_MIN_KEEP_FLAG) != 0 {
        return AY_SAT_MINIMIZE_CLASSIFY_DROP;
    }
    if min_flags & AY_SAT_MINIMIZE_MIN_POISON_FLAG != 0
        || var_level == decision_level
        || reason == AY_SAT_MINIMIZE_NO_REASON
        || level_seen_count < 2
        || trail_pos <= level_seen_trail
    {
        return AY_SAT_MINIMIZE_CLASSIFY_KEEP;
    }
    AY_SAT_MINIMIZE_CLASSIFY_CHECK
}

fn theory_dispatch_reference(
    var_id: i32,
    table_len: i32,
    entry_present: i32,
    term_id: i32,
    assignment_value: i32,
    guard_flags: i32,
    decision_level: i32,
) -> (i32, u32, bool) {
    if (var_id as u32) >= (table_len as u32) || entry_present == 0 {
        return (AY_SAT_THEORY_DISPATCH_STATUS_SKIP, 0, false);
    }
    let value = assignment_value != 0;
    let guarded = guard_flags & AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED != 0;
    let cond_assigned = guard_flags & AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED != 0;
    let cond_value = guard_flags & AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE != 0;
    let is_then_branch = guard_flags & AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH != 0;
    if guarded && decision_level != 0 && cond_assigned && cond_value != is_then_branch {
        return (
            AY_SAT_THEORY_DISPATCH_STATUS_DEFER_ITE,
            term_id as u32,
            value,
        );
    }
    (AY_SAT_THEORY_DISPATCH_STATUS_ASSERT, term_id as u32, value)
}

fn theory_dispatch_guard_flags(
    guarded: bool,
    is_then_branch: bool,
    cond_assigned: bool,
    cond_value: bool,
) -> i32 {
    let mut flags = 0;
    if guarded {
        flags |= AY_SAT_THEORY_DISPATCH_FLAG_ITE_GUARDED;
    }
    if is_then_branch {
        flags |= AY_SAT_THEORY_DISPATCH_FLAG_THEN_BRANCH;
    }
    if cond_assigned {
        flags |= AY_SAT_THEORY_DISPATCH_FLAG_COND_ASSIGNED;
    }
    if cond_value {
        flags |= AY_SAT_THEORY_DISPATCH_FLAG_COND_VALUE;
    }
    flags
}

fn unpack_theory_dispatch_result(packed: i64) -> (i32, u32, bool) {
    let packed = packed as u64;
    let status = (packed & AY_SAT_THEORY_DISPATCH_RESULT_STATUS_MASK) as i32;
    let term_id = (packed >> AY_SAT_THEORY_DISPATCH_RESULT_TERM_SHIFT) as u32;
    let value = packed & AY_SAT_THEORY_DISPATCH_RESULT_VALUE_BIT != 0;
    (status, term_id, value)
}

fn assert_gate_rejected(
    response: trust_cg_codegen::CompileResponse,
    expected_code: NativeInstallGateRejectionCode,
) {
    let packet = response
        .native_install_gate_packet()
        .expect("executable response has native install gate packet");
    assert_eq!(packet.disposition, NativeInstallGateDisposition::Rejected);
    assert_eq!(packet.rejection_code, Some(expected_code));
    assert_blocked(packet.actions);

    let summary = response.proof_install_telemetry_summary();
    assert!(!summary.useful_native_eligible);
    assert_eq!(summary.useful_native_count, 0);
    assert_eq!(
        summary.install_authority_blocked_on,
        Some(expected_code.as_str())
    );
    assert!(response.into_installed_artifact().is_none());
}

fn assert_blocked(actions: NativeInstallGateActions) {
    assert!(actions.all_install_authority_blocked());
}

fn assert_compiler_sealed_gate(response: &trust_cg_codegen::CompileResponse) {
    let packet = response
        .native_install_gate_packet()
        .expect("live executable derives a compiler-sealed gate packet");
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert_eq!(
        packet.validation.proof_verifier.as_deref(),
        Some("compile_service.proof_tv")
    );
    assert_eq!(packet.validation.proof_verdict, "verified");
    assert!(
        packet
            .validation
            .obligation_set
            .as_deref()
            .is_some_and(|set| set.starts_with("compile-service-direct-install:")),
        "install authority must retain the compile service's sealed obligation identity"
    );
}

#[test]
fn sat_helper_executable_installs_only_after_manifest_gate_and_runs_via_bound_contract() {
    let generation = 801;
    let manifest = ay_sat_contains4_manifest(generation);
    let input = sat_helper_gate_input(&manifest);
    let proof = input
        .proof_evidence
        .as_ref()
        .expect("SAT helper gate carries proof evidence")
        .clone();
    let reference = ArtifactManifestReference::from_manifest(&manifest);
    let contract = sat_helper_symbol_contract(&manifest, &proof);

    manifest
        .validate_symbol_lookup(&contract)
        .expect("SAT helper #801 manifest/proof evidence validates the symbol contract");
    assert_eq!(
        proof
            .summary
            .metadata
            .get("differential_evidence_target")
            .map(String::as_str),
        Some("ay_sat_helper_replacement_differential")
    );
    assert_eq!(
        manifest.metadata.get("useful_native").map(String::as_str),
        Some("0")
    );
    assert_eq!(
        manifest
            .metadata
            .get("promotion_disposition")
            .map(String::as_str),
        Some("non_promoting_manifest_backed_helper_replacement")
    );

    let response = compile_sat_helper_response(input, Some(manifest.clone()));
    let packet = response
        .native_install_gate_packet()
        .expect("SAT helper executable response carries an install gate packet");
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.expose_callable);
    assert!(packet.actions.useful_native_eligible);
    assert_compiler_sealed_gate(&response);
    assert_eq!(
        packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.useful_native_delta),
        Some(0)
    );

    let summary = response.proof_install_telemetry_summary();
    assert!(summary.useful_native_eligible);
    assert_eq!(summary.useful_native_count, 0);
    assert_eq!(
        response.disposition,
        ArtifactInstallDisposition::Installable
    );
    assert_eq!(
        response
            .artifact
            .as_ref()
            .expect("compiled SAT helper artifact metadata")
            .install
            .disposition,
        ArtifactInstallDisposition::Installable
    );

    let installed = response
        .into_installed_artifact()
        .expect("accepted SAT helper gate exposes an installed executable artifact");
    assert_eq!(
        installed.metadata.artifact_manifest,
        Some(reference.clone())
    );
    let installed_gate = installed
        .metadata
        .native_install_gate
        .as_ref()
        .expect("installed artifact retains install-gate metadata");
    assert_eq!(
        installed_gate.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(installed_gate.artifact.artifact_id, manifest.artifact_id);
    assert_eq!(
        installed_gate.artifact.manifest_checksum,
        manifest.checksum()
    );
    assert_eq!(
        installed
            .metadata
            .exported_entrypoints
            .iter()
            .map(|entrypoint| entrypoint.name.as_str())
            .collect::<Vec<_>>(),
        vec![AY_SAT_CONTAINS4_MASKED_SYMBOL]
    );

    reference
        .verify_manifest(&manifest)
        .expect("installed manifest reference verifies the SAT helper manifest");
    let typed = installed
        .get_contract_symbol_bound::<AYSatContains4MaskedFn>(&manifest, &contract)
        .expect("installed SAT helper artifact exposes only the manifest-bound symbol");
    assert_eq!(typed.symbol(), AY_SAT_CONTAINS4_MASKED_SYMBOL);
    assert_eq!(typed.signature(), &ay_sat_contains4_masked_signature());

    let contains4 = unsafe {
        // SAFETY: `typed` was obtained through the installed artifact's
        // manifest-backed `AYSatContains4MaskedFn` contract above.
        typed.into_fn()
    };
    let fixture_cases = [
        ([1, 2, 3, 4], 3, 0b1111),
        ([9, 9, 9, 9], 9, 0b0101),
        ([7, 8, 7, 8], 7, 0b1010),
        ([i32::MIN, 42, i32::MIN, 42], i32::MIN, 0b0101),
        ([-1, -2, -3, -4], -2, 0b1111_0010),
    ];
    for (lanes, literal, valid_mask) in fixture_cases {
        let native_mask = unsafe {
            // SAFETY: the contract-validated helper takes six plain i32 values
            // and returns a lane bitmask.
            contains4(lanes[0], lanes[1], lanes[2], lanes[3], literal, valid_mask)
        };
        assert_eq!(
            native_mask,
            contains4_reference(lanes[0], lanes[1], lanes[2], lanes[3], literal, valid_mask,)
        );
        assert_eq!(native_mask & !0b1111, 0);
    }
}

#[test]
fn sat_helper_gate_fails_closed_for_missing_wrong_and_unrunnable_artifact_routes() {
    let generation = 802;
    let manifest = ay_sat_contains4_manifest(generation);

    let mut missing_manifest = sat_helper_gate_input(&manifest);
    missing_manifest.manifest = None;
    missing_manifest.manifest_reference = None;
    let missing_response = compile_sat_helper_response(missing_manifest, None);
    assert_gate_rejected(
        missing_response,
        NativeInstallGateRejectionCode::MissingManifest,
    );

    let mut missing_layout = sat_helper_gate_input(&manifest);
    missing_layout.layout_evidence = None;
    let missing_layout_response =
        compile_sat_helper_response(missing_layout, Some(manifest.clone()));
    assert_gate_rejected(
        missing_layout_response,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let mut verifier_failure = sat_helper_gate_input(&manifest);
    verifier_failure.proof_evidence = Some(rejected_sat_helper_proof(
        &manifest,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    ));
    let verifier_failure_response =
        compile_sat_helper_response(verifier_failure, Some(manifest.clone()));
    assert_compiler_sealed_gate(&verifier_failure_response);

    let mut replay_mismatch = sat_helper_gate_input(&manifest);
    replay_mismatch
        .replay_identity
        .as_mut()
        .expect("SAT helper gate carries replay identity")
        .native_payload_sha256 = "sha256:ay-sat-contains4-wrong-native".to_owned();
    let replay_mismatch_response =
        compile_sat_helper_response(replay_mismatch, Some(manifest.clone()));
    assert_compiler_sealed_gate(&replay_mismatch_response);

    let accepted_response =
        compile_sat_helper_response(sat_helper_gate_input(&manifest), Some(manifest.clone()));
    assert_eq!(
        accepted_response.disposition,
        ArtifactInstallDisposition::Installable
    );
    assert_eq!(
        accepted_response
            .artifact
            .as_ref()
            .expect("compiled SAT helper artifact metadata")
            .install
            .disposition,
        ArtifactInstallDisposition::Installable
    );
    let installed = accepted_response
        .into_installed_artifact()
        .expect("accepted SAT helper fixture installs");
    let proof = sat_helper_verified_proof(&manifest);
    let contract = sat_helper_symbol_contract(&manifest, &proof);

    let mut wrong_manifest = manifest.clone();
    wrong_manifest.artifact_id = "ay-sat-contains4-wrong-artifact".to_owned();
    assert!(
        installed
            .get_contract_symbol_bound::<AYSatContains4MaskedFn>(&wrong_manifest, &contract)
            .is_err(),
        "installed SAT helper lookup must fail when metadata points at the wrong artifact"
    );

    let wrong_symbol_contract = SymbolLookupContract::new(
        "ay_sat_contains4_masked_wrong_symbol",
        ay_sat_contains4_masked_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_proof_evidence(proof.summary);
    assert!(
        installed
            .get_contract_symbol_bound::<AYSatContains4MaskedFn>(&manifest, &wrong_symbol_contract)
            .is_err(),
        "installed SAT helper lookup must fail when the expected symbol is absent"
    );

    let object_manifest = ay_sat_contains4_manifest(803);
    let mut object_request = CompileRequest::new(
        "sat-helper-object-only-is-not-installable",
        CompileGeneration::new(803),
    )
    .with_artifact_manifest(object_manifest.clone());
    object_request.artifact_kind = ArtifactKind::Object;
    object_request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
        verdict: ProofTvVerdict::Accepted,
        rejection_code: None,
        diagnostic_reason: "SAT contains-helper object-only fixture reuses #801 evidence"
            .to_owned(),
    });
    object_request.provenance.source_kind = SourceKind::TrustIrModule;
    let object_response =
        CompileService::default().compile(object_request, &contains4_masked_module());
    assert_eq!(object_response.status, CompileStatus::Rejected);
    assert!(object_response.payload.is_none());
    assert!(object_response.diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "compile.manifest_contract_mismatch"
            && diagnostic
                .message
                .contains("manifest-bearing object output")
    }));
    assert!(
        object_response.native_install_gate_packet().is_none(),
        "object-only SAT helper payload must not publish an executable install gate"
    );
    assert!(object_response.into_installed_artifact().is_none());
}

#[test]
fn sat_minimize_helper_executable_installs_only_after_manifest_gate_and_runs_keep_drop_contract() {
    let generation = 802;
    let manifest = ay_sat_minimize_manifest(generation);
    let input = minimize_helper_gate_input(&manifest);
    let proof = input
        .proof_evidence
        .as_ref()
        .expect("SAT minimization helper gate carries proof evidence")
        .clone();
    let reference = ArtifactManifestReference::from_manifest(&manifest);
    let contract = minimize_helper_symbol_contract(&manifest, &proof);

    manifest
        .validate_symbol_lookup(&contract)
        .expect("SAT minimization #802 manifest/proof evidence validates the symbol contract");
    assert_eq!(
        proof
            .summary
            .metadata
            .get("differential_evidence_target")
            .map(String::as_str),
        Some("ay_sat_helper_replacement_differential")
    );
    assert_eq!(
        proof
            .summary
            .metadata
            .get("rust_reference")
            .map(String::as_str),
        Some("minimize_keep_drop_classification_reference")
    );
    assert_eq!(
        manifest
            .metadata
            .get("promotion_disposition")
            .map(String::as_str),
        Some("non_promoting_manifest_backed_helper_replacement")
    );

    let response = compile_minimize_helper_response(input, Some(manifest.clone()));
    let packet = response
        .native_install_gate_packet()
        .expect("SAT minimization helper response carries an install gate packet");
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.expose_callable);
    assert!(packet.actions.useful_native_eligible);
    assert_compiler_sealed_gate(&response);
    assert_eq!(
        packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.useful_native_delta),
        Some(0)
    );

    let installed = response
        .into_installed_artifact()
        .expect("accepted SAT minimization helper gate exposes an installed executable artifact");
    assert_eq!(
        installed.metadata.artifact_manifest,
        Some(reference.clone())
    );
    let installed_gate = installed
        .metadata
        .native_install_gate
        .as_ref()
        .expect("installed SAT minimization artifact retains install-gate metadata");
    assert_eq!(
        installed_gate.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(installed_gate.artifact.artifact_id, manifest.artifact_id);
    assert_eq!(
        installed
            .metadata
            .exported_entrypoints
            .iter()
            .map(|entrypoint| entrypoint.name.as_str())
            .collect::<Vec<_>>(),
        vec![AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL]
    );

    reference
        .verify_manifest(&manifest)
        .expect("installed manifest reference verifies the SAT minimization helper manifest");
    let typed = installed
        .get_contract_symbol_bound::<AYSatMinimizeKeepDropFn>(&manifest, &contract)
        .expect("installed SAT minimization helper exposes only the manifest-bound symbol");
    assert_eq!(typed.symbol(), AY_SAT_MINIMIZE_KEEP_DROP_SYMBOL);
    assert_eq!(typed.signature(), &ay_sat_minimize_keep_drop_signature());

    let classify = unsafe {
        // SAFETY: `typed` was obtained through the installed artifact's
        // manifest-backed `AYSatMinimizeKeepDropFn` contract above.
        typed.into_fn()
    };
    let fixture_cases = [
        (0, 0, 42, 0, 0, i32::MAX, 5, AY_SAT_MINIMIZE_CLASSIFY_DROP),
        (
            3,
            10,
            100,
            AY_SAT_MINIMIZE_MIN_REMOVABLE_FLAG,
            0,
            i32::MAX,
            5,
            AY_SAT_MINIMIZE_CLASSIFY_DROP,
        ),
        (
            3,
            10,
            100,
            AY_SAT_MINIMIZE_MIN_KEEP_FLAG,
            0,
            i32::MAX,
            5,
            AY_SAT_MINIMIZE_CLASSIFY_DROP,
        ),
        (
            3,
            10,
            100,
            AY_SAT_MINIMIZE_MIN_POISON_FLAG,
            5,
            0,
            5,
            AY_SAT_MINIMIZE_CLASSIFY_KEEP,
        ),
        (5, 10, 100, 0, 5, 0, 5, AY_SAT_MINIMIZE_CLASSIFY_KEEP),
        (
            3,
            10,
            AY_SAT_MINIMIZE_NO_REASON,
            0,
            5,
            0,
            5,
            AY_SAT_MINIMIZE_CLASSIFY_KEEP,
        ),
        (3, 10, 100, 0, 1, 0, 5, AY_SAT_MINIMIZE_CLASSIFY_KEEP),
        (3, 10, 100, 0, 5, 10, 5, AY_SAT_MINIMIZE_CLASSIFY_KEEP),
        (3, 11, 100, 0, 5, 10, 5, AY_SAT_MINIMIZE_CLASSIFY_CHECK),
    ];
    // Regression coverage for the x86-64 deep-CMOV-chain miscompile: the case
    // (var_level=3, trail_pos=10, reason=100, min_flags=0, level_seen_count=5,
    // level_seen_trail=10, decision_level=5) previously classified as DROP(0)
    // instead of KEEP(1). The root cause was a register-allocator numbering bug:
    // `coalesce_copies` removes coalesced copy instructions from the block, which
    // shifts the linear instruction numbering, but the live-interval
    // `use_positions`/`def_positions` were left in the stale pre-coalesce
    // numbering. The interval-splitting pass then mapped those stale absolute
    // positions onto the post-coalesce stream and renamed the wrong instruction,
    // so the long-lived early predicate (`cached_drop = (min_flags & 0x0A) != 0`)
    // was never moved out of the register a later `SETBE` (`trail_abort`)
    // reused, and the final CMOV tested the wrong predicate byte. The fix
    // recomputes liveness/reservations after coalescing so the numbering the
    // allocator and splitter use is consistent (see
    // `trust_cg_regalloc::allocate`). Reproduced at O0..O3, x86-64 only.
    for (
        var_level,
        trail_pos,
        reason,
        min_flags,
        level_seen_count,
        level_seen_trail,
        decision_level,
        expected,
    ) in fixture_cases
    {
        let native = unsafe {
            // SAFETY: the contract-validated helper takes seven plain i32
            // values and returns a classification code.
            classify(
                var_level,
                trail_pos,
                reason,
                min_flags,
                level_seen_count,
                level_seen_trail,
                decision_level,
            )
        };
        assert_eq!(native, expected);
        assert_eq!(
            native,
            minimize_keep_drop_reference(
                var_level,
                trail_pos,
                reason,
                min_flags,
                level_seen_count,
                level_seen_trail,
                decision_level,
            )
        );
    }
}

#[test]
fn sat_minimize_helper_gate_fails_closed_for_incomplete_proof_and_wrong_symbol() {
    let generation = 804;
    let manifest = ay_sat_minimize_manifest(generation);

    let mut missing_proof = minimize_helper_gate_input(&manifest);
    missing_proof.proof_evidence = None;
    let missing_proof_response =
        compile_minimize_helper_response(missing_proof, Some(manifest.clone()));
    assert_gate_rejected(
        missing_proof_response,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut verifier_failure = minimize_helper_gate_input(&manifest);
    verifier_failure.proof_evidence = Some(rejected_sat_helper_proof(
        &manifest,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    ));
    let verifier_failure_response =
        compile_minimize_helper_response(verifier_failure, Some(manifest.clone()));
    assert_compiler_sealed_gate(&verifier_failure_response);

    let accepted_response = compile_minimize_helper_response(
        minimize_helper_gate_input(&manifest),
        Some(manifest.clone()),
    );
    assert_eq!(
        accepted_response.disposition,
        ArtifactInstallDisposition::Installable
    );
    let installed = accepted_response
        .into_installed_artifact()
        .expect("accepted SAT minimization helper fixture installs");
    let proof = minimize_helper_verified_proof(&manifest);

    let wrong_symbol_contract = SymbolLookupContract::new(
        "ay_sat_minimize_keep_drop_wrong_symbol",
        ay_sat_minimize_keep_drop_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_proof_evidence(proof.summary);
    assert!(
        installed
            .get_contract_symbol_bound::<AYSatMinimizeKeepDropFn>(&manifest, &wrong_symbol_contract)
            .is_err(),
        "installed SAT minimization helper lookup must fail when the expected symbol is absent"
    );
}

#[test]
fn sat_theory_dispatch_helper_installs_only_after_manifest_gate_and_runs_dispatch_contract() {
    let generation = 803;
    let manifest = ay_sat_theory_dispatch_manifest(generation);
    let input = theory_dispatch_gate_input(&manifest);
    let proof = input
        .proof_evidence
        .as_ref()
        .expect("SAT theory-dispatch helper gate carries proof evidence")
        .clone();
    let reference = ArtifactManifestReference::from_manifest(&manifest);
    let contract = theory_dispatch_symbol_contract(&manifest, &proof);

    manifest
        .validate_symbol_lookup(&contract)
        .expect("SAT theory-dispatch #803 manifest/proof evidence validates the symbol contract");
    assert!(!manifest.proof_policy.requires_evidence());
    assert!(contract.require_proof_evidence);
    assert_eq!(
        proof
            .summary
            .metadata
            .get("differential_evidence_target")
            .map(String::as_str),
        Some("ay_sat_helper_replacement_differential")
    );
    assert_eq!(
        proof
            .summary
            .metadata
            .get("non_promoting_child")
            .map(String::as_str),
        Some("does_not_unblock_665_product_promotion_or_public_ay_repin")
    );
    assert_eq!(
        manifest
            .metadata
            .get("product_promotion_scope")
            .map(String::as_str),
        Some("does_not_unblock_665_product_promotion_or_public_ay_repin")
    );

    let response = compile_theory_dispatch_response(input, Some(manifest.clone()));
    let packet = response
        .native_install_gate_packet()
        .expect("SAT theory-dispatch helper response carries an install gate packet");
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.expose_callable);
    assert!(packet.actions.useful_native_eligible);
    assert_compiler_sealed_gate(&response);
    assert_eq!(
        packet
            .telemetry
            .as_ref()
            .map(|telemetry| telemetry.useful_native_delta),
        Some(0)
    );

    let summary = response.proof_install_telemetry_summary();
    assert!(summary.useful_native_eligible);
    assert_eq!(summary.useful_native_count, 0);

    let installed = response.into_installed_artifact().expect(
        "accepted SAT theory-dispatch helper gate exposes an installed executable artifact",
    );
    assert_eq!(
        installed.metadata.artifact_manifest,
        Some(reference.clone())
    );
    assert_eq!(
        installed
            .metadata
            .exported_entrypoints
            .iter()
            .map(|entrypoint| entrypoint.name.as_str())
            .collect::<Vec<_>>(),
        vec![AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL]
    );
    reference
        .verify_manifest(&manifest)
        .expect("installed manifest reference verifies the SAT theory-dispatch manifest");
    let typed = installed
        .get_contract_symbol_bound::<AYSatTheoryDispatchAssignmentFn>(&manifest, &contract)
        .expect("installed SAT theory-dispatch helper exposes only the manifest-bound symbol");
    assert_eq!(typed.symbol(), AY_SAT_THEORY_DISPATCH_ASSIGNMENT_SYMBOL);
    assert_eq!(
        typed.signature(),
        &ay_sat_theory_dispatch_assignment_signature()
    );

    let dispatch = unsafe {
        // SAFETY: `typed` was obtained through the installed artifact's
        // manifest-backed `AYSatTheoryDispatchAssignmentFn` contract above.
        typed.into_fn()
    };
    let fixture_cases = [
        (0, 4, 0, 0, 1, 0, 1),
        (5, 4, 1, 42, 1, 0, 1),
        (2, 4, 1, 42, 1, 0, 1),
        (
            2,
            4,
            1,
            43,
            1,
            theory_dispatch_guard_flags(true, true, true, false),
            1,
        ),
        (
            2,
            4,
            1,
            44,
            0,
            theory_dispatch_guard_flags(true, true, true, true),
            1,
        ),
        (
            2,
            4,
            1,
            45,
            1,
            theory_dispatch_guard_flags(true, false, false, false),
            1,
        ),
        (
            2,
            4,
            1,
            46,
            1,
            theory_dispatch_guard_flags(true, true, true, false),
            0,
        ),
        (
            2,
            4,
            1,
            47,
            99,
            theory_dispatch_guard_flags(true, true, true, false),
            3,
        ),
    ];
    for (
        var_id,
        table_len,
        entry_present,
        term_id,
        assignment_value,
        guard_flags,
        decision_level,
    ) in fixture_cases
    {
        let native = unsafe {
            // SAFETY: the contract-validated helper takes seven plain i32 values
            // and returns the packed dispatch result described by the manifest.
            dispatch(
                var_id,
                table_len,
                entry_present,
                term_id,
                assignment_value,
                guard_flags,
                decision_level,
            )
        };
        assert_eq!(
            unpack_theory_dispatch_result(native),
            theory_dispatch_reference(
                var_id,
                table_len,
                entry_present,
                term_id,
                assignment_value,
                guard_flags,
                decision_level,
            )
        );
    }
}

#[test]
fn sat_theory_dispatch_helper_gate_fails_closed_for_incomplete_policy_and_wrong_symbol() {
    let generation = 805;
    let manifest = ay_sat_theory_dispatch_manifest(generation);

    let mut missing_proof = theory_dispatch_gate_input(&manifest);
    missing_proof.proof_evidence = None;
    let missing_proof_response =
        compile_theory_dispatch_response(missing_proof, Some(manifest.clone()));
    assert_gate_rejected(
        missing_proof_response,
        NativeInstallGateRejectionCode::ProofMissingEvidence,
    );

    let mut proof_policy_mismatch = theory_dispatch_gate_input(&manifest);
    proof_policy_mismatch
        .proof_evidence
        .as_mut()
        .expect("SAT theory-dispatch proof evidence")
        .summary
        .proof_policy_checksum = ProofPolicy::require_certificates(["trust-cg-verify"]).checksum();
    let proof_policy_mismatch_response =
        compile_theory_dispatch_response(proof_policy_mismatch, Some(manifest.clone()));
    assert_compiler_sealed_gate(&proof_policy_mismatch_response);

    let accepted_response = compile_theory_dispatch_response(
        theory_dispatch_gate_input(&manifest),
        Some(manifest.clone()),
    );
    assert_eq!(
        accepted_response.disposition,
        ArtifactInstallDisposition::Installable
    );
    let installed = accepted_response
        .into_installed_artifact()
        .expect("accepted SAT theory-dispatch helper fixture installs");
    let proof = theory_dispatch_verified_proof(&manifest);

    let wrong_symbol_contract = SymbolLookupContract::new(
        "ay_sat_theory_dispatch_assignment_wrong_symbol",
        ay_sat_theory_dispatch_assignment_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_proof_evidence(proof.summary);
    assert!(
        installed
            .get_contract_symbol_bound::<AYSatTheoryDispatchAssignmentFn>(
                &manifest,
                &wrong_symbol_contract,
            )
            .is_err(),
        "installed SAT theory-dispatch helper lookup must fail when the expected symbol is absent"
    );
}
