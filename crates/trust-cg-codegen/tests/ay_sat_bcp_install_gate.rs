// trust-cg-codegen/tests/ay_sat_bcp_install_gate.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#![cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]

use std::sync::OnceLock;

use trust_cg_codegen::ay_sat_bcp_contract::{
    AY_SAT_BCP_SYMBOL, ay_sat_watch_bcp_manifest_for_parts, ay_sat_watch_bcp_proof_policy,
    ay_sat_watch_bcp_signature, ay_sat_watch_bcp_symbol_lookup_contract,
    ay_sat_watch_bcp_verified_proof_evidence,
};
use trust_cg_codegen::compile_service::{
    ArtifactManifestReference, ProofTvEvidenceOutcome, ProofTvVerdict,
};
use trust_cg_codegen::jit_contract::{
    AbiDescriptor, ArtifactManifestV1, Endianness, LayoutManifest, ProofEvidenceRejectionCode,
    ProofEvidenceSummary, ProofEvidenceVerdict, SymbolLookupContract, TargetDescriptor,
    TargetOperatingSystem,
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
    Block as TrustIrBlock, BlockId, Constant, FuncId, FuncTy, Function as TrustIrFunction, Inst,
    InstrNode, Module as TrustIrModule, Ty, ValueId,
};

const BCP_OK_STATUS: i32 = 0;

#[repr(C)]
struct PropagationContext {
    _opaque: [u8; 0],
}

type AYSatWatchBcpFn = unsafe extern "C" fn(*mut PropagationContext) -> i32;

fn ay_sat_target() -> TargetDescriptor {
    TargetDescriptor::for_trust_cg_target_spec(
        trust_cg_codegen::target::TargetSpec::default_for_architecture(Target::host()),
    )
}

fn ay_sat_abi() -> AbiDescriptor {
    AbiDescriptor::for_trust_cg_target_os(Target::host(), TargetOperatingSystem::host())
}

fn ay_sat_watch_bcp_manifest(generation: u64) -> ArtifactManifestV1 {
    let (text_size_bytes, native_payload_sha256) = observed_bcp_payload_contract();
    // Compile preflight accepts only target-core layout facts it can derive
    // independently. Product pointee/record claims live in the separately
    // validated native-install layout evidence below.
    let layout = LayoutManifest::lp64(Endianness::Little, Target::host().stack_alignment() as u16);
    let mut manifest = ay_sat_watch_bcp_manifest_for_parts(
        ay_sat_target(),
        ay_sat_abi(),
        layout,
        ay_sat_watch_bcp_proof_policy(),
        generation,
        text_size_bytes,
    );
    manifest
        .metadata
        .insert("native_payload_sha256".to_owned(), native_payload_sha256);
    manifest
        .metadata
        .insert("differential_evidence_issue".to_owned(), "678".to_owned());
    manifest.metadata.insert(
        "differential_evidence_target".to_owned(),
        "ay_sat_bcp_differential".to_owned(),
    );
    manifest.metadata.insert(
        "rust_reference".to_owned(),
        "dense_reference_bcp".to_owned(),
    );
    manifest
        .metadata
        .insert("watch_impl".to_owned(), "watch_list_bcp".to_owned());
    manifest
        .metadata
        .insert("useful_native".to_owned(), "0".to_owned());
    manifest
}

fn sat_bcp_payload_identity() -> NativeInstallGatePayloadIdentity {
    NativeInstallGatePayloadIdentity {
        source_sha256: "sha256:ay-sat-watch-bcp-source".to_owned(),
        trust_ir_sha256: "sha256:ay-sat-watch-bcp-trust_ir".to_owned(),
        native_payload_sha256: observed_bcp_payload_contract().1,
    }
}

fn observed_bcp_payload_contract() -> (u64, String) {
    static CONTRACT: OnceLock<(u64, String)> = OnceLock::new();
    CONTRACT
        .get_or_init(|| {
            // Calibrate this portable fixture with a compile-only request that
            // carries no manifest or install-gate authority. The authoritative
            // compile below then independently rechecks both claims against a
            // fresh live executable before it may expose a callable symbol.
            let mut request =
                CompileRequest::new("sat-bcp-observe-live-payload", CompileGeneration::new(0));
            request.install_intent = trust_cg_codegen::InstallIntent::CompileOnly;
            request.provenance.source_kind = SourceKind::TrustIrModule;
            let response = CompileService::default().compile(request, &bcp_status_probe_module());
            assert_eq!(
                response.status,
                CompileStatus::Compiled,
                "compile-only SAT BCP observation diagnostics: {:?}",
                response.diagnostics
            );
            let binding = response
                .artifact
                .as_ref()
                .and_then(|artifact| artifact.install.installed_payload_binding.as_ref())
                .expect("compile-only SAT BCP compile seals a live payload binding");
            (
                binding.code_size_bytes,
                binding.native_payload_sha256.clone(),
            )
        })
        .clone()
}

fn sat_bcp_verified_proof(manifest: &ArtifactManifestV1) -> NativeInstallGateProofEvidence {
    let mut summary = ay_sat_watch_bcp_verified_proof_evidence("trust-cg-verify", manifest);
    summary.native_payload_sha256 = manifest
        .metadata
        .get("native_payload_sha256")
        .expect("live SAT BCP fixture manifest binds its payload digest")
        .clone();
    summary.metadata.insert(
        "differential_evidence_target".to_owned(),
        "ay_sat_bcp_differential".to_owned(),
    );
    summary.metadata.insert(
        "rust_reference".to_owned(),
        "dense_reference_bcp".to_owned(),
    );

    NativeInstallGateProofEvidence {
        summary,
        proof_report_sha256: Some("sha256:ay-sat-watch-bcp-proof-report".to_owned()),
        obligation_set: Some("ay-sat-watch-bcp-issue-678-cases".to_owned()),
        timeout_ms: Some(10_000),
        native_payload_sha256: Some(sat_bcp_payload_identity().native_payload_sha256),
    }
}

fn sat_bcp_gate_input(manifest: &ArtifactManifestV1) -> NativeInstallGateInput {
    let expected = NativeInstallGateExpectedBindings::from_manifest(manifest);
    let payload_identity = sat_bcp_payload_identity();
    let proof_evidence = sat_bcp_verified_proof(manifest);
    let counter_scope = format!(
        "{}:{}:{}:{}",
        "ay",
        "sat-watch-bcp-install-gate",
        NativeInstallGateSurface::DirectCompileInstall.as_str(),
        expected.artifact_id
    );
    let telemetry = NativeInstallGateTelemetryInput {
        schema: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA.to_owned(),
        schema_version: NATIVE_INSTALL_GATE_TELEMETRY_SCHEMA_VERSION,
        event_id: "ay-sat-watch-bcp-install-gate".to_owned(),
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
        replay_root_sha256: "sha256:ay-sat-watch-bcp-replay".to_owned(),
        replay_consumer: "ay".to_owned(),
        replay_family: "sat-watch-bcp-install-gate".to_owned(),
        artifact_id: expected.artifact_id.clone(),
        source_sha256: payload_identity.source_sha256.clone(),
        trust_ir_sha256: payload_identity.trust_ir_sha256.clone(),
        native_payload_sha256: payload_identity.native_payload_sha256.clone(),
        replay_record_sha256: String::new(),
    }
    .with_canonical_record_sha256();

    NativeInstallGateInput {
        consumer: "ay".to_owned(),
        consumer_mode: "sat-watch-bcp-install-gate".to_owned(),
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
                validation_provenance: "trust-cg.ay.sat_watch_bcp.layout_adapter.v1".to_owned(),
                evidence_sha256: None,
                wrapper_identity: manifest.layout.wrapper_identity.clone(),
                regions: vec![NativeInstallGateLayoutEvidence::region(
                    "ay_watch_bcp_state",
                    "watch_bcp_state",
                    8,
                    1024,
                    NativeInstallGateLayoutAccess::ReadWrite,
                    "ay-watch-bcp",
                    "ay_solver",
                )],
                entry_abis: vec![NativeInstallGateLayoutEvidence::entry_abi(
                    "ay_sat_watch_bcp_status_probe",
                    expected.abi_checksum,
                    &["ay_watch_bcp_state"],
                    "ay_watch_bcp_state",
                    "ay_solver",
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

fn rejected_sat_bcp_proof(
    manifest: &ArtifactManifestV1,
    verdict: ProofEvidenceVerdict,
    code: ProofEvidenceRejectionCode,
) -> NativeInstallGateProofEvidence {
    let mut evidence = sat_bcp_verified_proof(manifest);
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

fn sat_bcp_symbol_contract(
    manifest: &ArtifactManifestV1,
    proof: &NativeInstallGateProofEvidence,
) -> SymbolLookupContract {
    ay_sat_watch_bcp_symbol_lookup_contract(manifest, proof.summary.clone())
}

fn bcp_status_probe_module() -> TrustIrModule {
    let mut module = TrustIrModule::new("ay_sat_watch_bcp_install_gate");
    let ft_id = module.add_func_type(FuncTy {
        params: vec![Ty::Ptr],
        returns: vec![Ty::I32],
        is_vararg: false,
    });
    let mut func = TrustIrFunction::new(FuncId::new(0), AY_SAT_BCP_SYMBOL, ft_id, BlockId::new(0));
    func.attrs.params = vec![trust_ir::ParamAttrs {
        nonnull: true,
        ..Default::default()
    }];
    func.blocks = vec![TrustIrBlock {
        id: BlockId::new(0),
        params: vec![(ValueId::new(0), Ty::Ptr)],
        body: vec![
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(BCP_OK_STATUS.into()),
            })
            .with_result(ValueId::new(1)),
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(1)],
            }),
        ],
    }];
    module.add_function(func);
    module
}

fn compile_sat_bcp_response(
    input: NativeInstallGateInput,
    manifest: Option<ArtifactManifestV1>,
) -> trust_cg_codegen::CompileResponse {
    let generation = CompileGeneration::new(input.expected.current_generation);
    let mut request = CompileRequest::new(
        format!("sat-bcp-install-gate-{}", input.expected.artifact_id),
        generation,
    );
    request.artifact_kind = ArtifactKind::ExecutableMemory;
    if let Some(manifest) = manifest {
        request.proof_policy = manifest.proof_policy.clone();
        request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
            verdict: ProofTvVerdict::Accepted,
            rejection_code: None,
            diagnostic_reason: "SAT BCP install-gate fixture reuses #678 evidence".to_owned(),
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

    let mut response = CompileService::default().compile(request, &bcp_status_probe_module());
    assert_eq!(
        response.status,
        CompileStatus::Compiled,
        "SAT BCP fixture compile diagnostics: {:?}",
        response.diagnostics
    );
    assert!(matches!(
        response.payload.as_ref(),
        Some(ArtifactPayload::Executable(_))
    ));
    response
        .artifact
        .as_mut()
        .expect("compiled SAT BCP artifact metadata")
        .install
        .native_install_gate_input = Some(input);
    response
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

#[test]
fn sat_bcp_executable_artifact_installs_only_after_manifest_gate_and_runs_via_bound_contract() {
    let generation = 731;
    let manifest = ay_sat_watch_bcp_manifest(generation);
    let input = sat_bcp_gate_input(&manifest);
    let proof = input
        .proof_evidence
        .as_ref()
        .expect("SAT BCP gate carries proof evidence")
        .clone();
    let reference = ArtifactManifestReference::from_manifest(&manifest);
    let contract = sat_bcp_symbol_contract(&manifest, &proof);

    manifest
        .validate_symbol_lookup(&contract)
        .expect("SAT BCP #678 manifest/proof evidence validates the symbol contract");
    assert_eq!(
        proof
            .summary
            .metadata
            .get("differential_evidence_target")
            .map(String::as_str),
        Some("ay_sat_bcp_differential")
    );
    assert_eq!(
        manifest.metadata.get("useful_native").map(String::as_str),
        Some("0")
    );
    assert!(manifest.layout.records.is_empty());
    assert!(manifest.layout.slices.is_empty());
    assert!(manifest.layout.pointers.is_empty());

    let response = compile_sat_bcp_response(input, Some(manifest.clone()));
    let packet = response
        .native_install_gate_packet()
        .expect("SAT BCP executable response carries an install gate packet");
    assert_eq!(
        packet.disposition,
        NativeInstallGateDisposition::Installable
    );
    assert_eq!(packet.rejection_code, None);
    assert!(packet.actions.expose_callable);
    assert!(packet.actions.useful_native_eligible);
    assert!(
        packet
            .validation
            .obligation_set
            .as_deref()
            .is_some_and(|set| set.starts_with("compile-service-direct-install:")),
        "install authority must retain the compile service's sealed obligation identity"
    );
    assert_eq!(
        packet.validation.proof_verifier.as_deref(),
        Some("compile_service.proof_tv")
    );
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

    let installed = response
        .into_installed_artifact()
        .expect("accepted SAT BCP gate exposes an installed executable artifact");
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
        vec![AY_SAT_BCP_SYMBOL]
    );

    reference
        .verify_manifest(&manifest)
        .expect("installed manifest reference verifies the SAT BCP manifest");
    let typed = installed
        .get_contract_symbol_bound::<AYSatWatchBcpFn>(&manifest, &contract)
        .expect("installed SAT BCP artifact exposes only the manifest-bound symbol");
    assert_eq!(typed.symbol(), AY_SAT_BCP_SYMBOL);
    assert_eq!(typed.signature(), &ay_sat_watch_bcp_signature());

    let bcp_fn = unsafe {
        // SAFETY: `typed` was obtained through the installed artifact's
        // manifest-backed `AYSatWatchBcpFn` contract above.
        typed.into_fn()
    };
    let mut context = PropagationContext { _opaque: [] };
    let native_status = unsafe {
        // SAFETY: this fixture probe ignores the pointee, but the typed BCP
        // contract requires a non-null context pointer and `context` supplies
        // one for the duration of the call.
        bcp_fn(&mut context)
    };
    assert_eq!(native_status, BCP_OK_STATUS);
    assert_eq!(native_status, rust_reference_empty_bcp_status());
}

#[test]
fn sat_bcp_gate_fails_closed_for_missing_wrong_and_unrunnable_artifact_routes() {
    let generation = 732;
    let manifest = ay_sat_watch_bcp_manifest(generation);

    let mut missing_manifest = sat_bcp_gate_input(&manifest);
    missing_manifest.manifest = None;
    missing_manifest.manifest_reference = None;
    let missing_response = compile_sat_bcp_response(missing_manifest, None);
    assert_gate_rejected(
        missing_response,
        NativeInstallGateRejectionCode::MissingManifest,
    );

    let mut missing_layout = sat_bcp_gate_input(&manifest);
    missing_layout.layout_evidence = None;
    let missing_layout_response = compile_sat_bcp_response(missing_layout, Some(manifest.clone()));
    assert_gate_rejected(
        missing_layout_response,
        NativeInstallGateRejectionCode::MissingLayoutEvidence,
    );

    let mut verifier_failure = sat_bcp_gate_input(&manifest);
    verifier_failure.proof_evidence = Some(rejected_sat_bcp_proof(
        &manifest,
        ProofEvidenceVerdict::VerifierFailure,
        ProofEvidenceRejectionCode::VerifierFailure,
    ));
    let verifier_failure_response =
        compile_sat_bcp_response(verifier_failure, Some(manifest.clone()));
    let compiler_packet = verifier_failure_response
        .native_install_gate_packet()
        .expect("live executable derives a compiler-sealed gate packet");
    assert_eq!(
        compiler_packet.disposition,
        NativeInstallGateDisposition::Installable,
        "caller-supplied proof metadata must not overwrite live compiler evidence"
    );
    assert_eq!(
        compiler_packet.validation.proof_verifier.as_deref(),
        Some("compile_service.proof_tv")
    );
    assert_eq!(compiler_packet.validation.proof_verdict, "verified");

    let accepted_response =
        compile_sat_bcp_response(sat_bcp_gate_input(&manifest), Some(manifest.clone()));
    let installed = accepted_response
        .into_installed_artifact()
        .expect("accepted SAT BCP fixture installs");
    let proof = sat_bcp_verified_proof(&manifest);
    let contract = sat_bcp_symbol_contract(&manifest, &proof);

    let mut wrong_manifest = manifest.clone();
    wrong_manifest.artifact_id = "ay-sat-watch-bcp-wrong-artifact".to_owned();
    assert!(
        installed
            .get_contract_symbol_bound::<AYSatWatchBcpFn>(&wrong_manifest, &contract)
            .is_err(),
        "installed SAT BCP lookup must fail when metadata points at the wrong artifact"
    );

    let wrong_symbol_contract = SymbolLookupContract::new(
        "ay_sat_watch_bcp_wrong_symbol",
        ay_sat_watch_bcp_signature(),
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum())
    .with_proof_evidence(proof.summary);
    assert!(
        installed
            .get_contract_symbol_bound::<AYSatWatchBcpFn>(&manifest, &wrong_symbol_contract)
            .is_err(),
        "installed SAT BCP lookup must fail when the expected symbol is absent"
    );

    let object_manifest = ay_sat_watch_bcp_manifest(733);
    let mut object_request = CompileRequest::new(
        "sat-bcp-object-only-is-not-installable",
        CompileGeneration::new(733),
    )
    .with_artifact_manifest(object_manifest.clone());
    object_request.artifact_kind = ArtifactKind::Object;
    object_request.proof_policy = object_manifest.proof_policy.clone();
    object_request.proof_tv_evidence = Some(ProofTvEvidenceOutcome {
        verdict: ProofTvVerdict::Accepted,
        rejection_code: None,
        diagnostic_reason: "SAT BCP object-only negative fixture reuses #678 evidence".to_owned(),
    });
    object_request.provenance.source_kind = SourceKind::TrustIrModule;
    let object_response =
        CompileService::default().compile(object_request, &bcp_status_probe_module());
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
        "object-only SAT BCP payload must not publish an executable install gate"
    );
    assert!(object_response.into_installed_artifact().is_none());
}

fn rust_reference_empty_bcp_status() -> i32 {
    BCP_OK_STATUS
}
