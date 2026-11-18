// Copyright 2026 Andrew Yates | Apache-2.0
//! Common genuine certification, strict Core plan and actual-symbol manifest.
use super::cg;
use trust_ir::proof::{
    IslandEnvironment, ProofLineageId, ProofLineageManifest, ProofTransform, ProofTransformStage,
    SourceDefinitionRef,
};
use trust_ir::{BodyGate, GateEvidence, Module, ProofId};
use trust_ir_build::{ValidationConfig, certify_source_bound_byte_entry};
fn mint(
    m: &Module,
    island: &IslandEnvironment,
    declaration: &str,
) -> Result<trust_ir_build::SourceBoundCallCertificates, String> {
    certify_source_bound_byte_entry(
        m,
        ProofLineageId::new(10),
        ProofId::new(20),
        ProofTransform::new(
            ProofTransformStage::Frontend,
            "byte-entry",
            "independent-source",
            "1",
        ),
        island,
        &[(
            m.functions[0].id,
            SourceDefinitionRef {
                decl: declaration.into(),
                closure_digest: island.digest,
            },
        )],
    )
}
fn attach(
    m: &mut Module,
    rows: trust_ir_build::SourceBoundCallCertificates,
) -> ProofLineageManifest {
    let manifest = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        roots: rows.nodes.iter().map(|n| n.id).collect(),
        nodes: rows.nodes,
    };
    m.proof_obligations.extend(rows.obligations);
    m.proof_certificates.extend(rows.certificates);
    rebind_body(m);
    manifest
}
fn rebind_body(m: &mut Module) {
    let f = m.functions[0].id;
    let body_digest = m.function_body_digest(f).unwrap();
    m.functions[0].body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: Some(GateEvidence {
            obligation: ProofId::new(20),
            body_digest,
        }),
    });
}
fn config() -> ValidationConfig<'static> {
    ValidationConfig::pinned()
        .with_bound_certificates(true)
        .with_source_bound_certificates(true)
        .with_gate_evidence(true)
}

pub(crate) fn certify(
    mut module: Module,
    island: &IslandEnvironment,
    declaration: &str,
) -> Result<Module, String> {
    let rows = mint(&module, island, declaration)?;
    let lineage = attach(&mut module, rows);
    let report = trust_ir_build::validate_module_with_config(&module, &config());
    if !report.is_ok() {
        return Err(format!("{:?}", report.errors()));
    }
    trust_ir_build::source_byte_entry::check_byte_entry_source(&report)?;
    trust_ir_build::lineage_closed_with_validated_authority(&module, &lineage)
        .map_err(|error| format!("{error:?}"))?;
    Ok(module)
}

pub(crate) fn plan(module: Module) -> cg::compiler::PolicyQualifiedCoreJitCompilationPlan {
    let target = cg::CoreHostJitTarget::detect().expect("native host");
    let core = cg::admit_identity_core_module_for_host_jit(
        module,
        &target,
        cg::CoreDeclaredImportManifest::empty(),
    )
    .expect("ordinary exact source/Core admission");
    let mut config = cg::CompilerConfig::for_host_jit();
    config.emit_proofs = true;
    config.jit_validation_mode_override = Some(cg::compiler::JitValidationMode::AlwaysVerify);
    config.jit_external_symbol_resolution = cg::JitExternalSymbolResolutionPolicy::ExplicitOnly;
    cg::Compiler::new_for_target_spec(config, target.target_spec())
        .plan_core_module_for_jit_compilation(core)
        .unwrap()
        .qualify_for_proof_grade_compilation()
        .unwrap()
}
pub(crate) fn manifest(
    module: &Module,
    source: &str,
    generation: cg::compile_service::CompileGeneration,
) -> cg::jit_contract::ArtifactManifestV1 {
    use cg::jit_contract::*;
    let target = TargetDescriptor::for_trust_cg_host_jit();
    let abi = AbiDescriptor::for_trust_cg_target_os(
        cg::target::Target::Aarch64,
        target.operating_system.clone(),
    );
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let policy = ProofPolicy::require_certificates(std::iter::empty::<String>());
    let invalidation = InvalidationKey::new(
        source,
        "sealed-context-output",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        policy.checksum(),
        generation.get(),
    );
    let mut manifest = ArtifactManifestV1::new(
        "source-bound-context-output",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: module.functions[0].name.clone(),
        visibility: SymbolVisibility::Exported,
        signature: cg::compile_service::symbol_signature_for_core_function(
            module,
            module.functions[0].id,
            cg::CoreHostJitTarget::detect().unwrap().target_spec(),
        )
        .expect("same original module-to-installed-symbol ABI owner"),
        offset_bytes: None,
        checksum: None,
    });
    manifest
}
