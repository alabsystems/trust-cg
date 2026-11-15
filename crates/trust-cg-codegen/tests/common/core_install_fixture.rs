// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

// Shared causal fixture: actual independently authored source, default license and strict Core owner.
use super::cg;
use cg::compiler::JitValidationMode;
use cg::jit::JitExternalSymbolResolutionPolicy;
use cg::{
    Compiler, CompilerConfig, CoreDeclaredImportManifest, CoreHostJitTarget,
    admit_identity_core_module_for_host_jit,
};
use sha2::{Digest, Sha256};
use trust_ir::proof::{
    IslandEnvironment, ProofDigest, ProofLineageId, ProofTransform, ProofTransformStage,
    SourceDefinitionRef, encode_island_declarations_v1,
};
use trust_ir::{BodyGate, GateEvidence, Ty};
use trust_ir_build::clean_kernel::{Declaration, Expr, Name};
use trust_ir_build::{ModuleBuilder, certify_identity_lineage_rung_island_bound};

pub(crate) fn licensed_module(
    source_value: Option<u64>,
) -> Result<(trust_ir::Module, CoreHostJitTarget), String> {
    let target = CoreHostJitTarget::detect().expect("actual ARM64/macOS target");
    let mut builder = ModuleBuilder::new_with_target_info(
        "licensed_core_install_prerequisite",
        target.trust_ir_target_info().clone(),
    );
    let signature = builder.add_func_type(vec![], vec![Ty::U64]);
    let mut function = builder.function("answer", signature);
    let entry = function.create_block();
    function.switch_to_block(entry);
    let answer = function.iconst(Ty::U64, 42);
    function.ret(vec![answer]);
    let function_id = function.build();
    let mut module = builder.build().expect("well-typed ordinary Core literal");
    // Independent source declaration: authored directly, never obtained from
    // the backend denotation, code bytes, or a recorded-comparand certificate.
    let (_node, obligation, certificate) = if let Some(source_value) = source_value {
        let declarations = [Declaration::Definition {
            name: Name::from_string("CoreInstall.answer"),
            level_params: vec![],
            type_: Expr::const_str("Nat"),
            value: Expr::nat_lit(source_value),
            is_reducible: true,
        }];
        let source_bytes = encode_island_declarations_v1(&declarations).unwrap();
        let source_digest = ProofDigest::sha256(Sha256::digest(&source_bytes).into());
        let island = IslandEnvironment::new(source_bytes);
        certify_identity_lineage_rung_island_bound(
            &module,
            ProofLineageId::new(0),
            trust_ir::value::ProofId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "identity",
                "core-install-prerequisite",
                "1",
            ),
            function_id,
            &island,
            SourceDefinitionRef {
                decl: "CoreInstall.answer".into(),
                closure_digest: source_digest,
            },
        )
        .map_err(|error| format!("{error:?}"))?
    } else {
        trust_ir_build::certify_identity_lineage_rung_bound(
            &module,
            ProofLineageId::new(0),
            trust_ir::value::ProofId::new(0),
            ProofTransform::new(
                ProofTransformStage::Frontend,
                "identity",
                "source-none-control",
                "1",
            ),
            function_id,
        )
        .expect("existing recorded-comparand control")
    };
    let binding = certificate
        .evidence
        .clean_cic_kernel_recheck()
        .unwrap()
        .binding
        .as_ref()
        .expect("bound source certificate");
    assert_eq!(binding.source.is_some(), source_value.is_some());
    if let Some(source) = &binding.source {
        assert_eq!(source.decl, "CoreInstall.answer");
    }
    let obligation_id = obligation.id;
    module.proof_obligations.push(obligation);
    module.proof_certificates.push(certificate);
    let body_digest = module
        .function_body_digest(function_id)
        .expect("canonical actual body");
    module
        .functions
        .iter_mut()
        .find(|function| function.id == function_id)
        .unwrap()
        .body_gate = Some(BodyGate::Gated {
        authority: "clean-kernel-tv".into(),
        evidence: Some(GateEvidence {
            obligation: obligation_id,
            body_digest,
        }),
    });
    let errors = trust_ir_build::validate_module_for_codegen(&module);
    assert!(
        errors.is_empty(),
        "actual kernel-backed default codegen license: {errors:?}"
    );
    Ok((module, target))
}

pub(crate) fn licensed_plan(
    source_bound: bool,
) -> cg::compiler::PolicyQualifiedCoreJitCompilationPlan {
    let (module, target) =
        licensed_module(source_bound.then_some(42)).expect("independent source certificate");
    qualified_plan(module, target, CoreDeclaredImportManifest::empty())
}

pub(crate) fn qualified_plan(
    module: trust_ir::Module,
    target: CoreHostJitTarget,
    imports: CoreDeclaredImportManifest,
) -> cg::compiler::PolicyQualifiedCoreJitCompilationPlan {
    let core = admit_identity_core_module_for_host_jit(module, &target, imports)
        .expect("existing complete identity-Core admission");
    let mut config = CompilerConfig::for_host_jit();
    config.emit_proofs = true;
    config.jit_validation_mode_override = Some(JitValidationMode::AlwaysVerify);
    config.jit_external_symbol_resolution = JitExternalSymbolResolutionPolicy::ExplicitOnly;
    let compiler = Compiler::new_for_target_spec(config, target.target_spec());
    assert!(!compiler.codegen_license().permits_unlicensed());
    compiler
        .plan_core_module_for_jit_compilation(core)
        .expect("default policy accepts genuine body evidence")
        .qualify_for_proof_grade_compilation()
        .expect("ordinary proof-grade policy")
}

pub(crate) fn install_manifest() -> cg::jit_contract::ArtifactManifestV1 {
    use cg::jit_contract::*;
    let target = TargetDescriptor::for_trust_cg_host_jit();
    let abi = AbiDescriptor::for_trust_cg_target_os(
        cg::target::Target::Aarch64,
        target.operating_system.clone(),
    );
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let policy = ProofPolicy::require_certificates(std::iter::empty::<String>());
    let invalidation = InvalidationKey::new(
        "source:CoreInstall.answer",
        "sealed-core",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        policy.checksum(),
        1,
    );
    let mut manifest = ArtifactManifestV1::new(
        "source-bound-core-answer",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        policy,
    );
    manifest.symbols.push(ArtifactSymbol {
        name: "answer".into(),
        visibility: SymbolVisibility::Exported,
        signature: SymbolSignature::extern_c(vec![], vec![AbiValue::new(AbiValueKind::I64)]),
        offset_bytes: Some(0),
        checksum: None,
    });
    manifest
}
