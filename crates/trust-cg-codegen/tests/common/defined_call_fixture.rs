// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
//! Shared unchanged independently authored leaf/caller source fixture.

use super::cg;
use cg::compiler::JitValidationMode;
use cg::{
    Compiler, CompilerConfig, CoreDeclaredImportManifest, CoreHostJitTarget,
    JitExternalSymbolResolutionPolicy, admit_identity_core_module_for_host_jit,
};
use sha2::{Digest, Sha256};
use trust_ir::proof::{
    IslandEnvironment, ProofDigest, ProofLineageId, ProofLineageManifest, ProofTransform,
    ProofTransformStage, SourceDefinitionRef, encode_island_declarations_v1,
};
use trust_ir::{BodyGate, FuncId, GateEvidence, Linkage, Module, Ty};
use trust_ir_build::clean_kernel::{Declaration, Expr, Name};
use trust_ir_build::{ModuleBuilder, ValidationConfig, certify_source_bound_call_family};

pub(crate) fn raw_module() -> (Module, CoreHostJitTarget, FuncId, FuncId) {
    let target = CoreHostJitTarget::detect().expect("actual supported host");
    let mut builder = ModuleBuilder::new_with_target_info(
        "independent_defined_call_family",
        target.trust_ir_target_info().clone(),
    );
    let signature = builder.add_func_type(vec![], vec![Ty::U64]);
    let mut leaf = builder.function("leaf", signature);
    let entry = leaf.create_block();
    leaf.switch_to_block(entry);
    let value = leaf.iconst(Ty::U64, 42);
    leaf.ret(vec![value]);
    let leaf_id = leaf.build();
    let mut caller = builder.function("entry", signature);
    let entry = caller.create_block();
    caller.switch_to_block(entry);
    let value = caller.call(leaf_id, vec![]);
    caller.ret(vec![value]);
    let caller_id = caller.build();
    let mut module = builder.build().expect("well-typed actual call and body");
    module
        .functions
        .iter_mut()
        .find(|f| f.id == leaf_id)
        .unwrap()
        .linkage = Linkage::Internal;
    (module, target, leaf_id, caller_id)
}

pub(crate) fn source_island(leaf_value: u64) -> (IslandEnvironment, ProofDigest) {
    // Authored independently of IR denotation or proof output. The caller's
    // actual source references its own same-island source definition.
    let definition = |name: &str, value| Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
        value,
        is_reducible: true,
    };
    let bytes = encode_island_declarations_v1(&[
        definition("DefinedCalls.leaf", Expr::nat_lit(leaf_value)),
        definition("DefinedCalls.entry", Expr::const_str("DefinedCalls.leaf")),
    ])
    .unwrap();
    let digest = ProofDigest::sha256(Sha256::digest(&bytes).into());
    (IslandEnvironment::new(bytes), digest)
}

pub(crate) fn source(decl: &str, digest: ProofDigest) -> SourceDefinitionRef {
    SourceDefinitionRef {
        decl: decl.into(),
        closure_digest: digest,
    }
}

pub(crate) fn transform() -> ProofTransform {
    ProofTransform::new(
        ProofTransformStage::Frontend,
        "source-defined-calls",
        "cg-consumer",
        "1",
    )
}

pub(crate) fn certified(
    leaf_source: u64,
) -> Result<(Module, CoreHostJitTarget, ProofLineageManifest), String> {
    let (mut module, target, leaf, caller) = raw_module();
    let (island, digest) = source_island(leaf_source);
    let family = certify_source_bound_call_family(
        &module,
        ProofLineageId::new(0),
        trust_ir::value::ProofId::new(0),
        transform(),
        &island,
        &[
            (caller, source("DefinedCalls.entry", digest)),
            (leaf, source("DefinedCalls.leaf", digest)),
        ],
    )
    .map_err(|error| format!("{error:?}"))?;
    // Keep the ordinary gate-evidence owner: exact real obligation and current
    // body digest for EVERY defined body, with no unlicensed exception.
    let gates: Vec<_> = module
        .functions
        .iter()
        .map(|function| {
            let obligation = family
                .obligations
                .iter()
                .find(|o| o.function == Some(function.id))
                .unwrap();
            (
                function.id,
                GateEvidence {
                    obligation: obligation.id,
                    body_digest: module.function_body_digest(function.id).unwrap(),
                },
            )
        })
        .collect();
    for (id, evidence) in gates {
        module
            .functions
            .iter_mut()
            .find(|f| f.id == id)
            .unwrap()
            .body_gate = Some(BodyGate::Gated {
            authority: cg::CLEAN_KERNEL_TV_AUTHORITY.into(),
            evidence: Some(evidence),
        });
    }
    let manifest = ProofLineageManifest {
        schema_version: ProofLineageManifest::SCHEMA_VERSION,
        roots: family.nodes.iter().map(|n| n.id).collect(),
        nodes: family.nodes,
    };
    module.proof_obligations.extend(family.obligations);
    module.proof_certificates.extend(family.certificates);
    Ok((module, target, manifest))
}

pub(crate) fn source_validation(module: &Module) -> Result<(), String> {
    let report = trust_ir_build::validate_module_with_config(
        module,
        &ValidationConfig::pinned()
            .with_bound_certificates(true)
            .with_source_bound_certificates(true)
            .with_gate_evidence(true),
    );
    if !report.is_ok() {
        return Err(format!("{:?}", report.errors()));
    }
    cg::CodegenLicensePolicy::default()
        .enforce_module(module)
        .map_err(|error| error.to_string())
}

pub(crate) fn qualified_plan(
    module: Module,
    target: CoreHostJitTarget,
) -> cg::compiler::PolicyQualifiedCoreJitCompilationPlan {
    source_validation(&module).expect("ordinary independent source/license replay");
    let core = admit_identity_core_module_for_host_jit(
        module,
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .expect("ordinary exact Core/source and strict-LIR admission");
    let mut config = CompilerConfig::for_host_jit();
    config.emit_proofs = true;
    config.jit_validation_mode_override = Some(JitValidationMode::AlwaysVerify);
    config.jit_external_symbol_resolution = JitExternalSymbolResolutionPolicy::ExplicitOnly;
    let compiler = Compiler::new_for_target_spec(config, target.target_spec());
    assert!(!compiler.codegen_license().permits_unlicensed());
    compiler
        .plan_core_module_for_jit_compilation(core)
        .expect("ordinary source-bound planning")
        .qualify_for_proof_grade_compilation()
        .expect("ordinary proof-grade policy")
}
