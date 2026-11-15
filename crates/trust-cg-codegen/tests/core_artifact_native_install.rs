// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Prerequisite for a consuming proof-grade Core installation route.
//! No unlicensed-body exception or raw executable-byte path is used here.
#![cfg(all(feature = "verify", target_arch = "aarch64", target_os = "macos"))]

use trust_cg_codegen as cg;
#[path = "common/core_install_fixture.rs"]
mod fixture;
use fixture::{install_manifest, licensed_plan};

#[test]
fn source_authenticated_core_publishes_and_executes_through_existing_native_owner() {
    let artifact = licensed_plan(true)
        .compile_for_installation()
        .expect("actual complete machine proof and retained source");
    exercise_install(artifact);
}

fn exercise_install(mut artifact: trust_cg_codegen::compiler::CoreInstallationArtifact) {
    assert_eq!(
        artifact.artifact().function_names().collect::<Vec<_>>(),
        ["answer"]
    );
    assert!(artifact.artifact().fixup_inventory().entries().is_empty());
    assert!(
        artifact
            .artifact()
            .certificate("answer")
            .unwrap()
            .is_verified()
    );
    let manifest = install_manifest();
    let identity = artifact.artifact().identity();
    // Each refusal returns the identical noncallable predecessor for a valid retry.
    let bad_generation = artifact
        .install(
            manifest.clone(),
            trust_cg_codegen::compile_service::CompileGeneration::new(2),
        )
        .unwrap_err();
    assert!(
        bad_generation.reason().contains("generation"),
        "{bad_generation}"
    );
    artifact = bad_generation.into_predecessor();
    assert_eq!(artifact.artifact().identity(), identity);
    let mut bad_signature = manifest.clone();
    bad_signature.symbols[0].signature =
        trust_cg_codegen::jit_contract::SymbolSignature::extern_c(vec![], vec![]);
    let refused = artifact
        .install(
            bad_signature,
            trust_cg_codegen::compile_service::CompileGeneration::new(1),
        )
        .unwrap_err();
    assert!(refused.reason().contains("signature"), "{refused}");
    artifact = refused.into_predecessor();
    assert_eq!(artifact.artifact().identity(), identity);
    let mut bad_target = manifest.clone();
    bad_target.target.architecture = trust_cg_codegen::jit_contract::TargetArchitecture::X86_64;
    let refused = artifact
        .install(
            bad_target,
            trust_cg_codegen::compile_service::CompileGeneration::new(1),
        )
        .unwrap_err();
    assert!(refused.reason().contains("manifest"), "{refused}");
    artifact = refused.into_predecessor();
    assert_eq!(artifact.artifact().identity(), identity);
    let mut wrong_digest = manifest.clone();
    wrong_digest.metadata.insert(
        "native_payload_sha256".into(),
        format!("sha256:{}", "00".repeat(32)),
    );
    let refused = artifact
        .install(wrong_digest, cg::compile_service::CompileGeneration::new(1))
        .unwrap_err();
    assert!(refused.reason().contains("payload"), "{refused}");
    artifact = refused.into_predecessor();
    assert_eq!(artifact.artifact().identity(), identity);
    let (installed, manifest) = artifact
        .install(
            manifest.clone(),
            trust_cg_codegen::compile_service::CompileGeneration::new(1),
        )
        .expect("existing shared publication, payload binding and native-install gate");
    let signature = manifest.symbols[0].signature.clone();
    let mut contract = trust_cg_codegen::jit_contract::SymbolLookupContract::new(
        "answer",
        signature,
        manifest.target.checksum(),
        manifest.abi.checksum(),
        manifest.layout.checksum(),
    )
    .with_invalidation_checksum(manifest.invalidation.checksum())
    .with_manifest_checksum(manifest.checksum());
    assert!(installed.metadata.native_install_gate.is_some());
    assert!(installed.buffer.all_verified());
    contract = contract.with_proof_evidence(installed.metadata.proof_evidence_summary.clone());
    let mut wrong_contract = contract.clone();
    wrong_contract.symbol = "not_answer".into();
    assert!(
        installed
            .get_contract_symbol_bound::<extern "C" fn() -> u64>(&manifest, &wrong_contract)
            .is_err()
    );
    let mut wrong_identity = manifest.clone();
    wrong_identity.artifact_id = "foreign-artifact".into();
    assert!(
        installed
            .get_contract_symbol_bound::<extern "C" fn() -> u64>(&wrong_identity, &contract)
            .is_err()
    );
    let typed = installed
        .get_contract_symbol_bound::<extern "C" fn() -> u64>(&manifest, &contract)
        .expect("existing manifest-backed native-call owner");
    // SAFETY: the independent source, actual Core and manifest all state () -> U64.
    let answer = unsafe { typed.into_fn() };
    assert_eq!(answer(), 42);
    println!("CORE_INSTALL_SOURCE_BOUND_NATIVE_RESULT=42");
}

#[test]
fn source_none_recorded_comparand_cannot_enter_typed_installation() {
    let refusal = licensed_plan(false).compile_for_installation().unwrap_err();
    assert!(refusal.to_string().contains("source"), "{refusal}");
}

#[test]
fn unrelated_independent_source_cannot_license_the_core_body() {
    let refusal = fixture::licensed_module(Some(43)).unwrap_err();
    assert!(!refusal.is_empty());
}

#[test]
fn unused_typed_provider_inventory_refuses_without_losing_the_source_plan() {
    use cg::{
        CoreHostFunctionEffects, CoreHostFunctionImport, CoreHostImport, CoreHostMemoryEffect,
        CoreRuntimeIdentity,
    };
    use trust_ir::{BlockId, FuncId, Function, Linkage};
    let (mut module, target) = fixture::licensed_module(Some(42)).unwrap();
    let signature = module.functions[0].ty;
    let mut declaration = Function::new(
        FuncId::new(7),
        "unused_provider",
        signature,
        BlockId::new(0),
    );
    declaration.linkage = Linkage::External;
    declaration.attrs.readnone = true;
    // The unused declaration/import is a real typed address-free contract, no
    // callback or invented provider implementation. This domain must refuse it.
    let import = CoreHostFunctionImport::try_new(
        "unused_provider",
        module.func_types[signature.as_usize()].clone(),
        declaration.calling_conv,
        vec![],
        CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None),
        "negative-unused-v1",
        CoreRuntimeIdentity::try_new(
            "no-implementation",
            trust_ir::proof::ProofDigest::sha256_domain(
                "negative-unused",
                b"no provider implementation",
            ),
        )
        .unwrap(),
    )
    .unwrap();
    module.try_add_function(declaration).unwrap();
    let imports =
        cg::CoreDeclaredImportManifest::try_new(vec![CoreHostImport::Function(import)]).unwrap();
    let plan = fixture::qualified_plan(module, target, imports);
    let identity = plan.identity();
    let refusal = plan.compile_for_installation().unwrap_err();
    assert!(
        refusal.to_string().contains("typed runtime providers"),
        "{refusal}"
    );
    assert_eq!(refusal.plan().identity(), identity);
    assert_eq!(refusal.plan().retained_declared_external_call_count(), 0);
}
