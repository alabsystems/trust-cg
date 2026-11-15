// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! An admitted source entry through existing proof/publication owners and
//! invocation-owned storage. Conditional framed peers have their own consuming
//! owner and source integration test.
#![cfg(all(feature = "verify", target_arch = "aarch64", target_os = "macos"))]

use trust_cg_codegen as cg;
#[path = "common/core_install_fixture.rs"]
mod fixture;
use cg::compiler::JitValidationMode;
use cg::jit::JitExternalSymbolResolutionPolicy;
use cg::jit::entry_stack::OwnedEntryStack;
use cg::{
    Compiler, CompilerConfig, CoreDeclaredImportManifest, admit_identity_core_module_for_host_jit,
};

#[test]
fn forced_object_frames_retain_the_existing_core_planning_refusal() {
    let (module, target) = fixture::licensed_module(Some(42)).unwrap();
    let core = admit_identity_core_module_for_host_jit(
        module,
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .unwrap();
    let mut config = CompilerConfig::for_host_jit();
    config.emit_proofs = true;
    config.jit_validation_mode_override = Some(JitValidationMode::AlwaysVerify);
    config.jit_external_symbol_resolution = JitExternalSymbolResolutionPolicy::ExplicitOnly;
    config.aarch64_force_frame_pointers = true;
    let refusal = Compiler::new_for_target_spec(config, target.target_spec())
        .plan_core_module_for_jit_compilation(core)
        .unwrap_err();
    assert!(
        refusal
            .to_string()
            .contains("Core JIT does not model forced object frame records")
    );
    println!("CORE_OWNED_STACK_FORCED_OBJECT_FRAME_REFUSAL=RETAINED");
}

#[test]
fn genuine_source_entry_executes_on_owned_private_storage() {
    let artifact = fixture::licensed_plan(true)
        .compile_for_installation()
        .expect("existing source and full machine proof");
    let identity = artifact.artifact().identity();
    let refusal = artifact
        .install_owned_stack_entry(
            "foreign",
            fixture::install_manifest(),
            cg::compile_service::CompileGeneration::new(1),
        )
        .unwrap_err();
    assert_eq!(refusal.predecessor().artifact().identity(), identity);
    let artifact = refusal.into_predecessor();
    let (entry, _) = artifact
        .install_owned_stack_entry(
            "answer",
            fixture::install_manifest(),
            cg::compile_service::CompileGeneration::new(1),
        )
        .expect("ordinary source, payload, manifest and native-install gates");
    assert_eq!(entry.required_private_stack_bytes(), 0);
    let mut stack = OwnedEntryStack::allocate(65_536).unwrap();
    assert_eq!(entry.invoke0_u64(&mut stack).unwrap(), 42);
    assert_eq!(entry.invoke0_u64(&mut stack).unwrap(), 42);
    println!("CORE_SOURCE_BOUND_OWNED_STACK_NATIVE_RESULT=42");
}

#[test]
fn zero_footprint_source_entry_uses_no_unowned_signal_stack_slack() {
    let artifact = fixture::licensed_plan(true)
        .compile_for_installation()
        .unwrap();
    let (entry, _) = artifact
        .install_owned_stack_entry(
            "answer",
            fixture::install_manifest(),
            cg::compile_service::CompileGeneration::new(1),
        )
        .unwrap();
    assert_eq!(entry.required_private_stack_bytes(), 0);
    let mut stack = OwnedEntryStack::allocate(0).unwrap();
    assert_eq!(entry.invoke0_u64(&mut stack).unwrap(), 42);
}
