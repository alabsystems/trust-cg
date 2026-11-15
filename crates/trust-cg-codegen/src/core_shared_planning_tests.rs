// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared source custody through planning; no code is emitted or executed.

// This file's fixtures carry no codegen license (`body_gate: None`), which the
// Core JIT planner REFUSES by default (roadmap WS7.5, DG-73); its compilers
// state `Permit` through the main test module's helper, so no plan here
// passes or fails because it was silently refused.
use super::tests::{
    admitted_core_import_test_fixture, admitted_core_test_module, permit_unlicensed,
};
use super::*;
use crate::core_admission::{
    CoreHostJitTarget, try_admit_identity_core_module_for_host_jit,
    try_admit_shared_identity_core_module_for_host_jit,
};
use std::sync::Arc;

fn allocations(module: &trust_ir::Module) -> [usize; 5] {
    let definition = module
        .functions
        .iter()
        .find(|function| !function.blocks.is_empty())
        .unwrap();
    assert!(!definition.blocks[0].body.is_empty());
    [
        module.name.as_ptr() as usize,
        module.functions.as_ptr() as usize,
        module.func_types.as_ptr() as usize,
        definition.blocks.as_ptr() as usize,
        definition.blocks[0].body.as_ptr() as usize,
    ]
}

#[test]
fn shared_core_planning_preserves_exact_module_and_matches_owned_plan_identity() {
    let target = CoreHostJitTarget::detect().expect("a supported native Core host is required");
    let (module, manifest) = admitted_core_import_test_fixture(&target);
    let source = Arc::new(module);
    let original_allocations = allocations(&source);
    // Separate owned input for parity only; neither admission path makes this clone.
    let owned_input = source.as_ref().clone();
    let owned_allocations = allocations(&owned_input);
    let owned = try_admit_identity_core_module_for_host_jit(owned_input, &target, manifest.clone())
        .unwrap();
    let manifest_allocation = manifest.imports().as_ptr();
    let shared =
        try_admit_shared_identity_core_module_for_host_jit(Arc::clone(&source), &target, manifest)
            .unwrap();
    assert!(std::ptr::eq(shared.admitted_module(), source.as_ref()));
    assert_eq!(allocations(shared.admitted_module()), original_allocations);

    // Explicit diagnostic planning is sufficient for this custody test; it
    // grants no proof-grade compilation or execution authority.
    let config = CompilerConfig::for_host_jit_unchecked();
    let owned_plan = Compiler::new_for_target_spec(config.clone(), target.target_spec())
        .with_codegen_license(permit_unlicensed())
        .plan_core_module_for_jit_compilation(owned)
        .unwrap();
    let plan = Compiler::new_for_target_spec(config, target.target_spec())
        .with_codegen_license(permit_unlicensed())
        .plan_core_module_for_jit_compilation(shared)
        .unwrap();
    assert!(Arc::ptr_eq(&source, &plan.parts.module));
    assert_eq!(allocations(&plan.parts.module), original_allocations);
    assert_eq!(allocations(&owned_plan.parts.module), owned_allocations);
    assert_eq!(
        plan.declared_import_manifest().imports().as_ptr(),
        manifest_allocation
    );
    assert_eq!(plan.admission_receipt(), owned_plan.admission_receipt());
    assert_eq!(plan.identity(), owned_plan.identity());
    assert_eq!(Arc::strong_count(&source), 2);
    drop(plan);
    assert_eq!(Arc::strong_count(&source), 1);
    assert_eq!(allocations(&source), original_allocations);
}

#[test]
fn shared_core_planning_failure_recovers_exact_admission_for_retry() {
    let target = CoreHostJitTarget::detect().expect("a supported native Core host is required");
    let (module, manifest) = admitted_core_import_test_fixture(&target);
    let source = Arc::new(module);
    let original_allocations = allocations(&source);
    let manifest_allocation = manifest.imports().as_ptr();
    let admitted =
        try_admit_shared_identity_core_module_for_host_jit(Arc::clone(&source), &target, manifest)
            .unwrap();
    let receipt = admitted.receipt().clone();
    let config = CompilerConfig::for_host_jit_unchecked();
    let mut refusing_config = config.clone();
    refusing_config.relocation_model = RelocationModel::Pic;
    let failure = Compiler::new_for_target_spec(refusing_config, target.target_spec())
        .with_codegen_license(permit_unlicensed())
        .plan_core_module_for_jit_compilation(admitted)
        .expect_err("a shared owner cannot bypass the JIT relocation policy");
    assert!(matches!(
        failure.reason(),
        CoreJitPlanningError::RelocationModelUnsupported {
            model: RelocationModel::Pic,
        }
    ));
    assert!(std::ptr::eq(
        failure.core().admitted_module(),
        source.as_ref()
    ));
    assert_eq!(
        allocations(failure.core().admitted_module()),
        original_allocations
    );
    assert_eq!(
        failure.core().declared_import_manifest().imports().as_ptr(),
        manifest_allocation
    );
    assert_eq!(failure.core().receipt(), &receipt);
    let (_, recovered) = failure.into_parts();
    let plan = Compiler::new_for_target_spec(config, target.target_spec())
        .with_codegen_license(permit_unlicensed())
        .plan_core_module_for_jit_compilation(recovered)
        .unwrap();
    assert!(Arc::ptr_eq(&source, &plan.parts.module));
    assert_eq!(allocations(&plan.parts.module), original_allocations);
    assert_eq!(
        plan.declared_import_manifest().imports().as_ptr(),
        manifest_allocation
    );
    assert_eq!(plan.admission_receipt(), &receipt);
}

#[test]
fn shared_core_plan_keeps_a_strong_share_across_worker_transfer() {
    fn send<T: Send>() {}
    send::<CoreJitCompilationPlan>();
    send::<CoreJitPlanningFailure>();
    let target = CoreHostJitTarget::detect().expect("a supported native Core host is required");
    let source = Arc::new(admitted_core_test_module(&target));
    let original_allocations = allocations(&source);
    let weak = Arc::downgrade(&source);
    let admitted = try_admit_shared_identity_core_module_for_host_jit(
        Arc::clone(&source),
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .unwrap();
    let plan = Compiler::new_for_target_spec(
        CompilerConfig::for_host_jit_unchecked(),
        target.target_spec(),
    )
    .with_codegen_license(permit_unlicensed())
    .plan_core_module_for_jit_compilation(admitted)
    .unwrap();
    drop(source);
    assert_eq!(
        weak.strong_count(),
        1,
        "the plan retains the actual module, not a weak identity"
    );
    let plan = std::thread::spawn(move || plan).join().unwrap();
    assert_eq!(allocations(&plan.parts.module), original_allocations);
    assert!(Arc::ptr_eq(&weak.upgrade().unwrap(), &plan.parts.module));
    drop(plan);
    assert!(weak.upgrade().is_none());
}
