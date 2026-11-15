// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordinary TrustIR custody controls, not source or machine-code proofs.

use super::tests::{
    core_host_target, import_manifest, module_with_exact_call, module_with_import,
    self_contained_module,
};
use super::*;

fn allocations(module: &Module) -> [usize; 5] {
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
fn shared_and_owned_core_admission_have_identical_receipts_without_graph_clones() {
    let target = core_host_target();
    let imported = module_with_import();
    let imported_manifest = import_manifest(&imported);
    for (module, manifest) in [
        (self_contained_module(), CoreDeclaredImportManifest::empty()),
        (
            module_with_exact_call(),
            CoreDeclaredImportManifest::empty(),
        ),
        (imported, imported_manifest),
    ] {
        // The independent input clone is a test comparison, not an admission step.
        let owned_input = module.clone();
        let owned_allocations = allocations(&owned_input);
        let owned =
            try_admit_identity_core_module_for_host_jit(owned_input, &target, manifest.clone())
                .expect("ordinary owned Core fixture");
        assert_eq!(allocations(owned.admitted_module()), owned_allocations);
        assert_eq!(Arc::strong_count(&owned.module), 1);

        let mut source = Arc::new(module);
        let original_allocations = allocations(&source);
        let manifest_allocation = manifest.imports.as_ptr();
        let shared = try_admit_shared_identity_core_module_for_host_jit(
            Arc::clone(&source),
            &target,
            manifest,
        )
        .expect("same ordinary shared Core fixture");
        assert!(Arc::ptr_eq(&source, &shared.module));
        assert_eq!(allocations(shared.admitted_module()), original_allocations);
        assert_eq!(
            shared.declared_import_manifest().imports.as_ptr(),
            manifest_allocation
        );
        assert_eq!(shared.receipt(), owned.receipt());
        assert_eq!(
            shared.retained_strict_function_count(),
            owned.retained_strict_function_count()
        );
        assert_eq!(
            shared.retained_lir_proof_context_digest().unwrap(),
            owned.retained_lir_proof_context_digest().unwrap()
        );
        assert_eq!(Arc::strong_count(&source), 2);
        assert!(Arc::get_mut(&mut source).is_none());
        shared.check_consumption_integrity().unwrap();
        drop(shared);
        assert_eq!(Arc::strong_count(&source), 1);
        assert_eq!(allocations(&source), original_allocations);
        assert!(Arc::get_mut(&mut source).is_some());
    }
}

#[test]
fn shared_core_admission_refusal_returns_exact_share_and_manifest_for_retry() {
    let target = core_host_target();
    let source = Arc::new(module_with_import());
    let original_allocations = allocations(&source);
    let manifest = import_manifest(&source);
    let manifest_allocation = manifest.imports.as_ptr();
    let failure =
        crate::env_lock::with_env_overrides(&[("TCG_CORE_ADMISSION_FUTURE_UNKNOWN", "1")], || {
            try_admit_shared_identity_core_module_for_host_jit(
                Arc::clone(&source),
                &target,
                manifest,
            )
            .expect_err("shared custody cannot bypass the compiler-environment gate")
        });
    assert!(
        matches!(failure.reason(), CoreAdmissionError::UnkeyedAmbientCompilerControlsDuringAdmission { controls }
        if controls.iter().any(|name| name == "TCG_CORE_ADMISSION_FUTURE_UNKNOWN"))
    );
    assert!(Arc::ptr_eq(failure.module(), &source));
    assert_eq!(allocations(failure.module()), original_allocations);
    assert_eq!(
        failure.declared_import_manifest().imports.as_ptr(),
        manifest_allocation
    );
    let (_, returned_share, returned_manifest) = failure.into_parts();
    assert!(Arc::ptr_eq(&returned_share, &source));
    assert_eq!(returned_manifest.imports.as_ptr(), manifest_allocation);
    let admitted = try_admit_shared_identity_core_module_for_host_jit(
        returned_share,
        &target,
        returned_manifest,
    )
    .expect("same inputs after the transient environment refusal ends");
    assert!(Arc::ptr_eq(&admitted.module, &source));
    assert_eq!(
        allocations(admitted.admitted_module()),
        original_allocations
    );
    assert_eq!(
        admitted.declared_import_manifest().imports.as_ptr(),
        manifest_allocation
    );
}

#[test]
fn shared_core_admission_keeps_owned_target_validation_and_import_refusals() {
    let target = core_host_target();
    let mut targetless = self_contained_module();
    targetless.target_info = None;
    let mut invalid = self_contained_module();
    invalid.functions[0].ty = trust_ir::FuncTyId::new(999);
    let mut unlegalized = self_contained_module();
    unlegalized
        .types
        .push(Ty::Dialect(Box::new(trust_ir::DialectTy::new(
            "test", "Value", 1,
        ))));
    for (row, module) in [targetless, invalid, unlegalized, module_with_import()]
        .into_iter()
        .enumerate()
    {
        let owned_failure = try_admit_identity_core_module_for_host_jit(
            module.clone(),
            &target,
            CoreDeclaredImportManifest::empty(),
        )
        .expect_err("owned guard control");
        let source = Arc::new(module);
        let failure = try_admit_shared_identity_core_module_for_host_jit(
            Arc::clone(&source),
            &target,
            CoreDeclaredImportManifest::empty(),
        )
        .expect_err("the shared entry point must retain every admission guard");
        match (row, failure.reason()) {
            (0, CoreAdmissionError::Target(CoreTargetContractError::ModuleTargetMissing)) => {}
            (1, CoreAdmissionError::TrustIrValidation { errors }) => assert!(!errors.is_empty()),
            (
                2,
                CoreAdmissionError::ModuleClosure(CoreModuleClosureError::DialectTypeUnsupported {
                    ..
                }),
            ) => {}
            (
                3,
                CoreAdmissionError::ModuleClosure(CoreModuleClosureError::MissingFunction {
                    ..
                }),
            ) => {}
            _ => panic!("wrong refusal for row {row}: {:?}", failure.reason()),
        }
        assert_eq!(
            format!("{:?}", failure.reason()),
            format!("{:?}", owned_failure.reason())
        );
        assert!(Arc::ptr_eq(&source, failure.module()));
    }
}

#[test]
fn external_copy_on_write_cannot_mutate_the_admitted_shared_module() {
    let target = core_host_target();
    let source = Arc::new(self_contained_module());
    let original_allocations = allocations(&source);
    let admitted = try_admit_shared_identity_core_module_for_host_jit(
        Arc::clone(&source),
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .unwrap();
    let mut replacement = Arc::clone(&source);
    assert!(Arc::get_mut(&mut replacement).is_none());
    // This is an adversarial caller's deliberate graph clone, not production.
    Arc::make_mut(&mut replacement).functions[0].blocks[0]
        .body
        .clear();
    assert!(!Arc::ptr_eq(&source, &replacement));
    assert!(Arc::ptr_eq(&source, &admitted.module));
    assert_eq!(
        allocations(admitted.admitted_module()),
        original_allocations
    );
    admitted.check_consumption_integrity().unwrap();
    try_admit_shared_identity_core_module_for_host_jit(
        replacement,
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .expect_err("a mutated copy still needs independent admission");
}

#[test]
fn shared_core_owners_keep_worker_transfer_capability() {
    fn send<T: Send>() {}
    fn send_sync<T: Send + Sync>() {}
    send_sync::<Module>();
    send_sync::<Arc<Module>>();
    send::<CoreAdmittedModule>();
    send::<CoreSharedAdmissionFailure>();
    let target = core_host_target();
    let source = Arc::new(self_contained_module());
    let admitted = try_admit_shared_identity_core_module_for_host_jit(
        Arc::clone(&source),
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .unwrap();
    let admitted = std::thread::spawn(move || admitted).join().unwrap();
    assert!(Arc::ptr_eq(&source, &admitted.module));
    assert_eq!(Arc::strong_count(&source), 2);
}
