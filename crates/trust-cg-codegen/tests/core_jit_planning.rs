// End-to-end coverage for the consuming identity-Core JIT planning boundary.

#![cfg(any(
    all(
        target_arch = "aarch64",
        target_vendor = "apple",
        target_os = "macos",
        target_env = "",
        target_abi = "",
        target_pointer_width = "64",
        target_endian = "little"
    ),
    all(
        target_arch = "aarch64",
        target_vendor = "unknown",
        target_os = "linux",
        target_env = "gnu",
        target_abi = "",
        target_pointer_width = "64",
        target_endian = "little"
    ),
    all(
        target_arch = "x86_64",
        target_vendor = "apple",
        target_os = "macos",
        target_env = "",
        target_abi = "",
        target_pointer_width = "64",
        target_endian = "little"
    ),
    all(
        target_arch = "x86_64",
        target_vendor = "unknown",
        target_os = "linux",
        target_env = "gnu",
        target_abi = "",
        target_pointer_width = "64",
        target_endian = "little"
    ),
    all(
        target_arch = "x86_64",
        target_vendor = "pc",
        target_os = "windows",
        target_env = "msvc",
        target_abi = "",
        target_pointer_width = "64",
        target_endian = "little"
    )
))]

use trust_cg_codegen::compiler::JitValidationMode;
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_codegen::{CLEAN_KERNEL_TV_AUTHORITY, CodegenLicensePolicy, UnlicensedBodyPolicy};
use trust_cg_codegen::{
    CompilePolicyScope, Compiler, CompilerConfig, CompilerTraceLevel, CoreDeclaredImportManifest,
    CoreHostFunctionEffects, CoreHostFunctionImport, CoreHostImport, CoreHostJitTarget,
    CoreHostMemoryEffect, CoreJitCompilationPlan, CoreJitPlanningError,
    CoreLirNativeDependencyBindingCoverage, CoreNativeDependencyOrigin,
    CoreNativeDependencyReferenceCoverage, CoreNativeRuntimeCatalogCoverage,
    CorePermittedNativeMode, CoreRuntimeIdentity, DispatchVerifyMode,
    JitExternalSymbolResolutionPolicy, NativeDependencyId, ProfileHookMode, Target,
    admit_identity_core_module_for_host_jit,
};
use trust_cg_lower::AdapterError;
use trust_ir::proof::ProofDigest;
use trust_ir::{
    Block, BlockId, BodyGate, FuncAttrs, FuncId, FuncTy, Function, Inst, InstrNode, Linkage,
    Module, ParamAttrs, Ty, ValueId,
};

fn host_target() -> CoreHostJitTarget {
    CoreHostJitTarget::detect().expect("supported integration-test host")
}

fn host_target_spec() -> TargetSpec {
    host_target().target_spec()
}

fn self_contained_module(target: &CoreHostJitTarget) -> Module {
    let mut module = Module::new("core-jit-plan-self-contained");
    module.target_info = Some(target.trust_ir_target_info().clone());
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(0), "entry", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    entry.blocks.push(block);
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");
    module
}

fn internal_call_module(target: &CoreHostJitTarget) -> Module {
    let mut module = Module::new("core-jit-plan-internal-call");
    module.target_info = Some(target.trust_ir_target_info().clone());
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut callee = Function::new(FuncId::new(0), "callee", signature, BlockId::new(0));
    callee.linkage = Linkage::Internal;
    let mut callee_block = Block::new(BlockId::new(0));
    callee_block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    callee.blocks.push(callee_block);
    module
        .try_add_function(callee)
        .expect("Module::try_add_function: test fixture");

    let mut entry = Function::new(FuncId::new(1), "entry", signature, BlockId::new(0));
    entry.linkage = Linkage::Internal;
    let mut entry_block = Block::new(BlockId::new(0));
    entry_block.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(0),
        args: vec![],
    }));
    entry_block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    entry.blocks.push(entry_block);
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");
    module
}

fn declared_call_module(target: &CoreHostJitTarget) -> (Module, CoreDeclaredImportManifest) {
    const SYMBOL: &str = "typed_runtime_value";

    let mut module = Module::new("core-jit-plan-declared-call");
    module.target_info = Some(target.trust_ir_target_info().clone());
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U32],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    let mut declaration = Function::new(FuncId::new(7), SYMBOL, signature, BlockId::new(0));
    declaration.linkage = Linkage::External;
    declaration.attrs.readnone = true;
    module
        .try_add_function(declaration)
        .expect("Module::try_add_function: test fixture");

    let mut entry = Function::new(FuncId::new(11), "entry", signature, BlockId::new(0));
    entry.linkage = Linkage::Internal;
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Call {
            callee: FuncId::new(7),
            args: vec![],
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    entry.blocks.push(block);
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");

    let runtime = CoreRuntimeIdentity::try_new(
        "integration-test-runtime",
        ProofDigest::sha256_domain("test.runtime", b"declared identity only"),
    )
    .unwrap();
    let import = CoreHostFunctionImport::try_new(
        SYMBOL,
        module.func_types[signature.as_usize()].clone(),
        module.functions[0].calling_conv,
        normalized_parameter_attrs(&module.functions[0].attrs, 0),
        CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None),
        "integration.typed-value.v1",
        runtime,
    )
    .unwrap();
    let manifest =
        CoreDeclaredImportManifest::try_new(vec![CoreHostImport::Function(import)]).unwrap();
    (module, manifest)
}

fn sparse_declared_call_module(
    target: &CoreHostJitTarget,
    runtime_tag: &[u8],
) -> (Module, CoreDeclaredImportManifest) {
    let mut module = Module::new("core-jit-plan-sparse-declared-calls");
    module.target_info = Some(target.trust_ir_target_info().clone());
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");

    // Deliberately neither dense nor aligned with canonical manifest order.
    let mut zeta = Function::new(FuncId::new(7), "zeta_runtime", signature, BlockId::new(0));
    zeta.linkage = Linkage::External;
    zeta.attrs.readnone = true;
    module
        .try_add_function(zeta)
        .expect("Module::try_add_function: test fixture");
    let mut alpha = Function::new(FuncId::new(42), "alpha_runtime", signature, BlockId::new(0));
    alpha.linkage = Linkage::External;
    alpha.attrs.readnone = true;
    module
        .try_add_function(alpha)
        .expect("Module::try_add_function: test fixture");

    let mut entry = Function::new(FuncId::new(100), "entry", signature, BlockId::new(9));
    entry.linkage = Linkage::Internal;
    let mut block = Block::new(BlockId::new(9));
    block.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(7),
        args: vec![],
    }));
    block.body.push(InstrNode::new(Inst::Call {
        callee: FuncId::new(42),
        args: vec![],
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    entry.blocks.push(block);
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");

    let runtime = CoreRuntimeIdentity::try_new(
        "sparse-integration-runtime",
        ProofDigest::sha256_domain("test.sparse-runtime", runtime_tag),
    )
    .unwrap();
    let make_import = |function: &Function| {
        CoreHostImport::Function(
            CoreHostFunctionImport::try_new(
                function.name.clone(),
                module.func_types[function.ty.as_usize()].clone(),
                function.calling_conv,
                normalized_parameter_attrs(&function.attrs, 0),
                CoreHostFunctionEffects::deterministic(CoreHostMemoryEffect::None),
                "integration.sparse.v1",
                runtime.clone(),
            )
            .unwrap(),
        )
    };
    // Supply reverse alphabetical order; the manifest must canonicalize it.
    let manifest = CoreDeclaredImportManifest::try_new(vec![
        make_import(&module.functions[0]),
        make_import(&module.functions[1]),
    ])
    .unwrap();
    (module, manifest)
}

fn normalized_parameter_attrs(attrs: &FuncAttrs, arity: usize) -> Vec<ParamAttrs> {
    (0..arity)
        .map(|index| attrs.params.get(index).cloned().unwrap_or_default())
        .collect()
}

fn compiler_config(
    external_symbol_resolution: JitExternalSymbolResolutionPolicy,
) -> CompilerConfig {
    CompilerConfig {
        jit_external_symbol_resolution: external_symbol_resolution,
        ..CompilerConfig::for_host_jit_unchecked()
    }
}

/// The fixtures here are hand-built and carry no codegen license
/// (`body_gate: None`), which the compiler's DEFAULT policy refuses at plan
/// time (roadmap WS7.5, DG-73; admission only DEFERS it). The planning tests
/// therefore state `Permit`; [`default_compiler`] pins the default.
fn compiler(external_symbol_resolution: JitExternalSymbolResolutionPolicy) -> Compiler {
    default_compiler(external_symbol_resolution).with_codegen_license(
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit),
    )
}

/// The stated `Permit` of [`compiler`], for the tests that build their own
/// [`Compiler`] (a foreign target, explicit options).
fn permit_unlicensed() -> CodegenLicensePolicy {
    CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Permit)
}

/// [`compiler`] under the compiler's OWN default license policy.
fn default_compiler(external_symbol_resolution: JitExternalSymbolResolutionPolicy) -> Compiler {
    Compiler::new_for_target_spec(
        compiler_config(external_symbol_resolution),
        host_target_spec(),
    )
}

fn admit_self_contained() -> trust_cg_codegen::CoreAdmittedModule {
    let target = host_target();
    admit_identity_core_module_for_host_jit(
        self_contained_module(&target),
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .expect("self-contained fixture must pass identity-Core admission")
}

#[test]
fn plan_is_send_for_parallel_compile_workers() {
    fn assert_send<T: Send>() {}

    assert_send::<CoreJitCompilationPlan>();
}

#[test]
fn plan_consumes_core_and_seals_forced_policy() {
    let core = admit_self_contained();
    let admitted_profile = core.target_contract().host_jit_machine_profile();
    let admitted_digest = core.module_digest();
    let plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitThenProcess)
        .plan_core_module_for_jit_compilation(core)
        .expect("admitted self-contained Core module must produce an opaque plan");

    assert_eq!(plan.module_name(), "core-jit-plan-self-contained");
    assert_eq!(plan.module_digest(), admitted_digest);
    assert_eq!(
        plan.permitted_native_mode(),
        CorePermittedNativeMode::ClosedHostJit
    );
    assert_eq!(plan.effective_options().machine_profile(), admitted_profile);
    assert_eq!(plan.effective_options().target_spec(), host_target_spec());
    assert!(plan.effective_options().fast_regalloc());
    assert_eq!(
        plan.effective_options().external_symbol_resolution(),
        JitExternalSymbolResolutionPolicy::ExplicitOnly
    );
    assert_eq!(
        plan.effective_options().compile_policy().scope(),
        CompilePolicyScope::Combined
    );
    assert_eq!(
        plan.effective_options().compile_policy().target_spec(),
        host_target_spec()
    );
    assert_eq!(plan.retained_strict_function_count(), 1);
    assert_eq!(plan.retained_exact_module_call_count(), 0);
    assert!(plan.native_runtime_catalog().is_empty());
    assert_eq!(
        plan.native_runtime_catalog().coverage(),
        CoreNativeRuntimeCatalogCoverage::DeclaredImportsOnly
    );
    let references = plan.native_dependency_references();
    assert!(references.is_empty());
    assert!(references.is_intact());
    assert_eq!(references.core_module_digest(), plan.module_digest());
    assert_eq!(
        references.identity_transform_receipt_digest(),
        plan.admission_receipt().receipt_digest()
    );
    assert_eq!(
        references.native_runtime_catalog_digest(),
        plan.native_runtime_catalog().digest()
    );
    assert_eq!(
        references.coverage(),
        CoreNativeDependencyReferenceCoverage::DeclaredTrustIrFunctionIdentitiesOnly
    );
}

#[test]
fn plan_preserves_one_exact_internal_call_with_target_authority() {
    let target = host_target();
    let core = admit_identity_core_module_for_host_jit(
        internal_call_module(&target),
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .expect("defined internal call must pass exact-call replay");
    let target_digest = core.receipt().target_contract_digest();
    let profile = target.machine_profile();
    let plan = Compiler::new_for_target_spec(
        compiler_config(JitExternalSymbolResolutionPolicy::ExplicitOnly),
        target.target_spec(),
    )
    .with_codegen_license(permit_unlicensed())
    .plan_core_module_for_jit_compilation(core)
    .expect("sealed exact-call owner must survive the consuming plan split");

    assert_eq!(plan.retained_strict_function_count(), 2);
    assert_eq!(plan.retained_exact_module_call_count(), 1);
    assert_eq!(plan.target_contract().digest(), target_digest);
    assert_eq!(plan.effective_options().machine_profile(), profile);
    assert_eq!(plan.effective_options().target_spec(), target.target_spec());
    assert!(plan.native_dependency_references().is_empty());
}

#[test]
fn plan_forces_explicit_only_inside_the_canonical_policy() {
    let compatibility_plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitThenProcess)
        .plan_core_module_for_jit_compilation(admit_self_contained())
        .unwrap();
    let explicit_plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(admit_self_contained())
        .unwrap();

    assert_eq!(
        compatibility_plan.effective_options(),
        explicit_plan.effective_options(),
        "the compatibility resolver setting must be narrowed before policy hashing"
    );
    assert_eq!(
        compatibility_plan
            .effective_options()
            .compile_policy_digests(),
        explicit_plan.effective_options().compile_policy_digests()
    );
}

#[test]
fn plan_retains_complete_nondefault_explicit_options() {
    let mut config = compiler_config(JitExternalSymbolResolutionPolicy::ExplicitThenProcess);
    config.opt_level = OptLevel::O3;
    config.emit_proofs = true;
    config.trace_level = CompilerTraceLevel::Full;
    config.emit_debug = true;
    config.parallel = true;
    config.cegis_superopt_budget_sec = Some(17);
    config.enable_fsym_trust_ir_preflight = true;
    config.enable_jit_fast_regalloc = false;
    config.panic_unwind = true;
    let plan = Compiler::new_for_target_spec(config, host_target_spec())
        .with_codegen_license(permit_unlicensed())
        .plan_core_module_for_jit_compilation(admit_self_contained())
        .expect("explicit options must be sealed without running codegen");

    let options = plan.effective_options();
    assert_eq!(options.opt_level(), OptLevel::O3);
    assert!(options.emit_proofs());
    assert_eq!(options.trace_level(), CompilerTraceLevel::Full);
    assert!(options.emit_debug());
    assert!(options.parallel());
    assert_eq!(options.cegis_superopt_budget_sec(), Some(17));
    assert!(options.fsym_trust_ir_preflight_enabled());
    assert!(!options.fast_regalloc());
    assert!(options.panic_unwind());
    assert_eq!(options.validation_mode(), JitValidationMode::Unchecked);
    assert_eq!(
        options.configured_jit_validation_override(),
        Some(JitValidationMode::Unchecked)
    );
    assert!(!options.jit_verification_enabled());
    assert_eq!(options.jit_opt_level(), OptLevel::O3);
    assert_eq!(
        options.jit_dispatch_verification(),
        DispatchVerifyMode::ErrorOnFailure
    );
    assert_eq!(options.jit_profile_hooks(), ProfileHookMode::None);
    assert!(!options.jit_entry_counters_enabled());
    assert!(!options.jit_certificate_cache_enabled());
    assert_eq!(
        options.external_symbol_resolution(),
        JitExternalSymbolResolutionPolicy::ExplicitOnly
    );

    let baseline = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(admit_self_contained())
        .unwrap();
    assert_ne!(
        options.compile_policy_digests(),
        baseline.effective_options().compile_policy_digests(),
        "the complete non-default option set must affect canonical identity"
    );
}

#[test]
fn plan_retains_declared_imports_without_accepting_or_resolving_addresses() {
    let target = host_target();
    let (module, manifest) = declared_call_module(&target);
    let core = admit_identity_core_module_for_host_jit(module, &target, manifest)
        .expect("typed ordinary import must pass structural Core admission");

    // The planning API deliberately accepts only the admitted owner. There is
    // no address map, target codegen, resolution, or executable publication.
    let plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitThenProcess)
        .plan_core_module_for_jit_compilation(core)
        .expect("declared imports are retained for a later typed resolution boundary");

    assert_eq!(plan.declared_import_manifest().imports().len(), 1);
    let catalog = plan.native_runtime_catalog();
    assert_eq!(catalog.entries().len(), 1);
    assert_eq!(
        catalog.declared_import_manifest_digest(),
        plan.declared_import_manifest().digest()
    );
    let dependency = catalog
        .get(NativeDependencyId::new(0))
        .expect("the canonical declared import must receive the first catalog ID");
    assert_eq!(dependency.symbol(), "typed_runtime_value");
    assert_eq!(
        dependency.origin(),
        CoreNativeDependencyOrigin::DeclaredTrustIrImport
    );
    assert!(!catalog.digest().is_zero());
    let references = plan.native_dependency_references();
    assert_eq!(references.entries().len(), 1);
    assert_eq!(references.core_module_digest(), plan.module_digest());
    assert_eq!(
        references.identity_transform_receipt_digest(),
        plan.admission_receipt().receipt_digest()
    );
    assert_eq!(references.native_runtime_catalog_digest(), catalog.digest());
    assert_eq!(
        references.coverage(),
        CoreNativeDependencyReferenceCoverage::DeclaredTrustIrFunctionIdentitiesOnly
    );
    assert!(references.is_intact());
    let reference = references.entries()[0];
    assert_eq!(reference.function(), FuncId::new(7));
    assert_eq!(reference.dependency(), NativeDependencyId::new(0));
    assert_eq!(
        references.dependency_for_function(FuncId::new(7)),
        Some(NativeDependencyId::new(0))
    );
    assert_eq!(references.dependency_for_function(FuncId::new(0)), None);
    let bindings = plan.lir_native_dependency_bindings();
    assert!(bindings.is_intact());
    assert_eq!(bindings.entries().len(), 1);
    assert_eq!(
        bindings.coverage(),
        CoreLirNativeDependencyBindingCoverage::DeclaredTrustIrDirectCallsOnly
    );
    assert_eq!(bindings.core_module_digest(), plan.module_digest());
    assert_eq!(
        bindings.identity_transform_receipt_digest(),
        plan.admission_receipt().receipt_digest()
    );
    assert_eq!(bindings.native_runtime_catalog_digest(), catalog.digest());
    assert_eq!(
        bindings.native_dependency_reference_map_digest(),
        references.digest()
    );
    assert_eq!(bindings.entries()[0].caller(), FuncId::new(11));
    assert_eq!(bindings.entries()[0].imported_function(), FuncId::new(7));
    assert_eq!(
        bindings.entries()[0].dependency(),
        NativeDependencyId::new(0)
    );
    assert!(!plan.identity().artifact_cache_digest().is_zero());
    assert!(!plan.identity().verification_digest().is_zero());
    assert!(!plan.identity().full_digest().is_zero());
    assert_eq!(
        plan.retained_exact_module_call_count(),
        0,
        "host imports are typed manifest edges, not exact module-local calls"
    );
    assert_eq!(
        plan.effective_options().external_symbol_resolution(),
        JitExternalSymbolResolutionPolicy::ExplicitOnly
    );
}

#[test]
fn non_self_sparse_import_ids_and_call_order_bind_only_through_the_sealed_map() {
    let target = host_target();
    let (module, manifest) = sparse_declared_call_module(&target, b"image-a");
    let repeated_module = module.clone();
    let repeated_manifest = manifest.clone();
    let core = admit_identity_core_module_for_host_jit(module, &target, manifest).unwrap();
    assert_eq!(core.retained_declared_external_call_count(), 2);
    let plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(core)
        .unwrap();

    let references = plan.native_dependency_references();
    // Canonical manifest order is alpha then zeta, independent of FuncId and
    // source declaration/call order.
    assert_eq!(
        references.dependency_for_function(FuncId::new(42)),
        Some(NativeDependencyId::new(0))
    );
    assert_eq!(
        references.dependency_for_function(FuncId::new(7)),
        Some(NativeDependencyId::new(1))
    );
    let entries = plan.lir_native_dependency_bindings().entries();
    assert_eq!(entries.len(), 2);
    assert_eq!(entries[0].caller(), FuncId::new(100));
    assert_eq!(entries[0].imported_function(), FuncId::new(7));
    assert_eq!(entries[0].dependency(), NativeDependencyId::new(1));
    assert_eq!(entries[1].imported_function(), FuncId::new(42));
    assert_eq!(entries[1].dependency(), NativeDependencyId::new(0));
    assert_ne!(entries[0].edge_digest(), entries[1].edge_digest());

    let repeated = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(
            admit_identity_core_module_for_host_jit(repeated_module, &target, repeated_manifest)
                .unwrap(),
        )
        .unwrap();
    assert_eq!(
        plan.lir_native_dependency_bindings().digest(),
        repeated.lir_native_dependency_bindings().digest(),
        "independent HashMap seeds must not perturb canonical binding order or digest"
    );
    assert_eq!(plan.identity(), repeated.identity());
}

#[test]
fn runtime_catalog_digest_changes_binding_and_plan_identities() {
    let target = host_target();
    let (module_a, manifest_a) = sparse_declared_call_module(&target, b"image-a");
    let (module_b, manifest_b) = sparse_declared_call_module(&target, b"image-b");
    assert_eq!(module_a.stable_digest(), module_b.stable_digest());

    let plan_a = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(
            admit_identity_core_module_for_host_jit(module_a, &target, manifest_a).unwrap(),
        )
        .unwrap();
    let plan_b = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(
            admit_identity_core_module_for_host_jit(module_b, &target, manifest_b).unwrap(),
        )
        .unwrap();

    assert_ne!(
        plan_a.native_runtime_catalog().digest(),
        plan_b.native_runtime_catalog().digest()
    );
    assert_ne!(
        plan_a.lir_native_dependency_bindings().digest(),
        plan_b.lir_native_dependency_bindings().digest()
    );
    assert_ne!(
        plan_a.identity().artifact_cache_digest(),
        plan_b.identity().artifact_cache_digest()
    );
    assert_ne!(
        plan_a.identity().verification_digest(),
        plan_b.identity().verification_digest()
    );
}

#[test]
fn plan_rejects_compiler_target_drift() {
    let core = admit_self_contained();
    let module_digest = core.module_digest();
    let admitted = core.target_contract().target_spec();
    let foreign = match admitted.architecture {
        Target::Aarch64 => TargetSpec::parse("x86_64-unknown-linux-gnu").unwrap(),
        Target::X86_64 => TargetSpec::parse("aarch64-apple-darwin").unwrap(),
        Target::Riscv64 => unreachable!("Core admission rejects this host"),
    };
    let foreign_compiler =
        Compiler::new_for_target_spec(CompilerConfig::for_host_jit_unchecked(), foreign)
            .with_codegen_license(permit_unlicensed());

    let failure = foreign_compiler
        .plan_core_module_for_jit_compilation(core)
        .expect_err("foreign target must fail without consuming the Core owner");
    assert!(matches!(
        failure.reason(),
        CoreJitPlanningError::TargetMismatch {
            admitted: actual_admitted,
            compiler: actual_compiler,
        } if *actual_admitted == admitted && *actual_compiler == foreign
    ));
    assert_eq!(failure.core().module_digest(), module_digest);

    let (_, recovered_core) = failure.into_parts();
    let plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(recovered_core)
        .expect("the exact returned owner must be retryable with the matching compiler");
    assert_eq!(plan.module_digest(), module_digest);
}

#[test]
fn plan_rejects_unknown_ambient_compiler_controls() {
    let core = admit_self_contained();
    let error = trust_cg_codegen::env_lock::with_env_overrides(
        &[("TCG_CORE_PLAN_FUTURE_UNKNOWN", "1")],
        move || {
            compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
                .plan_core_module_for_jit_compilation(core)
                .expect_err("unknown compiler controls must fail closed")
        },
    );
    assert!(matches!(
        error.reason(),
        CoreJitPlanningError::UnkeyedAmbientCompilerControls { controls }
            if controls.iter().any(|name| name == "TCG_CORE_PLAN_FUTURE_UNKNOWN")
    ));
}

/// Core admission lowers under the license FLOOR (`Ungated`, unrecognized
/// authorities, and a `Gated` body without its evidence refused; a
/// claim-less body DEFERRED under the named `CoreAdmissionFloor` exception).
/// The compiler re-decides the whole license on the admitted module at plan
/// time — its DEFAULT refusing the claim-less body (roadmap WS7.5, DG-73) —
/// so no policy is silently ignored on the one compile entry that consumes an
/// admitted Core.
#[test]
fn plan_enforces_the_compiler_codegen_license_on_the_admitted_module() {
    // `body_gate: None` (no claim): admitted under the floor, refused by the
    // DEFAULT compiler (and by an explicit `Refuse`), and the owner comes back.
    let core = admit_self_contained();
    let module_digest = core.module_digest();
    let failure = default_compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(core)
        .expect_err("the default compiler refuses a claim-less body at plan time");
    assert!(
        matches!(
            failure.reason(),
            CoreJitPlanningError::CodegenLicense(AdapterError::UnlicensedBody { function })
                if function == "entry"
        ),
        "{:?}",
        failure.reason()
    );
    let (_, core) = failure.into_parts();
    let refusing = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly).with_codegen_license(
        CodegenLicensePolicy::default().with_unlicensed(UnlicensedBodyPolicy::Refuse),
    );
    let failure = refusing
        .plan_core_module_for_jit_compilation(core)
        .expect_err("a compiler refusing unlicensed bodies must refuse at plan time");
    assert!(
        matches!(
            failure.reason(),
            CoreJitPlanningError::CodegenLicense(AdapterError::UnlicensedBody { function })
                if function == "entry"
        ),
        "{:?}",
        failure.reason()
    );
    assert_eq!(failure.core().module_digest(), module_digest);
    let (_, recovered_core) = failure.into_parts();
    let plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(recovered_core)
        .expect("an explicit Permit compiler plans the claim-less body");
    assert_eq!(plan.module_digest(), module_digest);

    // `Gated { clean-kernel-tv }`: the default floor recognizes it — and it
    // is EVIDENCE-BOUND (trust-ir WS1.5): with no kernel-rechecked
    // TranslationValidation certificate the strict adapter refuses it at
    // admission, before any policy is consulted, as trust-ir's
    // `GatedWithoutEvidence` (KIND 4, 2026-09-24; corpus row
    // `body_gate_kernel_tv_without_certificate`). Recognition never stands
    // in for the evidence, so no admitted core can carry a `Gated` body
    // under the one default-recognized authority without a kernel
    // certificate; the plan-stage refusal of an UNRECOGNIZED authority is
    // exercised on the strict entries by trust-cg-lower
    // `tests/v41_codegen_license.rs`.
    let target = host_target();
    let mut module = self_contained_module(&target);
    module.functions[0].body_gate = Some(BodyGate::gated(CLEAN_KERNEL_TV_AUTHORITY.to_string()));
    let failure = admit_identity_core_module_for_host_jit(
        module,
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .expect_err("an evidence-bound license without its evidence is refused at admission");
    let text = format!("{failure:?}");
    assert!(
        text.contains("GatedWithoutEvidence") && text.contains(CLEAN_KERNEL_TV_AUTHORITY),
        "{text}"
    );
}

/// Core admission does not run the backend-symbol finder: Core can never bind
/// a call the backend makes by name to a module body. A module-local `fmod`
/// beside `frem` is admitted and planned, but proof-grade qualification
/// refuses it (the backend's `fmod` call carries no source call origin), and
/// had it qualified, address-free compilation refuses any by-name fixup to a
/// module definition (`InterposableModuleFixup`). The row fails if the module
/// ever reaches executable machine code. An Internal body named `memcpy` that
/// is only called exactly is admitted and plans like any exact call.
#[test]
fn core_never_binds_a_backend_call_to_a_module_body() {
    let target = host_target();
    let parse = |text: &str| {
        let mut module = trust_ir::parser::parse_module(text)
            .unwrap_or_else(|error| panic!("fixture parses: {error:?}"));
        module.target_info = Some(target.trust_ir_target_info().clone());
        module
    };
    let shadowing = parse(
        "module \"core_frem\"\nfuncty.0 = (f64, f64) -> (f64)\n\
         internal fn @fmod(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = const f64 42.0\n    ret %2\n}\n\
         fn @entry(functy.0) {\nbb0(%0: f64, %1: f64):\n    %2 = frem f64 %0, %1\n    ret %2\n}\n",
    );
    let core = admit_identity_core_module_for_host_jit(
        shadowing,
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .expect("admission leaves backend calls to the plan checks");
    let plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(core)
        .expect("planning leaves backend calls to qualification");
    let failure = plan
        .qualify_for_proof_grade_compilation()
        .expect_err("the backend's fmod call has no source call origin");
    let reason = format!("{:?}", failure.reason());
    assert!(
        reason.contains("LirCallSourceOriginMismatch")
            || reason.contains("LirCallMissingSourceOrigin"),
        "{reason}"
    );

    let exact = parse(
        "module \"core_memcpy\"\nfuncty.0 = () -> ()\n\
         internal fn @memcpy(functy.0) {\nbb0:\n    ret\n}\n\
         fn @entry(functy.0) {\nbb0:\n    call @func.0()\n    ret\n}\n",
    );
    let core = admit_identity_core_module_for_host_jit(
        exact,
        &target,
        CoreDeclaredImportManifest::empty(),
    )
    .expect("an exactly called Internal body owns its semantics whatever its name");
    let plan = compiler(JitExternalSymbolResolutionPolicy::ExplicitOnly)
        .plan_core_module_for_jit_compilation(core)
        .expect("the exact call plans");
    assert_eq!(plan.retained_exact_module_call_count(), 1);
}

/// Calls the backend makes below LIR, in instruction selection and frame
/// lowering, never reach a module body in Core either: the i128 division
/// helpers, an aggregate copy's `memcpy` and the stack protector's
/// `__stack_chk_fail` have no retained LIR call occurrence, so address-free
/// compilation refuses their fixup (`FixupOccurrenceMismatch`), whether or
/// not the module defines the name, at O0, O2 and O3. (Proof-grade
/// qualification cannot see them: they are not LIR calls.)
#[test]
fn core_refuses_backend_calls_made_below_lir() {
    let target = host_target();
    let parse = |text: &str| {
        let mut module = trust_ir::parser::parse_module(text)
            .unwrap_or_else(|error| panic!("fixture parses: {error:?}"));
        module.target_info = Some(target.trust_ir_target_info().clone());
        module
    };
    let divti3 = "module \"core_divti3\"\nfuncty.0 = (i128, i128) -> (i128)\n\
                  fn @entry(functy.0) {\nbb0(%0: i128, %1: i128):\n    %2 = sdiv i128 %0, %1\n    ret %2\n}\n";
    let local_divti3 = "internal fn @__divti3(functy.0) {\nbb0(%0: i128, %1: i128):\n    %2 = const i128 42\n    ret %2\n}\n";
    let aggregate = "module \"core_aggregate\"\nstruct @S { f0: i64, f1: i64, f2: i64, f3: i64, f4: i64, f5: i64, f6: i64, f7: i64 } id=0\n\
                     functy.0 = (ptr, ptr, i64) -> (ptr)\nfunctty.1 = (ptr, ptr) -> ()\n\
                     fn @entry(functy.1) {\nbb0(%0: ptr, %1: ptr):\n    %2 = load struct.0, ptr %1\n    store struct.0 %2, ptr %0\n    ret\n}\n"
        .replace("functty", "functy");
    let local_memcpy =
        "internal fn @memcpy(functy.0) {\nbb0(%0: ptr, %1: ptr, %2: i64):\n    ret %0\n}\n";
    let protector = "module \"core_protector\"\nfuncty.0 = (i64) -> (i64)\nfuncty.1 = () -> ()\n\
                     fn @entry(functy.0) {\n    ; #proof: custom(5460817)\nbb0(%0: i64):\n    %1 = alloca i64\n    store i64 %0, ptr %1\n    %2 = load i64, ptr %1\n    ret %2\n}\n";
    let local_fail = "internal fn @__stack_chk_fail(functy.1) {\nbb0:\n    ret\n}\n";
    let cases = [
        ("i128 division", divti3.to_string()),
        (
            "i128 division beside __divti3",
            format!("{divti3}{local_divti3}"),
        ),
        ("aggregate copy", aggregate.clone()),
        (
            "aggregate copy beside memcpy",
            format!("{aggregate}{local_memcpy}"),
        ),
        ("stack protector", protector.to_string()),
        (
            "stack protector beside __stack_chk_fail",
            format!("{protector}{local_fail}"),
        ),
    ];
    for (label, text) in &cases {
        for opt_level in [OptLevel::O0, OptLevel::O2, OptLevel::O3] {
            let core = admit_identity_core_module_for_host_jit(
                parse(text),
                &target,
                CoreDeclaredImportManifest::empty(),
            )
            .unwrap_or_else(|error| panic!("{label}: admission: {error}"));
            // Proof-grade qualification needs a verifying validation mode.
            let plan = Compiler::new_for_target_spec(
                CompilerConfig {
                    opt_level,
                    emit_proofs: true,
                    jit_validation_mode_override: Some(JitValidationMode::AlwaysVerify),
                    jit_external_symbol_resolution: JitExternalSymbolResolutionPolicy::ExplicitOnly,
                    ..CompilerConfig::for_host_jit()
                },
                target.target_spec(),
            )
            .with_codegen_license(permit_unlicensed())
            .plan_core_module_for_jit_compilation(core)
            .unwrap_or_else(|failure| panic!("{label} {opt_level:?}: plan: {failure:?}"));
            let qualified = plan
                .qualify_for_proof_grade_compilation()
                .unwrap_or_else(|failure| panic!("{label} {opt_level:?}: qualify: {failure:?}"));
            let failure = qualified
                .compile_to_address_free_machine()
                .expect_err("a call made below LIR has no retained call occurrence");
            let (error, _) = failure.into_parts();
            let error = format!("{error:?}");
            assert!(
                error.contains("FixupOccurrenceMismatch"),
                "{label} {opt_level:?}: {error}"
            );
        }
    }
}
