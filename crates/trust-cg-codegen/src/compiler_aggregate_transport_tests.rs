// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use crate::core_admission::*;
use trust_ir::{FieldDef, StructDef, StructId, StructRepr, Ty};
use trust_ir_build::ModuleBuilder;

fn ordinary_plan(level: OptLevel, mode: JitValidationMode) -> CoreJitCompilationPlan {
    let target = CoreHostJitTarget::detect().unwrap();
    let mut m = ModuleBuilder::new_with_target_info(
        "ordinary_sealed_aggregate",
        target.trust_ir_target_info().clone(),
    );
    let record = m.add_struct(StructDef {
        id: StructId::new(0),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "status".into(),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "value".into(),
                ty: Ty::I64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: None,
    });
    let declaration = trust_ir::FuncTy {
        params: vec![Ty::Ptr, Ty::U64],
        returns: vec![Ty::Struct(record)],
        abi: None,
        is_vararg: false,
    };
    let ty = m.add_func_type(declaration.params.clone(), declaration.returns.clone());
    let provider = m.declare_function("ordinary_pair_provider", ty);
    let ty = m.add_func_type(vec![Ty::Ptr, Ty::U64, Ty::Ptr], vec![]);
    let mut f = m.function("ordinary_pair_store_wrapper", ty);
    let b = f.create_block();
    let context = f.add_block_param(b, Ty::Ptr);
    let input = f.add_block_param(b, Ty::U64);
    let output = f.add_block_param(b, Ty::Ptr);
    f.switch_to_block(b);
    let result = f.call(provider, vec![context, input]);
    let first = f.extract_field(Ty::U64, result, 0);
    let second = f.extract_field(Ty::I64, result, 1);
    f.store(Ty::U64, output, first);
    let one = f.iconst(Ty::U64, 1);
    let next = f.gep(Ty::I64, output, vec![one]);
    f.store(Ty::I64, next, second);
    f.ret(vec![]);
    f.build();
    let module = m.build().unwrap();
    // Deliberately OpaqueRW and nondeterministic, with normality outstanding.
    // This declaration is not a proved provider implementation or ABI lease.
    let import = CoreHostFunctionImport::try_new(
        "ordinary_pair_provider",
        declaration,
        trust_ir::CallingConv::C,
        vec![trust_ir::ParamAttrs::default(); 2],
        CoreHostFunctionEffects {
            memory: CoreHostMemoryEffect::ReadWrite,
            may_unwind: false,
            may_not_return: true,
            determinism: CoreHostDeterminism::Nondeterministic,
        },
        "ordinary.pending-aggregate.v1",
        CoreRuntimeIdentity::try_new(
            "ordinary-test-provider",
            trust_ir::proof::ProofDigest::sha256_domain(
                "test.aggregate",
                b"unrefined provider identity",
            ),
        )
        .unwrap(),
    )
    .unwrap();
    let manifest =
        CoreDeclaredImportManifest::try_new(vec![CoreHostImport::Function(import)]).unwrap();
    let core = admit_identity_core_module_for_host_jit(module, &target, manifest).unwrap();
    let mut config = CompilerConfig::for_host_jit();
    config.opt_level = level;
    config.emit_proofs = mode == JitValidationMode::AlwaysVerify;
    config.jit_validation_mode_override = Some(mode);
    config.jit_external_symbol_resolution = JitExternalSymbolResolutionPolicy::ExplicitOnly;
    Compiler::new_for_target_spec(config, target.target_spec())
        .with_codegen_license(
            trust_cg_lower::codegen_license::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::codegen_license::UnlicensedBodyPolicy::Permit),
        )
        .plan_core_module_for_jit_compilation(core)
        .unwrap()
}

#[test]
fn aggregate_transport_ordinary_sealed_core_o0_o2_preserves_nonexecutable_boundary() {
    for level in [OptLevel::O0, OptLevel::O2] {
        let plan = ordinary_plan(level, JitValidationMode::Unchecked);
        let rows = plan.inspect_aggregate_result_transports().unwrap();
        assert_eq!(rows.functions().len(), 1);
        let row = &rows.functions()[0];
        assert_eq!(row.fields().len(), 2);
        assert_eq!(row.materializations().len(), 1);
        assert_eq!(
            row.materializations()[0].plan().intent().layout().bytes(),
            16
        );
        assert_eq!(
            row.materializations()[0]
                .plan()
                .unresolved_requirements()
                .len(),
            6
        );
        let failure = plan.qualify_for_proof_grade_compilation().unwrap_err();
        assert!(matches!(
            failure.reason(),
            CoreJitProofGradeQualificationError::ValidationMode {
                actual: JitValidationMode::Unchecked
            }
        ));
        println!(
            "ORDINARY_AGGREGATE_TRANSPORT {level:?} calls=1 fields=2 OpaqueRW=true nondeterministic=true normality_outstanding=true native_calls=0 Unchecked_nonexecutable=true"
        );
    }
}

#[test]
fn aggregate_transport_sealed_census_and_retained_mutants_refuse() {
    let mut plan = ordinary_plan(OptLevel::O0, JitValidationMode::Unchecked);
    let (lir, context) = &mut plan.parts.lir_functions[0];
    let call = context.aggregate_call_intents.calls()[0].clone();
    if let trust_cg_lower::instructions::Opcode::Call { binding, .. } =
        &mut lir.blocks.get_mut(&call.lir_block()).unwrap().instructions[call.lir_instruction()]
            .opcode
    {
        *binding = trust_cg_lower::instructions::DirectCallBinding::NativeDependency {
            function: call.callee().index(),
            dependency: trust_cg_ir::NativeDependencyId::new(99),
        };
    } else {
        panic!("actual call");
    }
    assert!(plan.inspect_aggregate_result_transports().is_err());
    let mut plan = ordinary_plan(OptLevel::O0, JitValidationMode::Unchecked);
    plan.parts.lir_functions[0].1.aggregate_call_intents = Default::default();
    assert!(plan.inspect_aggregate_result_transports().is_err());
    let mut plan = ordinary_plan(OptLevel::O0, JitValidationMode::Unchecked);
    std::sync::Arc::make_mut(&mut plan.parts.module).structs[0]
        .fields
        .swap(0, 1);
    assert!(plan.inspect_aggregate_result_transports().is_err());
}

#[test]
fn aggregate_transport_ordinary_proof_grade_machine_frontier_remains_closed() {
    for level in [OptLevel::O0, OptLevel::O2] {
        let plan = ordinary_plan(level, JitValidationMode::AlwaysVerify);
        let rows = plan.inspect_aggregate_result_transports().unwrap();
        assert_eq!(rows.functions()[0].materializations().len(), 1);
        let qualified = plan.qualify_for_proof_grade_compilation().unwrap();
        let failure = qualified.compile_to_address_free_machine().unwrap_err();
        println!(
            "ORDINARY_AGGREGATE_NATIVE_REFUSAL {level:?} artifacts=0 executed_calls=0 failure={failure}"
        );
        assert!(matches!(
            failure.reason(),
            CoreAddressFreeMachineCompilationError::Compile(_)
                | CoreAddressFreeMachineCompilationError::PlanIntegrity(_)
        ));
    }
}

#[test]
fn aggregate_transport_unused_original_payload_is_bounded_before_plan_hashing() {
    let mut plan = ordinary_plan(OptLevel::O0, JitValidationMode::Unchecked);
    std::sync::Arc::make_mut(&mut plan.parts.module).name = "x".repeat(4 * 1024 * 1024 + 1);
    assert!(matches!(
        plan.inspect_aggregate_result_transports(),
        Err(CoreAggregateResultTransportError::Binding(
            "aggregate complete original inventory"
        ))
    ));
}

#[test]
fn native_aggregate_source_event_ordinary_sealed_consumer_retains_world_and_frontier() {
    for level in [OptLevel::O0, OptLevel::O2] {
        let plan = ordinary_plan(level, JitValidationMode::Unchecked);
        let observed = plan
            .observe_native_aggregate_source_events("ordinary_pair_store_wrapper")
            .unwrap();
        assert_eq!(observed.plan_identity(), plan.identity());
        let source = observed.source_events();
        assert_eq!(source.events().len(), 1);
        assert_eq!(source.writes().len(), 2);
        let event = &source.events()[0];
        assert_ne!(event.prior_world(), event.post_world());
        assert_eq!(
            event.record().layout().fields(),
            &[
                trust_cg_lower::aggregate_call_transport::AggregateFieldCodec::Unsigned64,
                trust_cg_lower::aggregate_call_transport::AggregateFieldCodec::Signed64,
            ]
        );
        assert_eq!(event.outstanding_requirements().len(), 6);
        assert!(
            source
                .retained_field_load_frontier()
                .to_string()
                .contains("source/private-world ownership")
        );
        println!(
            "NATIVE_AGGREGATE_SOURCE_ORDINARY {level:?} events=1 Struct_results=1 fields=2 writes=2 distinct_full_post_world=true normality_outstanding=true target_loads_refused=true aggregate_proofs=0 native_calls=0"
        );
    }
}

#[test]
fn native_aggregate_target_ordinary_o0_o2_retains_pending_architectural_state() {
    for level in [OptLevel::O0, OptLevel::O2] {
        let plan = ordinary_plan(level, JitValidationMode::Unchecked);
        let source = plan
            .observe_native_aggregate_source_events("ordinary_pair_store_wrapper")
            .unwrap();
        let target = plan
            .observe_native_aggregate_target_events("ordinary_pair_store_wrapper")
            .unwrap();
        assert_eq!(source.plan_identity(), target.plan_identity());
        let observed = target.target();
        crate::compiler::conditional_wrapper_tests::emit_local_materialization_queries(
            &format!("ordinary_sealed_pair_{level:?}"),
            observed,
        );
        assert_eq!(observed.calls().len(), 1);
        assert_eq!(observed.accesses().iter().filter(|a| a.load).count(), 2);
        assert_eq!(observed.accesses().iter().filter(|a| !a.load).count(), 4);
        assert_eq!(observed.slot_address_demands().len(), 1);
        assert_ne!(
            source.source_events().events()[0].post_world(),
            observed.calls()[0].post_world()
        );
        assert_ne!(
            observed.calls()[0].before_registers()[31],
            observed.calls()[0].after_registers()[31]
        );
        assert_eq!(observed.calls()[0].outstanding_requirements().len(), 6);
        assert!(plan.qualify_for_proof_grade_compilation().is_err());
        println!(
            "ORDINARY_NATIVE_AGGREGATE_TARGET {level:?} calls=1 reads=2 writes=4 interval_frontier={:?} six_pending=true native_artifacts=0",
            observed.frontier()
        );
    }
}

#[test]
fn qualified_native_aggregate_observation_keeps_the_original_pending_state() {
    let plan = ordinary_plan(OptLevel::O0, JitValidationMode::AlwaysVerify);
    let before = plan
        .observe_native_aggregate_target_events("ordinary_pair_store_wrapper")
        .unwrap();
    let qualified = plan.qualify_for_proof_grade_compilation().unwrap();
    let after = qualified
        .observe_native_aggregate_target_events("ordinary_pair_store_wrapper")
        .unwrap();
    assert_eq!(before.plan_identity(), qualified.identity());
    assert_eq!(after.plan_identity(), qualified.identity());
    assert_eq!(
        before.target().original_module_digest(),
        after.target().original_module_digest()
    );
    let first = &before.target().calls()[0];
    let second = &after.target().calls()[0];
    assert_eq!(first.binding(), second.binding());
    assert_eq!(first.prior_world(), second.prior_world());
    assert_eq!(first.post_world(), second.post_world());
    assert_eq!(first.after_registers(), second.after_registers());
    assert_eq!(second.outstanding_requirements().len(), 6);
    assert!(
        qualified
            .observe_native_aggregate_target_events("absent_provider_caller")
            .is_err()
    );
}
