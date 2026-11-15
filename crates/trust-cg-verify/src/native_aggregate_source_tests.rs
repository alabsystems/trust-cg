// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;
use sha2::{Digest, Sha256};
use trust_ir::{FieldDef, StructDef, StructId, StructRepr};
use trust_ir_build::ModuleBuilder;

pub(crate) fn fixture(
    calls: usize,
    fork: bool,
) -> (Module, usize, Function, trust_cg_lower::ProofContext) {
    fixture_with_return_lanes(calls, fork, 1)
}

fn fixture_with_return_lanes(
    calls: usize,
    fork: bool,
    return_lanes: usize,
) -> (Module, usize, Function, trust_cg_lower::ProofContext) {
    let mut b = ModuleBuilder::new_with_target_info(
        "ordinary_event",
        trust_ir::TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64-darwin".into()),
            struct_passing: trust_ir::StructPassingPolicy::NativeC,
        },
    );
    let record = b.add_struct(StructDef {
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
    let ty = b.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::Struct(record)]);
    let provider = b.declare_function("opaque_pair", ty);
    let ty = b.add_func_type(vec![Ty::Ptr, Ty::U64], vec![Ty::I64; return_lanes]);
    let mut f = b.function("event_consumer", ty);
    let entry = f.create_block();
    let ptr = f.add_block_param(entry, Ty::Ptr);
    let n = f.add_block_param(entry, Ty::U64);
    f.switch_to_block(entry);
    if fork {
        let yes = f.create_block();
        let no = f.create_block();
        let join = f.create_block();
        let zero = f.iconst(Ty::U64, 0);
        let cond = f.icmp(trust_ir::ICmpOp::Eq, Ty::U64, n, zero);
        f.condbr(cond, yes, vec![], no, vec![]);
        f.switch_to_block(yes);
        f.br(join, vec![]);
        f.switch_to_block(no);
        f.br(join, vec![]);
        f.switch_to_block(join);
    }
    let mut last = None;
    for _ in 0..calls {
        let value = f.call(provider, vec![ptr, n]);
        f.extract_field(Ty::U64, value, 0);
        last = Some(f.extract_field(Ty::I64, value, 1));
    }
    f.load(Ty::I64, ptr);
    f.store(Ty::I64, ptr, last.unwrap());
    f.ret(vec![last.unwrap(); return_lanes]);
    f.build();
    let module = b.build().unwrap();
    assert!(trust_ir_build::validate_module(&module).is_empty());
    let ordinal = module
        .functions
        .iter()
        .position(|f| f.name == "event_consumer")
        .unwrap();
    let (mut lowered, validation) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &trust_cg_lower::codegen_license::CodegenLicensePolicy::default()
                .with_unlicensed(trust_cg_lower::codegen_license::UnlicensedBodyPolicy::Permit),
        )
        .unwrap();
    validation
        .replay_strict_call_bindings_exhaustive(&lowered)
        .unwrap();
    let (mut lir, context) = lowered.remove(0);
    // Nominal unit data only. The ordinary Core consumer separately checks
    // its genuine catalog/reference/occurrence owner before source observation.
    for block in lir.blocks.values_mut() {
        for node in &mut block.instructions {
            if let Opcode::Call {
                binding: value @ DirectCallBinding::DeclaredExternalFunction { .. },
                ..
            } = &mut node.opcode
            {
                let DirectCallBinding::DeclaredExternalFunction { function } = *value else {
                    unreachable!()
                };
                *value = DirectCallBinding::NativeDependency {
                    function,
                    dependency: trust_cg_ir::NativeDependencyId::new(7),
                };
            }
        }
    }
    (module, ordinal, lir, context)
}

#[test]
fn native_record_empty_return_requires_original_void_signature() {
    let (module, ordinal, lir, context) = fixture_with_return_lanes(1, false, 0);
    let observed =
        observe_native_aggregate_source(&module, ordinal, &lir, &context.aggregate_call_intents)
            .unwrap();
    assert_eq!(observed.events().len(), 1);
    assert_eq!(observed.normal_terminal_guards().len(), 1);
    assert_eq!(observed.normal_terminal_worlds().len(), 1);
    let mut refusals = Vec::new();
    for lanes in [1, 5] {
        let (mut module, ordinal, lir, context) = fixture_with_return_lanes(1, false, lanes);
        for block in &mut module.functions[ordinal].blocks {
            for node in &mut block.body {
                if let Inst::Return { values } = &mut node.inst {
                    values.clear();
                }
            }
        }
        assert!(!trust_ir_build::validate_module(&module).is_empty());
        let refusal = observe_native_aggregate_source(
            &module,
            ordinal,
            &lir,
            &context.aggregate_call_intents,
        )
        .err();
        println!("NATIVE_AGGREGATE_EMPTY_RETURN lanes={lanes} refusal={refusal:?}");
        refusals.push(refusal);
    }
    assert_eq!(
        refusals,
        vec![
            Some(ReadOnlySourceError::Source(
                "scalar return arity differs from original signature"
            ));
            2
        ]
    );
}

#[test]
fn native_record_event_has_full_fresh_world_normality_and_real_source_accesses() {
    let (module, ordinal, lir, context) = fixture(1, false);
    let observed =
        observe_native_aggregate_source(&module, ordinal, &lir, &context.aggregate_call_intents)
            .unwrap();
    assert_eq!(observed.events().len(), 1);
    assert_eq!(observed.original_module_digest(), module.stable_digest());
    assert_eq!(
        observed.normal_terminal_guards().len(),
        observed.normal_terminal_worlds().len()
    );
    assert!(observed.first_retained_field_load().is_some());
    assert_eq!(observed.reads().len(), 1);
    assert_eq!(observed.writes().len(), 1);
    let event = &observed.events()[0];
    assert_ne!(event.post_world(), event.prior_world());
    assert_ne!(event.record().fields()[0], event.record().fields()[1]);
    assert_eq!(event.post_world().sort(), memory_sort());
    assert_eq!(event.returned_normally().sort(), crate::smt::SmtSort::Bool);
    assert!(
        observed
            .definitions()
            .iter()
            .any(|e| e.to_string().contains(&event.post_world().to_string()))
    );
    assert!(
        observed.reads()[0]
            .guard
            .to_string()
            .contains(&event.returned_normally().to_string())
    );
    assert!(
        observed.writes()[0]
            .guard
            .to_string()
            .contains(&event.returned_normally().to_string())
    );
    assert!(
        observed.normal_terminal_guards()[0]
            .to_string()
            .contains(&event.returned_normally().to_string())
    );
    assert_eq!(event.outstanding_requirements().len(), 6);
    assert!(
        observed
            .retained_field_load_frontier()
            .to_string()
            .contains("StructGep/Load")
    );
    assert!(
        super::super::scalar_returns::bind_scalar_return_source(&module, ordinal, &lir).is_err()
    );
}

#[test]
fn native_record_repeated_callee_gets_independent_execution_outcomes_and_world_chain() {
    let (module, ordinal, lir, context) = fixture(2, false);
    let observed =
        observe_native_aggregate_source(&module, ordinal, &lir, &context.aggregate_call_intents)
            .unwrap();
    let [first, second] = observed.events() else {
        panic!("two original calls");
    };
    assert_eq!(first.intent().callee(), second.intent().callee());
    assert_ne!(
        first.intent().source_origin(),
        second.intent().source_origin()
    );
    assert_ne!(first.record().fields(), second.record().fields());
    assert_ne!(first.post_world(), second.post_world());
    assert_ne!(first.returned_normally(), second.returned_normally());
    assert_eq!(second.prior_world(), first.post_world());
    assert_eq!(second.guard(), first.continuation_guard());
    assert!(
        observed.writes()[0]
            .guard
            .to_string()
            .contains(&first.returned_normally().to_string())
    );
    assert!(
        observed.writes()[0]
            .guard
            .to_string()
            .contains(&second.returned_normally().to_string())
    );
}

#[test]
fn native_record_wrong_source_codec_layout_identity_and_binding_refuse() {
    let (module, ordinal, lir, context) = fixture(1, false);
    let mut changed = module.clone();
    changed.structs[0].fields.swap(0, 1);
    assert!(
        observe_native_aggregate_source(&changed, ordinal, &lir, &context.aggregate_call_intents)
            .is_err()
    );
    let mut changed = lir.clone();
    changed.name.push_str("_foreign");
    assert!(
        observe_native_aggregate_source(
            &module,
            ordinal,
            &changed,
            &context.aggregate_call_intents
        )
        .is_err()
    );
    let mut changed = lir.clone();
    let call = &context.aggregate_call_intents.calls()[0];
    if let Opcode::Call { binding, .. } = &mut changed
        .blocks
        .get_mut(&call.lir_block())
        .unwrap()
        .instructions[call.lir_instruction()]
    .opcode
    {
        *binding = DirectCallBinding::DeclaredExternalFunction {
            function: call.callee().index(),
        };
    }
    assert!(
        observe_native_aggregate_source(
            &module,
            ordinal,
            &changed,
            &context.aggregate_call_intents
        )
        .is_err()
    );
    assert!(observe_native_aggregate_source(&module, ordinal, &lir, &Default::default()).is_err());
}

#[test]
fn native_record_same_physical_site_on_two_paths_is_not_deterministic_by_site() {
    let (module, ordinal, lir, context) = fixture(1, true);
    let observed =
        observe_native_aggregate_source(&module, ordinal, &lir, &context.aggregate_call_intents)
            .unwrap();
    let [first, second] = observed.events() else {
        panic!("two guarded execution occurrences");
    };
    assert_eq!(first.intent(), second.intent());
    assert_eq!(first.site(), second.site());
    assert_ne!(first.guard(), second.guard());
    assert_ne!(first.record().fields(), second.record().fields());
    assert_ne!(first.post_world(), second.post_world());
    assert_ne!(first.returned_normally(), second.returned_normally());
}

#[test]
fn native_record_diagnostic_controls_do_not_assume_relation_memory_or_normality() {
    let (module, ordinal, lir, context) = fixture(2, false);
    let observed =
        observe_native_aggregate_source(&module, ordinal, &lir, &context.aggregate_call_intents)
            .unwrap();
    let first = &observed.events()[0];
    let second = &observed.events()[1];
    let address = E::var("observe", 64);
    let memory_equal = encode_load_le(first.post_world(), &address, 1).eq_expr(encode_load_le(
        first.prior_world(),
        &address,
        1,
    ));
    let no_relation = first.record().fields()[0]
        .clone()
        .eq_expr(second.record().fields()[0].clone());
    let normal_false = first
        .returned_normally()
        .clone()
        .or_expr(observed.writes()[0].guard.clone().not_expr());
    for (name, claim, expected, normal_inputs) in [
        (
            "opaque_world_may_change_observer",
            memory_equal,
            "sat",
            true,
        ),
        ("missing_eventwise_relation", no_relation, "sat", true),
        (
            "normal_false_suppresses_later_write_guard",
            normal_false,
            "unsat",
            false,
        ),
    ] {
        let mut definitions = observed.definitions().to_vec();
        if normal_inputs {
            definitions.extend([
                first.returned_normally().clone(),
                second.returned_normally().clone(),
            ]);
        }
        let obligation = ProofObligation {
            name: format!("Native aggregate SOURCE diagnostic {name}; no target/permission credit"),
            trust_ir_expr: claim,
            aarch64_expr: E::BoolConst(true),
            inputs: vec![
                ("abi_x0".into(), 64),
                ("abi_x1".into(), 64),
                ("observe".into(), 64),
            ],
            preconditions: definitions,
            fp_inputs: vec![],
            category: Some(TransvalCheckKind::MemoryModel),
            machine_side_provenance: MachineSideProvenance::StaticDb,
        };
        let query = crate::ay_bridge::generate_smt2_query_raw(
            &obligation,
            &crate::ay_bridge::AYConfig {
                solver: None,
                timeout_ms: crate::ay_bridge::DEFAULT_AY_TIMEOUT_MS,
                produce_models: true,
            },
        );
        println!(
            "NATIVE_AGGREGATE_SOURCE_CONTROL={}",
            serde_json::json!({
                "name":name,"expected":expected,"query":query,"bytes":query.len(),
                "sha256":format!("{:x}",Sha256::digest(query.as_bytes())),
                "diagnostic_normal_inputs":normal_inputs,"relation_assumed":false,
                "complete_body_query":false,"aggregate_proof_credit":false,"native_credit":false,
            })
        );
    }
}

#[test]
fn native_record_occurrence_budget_is_not_raised() {
    let (module, ordinal, lir, context) = fixture(65, false);
    assert_eq!(
        observe_native_aggregate_source(&module, ordinal, &lir, &context.aggregate_call_intents)
            .err(),
        Some(ReadOnlySourceError::Budget(
            "conditional retained instructions"
        ))
    );
    // Two execution paths traverse 33 real sites: the old physical LIR cap
    // still passes, while 66 guarded execution occurrences exceed 64.
    let (module, ordinal, lir, context) = fixture(33, true);
    assert_eq!(
        observe_native_aggregate_source(&module, ordinal, &lir, &context.aggregate_call_intents)
            .err(),
        Some(ReadOnlySourceError::Budget(
            "native aggregate execution occurrences"
        ))
    );
}

#[test]
fn native_record_normal_false_suppresses_actual_continuation_access_and_terminal_guards() {
    use super::super::scalar_memory::tests::{Substitutions, evaluate};
    use crate::smt::{EvalEnv, EvalResult, SmtSort};
    let (module, ordinal, lir, context) = fixture(2, false);
    let observed =
        observe_native_aggregate_source(&module, ordinal, &lir, &context.aggregate_call_intents)
            .unwrap();
    for first in [false, true] {
        for second in [false, true] {
            let mut substitutions = Substitutions::new();
            for (event, value) in observed.events().iter().zip([first, second]) {
                let E::UF {
                    name,
                    args,
                    ret_sort,
                } = event.returned_normally()
                else {
                    panic!("independent normal input");
                };
                assert!(args.is_empty());
                assert_eq!(*ret_sort, SmtSort::Bool);
                substitutions.insert(name.clone(), (SmtSort::Bool, E::BoolConst(value)));
            }
            let env = EvalEnv::default();
            assert_eq!(
                evaluate(observed.events()[1].guard(), &substitutions, &env),
                EvalResult::Bool(first)
            );
            for guard in [
                observed.reads()[0].guard.clone(),
                observed.writes()[0].guard.clone(),
                observed.normal_terminal_guards()[0].clone(),
            ] {
                assert_eq!(
                    evaluate(&guard, &substitutions, &env),
                    EvalResult::Bool(first && second)
                );
            }
        }
    }
}
