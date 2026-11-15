// Copyright 2026 Andrew Yates | Apache-2.0
use super::*;

fn original() -> (Module, Vec<Function>) {
    let raw = include_bytes!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../reports/2026-11-12-original-e1-machine/fixture/core.tmbc"
    ));
    let module = trust_cg_codegen::pipeline::decode_tmbc(raw).unwrap();
    assert_eq!(
        trust_cg_codegen::pipeline::encode_tmbc(&module).unwrap(),
        raw
    );
    let license = trust_cg_lower::CodegenLicensePolicy::default()
        .with_unlicensed(trust_cg_lower::UnlicensedBodyPolicy::Permit);
    let (lowered, report) =
        trust_cg_lower::translate_module_strict_for_arch_with_tls_and_validation_with_license(
            &module,
            trust_cg_lower::GuardCarrierArch::AArch64,
            trust_cg_lower::TlsDialect::MachOTlv,
            &license,
        )
        .unwrap();
    report
        .replay_strict_call_bindings_exhaustive(&lowered)
        .unwrap();
    assert_eq!(lowered.len(), 6);
    (module, lowered.into_iter().map(|(f, _)| f).collect())
}
#[test]
fn conditional_wrapper_actual_original_entries_keep_all_five_lanes_and_pending_relations() {
    let (module, lir) = original();
    let scope = PendingCalleeRelations::capture(&module, &lir).unwrap();
    for name in ["tla_native_semantic_entry_1", "tla_native_semantic_entry_3"] {
        let ordinal = module
            .functions
            .iter()
            .position(|f| f.name == name)
            .unwrap();
        let query = bind_conditional_wrapper_source(&module, ordinal, &lir, Some(&scope))
            .unwrap_or_else(|e| {
                panic!(
                    "{name}: {e}; original nodes: {:#?}",
                    module.functions[ordinal].blocks[0].body
                )
            });
        assert_eq!(query.retained_functions().len(), 6);
        assert_eq!(query.outstanding_relations().len(), 1);
        let call = &query.outstanding_relations()[0];
        assert_eq!(call.result_codecs.len(), 5);
        assert_eq!(query.source_writes().len(), 5);
        assert_eq!(query.lowering_writes().len(), 5);
        assert!(query.source_reads().is_empty() && query.lowering_reads().is_empty());
        assert_ne!(call.source_results, call.lowering_results);
        assert_ne!(call.source_post_memory, call.lowering_post_memory);
        assert!(!query.outstanding_source_geometry().is_empty());
        assert_eq!(query.conditional_obligations().len(), 12);
        // Dependency-epoch composition must retain the exact original SMT
        // statements; compare without launching a solver or accepting proofs.
        let retained: serde_json::Value = serde_json::from_str(include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../reports/2026-11-12-original-e1-conditional-wrappers/outcomes.json"
        )))
        .unwrap();
        let config = crate::ay_bridge::AYConfig {
            solver: None,
            timeout_ms: crate::ay_bridge::DEFAULT_AY_TIMEOUT_MS,
            produce_models: true,
        };
        for (index, obligation) in query.conditional_obligations().iter().enumerate() {
            let previous = retained["query_roster"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| {
                    row["wrapper"].as_str() == Some(name)
                        && row["index"].as_u64() == Some(index as u64)
                })
                .unwrap();
            let raw = crate::ay_bridge::generate_smt2_query_raw(obligation, &config);
            assert_eq!(raw.len(), previous["bytes"].as_u64().unwrap() as usize);
            assert_eq!(
                format!("{:x}", Sha256::digest(raw.as_bytes())),
                previous["sha256"].as_str().unwrap()
            );
        }
        println!(
            "CONDITIONAL_WRAPPER_ORIGINAL {name} relation_lanes={} queries={} codecs={:?}",
            call.result_codecs.len(),
            query.conditional_obligations().len(),
            call.result_codecs
        );
    }
}
#[test]
fn conditional_wrapper_missing_or_stale_relation_custody_refuses() {
    let (module, lir) = original();
    let scope = PendingCalleeRelations::capture(&module, &lir).unwrap();
    let ordinal = module
        .functions
        .iter()
        .position(|f| f.name == "tla_native_semantic_entry_1")
        .unwrap();
    assert!(bind_conditional_wrapper_source(&module, ordinal, &lir, None).is_err());
    let mut changed = lir.clone();
    changed[0].name.push_str("_foreign");
    assert!(bind_conditional_wrapper_source(&module, ordinal, &changed, Some(&scope)).is_err());
    assert!(PendingCalleeRelations::capture(&module, &lir[..5]).is_err());
    let mut foreign = module.clone();
    foreign.name.push_str("_foreign");
    assert!(bind_conditional_wrapper_source(&foreign, ordinal, &lir, Some(&scope)).is_err());
}

use crate::smt::{EvalEnv, EvalResult, SmtSort};
use std::convert::Infallible;
use trust_cg_lower::instructions::Value as LirValue;

type Substitutions = HashMap<String, (SmtSort, E)>;
fn substitute(expression: &E, substitutions: &Substitutions) -> E {
    expression
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok(match node {
                E::UF {
                    name,
                    args,
                    ret_sort,
                } if args.is_empty() => substitutions.get(name).map(|(sort, value)| {
                    assert_eq!(sort, ret_sort);
                    value.clone()
                }),
                _ => None,
            })
        })
        .unwrap()
        .unwrap_or_else(|| expression.clone())
}
fn symbol(substitutions: &mut Substitutions, expression: &E, value: E) {
    let E::UF {
        name,
        args,
        ret_sort,
    } = expression
    else {
        panic!("independent nullary input required")
    };
    assert!(args.is_empty());
    assert_eq!(*ret_sort, value.sort());
    assert!(
        substitutions
            .insert(name.clone(), (ret_sort.clone(), value))
            .is_none()
    );
}
fn memory(byte: u64) -> E {
    E::const_array(SmtSort::BitVec(64), E::bv_const(byte, 8))
}
// Concrete assignments are finite mutation controls, NEVER callee theorems.
fn assignment(
    queries: &ConditionalWrapperQueries<'_>,
    different_lower_outcomes: bool,
) -> (Substitutions, EvalEnv) {
    let mut substitutions = HashMap::from([("entry_memory".into(), (memory_sort(), memory(0x11)))]);
    for (event, relation) in queries.outstanding_relations().iter().enumerate() {
        for (lane, (source, lower)) in relation
            .source_results
            .iter()
            .zip(&relation.lowering_results)
            .enumerate()
        {
            let value = 0x1122334455667700u64 + (event as u64) * 0x10 + (lane as u64);
            symbol(&mut substitutions, source, E::bv_const(value, 64));
            symbol(
                &mut substitutions,
                lower,
                E::bv_const(value + u64::from(different_lower_outcomes), 64),
            );
        }
        symbol(
            &mut substitutions,
            &relation.source_post_memory,
            memory(0xa5),
        );
        symbol(
            &mut substitutions,
            &relation.lowering_post_memory,
            memory(if different_lower_outcomes { 0x5a } else { 0xa5 }),
        );
        symbol(
            &mut substitutions,
            &relation.source_returned_normally,
            E::BoolConst(true),
        );
        symbol(
            &mut substitutions,
            &relation.lowering_returned_normally,
            E::BoolConst(true),
        );
    }
    for equation in queries.encoding_definitions() {
        let E::Eq { lhs, rhs } = equation else {
            panic!("encoding equation")
        };
        let value = substitute(rhs, &substitutions);
        symbol(&mut substitutions, lhs, value);
    }
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), 0x1000);
    env.insert("abi_x1".into(), 0x2000);
    env.insert("observe".into(), 0x2100);
    (substitutions, env)
}
fn holds(query: &ProofObligation, substitutions: &Substitutions, env: &EvalEnv) -> bool {
    for premise in &query.preconditions {
        assert_eq!(
            substitute(premise, substitutions).try_eval(env).unwrap(),
            EvalResult::Bool(true)
        );
    }
    substitute(&query.trust_ir_expr, substitutions)
        .try_eval(env)
        .unwrap()
        == substitute(&query.aarch64_expr, substitutions)
            .try_eval(env)
            .unwrap()
}
fn caller(module: &Module) -> usize {
    module
        .functions
        .iter()
        .position(|f| f.name == "tla_native_semantic_entry_1")
        .unwrap()
}
fn lower_caller(lir: &mut [Function]) -> &mut Function {
    lir.iter_mut()
        .find(|f| f.name == "tla_native_semantic_entry_1")
        .unwrap()
}
fn build<'a>(module: &'a Module, lir: &'a [Function]) -> ConditionalWrapperQueries<'a> {
    let scope = PendingCalleeRelations::capture(module, lir).unwrap();
    bind_conditional_wrapper_source(module, caller(module), lir, Some(&scope)).unwrap()
}

#[test]
fn conditional_wrapper_original_finite_controls_and_independent_call_worlds() {
    let (module, lir) = original();
    let queries = build(&module, &lir);
    let (assignments, env) = assignment(&queries, false);
    assert!(
        queries
            .outstanding_source_geometry()
            .iter()
            .all(|e| substitute(e, &assignments).try_eval(&env).unwrap() == EvalResult::Bool(true))
    );
    assert!(
        queries
            .conditional_obligations()
            .iter()
            .all(|q| holds(q, &assignments, &env))
    );
    let relation = &queries.outstanding_relations()[0];
    assert_eq!(
        substitute(relation.required_relation(), &assignments)
            .try_eval(&env)
            .unwrap(),
        EvalResult::Bool(true)
    );
    // Entire post-call memory may change, including outside the output bytes.
    assert_ne!(
        substitute(&relation.source_post_memory, &assignments),
        memory(0x11)
    );
    let (different, env) = assignment(&queries, true);
    assert_eq!(
        substitute(relation.required_relation(), &different)
            .try_eval(&env)
            .unwrap(),
        EvalResult::Bool(false)
    );
    // Missing whole-memory transition relation must expose a real difference;
    // no frozen entry world or guessed source/target equality can hide it.
    let mut last = queries.conditional_obligations()[6].clone();
    last.aarch64_expr = last
        .aarch64_expr
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok((node == relation.required_relation()).then_some(E::BoolConst(true)))
        })
        .unwrap()
        .unwrap();
    assert!(!holds(&last, &different, &env));
}

#[test]
fn conditional_wrapper_wrong_callee_arity_origin_and_carrier_refuse() {
    let (module, lir) = original();
    for mutation in 0..5 {
        let mut changed = lir.clone();
        let f = lower_caller(&mut changed);
        let entry = f.entry_block;
        match mutation {
            0 => {
                let call = &mut f.blocks.get_mut(&entry).unwrap().instructions[1];
                call.opcode = Opcode::Call {
                    name: "tla_root_1".into(),
                    binding: DirectCallBinding::ExactModuleFunction { function: 9 },
                };
            }
            1 => {
                f.blocks.get_mut(&entry).unwrap().instructions[1].args.pop();
            }
            2 => {
                f.blocks.get_mut(&entry).unwrap().instructions[1]
                    .results
                    .pop();
            }
            3 => {
                f.trust_ir_origins.get_mut(&entry).unwrap()[1] =
                    Some(trust_cg_ir::TrustIrInstId(0));
            }
            4 => {
                f.value_types.insert(LirValue(3), LirType::I32);
            }
            _ => unreachable!(),
        }
        let custody = PendingCalleeRelations::capture(&module, &changed).unwrap();
        assert!(
            bind_conditional_wrapper_source(&module, caller(&module), &changed, Some(&custody))
                .is_err(),
            "mutation {mutation}"
        );
    }
}

#[test]
fn conditional_wrapper_lane_offset_and_order_changes_have_concrete_counterexamples() {
    let (module, lir) = original();
    for mutation in 0..3 {
        let mut changed = lir.clone();
        let f = lower_caller(&mut changed);
        let entry = f.entry_block;
        let body = &mut f.blocks.get_mut(&entry).unwrap().instructions;
        match mutation {
            0 => body[4].args[0] = LirValue(4),
            1 => {
                body[5].opcode = Opcode::Iconst {
                    ty: LirType::I64,
                    imm: 16,
                }
            }
            2 => {
                body[2..8].rotate_left(3);
                f.trust_ir_origins.get_mut(&entry).unwrap()[2..8].rotate_left(3);
            }
            _ => unreachable!(),
        }
        let queries = build(&module, &changed);
        let (assignments, env) = assignment(&queries, false);
        assert!(
            queries
                .conditional_obligations()
                .iter()
                .any(|q| !holds(q, &assignments, &env)),
            "mutation {mutation}"
        );
        if mutation == 2 {
            assert!(
                holds(&queries.conditional_obligations()[6], &assignments, &env),
                "disjoint reorder preserves final bytes, but ordered events must fail"
            );
        }
    }
}

#[test]
fn conditional_wrapper_complete_unused_payload_and_nesting_bounds_refuse() {
    let (module, lir) = original();
    let mut enormous = module.clone();
    enormous.functions[0].name = "x".repeat(4 * 1024 * 1024 + 1);
    assert!(matches!(
        PendingCalleeRelations::capture(&enormous, &lir),
        Err(ReadOnlySourceError::Budget(_))
    ));
    let mut enormous = lir.clone();
    enormous[0].name = "x".repeat(4 * 1024 * 1024 + 1);
    assert!(matches!(
        PendingCalleeRelations::capture(&module, &enormous),
        Err(ReadOnlySourceError::Budget(_))
    ));
    let mut deep = lir.clone();
    let mut ty = LirType::I64;
    for _ in 0..40 {
        ty = LirType::Array(Box::new(ty), 1);
    }
    deep[0].value_types.insert(LirValue(999), ty);
    assert!(matches!(
        PendingCalleeRelations::capture(&module, &deep),
        Err(ReadOnlySourceError::Budget(_))
    ));
    let mut origins = lir.clone();
    let entry = origins[0].entry_block;
    origins[0]
        .trust_ir_origins
        .insert(entry, vec![None; MAX_TOTAL_QUERY_NODES + 1]);
    assert!(matches!(
        PendingCalleeRelations::capture(&module, &origins),
        Err(ReadOnlySourceError::Budget(_))
    ));
}

#[test]
#[ignore = "requires authenticated AY and independent checker; conditional statements only"]
fn conditional_wrapper_original_raw_independent_replay_challenge() {
    use crate::ay_bridge::{
        AYConfig, AYResult, DEFAULT_AY_TIMEOUT_MS, generate_smt2_query_raw,
        verify_with_cli_raw_attributed,
    };
    let config = AYConfig {
        solver: Some(crate::ay_identity::resolve_for_process().expect("authenticated AY required")),
        timeout_ms: DEFAULT_AY_TIMEOUT_MS,
        produce_models: true,
    };
    let checker = crate::obligation_cert_store::resolve_proof_checker()
        .expect("authenticated independent checker required");
    let (module, lir) = original();
    let scope = PendingCalleeRelations::capture(&module, &lir).unwrap();
    let mut all_verified = true;
    for name in ["tla_native_semantic_entry_1", "tla_native_semantic_entry_3"] {
        let ordinal = module
            .functions
            .iter()
            .position(|f| f.name == name)
            .unwrap();
        let queries =
            bind_conditional_wrapper_source(&module, ordinal, &lir, Some(&scope)).unwrap();
        let mut premise_sat = queries.conditional_obligations()[0].clone();
        premise_sat.name = format!("{name}: complete conditional hypotheses satisfiable");
        premise_sat.trust_ir_expr = E::BoolConst(true);
        premise_sat.aarch64_expr = E::BoolConst(false);
        premise_sat
            .preconditions
            .extend(queries.outstanding_source_geometry().iter().cloned());
        premise_sat.preconditions.extend(
            queries
                .outstanding_relations()
                .iter()
                .map(|r| r.required_relation().clone()),
        );
        let raw = generate_smt2_query_raw(&premise_sat, &config);
        let hash = format!("{:x}", Sha256::digest(raw.as_bytes()));
        println!(
            "CONDITIONAL_WRAPPER_QUERY={}",
            serde_json::json!({"wrapper":name,"index":"premises-sat","name":premise_sat.name,"bytes":raw.len(),"sha256":hash,"query":raw,"checker":checker})
        );
        let result = verify_with_cli_raw_attributed(&premise_sat, &config);
        println!(
            "CONDITIONAL_WRAPPER_RESULT={}",
            serde_json::json!({"wrapper":name,"index":"premises-sat","sha256":hash,"result":format!("{:?}",result.result),"provenance":result.provenance()})
        );
        all_verified &= matches!(result.result, AYResult::CounterExample(_));
        for (index, query) in queries.conditional_obligations().iter().enumerate() {
            let raw = generate_smt2_query_raw(query, &config);
            let hash = format!("{:x}", Sha256::digest(raw.as_bytes()));
            println!(
                "CONDITIONAL_WRAPPER_QUERY={}",
                serde_json::json!({"wrapper":name,"index":index,"name":query.name,"bytes":raw.len(),"sha256":hash,"query":raw,"checker":checker})
            );
            let result = verify_with_cli_raw_attributed(query, &config);
            println!(
                "CONDITIONAL_WRAPPER_RESULT={}",
                serde_json::json!({"wrapper":name,"index":index,"sha256":hash,"result":format!("{:?}",result.result),"provenance":result.provenance()})
            );
            all_verified &= result.result == AYResult::Verified;
        }
    }
    assert!(
        all_verified,
        "every exact conditional query must independently replay; construction/Unknown gives no proof credit"
    );
}

#[test]
fn conditional_wrapper_repeated_identical_calls_keep_fresh_eventwise_worlds() {
    let (mut module, mut lir) = original();
    let ordinal = caller(&module);
    let mut second = module.functions[ordinal].blocks[0].body[1].clone();
    second.results = (18..23).map(ValueId::new).collect();
    module.functions[ordinal].blocks[0].body.insert(2, second);
    let f = lower_caller(&mut lir);
    let entry = f.entry_block;
    let mut second = f.blocks[&entry].instructions[1].clone();
    second.results = (18..23).map(LirValue).collect();
    f.blocks
        .get_mut(&entry)
        .unwrap()
        .instructions
        .insert(2, second);
    for id in 18..23 {
        f.value_types.insert(LirValue(id), LirType::I64);
    }
    let origins = f.trust_ir_origins.get_mut(&entry).unwrap();
    for origin in origins.iter_mut().flatten() {
        if origin.0 >= 2 {
            origin.0 += 1;
        }
    }
    origins.insert(2, Some(trust_cg_ir::TrustIrInstId(2)));
    let queries = build(&module, &lir);
    assert_eq!(queries.outstanding_relations().len(), 2);
    let calls = queries.outstanding_relations();
    assert_eq!(calls[0].source_arguments, calls[1].source_arguments);
    assert_ne!(calls[0].source_results, calls[1].source_results);
    assert_ne!(calls[0].source_post_memory, calls[1].source_post_memory);
    assert_eq!(calls[0].source_post_memory, calls[1].source_prior_memory);
    assert_eq!(
        calls[0].lowering_post_memory,
        calls[1].lowering_prior_memory
    );
    let (assignments, env) = assignment(&queries, false);
    assert!(
        queries
            .conditional_obligations()
            .iter()
            .all(|q| holds(q, &assignments, &env))
    );
}

#[test]
fn conditional_wrapper_complete_raw_occurrences_cannot_hide_behind_small_dag() {
    let mut value = Term::leaf(E::var("abi_x0", 64));
    for _ in 0..10 {
        value = value.binary(&value, 1, E::bvadd).unwrap();
    }
    let mut definitions = scalar_memory::Definitions::conditional(scalar_memory::Endpoint::Core);
    definitions.bind(value, SmtSort::BitVec(64)).unwrap();
    assert!(
        crate::smt_raw_print::preflight(&definitions.equations[0])
            .unwrap()
            .order
            .len()
            < 32
    );
    assert!(
        definitions.nodes > 2_000,
        "complete raw occurrences are retained despite DAG sharing"
    );
    let mut total = 0;
    for query in 0..130 {
        let before = total;
        match conditional_query(
            format!("shared-DAG collection {query}"),
            &Term::leaf(E::BoolConst(true)),
            Term::leaf(E::BoolConst(true)),
            &[("abi_x0".into(), 64)],
            &definitions.equations,
            definitions.nodes,
            &mut total,
        ) {
            Ok(_) => {}
            Err(ReadOnlySourceError::Budget(_)) => {
                assert_eq!(total, before);
                assert!(query > 0);
                return;
            }
            Err(e) => panic!("unexpected non-resource refusal: {e}"),
        }
    }
    panic!(
        "raw definitions repeated across the collection must exhaust the existing aggregate bound"
    );
}
