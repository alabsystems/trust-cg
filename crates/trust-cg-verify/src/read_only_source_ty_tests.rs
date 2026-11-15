// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Authentic TY source selection through the ordinary shared Core adapter.
//! Target stamping is disclosed and identical to TY's existing JIT boundary;
//! no original body is reconstructed. Pending queries are not proof credit.

use super::*;
use crate::memory_proofs::{encode_store_le, zeroed_memory};
use crate::smt::{EvalEnv, EvalResult};
use std::convert::Infallible;
use trust_cg_codegen::CoreHostJitTarget;

fn original() -> Module {
    let payload: serde_json::Value = serde_json::from_str(include_str!(
        "../tests/fixtures/ty_original_read_only_predicate.json"
    ))
    .unwrap();
    assert_eq!(
        payload["format"],
        "ty-original-read-only-predicate-source-v1"
    );
    assert_eq!(payload["selection"]["unit_key"], "inv:Second");
    assert_eq!(payload["original_core_instruction_count"], 59);
    let original: Module = serde_json::from_value(payload["module"].clone()).unwrap();
    assert!(original.target_info.is_none());
    assert_eq!(original.functions.len(), 1);
    assert_eq!(original.functions[0].id.index(), 60_004);
    assert_eq!(original.functions[0].name, "tyw1_u3");
    assert_eq!(original.functions[0].blocks.len(), 12);
    original
}

pub(super) fn targeted() -> Module {
    let original = original();
    let mut module = original.clone();
    // NativeModel::compile_with_predicates stamps this same ordinary host
    // metadata before validation. This is an explicit context-binding step,
    // NOT a claim that the targetless source already carried host authority.
    let host = CoreHostJitTarget::detect().expect("supported executing host");
    module.target_info = Some(host.trust_ir_target_info().clone());
    let mut restored = module.clone();
    restored.target_info = None;
    assert_eq!(
        serde_json::to_value(restored).unwrap(),
        serde_json::to_value(original).unwrap(),
        "only target context may change; all source and module metadata stay exact"
    );
    module
}

pub(super) fn instantiate(expr: &E, memory: &E, env: &EvalEnv) -> EvalResult {
    let bound = expr
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok(matches!(node, E::UF { name, args, ret_sort }
                if name == "entry_memory" && args.is_empty() && *ret_sort == memory_sort())
            .then(|| memory.clone()))
        })
        .unwrap()
        .unwrap_or_else(|| expr.clone());
    bound
        .try_eval(env)
        .expect("finite concrete array evaluation")
}

pub(super) fn case(ctx: u64, parent: u64, pool: u64, state: u64, literal: u64) -> (E, EvalEnv) {
    let mut memory = zeroed_memory();
    for (address, value) in [(ctx + 8, pool), (parent, state), (pool + 24, literal)] {
        memory = encode_store_le(
            &memory,
            &E::bv_const(address, 64),
            &E::bv_const(value, 64),
            8,
        );
    }
    let mut env = EvalEnv::default();
    for (i, value) in [ctx, parent, parent, parent].into_iter().enumerate() {
        env.insert(format!("abi_x{i}"), value);
    }
    (memory, env)
}

#[test]
fn actual_ty_original_predicate_binds_three_reads_and_full_status_queries() {
    let module = targeted();
    let (lowering, _proof_context) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let queries = bind_read_only_source(&module, 0, &lowering).unwrap_or_else(|error| {
        panic!("authentic 12-block original predicate must bind: {error}\n{lowering:#?}")
    });
    assert!(std::ptr::eq(queries.module(), &module));
    assert!(std::ptr::eq(queries.source(), &module.functions[0]));
    assert!(std::ptr::eq(queries.lir(), &lowering));
    assert_eq!(queries.read_requirements().len(), 3);
    assert_eq!(queries.lowering_reads().len(), 3);
    assert_eq!(queries.load_obligations().len(), 3);
    assert_eq!(
        queries.read_requirements()[0].value_type,
        ReadOnlyType::Pointer
    );
    let (memory, env) = case(0x1000, 0x2000, 0x3000, 1, 9);
    for (read, expected) in queries
        .read_requirements()
        .iter()
        .zip([0x1008, 0x2000, 0x3018])
    {
        assert_eq!(
            instantiate(&read.guard, &memory, &env),
            EvalResult::Bool(true)
        );
        assert_eq!(instantiate(&read.address, &memory, &env).as_u64(), expected);
        assert_eq!(read.byte_width, 8);
        assert_eq!(read.alignment, 8);
    }
    println!(
        "TY_ORIGINAL_READ_ONLY_SOURCE blocks=12 nodes=59 source_reads=3 lowering_reads=3 pending_load_queries=3 independent_proof=false native_credit=false"
    );
}

#[test]
fn actual_ty_original_predicate_queries_preserve_aliases_and_all_status_exits() {
    let module = targeted();
    let (lowering, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let queries = bind_read_only_source(&module, 0, &lowering).unwrap();
    // Integer CVWs have tag 1. Full status payloads are not truncated to a
    // Boolean or u32. The tag-4 route retains fallback before error checks.
    let error = 12_884_901_889;
    let fallback = 12_884_901_892;
    let samples = [
        (1, 9, 4_294_967_296),
        (9, 9, 0),
        (17, 9, 0),
        ((-1i64 as u64).wrapping_shl(3) | 1, 9, 4_294_967_296),
        (
            (i64::from(i32::MIN) as u64).wrapping_shl(3) | 1,
            9,
            4_294_967_296,
        ),
        ((i64::from(i32::MAX) as u64).wrapping_shl(3) | 1, 9, 0),
        ((1u64 << 31).wrapping_shl(3) | 1, 9, error),
        (2, 9, error),
        (1, 2, error),
        (4, 2, fallback),
        (2, 4, fallback),
    ];
    let mut count = 0;
    for (state, literal, expected) in samples {
        for parent in [0x2000, 0x1000] {
            // Parent may share ctx's allocation; different bytes remain
            // distinguishable. No noalias or uniform-array premise is used.
            let (memory, env) = case(0x1000, parent, 0x3000, state, literal);
            for precondition in &queries.return_obligation().preconditions {
                assert!(instantiate(precondition, &memory, &env).as_bool());
            }
            let returned = queries.return_obligation();
            assert_eq!(
                instantiate(&returned.trust_ir_expr, &memory, &env).as_u64(),
                expected
            );
            assert_eq!(
                instantiate(&returned.aarch64_expr, &memory, &env).as_u64(),
                expected
            );
            for query in queries.load_obligations() {
                assert_eq!(
                    instantiate(&query.trust_ir_expr, &memory, &env),
                    instantiate(&query.aarch64_expr, &memory, &env)
                );
            }
            count += 1;
        }
    }
    println!(
        "TY_ORIGINAL_READ_ONLY_CONCRETE cases={count} arbitrary_array_instantiations=true overlapping_ctx_parent=true proof_claim=false"
    );
}

#[test]
fn actual_ty_targetless_source_is_not_silently_given_layout_authority() {
    let module = original();
    let (lowering, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    assert!(matches!(
        bind_read_only_source(&module, 0, &lowering),
        Err(ReadOnlySourceError::Source("missing target layout"))
    ));
}
