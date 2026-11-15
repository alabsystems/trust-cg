// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The complete captured source, never a rebuilt/projection writer.
//! Constructing pending queries supplies no independently checked proof.

use super::*;
use trust_cg_codegen::CoreHostJitTarget;

fn original() -> Module {
    let capture: serde_json::Value = serde_json::from_str(include_str!(
        "../tests/fixtures/ty_original_scalar_action.json"
    ))
    .unwrap();
    assert_eq!(capture["format"], "ty-original-scalar-action-source-v1");
    assert_eq!(capture["selection"]["unit_key"], "next:Next@91-101");
    let module: Module = serde_json::from_value(capture["module"].clone()).unwrap();
    assert!(module.target_info.is_none());
    assert_eq!(module.functions.len(), 10);
    assert_eq!(module.functions[3].id.index(), 60_002);
    assert_eq!(module.functions[3].blocks.len(), 16);
    assert_eq!(
        module.functions[3]
            .blocks
            .iter()
            .map(|b| b.body.len())
            .sum::<usize>(),
        117
    );
    module
}

#[test]
fn actual_original_scalar_next_binds_full_status_bytes_and_accesses() {
    let original = original();
    let mut module = original.clone();
    module.target_info = Some(
        CoreHostJitTarget::detect()
            .unwrap()
            .trust_ir_target_info()
            .clone(),
    );
    let mut restored = module.clone();
    restored.target_info = None;
    assert_eq!(
        serde_json::to_value(restored).unwrap(),
        serde_json::to_value(original).unwrap()
    );
    let (lowering, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[3],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    assert!(bind_read_only_source(&module, 3, &lowering).is_err());
    let queries = bind_scalar_memory_source(&module, 3, &lowering)
        .unwrap_or_else(|error| panic!("complete original scalar Next must bind: {error}"));
    assert!(std::ptr::eq(queries.module(), &module));
    assert!(std::ptr::eq(queries.source(), &module.functions[3]));
    assert!(std::ptr::eq(queries.lir(), &lowering));
    assert_eq!(queries.source_reads().len(), queries.lowering_reads().len());
    assert_eq!(
        queries.source_writes().len(),
        queries.lowering_writes().len()
    );
    assert_eq!(
        queries.read_obligations().len(),
        queries.lowering_reads().len()
    );
    assert_eq!(
        queries.write_obligations().len(),
        queries.lowering_writes().len()
    );
    assert!(queries.source_reads().iter().any(|a| a.byte_width == 4));
    assert!(queries.source_writes().iter().any(|a| a.byte_width == 4));
    assert!(queries.source_writes().iter().any(|a| a.byte_width == 8));
    assert!(
        queries
            .source_reads()
            .iter()
            .any(|a| a.codec == ScalarMemoryCodec::Pointer)
    );
    let mut obligations = vec![queries.status_obligation(), queries.memory_obligation()];
    obligations.extend(queries.read_obligations());
    obligations.extend(queries.write_obligations());
    for obligation in &obligations {
        assert!(obligation.inputs.contains(&("observe".into(), 64)));
        assert_eq!(
            obligation.preconditions.len(),
            queries.source_geometry().len() + queries.encoding_definitions().len()
        );
        for equation in queries.encoding_definitions() {
            assert!(obligation.preconditions.contains(equation));
        }
    }
    println!(
        "TY_ORIGINAL_SCALAR_MEMORY_SOURCE blocks=16 nodes=117 source_reads={} source_writes={} lowering_reads={} lowering_writes={} geometry={} definitions={} pending_parts={} full_status=true unrestricted_final_bytes=true independent_proof=false native_credit=false",
        queries.source_reads().len(),
        queries.source_writes().len(),
        queries.lowering_reads().len(),
        queries.lowering_writes().len(),
        queries.source_geometry().len(),
        queries.encoding_definitions().len(),
        obligations.len()
    );
}

#[test]
fn actual_targetless_scalar_next_does_not_mint_layout_authority() {
    let module = original();
    let (lowering, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[3],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    assert!(matches!(
        bind_scalar_memory_source(&module, 3, &lowering),
        Err(ReadOnlySourceError::Source("missing target layout"))
    ));
}

#[test]
fn scalar_complete_query_connectives_are_charged_without_changing_readonly_limits() {
    // The source and target scalar leaves plus Eq/Not contribute four nodes;
    // each premise contributes its tree plus one AND, as implemented by
    // ProofObligation::negated_equivalence. The reservation remains bounded
    // by the SAME aggregate limit, and failed growth consumes nothing.
    let leaf = Term::leaf(E::bv_const(0, 64));
    let premises = vec![E::BoolConst(true), E::BoolConst(false)];
    let obligation = pending(
        "connective accounting".into(),
        leaf.expr.clone(),
        leaf.expr,
        &[],
        &premises,
    );
    let formula = obligation.negated_equivalence();
    let mut nodes = vec![&formula];
    let mut count = 0;
    while let Some(node) = nodes.pop() {
        count += 1;
        node.for_each_child(&mut |child| nodes.push(child));
    }
    assert_eq!(count, 8);
    let mut used = MAX_TOTAL_QUERY_NODES - count;
    reserve_query(&mut used, count).unwrap();
    assert_eq!(used, MAX_TOTAL_QUERY_NODES);
    assert!(reserve_query(&mut used, 1).is_err());
    assert_eq!(used, MAX_TOTAL_QUERY_NODES);
}
