// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Resource refusals for complete conditional queries, not proofs or measured
//! resident-memory bounds. Shared expression children do not make repeated
//! geometry/precondition serialization free.

use super::*;
use trust_ir::{
    Block as CoreBlock, BlockId, CallingConv, Constant, FuncId, FuncTy, Function as CoreFunction,
    Inst, InstrNode, TargetInfo, Ty, ValueId,
};

fn node(block: u32, instruction: usize, result: Option<(u32, Kind)>, operation: Operation) -> Node {
    Node {
        site: ReadOnlySite { block, instruction },
        result,
        operation,
    }
}

/// Every branch intentionally has the same destination. Both guards must
/// still be inspected; a constant condition cannot prune the untaken shape.
/// The final GEP chain is unused, so the return expression itself stays small.
fn repeated_geometry(branches: u32, offsets: u32) -> Graph {
    let mut blocks = Vec::new();
    for block in 0..=branches {
        let mut nodes = Vec::new();
        if block == 0 {
            nodes.push(node(0, 0, Some((1, Kind::Word)), Operation::Constant(0)));
            nodes.push(node(0, 1, Some((2, Kind::Word)), Operation::Constant(7)));
            nodes.push(node(0, 2, Some((3, Kind::Boolean)), Operation::Constant(1)));
        }
        if block < branches {
            nodes.push(node(
                block,
                nodes.len(),
                None,
                Operation::Branch {
                    condition: 3,
                    then_target: block + 1,
                    then_args: vec![],
                    else_target: block + 1,
                    else_args: vec![],
                },
            ));
        } else {
            let mut base = 0;
            for index in 0..offsets {
                let result = 4 + index;
                nodes.push(node(
                    block,
                    nodes.len(),
                    Some((result, Kind::Pointer)),
                    Operation::Offset {
                        base,
                        index: 1,
                        scale: 1,
                    },
                ));
                base = result;
            }
            nodes.push(node(block, nodes.len(), None, Operation::Return(2)));
        }
        blocks.push(Block {
            id: block,
            parameters: if block == 0 {
                vec![(0, Kind::Pointer)]
            } else {
                vec![]
            },
            nodes,
        });
    }
    Graph {
        entry: 0,
        parameters: vec![(0, Kind::Pointer)],
        blocks,
    }
}

fn observe(graph: &Graph) -> Result<Observations, ReadOnlySourceError> {
    graph::observe(
        graph,
        &[("abi_x0".into(), 64)],
        &E::uf("entry_memory", vec![], memory_sort()),
        Boundary::Source,
    )
}

#[test]
fn readonly_budget_unused_geometry_cannot_escape_the_aggregate_limit() {
    let graph = repeated_geometry(6, 246);
    assert_eq!(graph.blocks.len(), 7);
    assert_eq!(
        graph
            .blocks
            .iter()
            .map(|block| block.nodes.len())
            .sum::<usize>(),
        256
    );
    assert!(matches!(
        observe(&graph),
        Err(ReadOnlySourceError::Budget(
            "aggregate geometry expressions"
        ))
    ));
}

#[test]
fn readonly_budget_within_limit_same_destination_paths_remain_inspected() {
    let graph = repeated_geometry(1, 2);
    let observed = observe(&graph).expect("small duplicated path is in the bounded profile");
    assert!(observed.reads.is_empty());
    assert_eq!(
        observed.geometry.len(),
        4,
        "both paths retain both GEP premises"
    );
}

fn v(index: u32) -> ValueId {
    ValueId::new(index)
}

/// All dead loads read the same valid symbolic source interval. Their demands
/// are individually small, but every generated query carries source geometry.
fn repeated_queries(offsets: u32, loads: u32) -> Module {
    let mut module = Module::new("readonly_query_budget");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(0);
    let mut function = CoreFunction::new(FuncId::new(0), "readonly_many_demands", signature, entry);
    function.calling_conv = CallingConv::C;
    let mut block = CoreBlock::new(entry);
    block.params.push((v(0), Ty::Ptr));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(0),
        })
        .with_result(v(1)),
    );
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(7),
        })
        .with_result(v(2)),
    );
    let mut base = v(0);
    for index in 0..offsets {
        let result = v(3 + index);
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::U8,
                base,
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(result),
        );
        base = result;
    }
    for index in 0..loads {
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::U64,
                ptr: base,
                volatile: false,
                align: Some(8),
            })
            .with_result(v(3 + offsets + index)),
        );
    }
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn readonly_budget_cloned_preconditions_count_across_the_complete_query_collection() {
    let module = repeated_queries(30, 40);
    let lowering = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    // Isolate the collection limit from endpoint/profile refusals. Both
    // independently adapted endpoints and their observations must succeed.
    let source = core::graph(&module, 0).unwrap();
    let source = observe(&source).unwrap();
    assert_eq!(source.reads.len(), 40);
    let lowered = lir::graph(&lowering).unwrap();
    let lowered = observe(&lowered).unwrap();
    assert_eq!(lowered.reads.len(), 40);
    assert!(matches!(
        bind_read_only_source(&module, 0, &lowering),
        Err(ReadOnlySourceError::Budget(
            "aggregate obligation expressions"
        ))
    ));
}

#[test]
fn readonly_budget_small_complete_query_collection_is_not_refused() {
    let module = repeated_queries(2, 2);
    let lowering = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let pending = bind_read_only_source(&module, 0, &lowering).unwrap();
    assert_eq!(pending.read_requirements().len(), 2);
    assert_eq!(pending.lowering_reads().len(), 2);
    assert_eq!(pending.load_obligations().len(), 2);
}

#[test]
fn readonly_budget_load_demand_counts_guard_coverage_and_connectives() {
    assert_eq!(load_query_nodes(16_383, 16_383).unwrap(), MAX_QUERY_NODES);
    assert!(matches!(
        load_query_nodes(16_384, 16_383),
        Err(ReadOnlySourceError::Budget("load-demand expression"))
    ));
    // Neither argument alone exceeds the limit. Omitting the target guard
    // used to admit this final, oversized implication.
    assert!(matches!(
        load_query_nodes(MAX_QUERY_NODES - 2, 1),
        Err(ReadOnlySourceError::Budget("load-demand expression"))
    ));
    assert!(matches!(
        load_query_nodes(usize::MAX, 1),
        Err(ReadOnlySourceError::Budget("load-demand expression"))
    ));
}

#[test]
fn readonly_budget_total_reservation_is_exact_and_failure_does_not_consume_budget() {
    let mut used = 0;
    reserve_query(&mut used, MAX_TOTAL_QUERY_NODES - 1).unwrap();
    reserve_query(&mut used, 1).unwrap();
    assert_eq!(used, MAX_TOTAL_QUERY_NODES);
    assert!(matches!(
        reserve_query(&mut used, 1),
        Err(ReadOnlySourceError::Budget(
            "aggregate obligation expressions"
        ))
    ));
    assert_eq!(used, MAX_TOTAL_QUERY_NODES);
    assert!(matches!(
        reserve_query(&mut used, usize::MAX),
        Err(ReadOnlySourceError::Budget(
            "aggregate obligation expressions"
        ))
    ));
    assert_eq!(used, MAX_TOTAL_QUERY_NODES);
}
