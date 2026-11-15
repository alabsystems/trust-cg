// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Source CFG/SSA liveness controls under unchanged expression/query budgets.
//! Dead values may retire, not instructions, guards, geometry or load demands.
//! Concrete observations and connected adapter checks are not replay proof.

use super::*;
use crate::memory_proofs::{encode_store_le, zeroed_memory};
use crate::smt::{EvalEnv, EvalResult};
use std::convert::Infallible;
use trust_ir::{
    Block as CoreBlock, BlockId, Constant, FuncId, FuncTy, Inst, InstrNode, TargetInfo, Ty, ValueId,
};

fn block(
    id: u32,
    parameters: Vec<(u32, Kind)>,
    operations: Vec<(Option<(u32, Kind)>, Operation)>,
) -> Block {
    Block {
        id,
        parameters,
        nodes: operations
            .into_iter()
            .enumerate()
            .map(|(instruction, (result, operation))| Node {
                site: ReadOnlySite {
                    block: id,
                    instruction,
                },
                result,
                operation,
            })
            .collect(),
    }
}
fn constant(id: u32, kind: Kind, value: u64) -> (Option<(u32, Kind)>, Operation) {
    (Some((id, kind)), Operation::Constant(value))
}
fn observed(graph: &Graph) -> Result<Observations, ReadOnlySourceError> {
    let inputs: Vec<_> = (0..graph.parameters.len())
        .map(|i| (format!("abi_x{i}"), 64))
        .collect();
    graph::observe(
        graph,
        &inputs,
        &E::uf("entry_memory", vec![], memory_sort()),
        Boundary::Source,
    )
}
fn evaluate(expr: &E, inputs: &[u64], memory: &E) -> EvalResult {
    let mut env = EvalEnv::default();
    for (i, value) in inputs.iter().enumerate() {
        env.insert(format!("abi_x{i}"), *value);
    }
    let expr = expr.try_rewrite_dag::<Infallible>(&mut |node| {
        Ok(matches!(node, E::UF { name, args, ret_sort } if name == "entry_memory" && args.is_empty() && *ret_sort == memory_sort()).then(|| memory.clone()))
    }).unwrap().unwrap_or_else(|| expr.clone());
    expr.try_eval(&env).unwrap()
}

fn history(future_uses: bool) -> Graph {
    let mut entry = vec![constant(101, Kind::Word, 0), constant(102, Kind::Word, 7)];
    let mut previous = 9000;
    for level in 0..9 {
        let id = 10_000 + level;
        entry.push((
            Some((id, Kind::Word)),
            Operation::Binary {
                opcode: Opcode::Iadd,
                left: previous,
                right: previous,
            },
        ));
        previous = id;
    }
    for i in 0..40 {
        entry.push((Some((20_000 + i, Kind::Word)), Operation::Copy(previous)));
    }
    entry.push((
        Some((500, Kind::Boolean)),
        Operation::Compare {
            condition: IntCC::Equal,
            left: 9000,
            right: 101,
        },
    ));
    entry.push((
        None,
        Operation::Branch {
            condition: 500,
            then_target: 20,
            then_args: vec![],
            else_target: 30,
            else_args: vec![],
        },
    ));
    let arm = |id: u32| {
        let mut nodes = vec![];
        if future_uses {
            for i in 0..40 {
                nodes.push((
                    Some((100_000 + id * 100 + i, Kind::Word)),
                    Operation::Copy(20_000 + i),
                ));
            }
        }
        nodes.push((None, Operation::Return(102)));
        block(id, vec![], nodes)
    };
    Graph {
        entry: 70,
        parameters: vec![(9000, Kind::Word)],
        blocks: vec![arm(30), block(70, vec![(9000, Kind::Word)], entry), arm(20)],
    }
}

#[test]
fn long_dead_ssa_history_retires_before_fork_without_changing_any_fixed_limit() {
    // raw_arithmetic Iadd charges four nodes, so n -> 2*n+4.
    let max_term = 5 * (1usize << 9) - 4;
    assert_eq!(max_term, 2556);
    assert!(max_term <= super::super::MAX_NODES);
    assert!(
        40 * max_term > MAX_ENV_NODES,
        "the old retained-copy history alone exceeded the existing environment bound"
    );
    let graph = history(false);
    let result = observed(&graph)
        .expect("dead historical values no longer inflate the live fork environment");
    assert!(result.reads.is_empty());
    assert!(result.geometry.is_empty());
    for input in [0, 1, u64::MAX, 0x8000_0000_0000_0000] {
        assert_eq!(
            evaluate(
                &result.result.as_ref().unwrap().expr,
                &[input],
                &zeroed_memory()
            )
            .as_u64(),
            7
        );
    }
}

#[test]
fn the_same_large_values_future_used_on_both_successors_still_hit_the_original_budget() {
    assert!(matches!(
        observed(&history(true)),
        Err(ReadOnlySourceError::Budget("fork environments"))
    ));
}

#[test]
fn sparse_ids_reordered_blocks_and_parallel_edge_arguments_preserve_order() {
    let graph = Graph {
        entry: 70,
        parameters: vec![(9000, Kind::Word), (12, Kind::Word)],
        blocks: vec![
            block(
                4000,
                vec![(u32::MAX, Kind::Word), (700_000, Kind::Word)],
                vec![
                    (
                        Some((800_000, Kind::Word)),
                        Operation::Binary {
                            opcode: Opcode::Isub,
                            left: u32::MAX,
                            right: 700_000,
                        },
                    ),
                    (None, Operation::Return(800_000)),
                ],
            ),
            block(
                70,
                vec![(9000, Kind::Word), (12, Kind::Word)],
                vec![
                    (
                        Some((30_000, Kind::Boolean)),
                        Operation::Compare {
                            condition: IntCC::UnsignedLessThan,
                            left: 9000,
                            right: 12,
                        },
                    ),
                    (
                        None,
                        Operation::Branch {
                            condition: 30_000,
                            then_target: 4000,
                            then_args: vec![9000, 12],
                            else_target: 4000,
                            else_args: vec![12, 9000],
                        },
                    ),
                ],
            ),
        ],
    };
    let result = observed(&graph).unwrap();
    for (a, b) in [(5u64, 17u64), (17, 5), (u64::MAX, 0), (0, u64::MAX)] {
        let expected = if a < b {
            a.wrapping_sub(b)
        } else {
            b.wrapping_sub(a)
        };
        assert_eq!(
            evaluate(
                &result.result.as_ref().unwrap().expr,
                &[a, b],
                &zeroed_memory()
            )
            .as_u64(),
            expected
        );
    }
}

#[test]
fn constant_select_still_uses_both_dynamic_arms_and_inversion_is_preserved() {
    for invert in [false, true] {
        let graph = Graph {
            entry: 0,
            parameters: vec![(7000, Kind::Word), (9000, Kind::Word)],
            blocks: vec![block(
                0,
                vec![(7000, Kind::Word), (9000, Kind::Word)],
                vec![
                    constant(50, Kind::Boolean, 0),
                    (
                        Some((80, Kind::Word)),
                        Operation::Select {
                            condition: 50,
                            then_value: 7000,
                            else_value: 9000,
                            invert,
                        },
                    ),
                    (None, Operation::Return(80)),
                ],
            )],
        };
        let result = observed(&graph).unwrap();
        assert_eq!(
            evaluate(
                &result.result.as_ref().unwrap().expr,
                &[5, 19],
                &zeroed_memory()
            )
            .as_u64(),
            if invert { 5 } else { 19 }
        );
        let text = result.result.as_ref().unwrap().expr.to_string();
        assert!(text.contains("abi_x0"));
        assert!(text.contains("abi_x1"));
    }
}

#[test]
fn dead_load_in_constant_untaken_branch_keeps_address_guard_and_geometry() {
    let graph = Graph {
        entry: 5,
        parameters: vec![(100, Kind::Pointer)],
        blocks: vec![
            block(
                19,
                vec![],
                vec![
                    constant(501, Kind::Word, 8),
                    (
                        Some((502, Kind::Pointer)),
                        Operation::Offset {
                            base: 100,
                            index: 501,
                            scale: 1,
                        },
                    ),
                    (
                        Some((503, Kind::Word)),
                        Operation::Load {
                            address: 502,
                            alignment: 8,
                        },
                    ),
                    (None, Operation::Return(9)),
                ],
            ),
            block(
                5,
                vec![(100, Kind::Pointer)],
                vec![
                    constant(8, Kind::Boolean, 1),
                    constant(9, Kind::Word, 7),
                    (
                        None,
                        Operation::Branch {
                            condition: 8,
                            then_target: 21,
                            then_args: vec![],
                            else_target: 19,
                            else_args: vec![],
                        },
                    ),
                ],
            ),
            block(21, vec![], vec![(None, Operation::Return(9))]),
        ],
    };
    let result = observed(&graph).unwrap();
    assert_eq!(result.reads.len(), 1);
    assert_eq!(result.geometry.len(), 2);
    assert_eq!(
        result.reads[0].site,
        ReadOnlySite {
            block: 19,
            instruction: 2
        }
    );
    assert_eq!(
        evaluate(&result.reads[0].guard.expr, &[0x1000], &zeroed_memory()),
        EvalResult::Bool(false)
    );
    assert_eq!(
        evaluate(&result.reads[0].address.expr, &[0x1000], &zeroed_memory()).as_u64(),
        0x1008
    );
    assert_eq!(
        evaluate(
            &result.result.as_ref().unwrap().expr,
            &[0x1000],
            &zeroed_memory()
        )
        .as_u64(),
        7
    );
}

#[test]
fn unused_invalid_instructions_and_nondominating_operands_remain_errors() {
    let invalids = [
        (Some((20, Kind::Word)), Operation::Copy(999_999)),
        (Some((20, Kind::Boolean)), Operation::Constant(2)),
        (
            Some((20, Kind::Word)),
            Operation::Binary {
                opcode: Opcode::Iadd,
                left: 0,
                right: 0,
            },
        ),
    ];
    for invalid in invalids {
        let graph = Graph {
            entry: 0,
            parameters: vec![(0, Kind::Pointer)],
            blocks: vec![block(
                0,
                vec![(0, Kind::Pointer)],
                vec![
                    constant(10, Kind::Word, 7),
                    invalid,
                    (None, Operation::Return(10)),
                ],
            )],
        };
        assert!(
            matches!(observed(&graph), Err(ReadOnlySourceError::Source(_))),
            "retiring a dead result cannot erase an invalid instruction"
        );
    }
    let graph = Graph {
        entry: 0,
        parameters: vec![(0, Kind::Word)],
        blocks: vec![
            block(
                0,
                vec![(0, Kind::Word)],
                vec![
                    constant(1, Kind::Boolean, 1),
                    (
                        None,
                        Operation::Branch {
                            condition: 1,
                            then_target: 10,
                            then_args: vec![],
                            else_target: 20,
                            else_args: vec![],
                        },
                    ),
                ],
            ),
            block(
                10,
                vec![],
                vec![constant(50, Kind::Word, 7), (None, Operation::Return(50))],
            ),
            block(
                20,
                vec![],
                vec![
                    (Some((60, Kind::Word)), Operation::Copy(50)),
                    (None, Operation::Return(0)),
                ],
            ),
        ],
    };
    assert!(
        matches!(observed(&graph), Err(ReadOnlySourceError::Source(_))),
        "constant untaken branch still cannot use a sibling definition"
    );
}

#[test]
fn transitive_cross_block_uses_and_dead_load_results_preserve_the_real_observation() {
    let graph = Graph {
        entry: 3,
        parameters: vec![(100, Kind::Pointer)],
        blocks: vec![
            block(
                90,
                vec![(300, Kind::Pointer)],
                vec![
                    (
                        Some((301, Kind::Word)),
                        Operation::Load {
                            address: 300,
                            alignment: 8,
                        },
                    ),
                    constant(302, Kind::Word, 1),
                    (
                        Some((303, Kind::Word)),
                        Operation::Binary {
                            opcode: Opcode::Iadd,
                            left: 301,
                            right: 302,
                        },
                    ),
                    (None, Operation::Return(303)),
                ],
            ),
            block(
                3,
                vec![(100, Kind::Pointer)],
                vec![
                    (Some((101, Kind::Pointer)), Operation::Copy(100)),
                    (
                        Some((102, Kind::Word)),
                        Operation::Load {
                            address: 100,
                            alignment: 8,
                        },
                    ),
                    (
                        None,
                        Operation::Jump {
                            target: 90,
                            args: vec![101],
                        },
                    ),
                ],
            ),
        ],
    };
    let result = observed(&graph).unwrap();
    assert_eq!(
        result.reads.len(),
        2,
        "unused entry load remains a caller demand"
    );
    assert_eq!(result.geometry.len(), 2);
    let memory = encode_store_le(
        &zeroed_memory(),
        &E::bv_const(0x1000, 64),
        &E::bv_const(u64::MAX, 64),
        8,
    );
    assert_eq!(
        evaluate(&result.result.as_ref().unwrap().expr, &[0x1000], &memory).as_u64(),
        0
    );
    for read in &result.reads {
        assert_eq!(
            evaluate(&read.address.expr, &[0x1000], &memory).as_u64(),
            0x1000
        );
        assert_eq!(
            evaluate(&read.guard.expr, &[0x1000], &memory),
            EvalResult::Bool(true)
        );
    }
}

#[test]
fn unused_edge_formals_still_validate_every_argument_kind_and_definition() {
    for argument in [0, 999_999] {
        let graph = Graph {
            entry: 10,
            parameters: vec![(0, Kind::Pointer)],
            blocks: vec![
                block(
                    90,
                    vec![(u32::MAX, Kind::Word)],
                    vec![(None, Operation::Return(7))],
                ),
                block(
                    10,
                    vec![(0, Kind::Pointer)],
                    vec![
                        constant(7, Kind::Word, 23),
                        (
                            None,
                            Operation::Jump {
                                target: 90,
                                args: vec![argument],
                            },
                        ),
                    ],
                ),
            ],
        };
        assert!(
            matches!(observed(&graph), Err(ReadOnlySourceError::Source(_))),
            "unused Word formal must not hide Pointer or undefined incoming argument {argument}"
        );
    }
}

#[test]
fn dead_duplicate_ssa_definitions_are_refused_across_constant_untaken_blocks() {
    let graph = Graph {
        entry: 0,
        parameters: vec![(0, Kind::Word)],
        blocks: vec![
            block(
                0,
                vec![(0, Kind::Word)],
                vec![
                    constant(1, Kind::Boolean, 1),
                    (
                        None,
                        Operation::Branch {
                            condition: 1,
                            then_target: 10,
                            then_args: vec![],
                            else_target: 20,
                            else_args: vec![],
                        },
                    ),
                ],
            ),
            block(
                10,
                vec![],
                vec![
                    constant(u32::MAX, Kind::Word, 7),
                    (None, Operation::Return(0)),
                ],
            ),
            block(
                20,
                vec![],
                vec![
                    constant(u32::MAX, Kind::Word, 9),
                    (None, Operation::Return(0)),
                ],
            ),
        ],
    };
    assert!(matches!(
        observed(&graph),
        Err(ReadOnlySourceError::Source("duplicate SSA definition"))
    ));
}

#[test]
fn a_join_cannot_import_a_definition_from_only_one_constant_branch() {
    let graph = Graph {
        entry: 0,
        parameters: vec![(0, Kind::Word)],
        blocks: vec![
            block(
                30,
                vec![],
                vec![
                    (Some((60, Kind::Word)), Operation::Copy(50)),
                    (None, Operation::Return(0)),
                ],
            ),
            block(
                20,
                vec![],
                vec![(
                    None,
                    Operation::Jump {
                        target: 30,
                        args: vec![],
                    },
                )],
            ),
            block(
                0,
                vec![(0, Kind::Word)],
                vec![
                    constant(1, Kind::Boolean, 1),
                    (
                        None,
                        Operation::Branch {
                            condition: 1,
                            then_target: 10,
                            then_args: vec![],
                            else_target: 20,
                            else_args: vec![],
                        },
                    ),
                ],
            ),
            block(
                10,
                vec![],
                vec![
                    constant(50, Kind::Word, 7),
                    (
                        None,
                        Operation::Jump {
                            target: 30,
                            args: vec![],
                        },
                    ),
                ],
            ),
        ],
    };
    assert!(
        matches!(
            observed(&graph),
            Err(ReadOnlySourceError::Source(
                "undefined or nondominating SSA operand"
            ))
        ),
        "the unused join result and constant untaken predecessor cannot erase the invalid use"
    );
}

pub(super) fn original_branch_module(with_edge_parameters: bool) -> Module {
    let mut module = Module::new("source_liveness_connected_branch");
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::U64],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = trust_ir::Function::new(
        FuncId::new(91),
        "source_liveness_connected_branch",
        signature,
        BlockId::new(70),
    );
    let v = ValueId::new;
    let literal = |result, value| {
        InstrNode::new(Inst::Const {
            ty: Ty::U64,
            value: Constant::Int(value),
        })
        .with_result(v(result))
    };
    let mut entry = CoreBlock::new(BlockId::new(70));
    entry.params = vec![(v(100), Ty::Ptr), (v(200), Ty::U64)];
    entry.body = vec![
        literal(300, 0),
        InstrNode::new(Inst::ICmp {
            op: trust_ir::ICmpOp::Eq,
            ty: Ty::U64,
            lhs: v(200),
            rhs: v(300),
        })
        .with_result(v(400)),
        InstrNode::new(Inst::CondBr {
            cond: v(400),
            then_target: BlockId::new(90),
            then_args: if with_edge_parameters {
                vec![v(100)]
            } else {
                vec![]
            },
            else_target: BlockId::new(10),
            else_args: if with_edge_parameters {
                vec![v(100)]
            } else {
                vec![]
            },
        }),
    ];
    let mut yes = CoreBlock::new(BlockId::new(90));
    yes.params = if with_edge_parameters {
        vec![(v(900), Ty::Ptr)]
    } else {
        vec![]
    };
    yes.body = vec![
        InstrNode::new(Inst::Load {
            ty: Ty::U64,
            ptr: v(if with_edge_parameters { 900 } else { 100 }),
            volatile: false,
            align: Some(8),
        })
        .with_result(v(901)),
        InstrNode::new(Inst::Return {
            values: vec![v(901)],
        }),
    ];
    let mut no = CoreBlock::new(BlockId::new(10));
    no.params = if with_edge_parameters {
        vec![(v(500), Ty::Ptr)]
    } else {
        vec![]
    };
    no.body = vec![
        InstrNode::new(Inst::Load {
            ty: Ty::U64,
            ptr: v(if with_edge_parameters { 500 } else { 100 }),
            volatile: false,
            align: Some(8),
        })
        .with_result(v(501)),
        literal(502, 7),
        InstrNode::new(Inst::Return {
            values: vec![v(502)],
        }),
    ];
    function.blocks = vec![no, entry, yes];
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn original_core_edge_parameter_adapter_transport_has_checked_pending_projection() {
    // Preserve the exact legal original fixture which failed its first
    // connected run. The ordinary adapter's retained parameter copies repeat
    // LIR names. Raw SSA admission still refuses them; only exact checked
    // source-edge transport may project them into pending graph arguments.
    let module = original_branch_module(true);
    let original = format!("{module:#?}");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    assert!(matches!(
        super::lir::graph(&lir),
        Err(ReadOnlySourceError::Lowering(
            "duplicate retained LIR SSA definition"
        ))
    ));
    let projection =
        super::scalar_edge_projection::check_scalar_block_arguments(&module, 0, &lir).unwrap();
    assert_eq!(projection.transports().len(), 2);
    let queries = bind_read_only_source(&module, 0, &lir)
        .expect("checked ordinary scalar edge copies must project");
    let memory = encode_store_le(
        &zeroed_memory(),
        &E::bv_const(0x1000, 64),
        &E::bv_const(23, 64),
        8,
    );
    for (condition, expected) in [(0, 23), (1, 7), (u64::MAX, 7)] {
        let inputs = [0x1000, condition];
        assert_eq!(
            evaluate(&queries.return_obligation().trust_ir_expr, &inputs, &memory).as_u64(),
            expected
        );
        assert_eq!(
            evaluate(&queries.return_obligation().aarch64_expr, &inputs, &memory).as_u64(),
            expected
        );
    }
    assert_eq!(format!("{module:#?}"), original);
    println!(
        "SOURCE_LIVENESS_ORIGINAL_EDGE_PARAMETER_TRANSPORT function=91 ordinary_adapter_translated=true read_only_lir_bound=true checked_scalar_edge_projection=true proof_credit=false"
    );
}

#[test]
fn original_core_dominating_pointer_branch_and_adapter_keep_complete_pending_relations() {
    let module = original_branch_module(false);
    let original = format!("{module:#?}");
    let (lir, _) = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap();
    let queries = bind_read_only_source(&module, 0, &lir)
        .expect("ordinary original-Core branch must bind both paths");
    assert_eq!(queries.read_requirements().len(), 2);
    assert_eq!(queries.lowering_reads().len(), 2);
    assert_eq!(queries.load_obligations().len(), 2);
    let memory = encode_store_le(
        &zeroed_memory(),
        &E::bv_const(0x1000, 64),
        &E::bv_const(23, 64),
        8,
    );
    for (condition, expected) in [(0, 23), (1, 7), (u64::MAX, 7)] {
        let inputs = [0x1000, condition];
        assert_eq!(
            evaluate(&queries.return_obligation().trust_ir_expr, &inputs, &memory).as_u64(),
            expected
        );
        assert_eq!(
            evaluate(&queries.return_obligation().aarch64_expr, &inputs, &memory).as_u64(),
            expected
        );
        for demand in queries.load_obligations() {
            assert_eq!(
                evaluate(&demand.aarch64_expr, &inputs, &memory),
                EvalResult::Bool(true)
            );
        }
    }
    assert_eq!(format!("{module:#?}"), original);
}
