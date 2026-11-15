// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Finite controls for pending scalar-memory queries. Definition expansion is
//! test-only concrete evaluation, not independent replay, initialized storage,
//! pointer provenance, native execution or permission/publication authority.

use super::*;
use crate::smt::{EvalEnv, EvalResult};
use std::convert::Infallible;
use trust_cg_lower::instructions::{Instruction, Value as LirValue};
use trust_ir::{
    BinOp, Block as CoreBlock, BlockId, CallingConv, CastOp, Constant, FuncId, FuncTy,
    Function as CoreFunction, Inst, InstrNode, TargetInfo, Ty, ValueId,
};

fn variable(name: &str, bits: u32) -> Term {
    Term::leaf(E::var(name, bits))
}

fn definition_name(term: &Term) -> &str {
    let E::UF { name, args, .. } = &term.expr else {
        panic!("definition must return its exact zero-argument symbol");
    };
    assert!(args.is_empty());
    name
}

#[test]
fn scalar_definitions_reject_unknown_cross_stage_and_uncaptured_inputs() {
    for expression in [
        E::var("other_input", 64),
        E::var("abi_x0", 32),
        E::var("abi_x8", 64),
        E::var("observe", 64),
        E::uf("unknown", vec![], SmtSort::BitVec(64)),
        E::uf("scalar_memory_lir_d0", vec![], SmtSort::BitVec(64)),
        E::uf("scalar_memory_core_d0", vec![], SmtSort::BitVec(64)),
        E::uf("recursive", vec![E::var("abi_x0", 64)], SmtSort::BitVec(64)),
    ] {
        let mut definitions = Definitions::new(Endpoint::Core);
        let sort = if expression.try_bv_width().ok() == Some(32) {
            SmtSort::BitVec(32)
        } else {
            SmtSort::BitVec(64)
        };
        assert!(matches!(
            definitions.bind(Term::leaf(expression), sort),
            Err(ReadOnlySourceError::Source(_))
        ));
        assert!(definitions.equations.is_empty());
        assert!(definitions.sorts.is_empty());
        assert_eq!(definitions.nodes, 0);
    }
}

#[test]
fn scalar_definitions_preserve_sort_and_prior_occurrences_without_self_reference() {
    let mut definitions = Definitions::new(Endpoint::Core);
    let first = definitions
        .bind(variable("abi_x0", 64), SmtSort::BitVec(64))
        .unwrap();
    let retained = definitions.equations[0].clone();
    let second = definitions
        .bind(first.clone(), SmtSort::BitVec(64))
        .unwrap();
    assert_ne!(definition_name(&first), definition_name(&second));
    assert_eq!(definitions.equations[0], retained);
    let E::Eq { lhs, rhs } = &definitions.equations[1] else {
        panic!("exact equation");
    };
    assert_eq!(lhs.as_ref(), &second.expr);
    assert_eq!(rhs.as_ref(), &first.expr);

    let before = definitions.equations.len();
    for (expression, sort) in [
        (
            E::uf(definition_name(&first), vec![], SmtSort::BitVec(32)),
            SmtSort::BitVec(32),
        ),
        (
            E::uf("scalar_memory_core_d2", vec![], SmtSort::BitVec(64)),
            SmtSort::BitVec(64),
        ),
        (
            E::uf(definition_name(&first), vec![], SmtSort::BitVec(64)),
            SmtSort::BitVec(32),
        ),
    ] {
        assert!(matches!(
            definitions.bind(Term::leaf(expression), sort),
            Err(ReadOnlySourceError::Source(_))
        ));
        assert_eq!(definitions.equations.len(), before);
    }
    let narrow = variable("abi_x0", 64)
        .unary(1, |e| e.extract(31, 0))
        .unwrap();
    assert!(definitions.bind(narrow, SmtSort::BitVec(32)).is_ok());
}

pub(in crate::source_bound_body::read_only_source) type Substitutions =
    HashMap<String, (SmtSort, E)>;

fn substitute(expression: &E, substitutions: &Substitutions) -> E {
    expression
        .try_rewrite_dag::<Infallible>(&mut |node| {
            Ok(match node {
                E::UF {
                    name,
                    args,
                    ret_sort,
                } if args.is_empty() => substitutions.get(name).map(|(sort, value)| {
                    assert_eq!(
                        ret_sort, sort,
                        "exact sort retained by concrete substitution"
                    );
                    value.clone()
                }),
                _ => None,
            })
        })
        .unwrap()
        .unwrap_or_else(|| expression.clone())
}

pub(in crate::source_bound_body::read_only_source) fn expand(
    equations: &[E],
    memory: &E,
) -> Substitutions {
    let mut substitutions =
        HashMap::from([("entry_memory".into(), (memory_sort(), memory.clone()))]);
    for equation in equations {
        let E::Eq { lhs, rhs } = equation else {
            panic!("semantic equation, not caller geometry");
        };
        let E::UF {
            name,
            args,
            ret_sort,
        } = lhs.as_ref()
        else {
            panic!("defined zero-argument symbol");
        };
        assert!(args.is_empty());
        assert!(
            !substitutions.contains_key(name),
            "each occurrence is fresh"
        );
        let expanded = substitute(rhs, &substitutions);
        let mut remaining = vec![&expanded];
        while let Some(node) = remaining.pop() {
            assert!(
                !matches!(node, E::UF { .. }),
                "RHS must reference only earlier definitions"
            );
            node.for_each_child(&mut |child| remaining.push(child));
        }
        substitutions.insert(name.clone(), (ret_sort.clone(), expanded));
    }
    substitutions
}

pub(in crate::source_bound_body::read_only_source) fn evaluate(
    expression: &E,
    substitutions: &Substitutions,
    environment: &EvalEnv,
) -> EvalResult {
    substitute(expression, substitutions)
        .try_eval(environment)
        .expect("finite byte-array fixture")
}

fn v(id: u32) -> ValueId {
    ValueId::new(id)
}
fn core_node(instruction: Inst, result: Option<u32>) -> InstrNode {
    let mut node = InstrNode::new(instruction);
    node.results.extend(result.map(v));
    node
}

fn module(name: &str, parameters: usize) -> (Module, CoreFunction, CoreBlock) {
    let mut module = Module::new(name);
    module.target_info = Some(TargetInfo {
        triple: "aarch64-apple-darwin".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr; parameters],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let entry = BlockId::new(0);
    let mut function = CoreFunction::new(FuncId::new(0), name, signature, entry);
    function.calling_conv = CallingConv::C;
    let mut block = CoreBlock::new(entry);
    block.params = (0..parameters).map(|i| (v(i as u32), Ty::Ptr)).collect();
    (module, function, block)
}

fn alias_consumer() -> Module {
    let (mut module, mut function, mut block) = module("ordinary_aliasing_scalar_consumer", 2);
    block.body = vec![
        core_node(
            Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            },
            Some(2),
        ),
        core_node(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            Some(3),
        ),
        core_node(
            Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::U64,
                lhs: v(3),
                rhs: v(2),
            },
            Some(4),
        ),
        core_node(
            Inst::Store {
                ty: Ty::U64,
                ptr: v(1),
                value: v(4),
                volatile: false,
                align: Some(8),
            },
            None,
        ),
        core_node(
            Inst::Load {
                ty: Ty::U64,
                ptr: v(0),
                volatile: false,
                align: Some(8),
            },
            Some(5),
        ),
        core_node(Inst::Return { values: vec![v(5)] }, None),
    ];
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

const PARENT: u64 = 0x1000;
const OUTPUT: u64 = 0x2000;
const ORIGINAL: u64 = 0x0807_0605_0403_0201;

fn fixture(output: u64) -> (E, EvalEnv) {
    let mut memory = E::const_array(SmtSort::BitVec(64), E::bv_const(0xa5, 8));
    memory = encode_store_le(
        &memory,
        &E::bv_const(PARENT, 64),
        &E::bv_const(ORIGINAL, 64),
        8,
    );
    if output != PARENT {
        memory = encode_store_le(
            &memory,
            &E::bv_const(output, 64),
            &E::bv_const(0xe8e7_e6e5_e4e3_e2e1, 64),
            8,
        );
    }
    let mut environment = EvalEnv::default();
    environment.insert("abi_x0".into(), PARENT);
    environment.insert("abi_x1".into(), output);
    environment.insert("observe".into(), output);
    (memory, environment)
}

fn all_obligations<'q>(queries: &'q ScalarMemorySourceQueries<'_>) -> Vec<&'q ProofObligation> {
    std::iter::once(queries.status_obligation())
        .chain(std::iter::once(queries.memory_obligation()))
        .chain(queries.read_obligations())
        .chain(queries.write_obligations())
        .collect()
}

fn holds(
    obligation: &ProofObligation,
    substitutions: &Substitutions,
    environment: &EvalEnv,
) -> bool {
    assert!(
        obligation
            .preconditions
            .iter()
            .all(|p| evaluate(p, substitutions, environment).as_bool()),
        "original geometry and exact definitions must hold"
    );
    evaluate(&obligation.trust_ir_expr, substitutions, environment)
        == evaluate(&obligation.aarch64_expr, substitutions, environment)
}

#[test]
fn scalar_ordinary_consumer_threads_aliases_and_keeps_all_definitions_in_every_query() {
    let module = alias_consumer();
    let lowering = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let queries = bind_scalar_memory_source(&module, 0, &lowering).unwrap();
    assert_eq!(queries.source_reads().len(), 2);
    assert_eq!(queries.source_writes().len(), 1);
    assert_eq!(queries.lowering_reads().len(), 2);
    assert_eq!(queries.lowering_writes().len(), 1);
    assert!(std::ptr::eq(queries.module(), &module));
    assert!(std::ptr::eq(queries.lir(), &lowering));
    for obligation in all_obligations(&queries) {
        assert_eq!(
            obligation.preconditions.len(),
            queries.source_geometry().len() + queries.encoding_definitions().len()
        );
        assert_eq!(
            &obligation.preconditions[..queries.source_geometry().len()],
            queries.source_geometry()
        );
        assert_eq!(
            &obligation.preconditions[queries.source_geometry().len()..],
            queries.encoding_definitions()
        );
    }
    for output in [PARENT, OUTPUT] {
        let (memory, mut environment) = fixture(output);
        let substitutions = expand(queries.encoding_definitions(), &memory);
        let expected = if output == PARENT {
            ORIGINAL + 1
        } else {
            ORIGINAL
        };
        assert_eq!(
            evaluate(
                &queries.status_obligation().trust_ir_expr,
                &substitutions,
                &environment
            )
            .as_u64(),
            expected
        );
        for observer in [
            PARENT - 1,
            PARENT,
            PARENT + 3,
            PARENT + 4,
            PARENT + 7,
            PARENT + 8,
            output - 1,
            output,
            output + 3,
            output + 4,
            output + 7,
            output + 8,
            0x7000,
        ] {
            environment.insert("observe".into(), observer);
            assert!(all_obligations(&queries).into_iter().all(|q| holds(
                q,
                &substitutions,
                &environment
            )));
        }
    }
}

#[test]
fn scalar_stale_alias_load_is_falsified_by_status_not_hidden_by_equal_final_memory() {
    let module = alias_consumer();
    let mut lowering = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let block = lowering.blocks.get_mut(&lowering.entry_block).unwrap();
    let loads: Vec<_> = block
        .instructions
        .iter()
        .enumerate()
        .filter_map(|(i, n)| matches!(n.opcode, Opcode::Load { .. }).then_some(i))
        .collect();
    let previous = block.instructions[loads[0]].results[0];
    block.instructions[loads[1]].opcode = Opcode::Copy;
    block.instructions[loads[1]].args = vec![previous];
    let queries = bind_scalar_memory_source(&module, 0, &lowering).unwrap();
    let (memory, environment) = fixture(PARENT);
    let substitutions = expand(queries.encoding_definitions(), &memory);
    assert!(!holds(
        queries.status_obligation(),
        &substitutions,
        &environment
    ));
    assert!(holds(
        queries.memory_obligation(),
        &substitutions,
        &environment
    ));
}

#[test]
fn scalar_extra_dead_read_is_falsified_even_when_status_and_final_memory_agree() {
    let module = alias_consumer();
    let mut lowering = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let block = lowering.blocks.get_mut(&lowering.entry_block).unwrap();
    let output = block.params[1].0;
    block.instructions.insert(
        block.instructions.len() - 1,
        Instruction {
            opcode: Opcode::Load {
                ty: LirType::I64,
                align: Some(8),
            },
            args: vec![output],
            results: vec![LirValue(100)],
        },
    );
    lowering.value_types.insert(LirValue(100), LirType::I64);
    let queries = bind_scalar_memory_source(&module, 0, &lowering).unwrap();
    let (memory, environment) = fixture(OUTPUT);
    let substitutions = expand(queries.encoding_definitions(), &memory);
    assert!(holds(
        queries.status_obligation(),
        &substitutions,
        &environment
    ));
    assert!(holds(
        queries.memory_obligation(),
        &substitutions,
        &environment
    ));
    assert!(
        queries
            .read_obligations()
            .iter()
            .any(|q| !holds(q, &substitutions, &environment))
    );
}

#[test]
fn scalar_write_then_restore_needs_its_own_writable_footprint() {
    let module = alias_consumer();
    let mut lowering = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let block = lowering.blocks.get_mut(&lowering.entry_block).unwrap();
    let parent = block.params[0].0;
    let original = block
        .instructions
        .iter()
        .find(|n| matches!(n.opcode, Opcode::Load { .. }))
        .unwrap()
        .results[0];
    let updated = block
        .instructions
        .iter()
        .find(|n| matches!(n.opcode, Opcode::Iadd))
        .unwrap()
        .results[0];
    for value in [updated, original] {
        block.instructions.insert(
            block.instructions.len() - 1,
            Instruction {
                opcode: Opcode::Store {
                    ty: LirType::I64,
                    align: Some(8),
                },
                args: vec![value, parent],
                results: vec![],
            },
        );
    }
    let queries = bind_scalar_memory_source(&module, 0, &lowering).unwrap();
    let (memory, mut environment) = fixture(OUTPUT);
    let substitutions = expand(queries.encoding_definitions(), &memory);
    environment.insert("observe".into(), PARENT);
    assert!(holds(
        queries.status_obligation(),
        &substitutions,
        &environment
    ));
    assert!(holds(
        queries.memory_obligation(),
        &substitutions,
        &environment
    ));
    assert!(
        queries
            .write_obligations()
            .iter()
            .any(|q| !holds(q, &substitutions, &environment))
    );
}

#[test]
fn scalar_narrow_store_cannot_hide_changed_neighbour_bytes() {
    let module = alias_consumer();
    let mut lowering = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let block = lowering.blocks.get_mut(&lowering.entry_block).unwrap();
    let store = block
        .instructions
        .iter()
        .position(|n| matches!(n.opcode, Opcode::Store { .. }))
        .unwrap();
    block.instructions.insert(
        store,
        Instruction {
            opcode: Opcode::Iconst {
                ty: LirType::I32,
                imm: 0x0403_0202,
            },
            args: vec![],
            results: vec![LirValue(100)],
        },
    );
    block.instructions[store + 1].opcode = Opcode::Store {
        ty: LirType::I32,
        align: Some(4),
    };
    block.instructions[store + 1].args[0] = LirValue(100);
    lowering.value_types.insert(LirValue(100), LirType::I32);
    let queries = bind_scalar_memory_source(&module, 0, &lowering).unwrap();
    let (memory, mut environment) = fixture(OUTPUT);
    let substitutions = expand(queries.encoding_definitions(), &memory);
    environment.insert("observe".into(), OUTPUT);
    assert!(
        holds(queries.memory_obligation(), &substitutions, &environment),
        "low bytes intentionally unchanged"
    );
    environment.insert("observe".into(), OUTPUT + 4);
    assert!(!holds(
        queries.memory_obligation(),
        &substitutions,
        &environment
    ));
    assert!(
        queries
            .write_obligations()
            .iter()
            .all(|q| holds(q, &substitutions, &environment)),
        "permission coverage cannot replace final-byte equality"
    );
}

#[test]
fn scalar_signed_i32_constant_store_and_zext_preserve_upper_neighbours() {
    let (mut module, mut function, mut block) = module("ordinary_i32_zext_consumer", 1);
    block.body = vec![
        core_node(
            Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(-1),
            },
            Some(1),
        ),
        core_node(
            Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: Some(4),
            },
            None,
        ),
        core_node(
            Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: Some(4),
            },
            Some(2),
        ),
        core_node(
            Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I32,
                dst_ty: Ty::U64,
                operand: v(2),
            },
            Some(3),
        ),
        core_node(Inst::Return { values: vec![v(3)] }, None),
    ];
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    let lowering = trust_cg_lower::translate_function_with_license(
        &module.functions[0],
        &module,
        &crate::license_test_support::permit_unlicensed(),
    )
    .unwrap()
    .0;
    let queries = bind_scalar_memory_source(&module, 0, &lowering).unwrap();
    let (memory, mut environment) = fixture(PARENT);
    let substitutions = expand(queries.encoding_definitions(), &memory);
    assert_eq!(
        evaluate(
            &queries.status_obligation().trust_ir_expr,
            &substitutions,
            &environment
        )
        .as_u64(),
        u64::from(u32::MAX)
    );
    assert!(holds(
        queries.status_obligation(),
        &substitutions,
        &environment
    ));
    for offset in 0..9 {
        environment.insert("observe".into(), PARENT + offset);
        assert!(holds(
            queries.memory_obligation(),
            &substitutions,
            &environment
        ));
        if (4..8).contains(&offset) {
            assert_eq!(
                evaluate(
                    &queries.memory_obligation().trust_ir_expr,
                    &substitutions,
                    &environment
                )
                .as_u64(),
                (ORIGINAL >> (offset * 8)) & 0xff
            );
        }
    }
}

fn graph_node(
    block: u32,
    instruction: usize,
    result: Option<(u32, Kind)>,
    operation: Operation,
) -> Node {
    Node {
        site: ReadOnlySite { block, instruction },
        result,
        operation,
    }
}

#[test]
fn scalar_fork_memory_versions_are_fresh_and_do_not_import_sibling_writes() {
    let graph = Graph {
        entry: 0,
        parameters: vec![(0, Kind::Pointer)],
        blocks: vec![
            Block {
                id: 0,
                parameters: vec![(0, Kind::Pointer)],
                nodes: vec![
                    graph_node(0, 0, Some((1, Kind::Word)), Operation::Constant(9)),
                    graph_node(0, 1, Some((2, Kind::Boolean)), Operation::Constant(1)),
                    graph_node(
                        0,
                        2,
                        None,
                        Operation::Branch {
                            condition: 2,
                            then_target: 1,
                            then_args: vec![],
                            else_target: 2,
                            else_args: vec![],
                        },
                    ),
                ],
            },
            Block {
                id: 1,
                parameters: vec![],
                nodes: vec![
                    graph_node(
                        1,
                        0,
                        None,
                        Operation::Store {
                            address: 0,
                            value: 1,
                            alignment: 8,
                            byte_width: 8,
                        },
                    ),
                    graph_node(
                        1,
                        1,
                        Some((3, Kind::Word)),
                        Operation::MemoryLoad {
                            address: 0,
                            alignment: 8,
                            byte_width: 8,
                        },
                    ),
                    graph_node(1, 2, None, Operation::Return(3)),
                ],
            },
            Block {
                id: 2,
                parameters: vec![],
                nodes: vec![
                    graph_node(
                        2,
                        0,
                        None,
                        Operation::Store {
                            address: 0,
                            value: 1,
                            alignment: 8,
                            byte_width: 8,
                        },
                    ),
                    graph_node(
                        2,
                        1,
                        Some((4, Kind::Word)),
                        Operation::MemoryLoad {
                            address: 0,
                            alignment: 8,
                            byte_width: 8,
                        },
                    ),
                    graph_node(2, 2, None, Operation::Return(4)),
                ],
            },
        ],
    };
    let observed = graph::observe_profile(
        &graph,
        &[("abi_x0".into(), 64)],
        &E::uf("entry_memory", vec![], memory_sort()),
        Boundary::Source,
        Profile::ScalarMemory(Endpoint::Core),
    )
    .unwrap();
    let memory = observed.memory.as_ref().unwrap();
    assert_eq!(observed.reads.len(), 2);
    assert_eq!(
        memory.writes.len(),
        2,
        "untaken constant branch still retains store demand"
    );
    assert_eq!(memory.returns.len(), 2);
    assert_eq!(memory.definitions.equations.len(), 4);
    let (initial, environment) = fixture(PARENT);
    let substitutions = expand(&memory.definitions.equations, &initial);
    assert_eq!(
        evaluate(
            &observed.result.as_ref().unwrap().expr,
            &substitutions,
            &environment
        )
        .as_u64(),
        9
    );
    let E::Eq {
        lhs: first_store, ..
    } = &memory.definitions.equations[0]
    else {
        panic!("store definition");
    };
    let E::Eq {
        lhs: next_store,
        rhs: next_rhs,
    } = &memory.definitions.equations[2]
    else {
        panic!("other store definition");
    };
    assert_ne!(first_store, next_store);
    let mut pending = vec![next_rhs.as_ref()];
    while let Some(node) = pending.pop() {
        assert_ne!(
            node,
            first_store.as_ref(),
            "other path starts from entry memory, not its sibling's store"
        );
        node.for_each_child(&mut |child| pending.push(child));
    }
}

#[test]
fn scalar_i32_shifts_keep_exact_width_sign_and_zero_extension() {
    for (opcode, expected) in [
        (Opcode::Ishl, u64::from(u32::MAX - 1)),
        (Opcode::Ushr, u64::from(u32::MAX >> 1)),
        (Opcode::Sshr, u64::from(u32::MAX)),
    ] {
        let (mut module, mut function, mut block) = module("ordinary_i32_shift_consumer", 1);
        let op = match opcode {
            Opcode::Ishl => BinOp::Shl,
            Opcode::Ushr => BinOp::LShr,
            Opcode::Sshr => BinOp::AShr,
            _ => unreachable!(),
        };
        block.body = vec![
            core_node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(-1),
                },
                Some(1),
            ),
            core_node(
                Inst::Const {
                    ty: Ty::I32,
                    value: Constant::Int(1),
                },
                Some(2),
            ),
            core_node(
                Inst::BinOp {
                    op,
                    ty: Ty::I32,
                    lhs: v(1),
                    rhs: v(2),
                },
                Some(3),
            ),
            core_node(
                Inst::Cast {
                    op: CastOp::ZExt,
                    src_ty: Ty::I32,
                    dst_ty: Ty::U64,
                    operand: v(3),
                },
                Some(4),
            ),
            core_node(Inst::Return { values: vec![v(4)] }, None),
        ];
        function.blocks.push(block);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        let lowering = trust_cg_lower::translate_function_with_license(
            &module.functions[0],
            &module,
            &crate::license_test_support::permit_unlicensed(),
        )
        .unwrap()
        .0;
        let queries = bind_scalar_memory_source(&module, 0, &lowering).unwrap();
        let (memory, environment) = fixture(PARENT);
        let substitutions = expand(queries.encoding_definitions(), &memory);
        assert_eq!(
            evaluate(
                &queries.status_obligation().trust_ir_expr,
                &substitutions,
                &environment
            )
            .as_u64(),
            expected
        );
        assert!(holds(
            queries.status_obligation(),
            &substitutions,
            &environment
        ));
        assert!(holds(
            queries.memory_obligation(),
            &substitutions,
            &environment
        ));
    }
}
