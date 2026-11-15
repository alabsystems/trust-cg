// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Admission/resource controls, not solver or native-execution evidence.

use super::*;
use trust_cg_ir::function::{MachBlock, Signature as MSignature, Type as MType};
use trust_cg_ir::regs::PReg;
use trust_cg_ir::{AArch64Opcode as M, BlockId, InstId, MachFunction, MachInst, MachOperand as O};
use trust_cg_lower::function::{BasicBlock, Signature};

fn ins(opcode: L, args: &[u32], results: &[u32]) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(Value).collect(),
        results: results.iter().copied().map(Value).collect(),
    }
}

fn function(params: Vec<Type>, blocks: Vec<BasicBlock>) -> Function {
    let mut source = Function::new(
        "ordinary_resource_consumer",
        Signature {
            params,
            returns: vec![Type::I64],
        },
    );
    for (id, block) in blocks.into_iter().enumerate() {
        source.blocks.insert(Block(id as u32), block);
        source.block_order.push(Block(id as u32));
    }
    source
}

fn block(instructions: Vec<Instruction>) -> BasicBlock {
    BasicBlock {
        instructions,
        ..Default::default()
    }
}

fn detail(source: &Function) -> String {
    match admit(source) {
        Err(A64BodyRefusal::Unsupported(A64BodyUnsupported::SourceShape(why)))
        | Err(A64BodyRefusal::Unsupported(A64BodyUnsupported::SourceDomain(why))) => why,
        Err(other) => panic!("expected source shape/domain refusal, got {other}"),
        Ok(_) => panic!("expected source refusal"),
    }
}

#[test]
fn oversized_operands_and_results_refuse_before_cfg_or_value_traversal() {
    for size in [4_096, 65_536] {
        let mut bad_add = ins(L::Iadd, &[], &[1]);
        bad_add.args = vec![Value(0); size];
        let source = function(
            vec![Type::I64],
            vec![block(vec![
                bad_add,
                ins(L::Jump { dest: Block(99) }, &[], &[]),
            ])],
        );
        let why = detail(&source);
        assert!(
            why.contains("Iadd takes 2 arguments and 1 results"),
            "{why}"
        );
        assert!(why.contains(&format!("got {size} arguments")), "{why}");
        assert!(why.len() < 256);

        let mut bad_constant = ins(
            L::Iconst {
                ty: Type::I64,
                imm: 1,
            },
            &[],
            &[],
        );
        bad_constant.results = vec![Value(u32::MAX); size];
        let source = function(
            vec![Type::I64],
            vec![block(vec![bad_constant, ins(L::Return, &[0], &[])])],
        );
        let why = detail(&source);
        assert!(
            why.contains("Iconst takes 0 arguments and 1 results"),
            "{why}"
        );
        assert!(why.contains(&format!("{size} results")), "{why}");
        assert!(why.len() < 256);
    }
}

#[test]
fn every_admitted_opcode_has_its_exact_early_shape() {
    let shapes = [
        (
            L::Iconst {
                ty: Type::I64,
                imm: 0,
            },
            0,
            1,
        ),
        (
            L::Uextend {
                from_ty: Type::I8,
                to_ty: Type::I32,
            },
            1,
            1,
        ),
        (L::Copy, 1, 1),
        (L::Iadd, 2, 1),
        (L::Isub, 2, 1),
        (L::Ineg, 1, 1),
        (L::Band, 2, 1),
        (L::Bor, 2, 1),
        (L::Bxor, 2, 1),
        (L::Bnot, 1, 1),
        (L::BandNot, 2, 1),
        (L::BorNot, 2, 1),
        (L::Ishl, 2, 1),
        (L::Ushr, 2, 1),
        (L::Sshr, 2, 1),
        (L::Icmp { cond: IntCC::Equal }, 2, 1),
        (L::Select { cond: IntCC::Equal }, 3, 1),
        (
            L::Brif {
                cond: Value(0),
                then_dest: Block(1),
                else_dest: Block(2),
            },
            1,
            0,
        ),
        (L::Jump { dest: Block(1) }, 0, 0),
        (L::Return, 1, 0),
    ];
    assert_eq!(shapes.len(), ADMITTED_LIR_OPCODES.len());
    for (opcode, args, results) in shapes {
        assert!(admitted_opcode(&opcode));
        let name = opcode_name(&opcode);
        assert!(ADMITTED_LIR_OPCODES.contains(&name.as_str()));
        let instruction = ins(opcode, &vec![0; args], &vec![1; results]);
        let good = function(vec![Type::I64], vec![block(vec![instruction])]);
        // This is only the shape preflight: malformed control/SSA must still
        // be rejected separately by full admission.
        assert!(preflight_shape(&good).is_ok(), "{name}");
        for wrong_args in [true, false] {
            let mut bad = good.clone();
            let instruction = &mut bad.blocks.get_mut(&Block(0)).unwrap().instructions[0];
            if wrong_args {
                instruction.args.push(Value(0));
            } else {
                instruction.results.push(Value(1));
            }
            assert!(preflight_shape(&bad).is_err(), "{name}");
        }
    }
}

#[test]
fn excess_join_parameters_refuse_before_owner_map_or_copy_search() {
    let mut join = block(vec![ins(L::Return, &[0], &[])]);
    join.params = (1..=65_536).map(|id| (Value(id), Type::I64)).collect();
    let source = function(
        vec![Type::I64],
        vec![block(vec![ins(L::Jump { dest: Block(1) }, &[], &[])]), join],
    );
    let why = detail(&source);
    assert!(
        why.contains("65536 non-entry parameters exceed 2 possible argument Copy witnesses"),
        "{why}"
    );
    assert!(why.len() < 256);

    // Fits the coarse instruction bound, but only one Copy witnesses two
    // parameters. The tighter bound is still before parameter-map allocation.
    let mut join = block(vec![ins(L::Return, &[1], &[])]);
    join.params = vec![(Value(1), Type::I64), (Value(2), Type::I64)];
    let source = function(
        vec![Type::I64],
        vec![
            block(vec![
                ins(L::Copy, &[0], &[1]),
                ins(L::Jump { dest: Block(1) }, &[], &[]),
            ]),
            join,
        ],
    );
    assert!(detail(&source).contains("2 non-entry parameters exceed 1 argument Copy witnesses"));
}

#[test]
fn excess_hints_refuse_before_hint_or_operand_validation() {
    let mut source = function(
        vec![Type::I64],
        vec![block(vec![
            ins(L::Copy, &[0], &[1]),
            ins(L::Return, &[1], &[]),
        ])],
    );
    for id in 0..4_096 {
        source.value_types.insert(Value(id), Type::I64);
    }
    assert!(detail(&source).contains("4096 type hints exceed 3 possible inferred values"));
    source.value_types.retain(|value, _| value.0 < 3);
    assert!(detail(&source).contains("3 type hints exceed 2 possible inferred values"));
    source.value_types.remove(&Value(2));
    assert!(admit(&source).is_ok());
}

fn constants(count: usize) -> Function {
    let mut body: Vec<_> = (0..count)
        .map(|index| {
            ins(
                L::Iconst {
                    ty: Type::I64,
                    imm: index as i64,
                },
                &[],
                &[(8 + index) as u32],
            )
        })
        .collect();
    body.push(ins(L::Return, &[0], &[]));
    let mut source = function(vec![Type::I64; 8], vec![block(body)]);
    for id in 0..8 + count {
        source.value_types.insert(Value(id as u32), Type::I64);
    }
    source
}

#[test]
fn existing_instruction_input_and_inferred_value_boundaries_remain_exact() {
    let source = constants(MAX_SOURCE_INSTRUCTIONS - 1);
    assert_eq!(
        source.blocks[&Block(0)].instructions.len(),
        MAX_SOURCE_INSTRUCTIONS
    );
    assert_eq!(source.value_types.len(), 8 + MAX_SOURCE_INSTRUCTIONS - 1);
    assert!(admit(&source).is_ok());
    assert!(detail(&constants(MAX_SOURCE_INSTRUCTIONS)).contains("257 instructions"));
    let mut too_many_inputs = source;
    too_many_inputs.signature.params.push(Type::I64);
    assert!(detail(&too_many_inputs).contains("more than eight register parameters"));
}

#[test]
fn joins_can_still_use_all_copy_witnesses_without_an_arbitrary_parameter_cap() {
    let count = MAX_SOURCE_INSTRUCTIONS - 2;
    let mut copies: Vec<_> = (1..=count)
        .map(|id| ins(L::Copy, &[0], &[id as u32]))
        .collect();
    copies.push(ins(L::Jump { dest: Block(1) }, &[], &[]));
    let mut join = block(vec![ins(L::Return, &[count as u32], &[])]);
    join.params = (1..=count)
        .map(|id| (Value(id as u32), Type::I64))
        .collect();
    let mut source = function(vec![Type::I64], vec![block(copies), join]);
    for id in 0..=count {
        source.value_types.insert(Value(id as u32), Type::I64);
    }
    assert!(admit(&source).is_ok());
    assert_eq!(source.blocks[&Block(1)].params.len(), 254);
}

#[test]
fn existing_sixteen_block_boundary_remains_exact() {
    let chain = |count: usize| {
        let blocks = (0..count)
            .map(|index| {
                block(vec![if index + 1 == count {
                    ins(L::Return, &[0], &[])
                } else {
                    ins(
                        L::Jump {
                            dest: Block((index + 1) as u32),
                        },
                        &[],
                        &[],
                    )
                }])
            })
            .collect();
        function(vec![Type::I64], blocks)
    };
    assert!(admit(&chain(MAX_SOURCE_BLOCKS)).is_ok());
    assert!(detail(&chain(MAX_SOURCE_BLOCKS + 1)).contains("17 blocks"));
}

#[test]
fn early_shape_checks_do_not_replace_existing_semantic_checks() {
    let undefined = function(
        vec![Type::I64],
        vec![block(vec![
            ins(L::Iadd, &[0, 99], &[1]),
            ins(L::Return, &[1], &[]),
        ])],
    );
    assert!(preflight_shape(&undefined).is_ok());
    assert!(detail(&undefined).contains("before any definition reaches"));
    let mixed = function(
        vec![Type::I64, Type::I32],
        vec![block(vec![
            ins(L::Iadd, &[0, 1], &[2]),
            ins(L::Return, &[2], &[]),
        ])],
    );
    assert!(preflight_shape(&mixed).is_ok());
    assert!(detail(&mixed).contains("operand types"));
    let mut wrong_hint = constants(1);
    wrong_hint.value_types.insert(Value(8), Type::I32);
    assert!(preflight_shape(&wrong_hint).is_ok());
    assert!(detail(&wrong_hint).contains("inconsistent type hint"));
}

#[test]
fn unsupported_payload_diagnostics_visit_only_the_variant_name() {
    let source = function(
        vec![Type::I64],
        vec![block(vec![ins(
            L::Switch {
                cases: vec![(0, Block(0)); 65_536],
                default: Block(0),
            },
            &[0],
            &[],
        )])],
    );
    let why = detail(&source);
    assert!(why.contains("Switch is outside the body owner"), "{why}");
    assert!(why.len() < 128);
    let aggregate = Type::Struct(vec![Type::I64; 65_536]);
    let source = function(
        vec![aggregate.clone()],
        vec![block(vec![ins(L::Return, &[0], &[])])],
    );
    assert_eq!(detail(&source), "parameter type Struct");
    let source = function(
        vec![],
        vec![block(vec![
            ins(
                L::Iconst {
                    ty: aggregate,
                    imm: 0,
                },
                &[],
                &[0],
            ),
            ins(L::Return, &[0], &[]),
        ])],
    );
    assert!(detail(&source).contains("constant of type Struct"));
}

#[test]
fn diagnostic_name_stops_before_any_payload_formatter_is_called() {
    struct Payload<'a>(&'a std::cell::Cell<usize>);
    impl std::fmt::Debug for Payload<'_> {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            self.0.set(self.0.get() + 1);
            formatter.write_str("must_not_be_visited")
        }
    }
    struct Compound<'a>(Payload<'a>);
    impl std::fmt::Debug for Compound<'_> {
        fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            formatter
                .debug_struct("Compound")
                .field("payload", &self.0)
                .finish()
        }
    }
    let visits = std::cell::Cell::new(0);
    assert_eq!(debug_variant_name(&Compound(Payload(&visits))), "Compound");
    assert_eq!(visits.get(), 0);
}

fn add_pair(ty: Type) -> (Function, MachFunction) {
    let mut source = function(
        vec![ty.clone(); 2],
        vec![block(vec![
            ins(L::Iadd, &[0, 1], &[2]),
            ins(L::Return, &[2], &[]),
        ])],
    );
    source.signature.returns = vec![ty.clone()];
    let machine_type = if ty == Type::I64 {
        MType::I64
    } else {
        MType::I32
    };
    let offset = if ty == Type::I64 { 0 } else { 32 };
    let mut machine = MachFunction::new(
        source.name.clone(),
        MSignature {
            params: vec![machine_type.clone(); 2],
            returns: vec![machine_type],
        },
    );
    machine.insts = vec![
        MachInst::new(
            M::AddRR,
            vec![
                O::PReg(PReg::new(offset)),
                O::PReg(PReg::new(offset)),
                O::PReg(PReg::new(offset + 1)),
            ],
        ),
        MachInst::new(M::Ret, vec![O::PReg(PReg::new(30))]),
    ];
    machine.blocks = vec![MachBlock {
        insts: vec![InstId(0), InstId(1)],
        preds: vec![],
        succs: vec![],
        loop_depth: 0,
    }];
    machine.block_order = vec![BlockId(0)];
    machine.entry = BlockId(0);
    (source, machine)
}

#[test]
fn ordinary_whole_body_obligations_keep_exact_inputs_endpoints_and_premises() {
    for ty in [Type::I32, Type::I64] {
        let (source, machine) = add_pair(ty.clone());
        let original = super::super::source_bound_a64_body(&source, &machine).unwrap();
        let mut hinted = source.clone();
        for id in 0..3 {
            hinted.value_types.insert(Value(id), ty.clone());
        }
        hinted.blocks.get_mut(&Block(0)).unwrap().params =
            vec![(Value(0), ty.clone()), (Value(1), ty)];
        let same = super::super::source_bound_a64_body(&hinted, &machine).unwrap();
        assert_eq!(original.obligation(), same.obligation());
        assert_eq!(original.covered(), same.covered());
        assert_eq!(original.copies_and_constants(), same.copies_and_constants());
        assert_eq!(original.covered(), &[InstId(0)]);
    }
}
