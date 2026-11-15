// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Arithmetic-arm normalization and the existing complete-body frame gate.
//! These controls do not discharge frame/body obligations or check final bytes.

use super::*;
use trust_cg_ir::function::{MachBlock, Signature, Type as MachineType};
use trust_cg_ir::regs::PReg;
use trust_cg_ir::{AArch64Opcode as M, BlockId};
use trust_cg_lower::Type;
use trust_cg_lower::function::BasicBlock;
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode as L, Value};

fn inst(opcode: L, args: &[u32], output: Option<u32>) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(Value).collect(),
        results: output.into_iter().map(Value).collect(),
    }
}

/// `if a <s b { (copy(a+b))-7 } else { (copy(b-a))+11 }`, with the
/// adapter's single merge ID defined in both arms. No instruction/proof
/// metadata is trusted to choose the machine operands or the branch.
fn fixture(bits: u32) -> (Function, MachFunction) {
    let ty = if bits == 32 { Type::I32 } else { Type::I64 };
    let mut source = Function::new(
        "arithmetic_diamond",
        trust_cg_lower::function::Signature {
            params: vec![ty.clone(); 2],
            returns: vec![ty.clone()],
        },
    );
    let entry = BasicBlock {
        params: vec![(Value(0), ty.clone()), (Value(1), ty.clone())],
        instructions: vec![
            inst(
                L::Icmp {
                    cond: IntCC::SignedLessThan,
                },
                &[0, 1],
                Some(2),
            ),
            inst(
                L::Brif {
                    cond: Value(2),
                    then_dest: Block(1),
                    else_dest: Block(2),
                },
                &[2],
                None,
            ),
        ],
        ..Default::default()
    };
    let arm = |body: Vec<Instruction>| BasicBlock {
        instructions: body
            .into_iter()
            .chain([inst(L::Jump { dest: Block(3) }, &[], None)])
            .collect(),
        ..Default::default()
    };
    source.blocks.insert(Block(0), entry);
    source.blocks.insert(
        Block(1),
        arm(vec![
            inst(
                L::Iconst {
                    ty: ty.clone(),
                    imm: 7,
                },
                &[],
                Some(3),
            ),
            inst(L::Iadd, &[0, 1], Some(4)),
            inst(L::Copy, &[4], Some(5)),
            inst(L::Isub, &[5, 3], Some(9)),
        ]),
    );
    source.blocks.insert(
        Block(2),
        arm(vec![
            inst(
                L::Iconst {
                    ty: ty.clone(),
                    imm: 11,
                },
                &[],
                Some(6),
            ),
            inst(L::Isub, &[1, 0], Some(7)),
            inst(L::Copy, &[7], Some(8)),
            inst(L::Iadd, &[8, 6], Some(9)),
        ]),
    );
    source.blocks.insert(
        Block(3),
        BasicBlock {
            params: vec![(Value(9), ty.clone())],
            instructions: vec![inst(L::Return, &[9], None)],
            ..Default::default()
        },
    );
    source.block_order = (0..4).map(Block).collect();
    for value in 0..=9 {
        source
            .value_types
            .insert(Value(value), if value == 2 { Type::B1 } else { ty.clone() });
    }
    let machine_type = if bits == 32 {
        MachineType::I32
    } else {
        MachineType::I64
    };
    let mut machine = MachFunction::new(
        source.name.clone(),
        Signature::new(vec![machine_type.clone(); 2], vec![machine_type]),
    );
    let r = |index: u16| MachOperand::PReg(PReg::new(index + if bits == 32 { 32 } else { 0 }));
    let i = MachOperand::Imm;
    let target = |block| MachOperand::Block(BlockId(block));
    let frame = |offset| {
        vec![
            MachOperand::PReg(X29),
            MachOperand::PReg(X30),
            MachOperand::Special(SpecialReg::SP),
            i(offset),
        ]
    };
    let copy = if bits == 32 { M::MOVWrr } else { M::MOVXrr };
    for (opcode, operands) in [
        (M::StpPreIndex, frame(-16)),
        (
            M::AddRI,
            vec![
                MachOperand::PReg(X29),
                MachOperand::Special(SpecialReg::SP),
                i(0),
            ],
        ),
        (M::CmpRR, vec![r(0), r(1)]),
        (M::BCond, vec![i(11), target(1)]),
        (M::B, vec![target(2)]),
        (M::Movz, vec![r(3), i(7)]),
        (M::AddRR, vec![r(2), r(0), r(1)]),
        (copy, vec![r(4), r(2)]),
        (M::SubRR, vec![r(0), r(4), r(3)]),
        (M::B, vec![target(3)]),
        (M::Movz, vec![r(3), i(11)]),
        (M::SubRR, vec![r(2), r(1), r(0)]),
        (copy, vec![r(4), r(2)]),
        (M::AddRR, vec![r(0), r(4), r(3)]),
        (M::B, vec![target(3)]),
        (M::LdpPostIndex, frame(16)),
        (M::Ret, vec![MachOperand::PReg(X30)]),
    ] {
        machine.insts.push(MachInst::new(opcode, operands));
    }
    let block = |ids: std::ops::Range<u32>, preds: &[u32], succs: &[u32]| MachBlock {
        insts: ids.map(InstId).collect(),
        preds: preds.iter().copied().map(BlockId).collect(),
        succs: succs.iter().copied().map(BlockId).collect(),
        loop_depth: 0,
    };
    machine.blocks = vec![
        block(0..5, &[], &[1, 2]),
        block(5..10, &[0], &[3]),
        block(10..15, &[0], &[3]),
        block(15..17, &[1, 2], &[]),
    ];
    machine.block_order = (0..4).map(BlockId).collect();
    (source, machine)
}

#[test]
fn arithmetic_diamond_view_renames_each_arm_and_keeps_its_original_operators() {
    for bits in [32, 64] {
        let (source, _) = fixture(bits);
        let view = diamond::source_view(&source).expect("pure arithmetic arms");
        let body = &view.blocks[&Block(0)].instructions;
        assert_eq!(view.blocks.len(), 1);
        assert_eq!(body.len(), 11);
        assert_eq!(body[1].results, [Value(10)]);
        assert_eq!(body[2], inst(L::Iadd, &[0, 1], Some(11)));
        assert_eq!(body[3], inst(L::Copy, &[11], Some(12)));
        assert_eq!(body[4], inst(L::Isub, &[12, 10], Some(13)));
        assert_eq!(body[5].results, [Value(14)]);
        assert_eq!(body[6], inst(L::Isub, &[1, 0], Some(15)));
        assert_eq!(body[7], inst(L::Copy, &[15], Some(16)));
        assert_eq!(body[8], inst(L::Iadd, &[16, 14], Some(17)));
        assert_eq!(
            body[9],
            inst(
                L::Select {
                    cond: IntCC::NotEqual
                },
                &[2, 13, 17],
                Some(18)
            )
        );
        assert_eq!(body[10], inst(L::Return, &[18], None));
        assert_eq!(view.value_types[&Value(13)], source.signature.returns[0]);
        assert_eq!(view.value_types[&Value(17)], source.signature.returns[0]);
        assert!(view.trust_ir_origins.is_empty());
        assert!(view.blocks[&Block(0)].source_locs.is_empty());
        assert_eq!(
            source.blocks.len(),
            4,
            "the view does not replace its source"
        );
        crate::aarch64_affine_lowering::check_affine_source_domain(&view).unwrap();
    }
}

#[test]
fn arithmetic_diamond_frame_binds_both_paths_and_the_common_original_envelope() {
    for bits in [32, 64] {
        let (source, machine) = fixture(bits);
        let frame = source_bound_frame(&source, &machine).expect("both arithmetic arms match");
        assert!(std::ptr::eq(frame.source(), &source));
        assert!(std::ptr::eq(frame.machine(), &machine));
        assert_eq!(
            frame.envelope_instructions(),
            [InstId(0), InstId(1), InstId(15)]
        );
    }
}

#[test]
fn arithmetic_diamond_semantic_mutations_are_supported_body_mismatches() {
    for bits in [32, 64] {
        let (source, machine) = fixture(bits);
        for mutation in 0..4 {
            let mut wrong = machine.clone();
            match mutation {
                0 => wrong.insts[8].opcode = M::AddRR,
                1 => wrong.insts[13].opcode = M::SubRR,
                2 => wrong.insts[5].operands[1] = MachOperand::Imm(8),
                _ => wrong.insts[3].operands[0] = MachOperand::Imm(10),
            }
            assert!(
                matches!(
                    source_bound_frame(&source, &wrong),
                    Err(SourceBoundFrameRefusal::Mismatch(
                        FrameBindingMismatch::Body(AffineLoweringError::ReturnMismatch)
                    ))
                ),
                "i{bits}, machine mutation {mutation}"
            );
        }
        let mut wrong = source.clone();
        wrong.blocks.get_mut(&Block(1)).unwrap().instructions[3].opcode = L::Iadd;
        assert!(matches!(
            source_bound_frame(&wrong, &machine),
            Err(SourceBoundFrameRefusal::Mismatch(
                FrameBindingMismatch::Body(AffineLoweringError::ReturnMismatch)
            ))
        ));
    }
}

#[test]
fn arithmetic_diamond_undefined_forward_sibling_and_aliased_definitions_refuse() {
    for mutation in 0..7 {
        let (mut source, _) = fixture(64);
        match mutation {
            0 => source.blocks.get_mut(&Block(1)).unwrap().instructions[1].args[0] = Value(99),
            1 => {
                source.blocks.get_mut(&Block(1)).unwrap().instructions[0] =
                    inst(L::Copy, &[4], Some(3))
            }
            2 => source.blocks.get_mut(&Block(2)).unwrap().instructions[1].args[0] = Value(5),
            3 => source.blocks.get_mut(&Block(2)).unwrap().instructions[0].results[0] = Value(3),
            4 => source.blocks.get_mut(&Block(1)).unwrap().instructions[0].results[0] = Value(0),
            5 => source.blocks.get_mut(&Block(1)).unwrap().instructions[2].results[0] = Value(4),
            _ => source.blocks.get_mut(&Block(1)).unwrap().instructions[3].results[0] = Value(10),
        }
        assert!(
            diamond::source_view(&source).is_none(),
            "definition mutation {mutation}"
        );
    }
}

#[test]
fn arithmetic_diamond_wrong_arities_widths_types_and_extra_control_refuse() {
    for mutation in 0..12 {
        let (mut source, _) = fixture(64);
        match mutation {
            0 => source.blocks.get_mut(&Block(1)).unwrap().instructions[0]
                .args
                .push(Value(0)),
            1 => {
                source.blocks.get_mut(&Block(1)).unwrap().instructions[1]
                    .args
                    .pop()
                    .unwrap();
            }
            2 => source.blocks.get_mut(&Block(1)).unwrap().instructions[2]
                .results
                .clear(),
            3 => source.blocks.get_mut(&Block(1)).unwrap().instructions[1]
                .results
                .push(Value(10)),
            4 => {
                source.blocks.get_mut(&Block(1)).unwrap().instructions[0].opcode = L::Iconst {
                    ty: Type::I32,
                    imm: 7,
                }
            }
            5 => source.signature.params[0] = Type::I32,
            6 => {
                source.value_types.insert(Value(9), Type::B1);
            }
            7 => source
                .blocks
                .get_mut(&Block(1))
                .unwrap()
                .params
                .push((Value(10), Type::I64)),
            8 => source.blocks.get_mut(&Block(1)).unwrap().instructions[4]
                .args
                .push(Value(9)),
            9 => {
                source.blocks.get_mut(&Block(2)).unwrap().instructions[4].opcode =
                    L::Jump { dest: Block(0) }
            }
            10 => source.blocks.get_mut(&Block(1)).unwrap().instructions[1].opcode = L::Imul,
            _ => source.blocks.get_mut(&Block(1)).unwrap().instructions[1].opcode = L::Trap,
        }
        assert!(
            diamond::source_view(&source).is_none(),
            "shape mutation {mutation}"
        );
    }
}

#[test]
fn arithmetic_diamond_instruction_budget_and_fresh_id_overflow_refuse() {
    let (mut oversized, _) = fixture(64);
    let arm = &mut oversized.blocks.get_mut(&Block(1)).unwrap().instructions;
    let jump = arm.pop().unwrap();
    for value in 10..260 {
        arm.push(inst(L::Copy, &[0], Some(value)));
    }
    arm.push(jump);
    assert!(diamond::source_view(&oversized).is_none());
    let (mut overflow, _) = fixture(64);
    overflow.blocks.get_mut(&Block(1)).unwrap().instructions[0].results[0] = Value(u32::MAX);
    assert!(diamond::source_view(&overflow).is_none());
}
