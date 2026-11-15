// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent caller-placement regression gate. These checks inspect selected
//! instructions and their actual source values; they do not call the production
//! ABI classifier to construct expectations and do not claim formal proof.
//!
//! References: AAPCS64 2025Q4, "Variadic subroutines" and stages C.1/C.9/C.14;
//! Apple "Writing ARM64 code for Apple platforms", variadic arguments.

use trust_cg_ir::{AArch64Opcode, regs::SP};
use trust_cg_lower::abi::{AArch64AbiVariant, PReg, gpr};
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::{Block, Value};
use trust_cg_lower::isel::{ISelInst, ISelOperand, InstructionSelector};
use trust_cg_lower::types::Type;

#[derive(Clone, Debug, PartialEq)]
enum Destination {
    Register(PReg),
    Stack(i64),
}

fn selected(variant: AArch64AbiVariant, types: &[Type], fixed: usize) -> Vec<ISelInst> {
    let signature = Signature {
        params: vec![],
        returns: vec![],
    };
    let mut selector = InstructionSelector::new("variadic_abi".into(), signature);
    selector.set_abi_variant(variant);
    let params: Vec<_> = types
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, ty)| (Value(index as u32), ty))
        .collect();
    selector.define_block_params(&params);
    let args: Vec<_> = params.iter().map(|(value, _)| *value).collect();
    selector
        .select_variadic_call("external", fixed, &args, &[], &[], Block(0))
        .unwrap();
    selector.finalize().blocks.remove(&Block(0)).unwrap().insts
}

fn check_placements(insts: &[ISelInst], expected: &[Destination]) -> Result<(), String> {
    let mut observed = vec![None; expected.len()];
    let mut calls = 0;
    for inst in insts {
        let (source, destination) = match (inst.opcode, inst.operands.as_slice()) {
            (AArch64Opcode::Copy, [ISelOperand::PReg(dst), ISelOperand::VReg(src)]) => {
                (src.id as usize, Destination::Register(*dst))
            }
            (
                AArch64Opcode::StrRI,
                [
                    ISelOperand::VReg(src),
                    ISelOperand::PReg(base),
                    ISelOperand::Imm(offset),
                ],
            ) if *base == SP => (src.id as usize, Destination::Stack(*offset)),
            (AArch64Opcode::Bl, [ISelOperand::Symbol(name)]) if name == "external" => {
                calls += 1;
                let required: Vec<_> = expected
                    .iter()
                    .filter_map(|location| match location {
                        Destination::Register(reg) => Some(*reg),
                        Destination::Stack(_) => None,
                    })
                    .collect();
                if inst.implicit_uses != required {
                    return Err("wrong call register uses".into());
                }
                continue;
            }
            _ => return Err(format!("unexpected marshalling instruction: {inst:?}")),
        };
        if calls != 0 || source >= observed.len() || observed[source].replace(destination).is_some()
        {
            return Err("duplicate, unknown, or post-call source placement".into());
        }
    }
    if calls != 1 || observed != expected.iter().cloned().map(Some).collect::<Vec<_>>() {
        return Err(format!("expected {expected:?}, observed {observed:?}"));
    }
    Ok(())
}

#[test]
fn variadic_scalar_register_banks_and_stack_exhaustion() {
    // Independently enumerate integer and FP exhaustion, and every named/tail
    // split. Both banks advance independently under AAPCS64. Darwin's unnamed
    // arguments begin on the stack, even with free registers in either bank.
    for integers in 0..=10 {
        for floats in 0..=10 {
            let types: Vec<_> = (0..integers.max(floats))
                .flat_map(|index| {
                    (index < integers)
                        .then_some(Type::I64)
                        .into_iter()
                        .chain((index < floats).then_some(Type::F64))
                })
                .collect();
            for fixed in 0..=types.len() {
                for variant in [AArch64AbiVariant::Aapcs64, AArch64AbiVariant::Darwin] {
                    let (mut integer, mut float, mut stack) = (0, 0, 0);
                    let expected: Vec<_> = types
                        .iter()
                        .enumerate()
                        .map(|(index, ty)| {
                            let counter = if *ty == Type::I64 {
                                &mut integer
                            } else {
                                &mut float
                            };
                            if *counter < 8
                                && (variant == AArch64AbiVariant::Aapcs64 || index < fixed)
                            {
                                let base = if *ty == Type::I64 { gpr::X0 } else { gpr::D0 };
                                let register = PReg::new(base.encoding() + *counter);
                                *counter += 1;
                                Destination::Register(register)
                            } else {
                                let offset = stack;
                                stack += 8;
                                Destination::Stack(offset)
                            }
                        })
                        .collect();
                    assert!(
                        check_placements(&selected(variant, &types, fixed), &expected).is_ok(),
                        "{variant:?}: integers={integers}, floats={floats}, fixed={fixed}"
                    );
                }
            }
        }
    }
}

#[test]
fn placement_gate_refutes_darwin_on_linux_wrong_values_and_missing_effects() {
    let types = [Type::I64, Type::I64, Type::F64];
    let linux = [
        Destination::Register(gpr::X0),
        Destination::Register(gpr::X1),
        Destination::Register(gpr::D0),
    ];
    let darwin = [
        Destination::Register(gpr::X0),
        Destination::Stack(0),
        Destination::Stack(8),
    ];
    let original = selected(AArch64AbiVariant::Darwin, &types, 1);
    assert!(check_placements(&original, &darwin).is_ok());
    // Exact original failure class: a valid Darwin marshalling is invalid Linux.
    assert!(check_placements(&original, &linux).is_err());
    let mut wrong_source = original.clone();
    wrong_source[1].operands[0] = wrong_source[2].operands[0].clone();
    assert!(check_placements(&wrong_source, &darwin).is_err());
    let mut wrong_stack = original.clone();
    wrong_stack[2].operands[2] = ISelOperand::Imm(0);
    assert!(check_placements(&wrong_stack, &darwin).is_err());
    let mut dropped_store = original;
    dropped_store.remove(1);
    assert!(check_placements(&dropped_store, &darwin).is_err());
}

#[test]
fn variadic_i128_register_alignment_and_both_stack_limbs() {
    for (variant, prefix, expected_registers, expected_stores) in [
        (
            AArch64AbiVariant::Aapcs64,
            1,
            vec![gpr::X0, gpr::X2, gpr::X3, gpr::X4],
            vec![],
        ),
        (
            AArch64AbiVariant::Aapcs64,
            7,
            vec![
                gpr::X0,
                gpr::X1,
                gpr::X2,
                gpr::X3,
                gpr::X4,
                gpr::X5,
                gpr::X6,
            ],
            vec![0, 8, 16],
        ),
        (AArch64AbiVariant::Darwin, 1, vec![gpr::X0], vec![0, 8, 16]),
        (
            AArch64AbiVariant::Darwin,
            7,
            vec![gpr::X0],
            vec![0, 8, 16, 24, 32, 40, 48, 56, 64],
        ),
    ] {
        let mut types = vec![Type::I64; prefix];
        types.extend([Type::I128, Type::I64]);
        let signature = Signature {
            params: types.clone(),
            returns: vec![],
        };
        let mut selector = InstructionSelector::new("variadic_i128".into(), signature.clone());
        selector.set_abi_variant(variant);
        selector
            .lower_formal_arguments(&signature, Block(0))
            .unwrap();
        let args = (0..types.len())
            .map(|index| Value(index as u32))
            .collect::<Vec<_>>();
        selector
            .select_variadic_call("external", 1, &args, &[], &[], Block(0))
            .unwrap();
        let result = selector.finalize();
        let instructions = &result.blocks[&Block(0)].insts;
        let call = instructions
            .iter()
            .find(|inst| inst.opcode == AArch64Opcode::Bl)
            .unwrap();
        assert_eq!(
            call.implicit_uses, expected_registers,
            "{variant:?}, prefix={prefix}"
        );
        let stores = instructions
            .iter()
            .filter_map(|inst| match (inst.opcode, inst.operands.as_slice()) {
                (AArch64Opcode::StrRI, [_, ISelOperand::PReg(base), ISelOperand::Imm(offset)])
                    if *base == SP =>
                {
                    Some(*offset)
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert_eq!(stores, expected_stores, "{variant:?}, prefix={prefix}");
    }
}
