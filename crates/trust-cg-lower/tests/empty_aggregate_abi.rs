// Copyright 2026 Andrew Yates | Apache-2.0
//! Empty logical parameters have no physical argument slot. These are backend
//! regression checks, not source-compiler or ABI proof qualification.

use trust_cg_ir::AArch64Opcode;
use trust_cg_lower::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation, gpr};
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::{Block, Value};
use trust_cg_lower::isel::{ISelOperand, InstructionSelector};
use trust_cg_lower::types::Type;

fn empty() -> Type {
    Type::Struct(Vec::new())
}

#[test]
fn empty_parameters_preserve_scalar_registers_and_overflow_offsets() {
    let registers = [
        gpr::X0,
        gpr::X1,
        gpr::X2,
        gpr::X3,
        gpr::X4,
        gpr::X5,
        gpr::X6,
        gpr::X7,
    ];
    for variant in [AArch64AbiVariant::Darwin, AArch64AbiVariant::Aapcs64] {
        assert_eq!(
            AppleAArch64ABI::classify_params_with(variant, &[empty(), Type::I64]),
            [ArgLocation::Ignore, ArgLocation::Reg(gpr::X0)]
        );
        for scalars in 0..=12 {
            let mut params = vec![empty(), empty()];
            let mut expected = vec![ArgLocation::Ignore, ArgLocation::Ignore];
            for index in 0..scalars {
                params.extend([Type::I64, empty()]);
                expected.push(if index < 8 {
                    ArgLocation::Reg(registers[index])
                } else {
                    ArgLocation::Stack {
                        offset: (index as i64 - 8) * 8,
                        size: 8,
                    }
                });
                expected.push(ArgLocation::Ignore);
            }
            assert_eq!(
                AppleAArch64ABI::classify_params_with(variant, &params),
                expected
            );
        }
        // A real capture word and FP parameters retain their old banks.
        assert_eq!(
            AppleAArch64ABI::classify_params_with(
                variant,
                &[
                    empty(),
                    Type::Struct(vec![Type::I64]),
                    Type::F64,
                    empty(),
                    Type::I64
                ]
            ),
            [
                ArgLocation::Ignore,
                ArgLocation::Reg(gpr::X0),
                ArgLocation::Reg(gpr::D0),
                ArgLocation::Ignore,
                ArgLocation::Reg(gpr::X1)
            ]
        );
    }
}

#[test]
fn formal_empty_values_keep_their_own_homes_without_reading_an_argument_register() {
    let signature = Signature {
        params: vec![empty(), Type::I64, empty(), Type::I64],
        returns: vec![],
    };
    let mut selector = InstructionSelector::new("empty_formals".into(), signature.clone());
    selector.set_abi_variant(AArch64AbiVariant::Darwin);
    selector
        .lower_formal_arguments(&signature, Block(0))
        .unwrap();
    // Reading both original logical values at another call proves neither was
    // erased or replaced with the neighboring scalar's formal identity.
    selector
        .select_call(
            "empty_callee",
            &[Value(0), Value(1), Value(2), Value(3)],
            &[],
            &[],
            Block(0),
        )
        .unwrap();
    let function = selector.finalize();
    assert_eq!(function.incoming_stack_arg_bytes, Some(0));
    assert_eq!(function.stack_slots.len(), 2);
    let instructions = &function.blocks[&Block(0)].insts;
    let homes = instructions
        .iter()
        .filter(|i| i.opcode == AArch64Opcode::AddPCRel)
        .count();
    assert_eq!(homes, 2);
    let incoming: Vec<_> = instructions
        .iter()
        .filter_map(|i| {
            if i.is_call_arg_setup {
                return None;
            }
            match i.operands.as_slice() {
                [ISelOperand::VReg(_), ISelOperand::PReg(p)] if i.opcode == AArch64Opcode::Copy => {
                    Some(*p)
                }
                _ => None,
            }
        })
        .collect();
    assert_eq!(incoming, [gpr::X0, gpr::X1]);
    let outgoing: Vec<_> = instructions
        .iter()
        .filter(|i| i.is_call_arg_setup)
        .map(|i| i.operands[0].clone())
        .collect();
    assert_eq!(
        outgoing,
        [ISelOperand::PReg(gpr::X0), ISelOperand::PReg(gpr::X1)]
    );
    let call = instructions
        .iter()
        .find(|i| i.opcode == AArch64Opcode::Bl)
        .unwrap();
    assert_eq!(call.implicit_uses, [gpr::X0, gpr::X1]);
}

#[test]
fn empty_arguments_do_not_add_stack_stores_or_change_the_overflow_extent() {
    for variant in [AArch64AbiVariant::Darwin, AArch64AbiVariant::Aapcs64] {
        let mut params = vec![];
        for _ in 0..8 {
            params.extend([empty(), Type::I64]);
        }
        params.extend([empty(), Type::I8, empty(), Type::I64, empty()]);
        let signature = Signature {
            params,
            returns: vec![],
        };
        let mut selector = InstructionSelector::new("empty_overflow".into(), signature.clone());
        selector.set_abi_variant(variant);
        selector
            .lower_formal_arguments(&signature, Block(0))
            .unwrap();
        let args = (0..signature.params.len() as u32)
            .map(Value)
            .collect::<Vec<_>>();
        selector
            .select_call("callee", &args, &[], &[], Block(0))
            .unwrap();
        let function = selector.finalize().to_ir_func();
        assert_eq!(function.incoming_stack_arg_bytes, Some(16));
        let facts = function.call_abi_facts.values().next().unwrap();
        assert_eq!(facts.stack_arg_bytes, 16);
        assert!(!facts.aggregate_stack_args);
        assert!(!facts.by_reference_argument_copies);
        let mut stores = facts
            .stack_stores
            .iter()
            .map(|s| (s.offset, s.bytes))
            .collect::<Vec<_>>();
        stores.sort_unstable();
        assert_eq!(stores, [(0, 1), (8, 8)]);
    }
}

#[test]
fn indirect_call_omits_the_same_empty_argument() {
    let signature = Signature {
        params: vec![Type::I64, empty(), Type::I64],
        returns: vec![],
    };
    let mut selector = InstructionSelector::new("empty_indirect".into(), signature.clone());
    selector.set_abi_variant(AArch64AbiVariant::Darwin);
    selector
        .lower_formal_arguments(&signature, Block(0))
        .unwrap();
    selector
        .select_call_indirect(&Value(0), &[Value(1), Value(2)], &[], &[], Block(0))
        .unwrap();
    let function = selector.finalize();
    let instructions = &function.blocks[&Block(0)].insts;
    let outgoing: Vec<_> = instructions
        .iter()
        .filter(|i| i.is_call_arg_setup)
        .map(|i| i.operands[0].clone())
        .collect();
    assert_eq!(outgoing, [ISelOperand::PReg(gpr::X0)]);
    let call = instructions
        .iter()
        .find(|i| i.opcode == AArch64Opcode::Blr)
        .unwrap();
    assert_eq!(call.implicit_uses, [gpr::X0]);
}
