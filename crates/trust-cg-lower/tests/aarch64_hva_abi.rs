// Copyright 2026 Andrew Yates | Apache-2.0
//! Independent AAPCS64 homogeneous-vector placement/refutation gate.
//! Expectations come from explicit register/stack rules, never from another
//! invocation of the production classifier. This is regression evidence, not
//! formal proof of ABI correctness.

use trust_cg_ir::AArch64Opcode;
use trust_cg_lower::abi::{AArch64AbiVariant, AppleAArch64ABI, ArgLocation, PReg, gpr};
use trust_cg_lower::function::Signature;
use trust_cg_lower::instructions::{Block, Instruction, Opcode, Value};
use trust_cg_lower::isel::{ISelOperand, InstructionSelector};
use trust_cg_lower::types::Type;

#[test]
fn address_carried_aggregate_type_survives_materialization_before_call() {
    for (element, base, bytes) in [
        (Type::I64, gpr::X0, 8),
        (Type::V64, gpr::D0, 8),
        (Type::V128, gpr::V0, 16),
    ] {
        let aggregate = Type::Struct(vec![element; 2]);
        let mut selector = InstructionSelector::new(
            "materialized_aggregate".into(),
            Signature {
                params: vec![],
                returns: vec![],
            },
        );
        selector.set_abi_variant(trust_cg_lower::abi::AArch64AbiVariant::Darwin);
        selector.seed_value_types(&std::collections::HashMap::from([(Value(0), aggregate)]));
        selector
            .select_block(
                Block(0),
                &[Instruction {
                    opcode: Opcode::StackAddr { slot: 0 },
                    args: vec![],
                    results: vec![Value(0)],
                }],
            )
            .unwrap();
        selector
            .select_call("external", &[Value(0)], &[], &[], Block(0))
            .unwrap();
        let insts = selector.finalize().blocks.remove(&Block(0)).unwrap().insts;
        let loads: Vec<_> = insts
            .iter()
            .filter_map(|inst| match (inst.opcode, inst.operands.as_slice()) {
                (AArch64Opcode::LdrRI, [ISelOperand::PReg(reg), _, ISelOperand::Imm(offset)]) => {
                    Some((*reg, *offset))
                }
                _ => None,
            })
            .collect();
        let expected = vec![(base, 0), (PReg::new(base.encoding() + 1), bytes)];
        assert_eq!(
            loads, expected,
            "StackAddr must not erase aggregate ABI lanes"
        );
    }
}

fn check(actual: &[ArgLocation], expected: &[ArgLocation]) -> Result<(), String> {
    if actual == expected {
        Ok(())
    } else {
        Err(format!("expected {expected:?}, got {actual:?}"))
    }
}

fn regs(base: PReg, first: usize, count: usize) -> ArgLocation {
    ArgLocation::RegSequence(
        (first..first + count)
            .map(|i| PReg::new(base.encoding() + i as u16))
            .collect(),
    )
}

#[test]
fn homogeneous_vectors_preserve_member_width_count_and_exhaustion() {
    for (element, base, bytes) in [(Type::V64, gpr::D0, 8), (Type::V128, gpr::V0, 16)] {
        for count in 1..=4 {
            for aggregate in [
                Type::Struct(vec![element.clone(); count]),
                Type::Array(Box::new(element.clone()), count as u32),
                Type::Struct(vec![Type::Array(Box::new(element.clone()), count as u32)]),
            ] {
                assert_eq!(
                    AppleAArch64ABI::classify_hfa(&aggregate),
                    None,
                    "HVA must not change public HFA meaning"
                );
                assert!(
                    check(
                        &AppleAArch64ABI::classify_returns(std::slice::from_ref(&aggregate)),
                        &[regs(base, 0, count)]
                    )
                    .is_ok(),
                    "return {aggregate:?}"
                );
                for variant in [AArch64AbiVariant::Aapcs64, AArch64AbiVariant::Darwin] {
                    for prefix in 0..=9 {
                        let mut types = vec![Type::F64; prefix];
                        types.extend([aggregate.clone(), Type::F64, Type::I64]);
                        let mut expected: Vec<_> = (0..prefix)
                            .map(|i| {
                                if i < 8 {
                                    ArgLocation::Reg(PReg::new(gpr::D0.encoding() + i as u16))
                                } else {
                                    ArgLocation::Stack {
                                        offset: ((i - 8) * 8) as i64,
                                        size: 8,
                                    }
                                }
                            })
                            .collect();
                        let mut stack = prefix.saturating_sub(8) as i64 * 8;
                        if prefix + count <= 8 {
                            expected.push(regs(base, prefix, count));
                            expected.push(if prefix + count < 8 {
                                ArgLocation::Reg(PReg::new(
                                    gpr::D0.encoding() + (prefix + count) as u16,
                                ))
                            } else {
                                ArgLocation::Stack {
                                    offset: stack,
                                    size: 8,
                                }
                            });
                        } else {
                            stack = (stack + bytes - 1) / bytes * bytes;
                            expected.push(ArgLocation::Stack {
                                offset: stack,
                                size: count as u32 * bytes as u32,
                            });
                            stack += count as i64 * bytes;
                            expected.push(ArgLocation::Stack {
                                offset: stack,
                                size: 8,
                            });
                        }
                        expected.push(ArgLocation::Reg(gpr::X0));
                        assert!(
                            check(
                                &AppleAArch64ABI::classify_params_with(variant, &types),
                                &expected
                            )
                            .is_ok(),
                            "{variant:?} {aggregate:?} prefix={prefix}: {:?}",
                            check(
                                &AppleAArch64ABI::classify_params_with(variant, &types),
                                &expected
                            )
                        );
                        if variant == AArch64AbiVariant::Aapcs64 {
                            for fixed in 0..=types.len() {
                                assert!(
                                    check(
                                        &AppleAArch64ABI::classify_params_variadic_with(
                                            variant, fixed, &types
                                        ),
                                        &expected
                                    )
                                    .is_ok()
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn placement_gate_refutes_gpr_indirection_wrong_width_and_backfill() {
    let expected = [regs(gpr::V0, 0, 2), ArgLocation::Reg(gpr::X0)];
    assert!(check(&expected, &expected).is_ok());
    for bad in [
        vec![
            ArgLocation::Indirect { ptr_reg: gpr::X0 },
            ArgLocation::Reg(gpr::X1),
        ],
        vec![
            ArgLocation::RegPair(gpr::X0, gpr::X1),
            ArgLocation::Reg(gpr::X2),
        ],
        vec![regs(gpr::D0, 0, 2), ArgLocation::Reg(gpr::X0)],
        vec![regs(gpr::V0, 0, 1), ArgLocation::Reg(gpr::X0)],
        vec![regs(gpr::V0, 1, 2), ArgLocation::Reg(gpr::X0)],
    ] {
        assert!(check(&bad, &expected).is_err());
    }
    let spilled = [
        ArgLocation::Stack {
            offset: 16,
            size: 32,
        },
        ArgLocation::Stack {
            offset: 48,
            size: 8,
        },
    ];
    assert!(check(&[spilled[0].clone(), ArgLocation::Reg(gpr::D7)], &spilled).is_err());
    assert!(
        check(
            &[
                ArgLocation::Stack {
                    offset: 8,
                    size: 32
                },
                spilled[1].clone()
            ],
            &spilled
        )
        .is_err()
    );
}

#[test]
fn heterogeneous_and_five_member_vectors_are_not_homogeneous_register_sequences() {
    for ty in [
        Type::Struct(vec![Type::V64, Type::V128]),
        Type::Struct(vec![Type::V64, Type::F64]),
        Type::Struct(vec![Type::V128; 5]),
        Type::Array(Box::new(Type::V64), 5),
    ] {
        assert!(!matches!(
            AppleAArch64ABI::classify_params(std::slice::from_ref(&ty))[0],
            ArgLocation::RegSequence(_)
        ));
        assert!(!matches!(
            AppleAArch64ABI::classify_returns(&[ty])[0],
            ArgLocation::RegSequence(_)
        ));
    }
}
