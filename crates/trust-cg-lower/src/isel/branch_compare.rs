// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Select adjacent integer compare/branch pairs without an intermediate boolean.
//! Whole-function uses are required: a block-local count cannot rule out an
//! escaping value. The original compare and branch retain separate provenance.

use super::*;

impl InstructionSelector {
    pub(super) fn direct_branch_compares(
        &self,
        instructions: &[Instruction],
        types: &BlockTypes<'_>,
    ) -> HashMap<usize, IntCC> {
        let Some(uses) = &self.value_use_counts else {
            return HashMap::default();
        };
        let mut branches = HashMap::default();
        for (index, pair) in instructions.windows(2).enumerate() {
            let [compare, branch] = pair else {
                continue;
            };
            let (Opcode::Icmp { cond }, Opcode::Brif { cond: value, .. }) =
                (&compare.opcode, &branch.opcode)
            else {
                continue;
            };
            if compare.args.len() != 2
                || compare.results.as_slice() != [*value]
                || branch.args.as_slice() != [*value]
                || !branch.results.is_empty()
                || uses.get(value) != Some(&1)
                || instructions
                    .iter()
                    .filter(|inst| inst.results.contains(value))
                    .count()
                    != 1
                || self.idx_claimed_by_idiom(index)
                || self.idx_claimed_by_idiom(index + 1)
                || self.select_cond_fold_analysis.is_skipped(index)
                || self.select_cond_fold_analysis.is_skipped(index + 1)
            {
                continue;
            }
            let Some(lhs) = types.get(&compare.args[0]) else {
                continue;
            };
            if !matches!(lhs, Type::I8 | Type::I16 | Type::I32 | Type::I64)
                || types.get(&compare.args[1]) != Some(lhs)
            {
                continue;
            }
            branches.insert(index + 1, *cond);
        }
        branches
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::function::{BasicBlock, Function};
    use trust_cg_ir::TrustIrInstId;

    fn input(ty: Type, cond: IntCC) -> Function {
        let mut function = Function::new(
            "direct_branch",
            Signature {
                params: vec![ty.clone(), ty],
                returns: vec![],
            },
        );
        function.blocks.insert(
            Block(0),
            BasicBlock {
                instructions: vec![
                    Instruction {
                        opcode: Opcode::Icmp { cond },
                        args: vec![Value(0), Value(1)],
                        results: vec![Value(2)],
                    },
                    Instruction {
                        opcode: Opcode::Brif {
                            cond: Value(2),
                            then_dest: Block(1),
                            else_dest: Block(2),
                        },
                        args: vec![Value(2)],
                        results: vec![],
                    },
                ],
                ..Default::default()
            },
        );
        for block in [Block(1), Block(2)] {
            function.blocks.insert(
                block,
                BasicBlock {
                    instructions: vec![Instruction {
                        opcode: Opcode::Return,
                        args: vec![],
                        results: vec![],
                    }],
                    ..Default::default()
                },
            );
        }
        function
    }

    fn selector(function: &Function, seed: bool) -> InstructionSelector {
        let mut selector =
            InstructionSelector::new(function.name.clone(), function.signature.clone());
        // Compare/branch fusion is convention-independent; the selector still
        // refuses to place formals until a target convention is named.
        selector.set_abi_variant(AArch64AbiVariant::Aapcs64);
        selector
            .lower_formal_arguments(&function.signature, Block(0))
            .unwrap();
        if seed {
            selector.seed_function_value_use_counts(function);
        }
        selector
    }

    fn plan(selector: &InstructionSelector, body: &[Instruction]) -> HashMap<usize, IntCC> {
        let types = InstructionSelector::infer_block_value_types(body, &selector.value_types);
        selector.direct_branch_compares(body, &types)
    }

    #[test]
    fn direct_branch_preserves_compare_flags_cfg_and_each_source_identity() {
        let conditions = [
            IntCC::Equal,
            IntCC::NotEqual,
            IntCC::SignedLessThan,
            IntCC::SignedGreaterThanOrEqual,
            IntCC::SignedGreaterThan,
            IntCC::SignedLessThanOrEqual,
            IntCC::UnsignedLessThan,
            IntCC::UnsignedGreaterThanOrEqual,
            IntCC::UnsignedGreaterThan,
            IntCC::UnsignedLessThanOrEqual,
        ];
        for ty in [Type::I8, Type::I16, Type::I32, Type::I64] {
            for cond in conditions {
                let function = input(ty.clone(), cond);
                let body = &function.blocks[&Block(0)].instructions;
                let mut direct = selector(&function, true);
                let start = direct.func.blocks[&Block(0)].insts.len();
                let mut materialized = selector(&function, false);
                materialized.select_instruction(&body[0], Block(0)).unwrap();
                let old = &materialized.func.blocks[&Block(0)].insts[start..];
                assert_eq!(old.last().unwrap().opcode, AArch64Opcode::CSet);
                direct
                    .select_block_with_provenance(
                        Block(0),
                        body,
                        &[],
                        &[Some(TrustIrInstId(40)), Some(TrustIrInstId(41))],
                    )
                    .unwrap();
                let block = &direct.func.blocks[&Block(0)];
                let selected = &block.insts[start..];
                assert_eq!(selected.len(), old.len() + 1);
                for (before, after) in old[..old.len() - 1].iter().zip(selected) {
                    assert_eq!(before.opcode, after.opcode);
                    assert_eq!(before.operands, after.operands);
                }
                assert!(
                    !selected
                        .iter()
                        .any(|inst| inst.opcode == AArch64Opcode::CSet)
                );
                let branch = &selected[selected.len() - 2];
                assert_eq!(branch.opcode, AArch64Opcode::BCond);
                assert_eq!(
                    branch.operands,
                    vec![
                        ISelOperand::CondCode(AArch64CC::from_intcc(cond)),
                        ISelOperand::Block(Block(1))
                    ]
                );
                assert_eq!(
                    selected.last().unwrap().operands,
                    vec![ISelOperand::Block(Block(2))]
                );
                assert_eq!(block.successors, vec![Block(1), Block(2)]);
                assert_eq!(block.lowering_provenance.len(), block.insts.len());
                for (index, provenance) in block.lowering_provenance[start..].iter().enumerate() {
                    let source_index = usize::from(index >= old.len() - 1);
                    assert_eq!(
                        *provenance,
                        LoweringProvenance::SourceInst {
                            id: SourceInstId {
                                block: 0,
                                index: source_index as u32
                            },
                            digest: body[source_index].lowering_digest(),
                            trust_ir_inst: Some(TrustIrInstId(40 + source_index as u32)),
                        }
                    );
                }
            }
        }
    }

    #[test]
    fn direct_branch_requires_complete_uses_and_keeps_escaping_booleans() {
        let mut function = input(Type::I64, IntCC::UnsignedLessThan);
        let body = function.blocks[&Block(0)].instructions.clone();
        assert!(plan(&selector(&function, false), &body).is_empty());
        for target in [Block(1), Block(2)] {
            function.blocks.get_mut(&target).unwrap().instructions[0].args = vec![Value(2)];
            let mut isel = selector(&function, true);
            assert!(plan(&isel, &body).is_empty());
            isel.select_block(Block(0), &body).unwrap();
            assert!(
                isel.func.blocks[&Block(0)]
                    .insts
                    .iter()
                    .any(|inst| inst.opcode == AArch64Opcode::CSet)
            );
            assert!(isel.value_map.contains_key(&Value(2)));
        }
    }

    #[test]
    fn direct_branch_keeps_nonadjacent_flag_writers_and_local_multiple_uses() {
        for opcode in [Opcode::Icmp { cond: IntCC::Equal }, Opcode::Copy] {
            let mut function = input(Type::I64, IntCC::UnsignedLessThan);
            let extra = if matches!(opcode, Opcode::Copy) {
                Instruction {
                    opcode,
                    args: vec![Value(2)],
                    results: vec![Value(3)],
                }
            } else {
                Instruction {
                    opcode,
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(3)],
                }
            };
            function
                .blocks
                .get_mut(&Block(0))
                .unwrap()
                .instructions
                .insert(1, extra);
            let body = &function.blocks[&Block(0)].instructions;
            let mut isel = selector(&function, true);
            assert!(plan(&isel, body).is_empty());
            isel.select_block(Block(0), body).unwrap();
            assert!(
                isel.func.blocks[&Block(0)]
                    .insts
                    .iter()
                    .any(|inst| inst.opcode == AArch64Opcode::CSet)
            );
        }
    }

    #[test]
    fn direct_branch_refuses_malformed_unknown_width_and_claimed_shapes() {
        for mutation in 0..12 {
            let mut function = input(Type::I64, IntCC::Equal);
            let body = &mut function.blocks.get_mut(&Block(0)).unwrap().instructions;
            match mutation {
                0 => body[0].args.clear(),
                1 => body[0].args.push(Value(0)),
                2 => body[0].results.clear(),
                3 => body[0].results.push(Value(3)),
                4 => body[1].args.clear(),
                5 => body[1].args.push(Value(2)),
                6 => body[1].results.push(Value(3)),
                7 => body[1].args[0] = Value(0),
                8 => {
                    body[1].opcode = Opcode::Brif {
                        cond: Value(0),
                        then_dest: Block(1),
                        else_dest: Block(2),
                    }
                }
                9 => body.push(Instruction {
                    opcode: Opcode::Iconst {
                        ty: Type::I64,
                        imm: 0,
                    },
                    args: vec![],
                    results: vec![Value(2)],
                }),
                10 => function.signature.params[1] = Type::I32,
                11 => {}
                _ => unreachable!(),
            }
            let body = &function.blocks[&Block(0)].instructions;
            let mut isel = selector(&function, true);
            if mutation == 11 {
                isel.select_cond_fold_analysis.skip.insert(0);
            }
            assert!(plan(&isel, body).is_empty(), "mutation {mutation}");
        }
        for ty in [Type::I128, Type::B1, Type::F32, Type::F64] {
            let function = input(ty, IntCC::Equal);
            let isel = selector(&function, true);
            assert!(plan(&isel, &function.blocks[&Block(0)].instructions).is_empty());
        }
        let function = input(Type::I64, IntCC::Equal);
        let mut isel = selector(&function, true);
        isel.value_types.remove(&Value(1));
        assert!(plan(&isel, &function.blocks[&Block(0)].instructions).is_empty());
    }
}
