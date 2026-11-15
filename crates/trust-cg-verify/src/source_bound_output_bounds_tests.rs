// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;

fn captured() -> Module {
    serde_json::from_str(include_str!(
        "../tests/fixtures/output_memory_writer-O0.trust-ir.json"
    ))
    .unwrap()
}

#[test]
fn output_bounds_probes_require_true_operands_even_with_proof_references() {
    let original = captured();
    let lir = lower(&original);
    let code = code(false);
    for block in 0..5 {
        for mutation in 0..4 {
            let mut wrong = original.clone();
            let node = wrong.functions[0].blocks[block]
                .body
                .iter_mut()
                .find(|n| n.proofs.contains(&ProofAnnotation::InBounds))
                .unwrap();
            let Inst::ICmp { op, ty, lhs, rhs } = &mut node.inst else {
                panic!("probe")
            };
            match mutation {
                0 => *lhs = *rhs,       // Equality must trap under Ult, even with a ProofRef.
                1 => *op = ICmpOp::Ule, // A true comparison with the wrong probe semantics.
                2 => {
                    *ty = Ty::U64;
                    *lhs = v(2);
                    *rhs = v(3); // Runtime inputs, not a constant proof.
                }
                _ => *ty = Ty::U64, // Operand types no longer agree.
            }
            assert!(
                check_aarch64_trust_ir_output_bytes(&wrong, 0, &lir, &code).is_err(),
                "block={block} mutation={mutation}"
            );
        }
    }
    // Independently true probes need no authority from the attached proof IDs.
    // The adapter retains an unbound guard; this checker evaluates it itself.
    let mut no_ids = original.clone();
    for node in no_ids.functions[0]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.body)
    {
        node.proofs
            .retain(|p| !matches!(p, ProofAnnotation::ProofRef(_)));
    }
    let unbound = lower(&no_ids);
    assert!(
        unbound
            .blocks
            .values()
            .flat_map(|b| &b.instructions)
            .filter_map(|i| match i.opcode {
                Opcode::GuardBoundsCheck { obligation, .. } => Some(obligation),
                _ => None,
            })
            .all(|id| id.is_none())
    );
    check_aarch64_trust_ir_output_bytes(&no_ids, 0, &unbound, &code).unwrap();
}

#[test]
fn output_bounds_lir_guards_and_comparison_liveness_are_checked() {
    let original = captured();
    let lir = lower(&original);
    let code = code(false);
    let guards: Vec<_> = lir
        .blocks
        .iter()
        .flat_map(|(block, body)| {
            body.instructions
                .iter()
                .enumerate()
                .filter_map(move |(index, inst)| {
                    matches!(inst.opcode, Opcode::GuardBoundsCheck { .. })
                        .then_some((*block, index))
                })
        })
        .collect();
    assert_eq!(guards.len(), 5);
    for (block, index) in guards {
        for mutation in 0..5 {
            let mut wrong = lir.clone();
            let inst = &mut wrong.blocks.get_mut(&block).unwrap().instructions[index];
            match mutation {
                0 => {
                    let Opcode::GuardBoundsCheck { bound, .. } = &mut inst.opcode else {
                        unreachable!()
                    };
                    *bound = 0;
                }
                1 => inst.args = vec![Value(0), Value(0)],
                2 => inst.args.pop().map(|_| ()).unwrap(),
                3 => inst.results.push(Value(0)),
                _ => inst.args[0] = Value(u32::MAX),
            }
            assert!(
                check_aarch64_trust_ir_output_bytes(&original, 0, &wrong, &code).is_err(),
                "block={block:?} index={index} mutation={mutation}"
            );
        }
    }
    for mutation in 0..6 {
        let mut wrong = lir.clone();
        let cmp = wrong
            .blocks
            .get_mut(&wrong.entry_block)
            .unwrap()
            .instructions
            .iter_mut()
            .find(|i| matches!(i.opcode, Opcode::Icmp { .. }))
            .unwrap();
        let result = cmp.results[0];
        match mutation {
            0 => cmp.args[0] = Value(0),
            1 => cmp.results[0] = Value(0),
            2 => cmp.args.push(Value(0)),
            3 => {
                wrong.value_types.insert(result, Type::I64);
            }
            4 => {
                let store = wrong
                    .blocks
                    .values_mut()
                    .flat_map(|b| &mut b.instructions)
                    .find(|i| matches!(i.opcode, Opcode::Store { .. }))
                    .unwrap();
                store.args[0] = result; // A comparison result is now observable.
            }
            _ => {
                let cmp = cmp.clone();
                let terminal = wrong
                    .blocks
                    .values_mut()
                    .find(|b| {
                        b.instructions
                            .last()
                            .is_some_and(|i| matches!(i.opcode, Opcode::Return))
                    })
                    .unwrap();
                terminal.instructions.push(cmp); // Cannot erase code after a terminator.
            }
        }
        assert!(
            check_aarch64_trust_ir_output_bytes(&original, 0, &wrong, &code).is_err(),
            "comparison mutation={mutation}"
        );
    }
}

#[test]
fn output_literal_comparisons_cover_signed_and_unsigned_boundaries() {
    let cases = [
        (ICmpOp::Eq, -1, -1, true),
        (ICmpOp::Ne, -1, -1, false),
        (ICmpOp::Ult, -1, 0, false),
        (ICmpOp::Ule, 0, -1, true),
        (ICmpOp::Ugt, -1, 0, true),
        (ICmpOp::Uge, 0, -1, false),
        (ICmpOp::Slt, -1, 0, true),
        (ICmpOp::Sle, 0, -1, false),
        (ICmpOp::Sgt, i64::MAX, i64::MIN, true),
        (ICmpOp::Sge, i64::MIN, i64::MAX, false),
    ];
    for (op, left, right, expected) in cases {
        assert_eq!(
            literal_bounds::compare(op, left as u64, right as u64),
            expected
        );
        let mut module = fixture();
        let body = &mut module.functions[0].blocks[0].body;
        body.splice(
            0..0,
            [
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(i128::from(left)),
                })
                .with_result(v(100)),
                InstrNode::new(Inst::Const {
                    ty: Ty::I64,
                    value: Constant::Int(i128::from(right)),
                })
                .with_result(v(101)),
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: Ty::I64,
                    lhs: v(100),
                    rhs: v(101),
                })
                .with_result(v(102)),
            ],
        );
        let lir = lower(&module);
        check_aarch64_trust_ir_output_bytes(&module, 0, &lir, &code(false)).unwrap();
    }
}
