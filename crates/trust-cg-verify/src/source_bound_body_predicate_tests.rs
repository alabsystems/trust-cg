// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Concrete checks of the raw integer-comparison residual, separately from
//! the frame binder's structural refusals. Concrete agreement is a regression
//! test, not proof evidence; the explicit replay gate requires AY/Clean.

use super::{SourceBoundBody, raw_body};
use crate::lowering_proof::ProofObligation;
use crate::smt::{EvalEnv, EvalResult};
use crate::source_bound_frame::source_bound_frame;
use trust_cg_ir::function::Type as MachineType;
use trust_cg_ir::regs::{PReg, SpecialReg};
use trust_cg_ir::{AArch64Opcode as M, InstId, MachFunction, MachInst, MachOperand as O};
use trust_cg_lower::Type;
use trust_cg_lower::function::{BasicBlock, Function, Signature};
use trust_cg_lower::instructions::{Instruction, IntCC, Opcode as L, Value};

const CONDITIONS: [(IntCC, i64); 10] = [
    (IntCC::Equal, 0),
    (IntCC::NotEqual, 1),
    (IntCC::SignedLessThan, 11),
    (IntCC::SignedGreaterThanOrEqual, 10),
    (IntCC::SignedGreaterThan, 12),
    (IntCC::SignedLessThanOrEqual, 13),
    (IntCC::UnsignedLessThan, 3),
    (IntCC::UnsignedGreaterThanOrEqual, 2),
    (IntCC::UnsignedGreaterThan, 8),
    (IntCC::UnsignedLessThanOrEqual, 9),
];

const INPUTS: [u64; 13] = [
    0,
    1,
    2,
    4095,
    4096,
    i32::MAX as u64,
    1 << 31,
    u32::MAX as u64,
    1 << 32,
    (1 << 32) + 1,
    i64::MAX as u64,
    1 << 63,
    u64::MAX,
];

fn r(index: u16, bits: u32) -> O {
    O::PReg(PReg::new(index + if bits == 32 { 32 } else { 0 }))
}

fn copy(bits: u32) -> M {
    if bits == 32 { M::MOVWrr } else { M::MOVXrr }
}

fn ty(bits: u32) -> Type {
    if bits == 32 { Type::I32 } else { Type::I64 }
}

#[derive(Clone, Copy)]
struct Ids {
    left: InstId,
    right: InstId,
    stale_result: InstId,
    dead_copy: InstId,
    cmp: InstId,
    cset: InstId,
    result: InstId,
}

/// Actual operand copies, CMP, CSET and return copy inside the real leaf
/// envelope. `stale_result` is overwritten by CSET; retaining it makes a
/// destination mutation produce a defined but wrong raw result.
fn fixture(bits: u32, carrier: u32, cond: IntCC, cc: i64) -> (Function, MachFunction, Ids) {
    let (_, mut machine) = crate::source_bound_alu::tests::fixture(bits, M::AddRR, r(1, bits));
    let integer = ty(bits);
    let mut source = Function::new(
        "raw_integer_predicate",
        Signature {
            params: vec![integer.clone(); 2],
            returns: vec![Type::B1],
        },
    );
    let params = vec![(Value(0), integer.clone()), (Value(1), integer)];
    source.value_types.extend(params.iter().cloned());
    source.value_types.insert(Value(2), Type::B1);
    source.blocks.insert(
        source.entry_block,
        BasicBlock {
            params,
            instructions: vec![
                Instruction {
                    opcode: L::Icmp { cond },
                    args: vec![Value(0), Value(1)],
                    results: vec![Value(2)],
                },
                Instruction {
                    opcode: L::Return,
                    args: vec![Value(2)],
                    results: vec![],
                },
            ],
            ..Default::default()
        },
    );
    machine.name.clone_from(&source.name);
    machine.signature.returns = vec![MachineType::B1];
    machine.insts[2] = MachInst::new(M::CmpRR, vec![r(9, bits), r(10, bits)]);
    let left = machine.push_inst(MachInst::new(copy(bits), vec![r(9, bits), r(0, bits)]));
    let right = machine.push_inst(MachInst::new(copy(bits), vec![r(10, bits), r(1, bits)]));
    let stale_result = machine.push_inst(MachInst::new(copy(bits), vec![r(11, bits), r(0, bits)]));
    let dead_copy = machine.push_inst(MachInst::new(copy(bits), vec![r(12, bits), r(1, bits)]));
    let cset = machine.push_inst(MachInst::new(M::CSet, vec![r(11, carrier), O::Imm(cc)]));
    let result = machine.push_inst(MachInst::new(
        copy(carrier),
        vec![r(0, carrier), r(11, carrier)],
    ));
    machine.blocks[0].insts = vec![
        InstId(0),
        InstId(1),
        left,
        right,
        stale_result,
        dead_copy,
        InstId(2),
        cset,
        result,
        InstId(3),
        InstId(4),
    ];
    (
        source,
        machine,
        Ids {
            left,
            right,
            stale_result,
            dead_copy,
            cmp: InstId(2),
            cset,
            result,
        },
    )
}

fn immediate_fixture(
    bits: u32,
    carrier: u32,
    cond: IntCC,
    cc: i64,
    imm: i64,
) -> (Function, MachFunction, Ids) {
    let (mut source, mut machine, ids) = fixture(bits, carrier, cond, cc);
    let integer = ty(bits);
    source.value_types.insert(Value(2), integer.clone());
    source.value_types.insert(Value(3), Type::B1);
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions = vec![
        Instruction {
            opcode: L::Iconst { ty: integer, imm },
            args: vec![],
            results: vec![Value(2)],
        },
        Instruction {
            opcode: L::Icmp { cond },
            args: vec![Value(0), Value(2)],
            results: vec![Value(3)],
        },
        Instruction {
            opcode: L::Return,
            args: vec![Value(3)],
            results: vec![],
        },
    ];
    machine.insts[ids.cmp.0 as usize] = MachInst::new(M::CmpRI, vec![r(9, bits), O::Imm(imm)]);
    (source, machine, ids)
}

fn expected(cond: IntCC, bits: u32, a: u64, b: u64) -> u64 {
    let (a, b) = if bits == 32 {
        (a as u32 as u64, b as u32 as u64)
    } else {
        (a, b)
    };
    let (signed_a, signed_b) = if bits == 32 {
        (a as i32 as i64, b as i32 as i64)
    } else {
        (a as i64, b as i64)
    };
    u64::from(match cond {
        IntCC::Equal => a == b,
        IntCC::NotEqual => a != b,
        IntCC::SignedLessThan => signed_a < signed_b,
        IntCC::SignedGreaterThanOrEqual => signed_a >= signed_b,
        IntCC::SignedGreaterThan => signed_a > signed_b,
        IntCC::SignedLessThanOrEqual => signed_a <= signed_b,
        IntCC::UnsignedLessThan => a < b,
        IntCC::UnsignedGreaterThanOrEqual => a >= b,
        IntCC::UnsignedGreaterThan => a > b,
        IntCC::UnsignedLessThanOrEqual => a <= b,
    })
}

fn evaluate(obligation: &ProofObligation, a: u64, b: u64) -> (EvalResult, EvalResult) {
    let mut env = EvalEnv::default();
    env.insert("abi_x0".into(), a);
    env.insert("abi_x1".into(), b);
    (
        obligation.trust_ir_expr.eval(&env),
        obligation.aarch64_expr.eval(&env),
    )
}

fn raw(
    source: &Function,
    machine: &MachFunction,
) -> (ProofObligation, std::collections::HashSet<InstId>) {
    raw_body(
        source,
        machine,
        machine.blocks[0].insts.clone(),
        [InstId(0), InstId(1), InstId(3)],
    )
    .expect("supported wrong raw sequence must construct its semantic residual")
}

fn refuted(
    source: &Function,
    correct: &MachFunction,
    wrong: &MachFunction,
    a: u64,
    b: u64,
    label: &str,
) -> ProofObligation {
    let (correct, _) = raw(source, correct);
    let (wrong, _) = raw(source, wrong);
    assert!(
        !wrong.is_degenerate(),
        "{label}: a raw identity is not a residual"
    );
    assert_ne!(
        crate::serialize_to_smt2(&correct),
        crate::serialize_to_smt2(&wrong),
        "{label}: actual machine mutation must change the query"
    );
    let (source_value, machine_value) = evaluate(&wrong, a, b);
    assert_ne!(
        source_value, machine_value,
        "{label}: concrete ({a:#x}, {b:#x}) must refute the raw residual; structural refusal is insufficient"
    );
    assert_eq!(
        source_value,
        evaluate(&correct, a, b).0,
        "{label}: the machine mutation must not rewrite the source side"
    );
    println!(
        "A64_RAW_PREDICATE_COUNTEREXAMPLE mutation={label} a={a:#x} b={b:#x} source={source_value:?} machine={machine_value:?}"
    );
    wrong
}

#[test]
fn raw_comparisons_cover_all_integer_conditions_and_canonical_w_x_carriers() {
    let mut cases = 0;
    for bits in [32, 64] {
        for carrier in [32, 64] {
            for (cond, cc) in CONDITIONS {
                let (source, machine, ids) = fixture(bits, carrier, cond, cc);
                let frame = source_bound_frame(&source, &machine).expect("correct CMP/CSET frame");
                let body = SourceBoundBody::bind(&frame).expect("comparison raw owner");
                assert_eq!(
                    body.category(),
                    crate::proof_database::ProofCategory::Comparison
                );
                let obligation = body.obligation();
                assert!(!obligation.is_degenerate());
                assert_eq!(obligation.trust_ir_expr.bv_width(), 64);
                assert_eq!(obligation.aarch64_expr.bv_width(), 64);
                assert_eq!(
                    obligation.inputs,
                    [("abi_x0".to_string(), 64), ("abi_x1".to_string(), 64)]
                );
                for id in [ids.left, ids.right, ids.cmp, ids.cset, ids.result] {
                    assert!(
                        body.credits(id),
                        "{bits}/{carrier}/{cond:?}: live dependency {id:?}"
                    );
                }
                for id in [
                    ids.stale_result,
                    ids.dead_copy,
                    InstId(0),
                    InstId(1),
                    InstId(3),
                    InstId(4),
                    InstId(99),
                ] {
                    assert!(
                        !body.credits(id),
                        "{bits}/{carrier}/{cond:?}: dead/envelope {id:?}"
                    );
                }
                for a in INPUTS {
                    for b in INPUTS {
                        let want = EvalResult::Bv(expected(cond, bits, a, b));
                        assert_eq!(
                            evaluate(obligation, a, b),
                            (want.clone(), want),
                            "{bits}/{carrier}/{cond:?}/{a:#x}/{b:#x}"
                        );
                    }
                }
                let query = crate::serialize_to_smt2(obligation);
                assert!(
                    query.contains("bvsub"),
                    "CMP must retain subtraction/flags, not a source-derived predicate"
                );
                assert!(
                    query.contains("zero_extend 63"),
                    "B1 return must be canonically lifted to full X0"
                );
                if bits == 32 || carrier == 32 {
                    assert!(
                        query.contains("zero_extend 32"),
                        "W writes clear their X alias's upper bits"
                    );
                }
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 40);
}

#[test]
fn raw_immediate_comparisons_keep_source_constants_and_live_operand_dependencies() {
    for bits in [32, 64] {
        for carrier in [32, 64] {
            for (cond, cc) in CONDITIONS {
                for imm in [0, 4095] {
                    let (source, machine, ids) = immediate_fixture(bits, carrier, cond, cc, imm);
                    let frame =
                        source_bound_frame(&source, &machine).expect("correct immediate CMP");
                    let body = SourceBoundBody::bind(&frame).expect("raw immediate comparison");
                    assert!(
                        body.credits(ids.left)
                            && body.credits(ids.cmp)
                            && body.credits(ids.cset)
                            && body.credits(ids.result)
                    );
                    assert!(
                        !body.credits(ids.right),
                        "unused RHS parameter copy is dead"
                    );
                    for a in INPUTS {
                        let want = EvalResult::Bv(expected(cond, bits, a, imm as u64));
                        assert_eq!(
                            evaluate(body.obligation(), a, u64::MAX),
                            (want.clone(), want)
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn cmp_operands_cset_condition_destination_and_reaching_flags_have_raw_counterexamples() {
    for bits in [32, 64] {
        let (source, machine, ids) = fixture(bits, 64, IntCC::SignedLessThan, 11);
        for mutation in 0..6 {
            let mut wrong = machine.clone();
            let label = match mutation {
                0 => {
                    wrong.insts[ids.cmp.0 as usize].operands.swap(0, 1);
                    "cmp-swapped-operands"
                }
                1 => {
                    wrong.insts[ids.cmp.0 as usize].operands[0] = r(10, bits);
                    "cmp-wrong-lhs"
                }
                2 => {
                    wrong.insts[ids.cmp.0 as usize].operands[1] = r(9, bits);
                    "cmp-wrong-rhs"
                }
                3 => {
                    wrong.insts[ids.cset.0 as usize].operands[1] = O::Imm(10);
                    "cset-complemented-condition"
                }
                4 => {
                    wrong.insts[ids.cset.0 as usize].operands[0] = r(12, 64);
                    "cset-wrong-destination"
                }
                _ => {
                    let clobber =
                        wrong.push_inst(MachInst::new(M::CmpRR, vec![r(10, bits), r(9, bits)]));
                    let at = wrong.blocks[0]
                        .insts
                        .iter()
                        .position(|&id| id == ids.cset)
                        .unwrap();
                    wrong.blocks[0].insts.insert(at, clobber);
                    "cset-reaches-later-cmp"
                }
            };
            assert!(
                source_bound_frame(&source, &wrong).is_err(),
                "the independent frame checker also rejects {label}"
            );
            let obligation = refuted(&source, &machine, &wrong, 7, 23, label);
            assert_eq!(evaluate(&obligation, 7, 23).0, EvalResult::Bv(1));
        }
    }
}

#[test]
fn cmp_width_and_integer_copy_width_changes_are_semantic_counterexamples() {
    let (source, machine, ids) = fixture(64, 64, IntCC::UnsignedLessThan, 3);
    let mut narrow = machine.clone();
    narrow.insts[ids.cmp.0 as usize].operands = vec![r(9, 32), r(10, 32)];
    assert!(source_bound_frame(&source, &narrow).is_err());
    let obligation = refuted(
        &source,
        &machine,
        &narrow,
        (1 << 32) + 1,
        2,
        "cmp-x-to-w-width",
    );
    assert_eq!(
        evaluate(&obligation, (1 << 32) + 1, 2),
        (EvalResult::Bv(0), EvalResult::Bv(1))
    );
    let mut narrow = machine.clone();
    // Typed W moves apply W semantics even when allocation keeps X alias
    // spellings. This is an operand-dataflow mutation, not a shape refusal.
    narrow.insts[ids.left.0 as usize].opcode = M::MOVWrr;
    assert!(source_bound_frame(&source, &narrow).is_err());
    refuted(
        &source,
        &machine,
        &narrow,
        (1 << 32) + 1,
        2,
        "cmp-input-copy-x-to-w-width",
    );
    let (source, mut machine, ids) = fixture(32, 64, IntCC::UnsignedLessThan, 3);
    // Compare incoming W ABI aliases directly: no earlier W copy clears
    // the original X0/X1 high bits. W->X therefore changes semantics.
    machine.insts[ids.cmp.0 as usize].operands = vec![r(0, 32), r(1, 32)];
    let frame = source_bound_frame(&source, &machine).expect("direct incoming W compare");
    let body = SourceBoundBody::bind(&frame).expect("raw incoming W comparison");
    assert_eq!(
        evaluate(body.obligation(), (1 << 32) + 1, 2),
        (EvalResult::Bv(1), EvalResult::Bv(1))
    );
    let mut wide = machine.clone();
    wide.insts[ids.cmp.0 as usize].operands = vec![r(0, 64), r(1, 64)];
    assert!(source_bound_frame(&source, &wide).is_err());
    let obligation = refuted(
        &source,
        &machine,
        &wide,
        (1 << 32) + 1,
        2,
        "cmp-incoming-w-to-x-width",
    );
    assert_eq!(
        evaluate(&obligation, (1 << 32) + 1, 2),
        (EvalResult::Bv(1), EvalResult::Bv(0))
    );
}

#[test]
fn boolean_return_checks_all_x0_bits_and_writes_clear_old_upper_bits() {
    for bits in [32, 64] {
        for carrier in [32, 64] {
            let (source, machine, ids) = fixture(bits, carrier, IntCC::Equal, 0);
            let frame = source_bound_frame(&source, &machine).unwrap();
            let body = SourceBoundBody::bind(&frame).unwrap();
            // Result X11 starts as this noncanonical incoming integer;
            // either CSET carrier must fully replace it with canonical 1.
            assert_eq!(
                evaluate(body.obligation(), u64::MAX, u64::MAX),
                (EvalResult::Bv(1), EvalResult::Bv(1))
            );
            let mut wrong = machine.clone();
            let high = wrong.push_inst(MachInst::new(
                M::Movz,
                vec![r(12, 64), O::Imm(1), O::Imm(32)],
            ));
            let corrupt =
                wrong.push_inst(MachInst::new(M::AddRR, vec![r(0, 64), r(0, 64), r(12, 64)]));
            let at = wrong.blocks[0]
                .insts
                .iter()
                .position(|&id| id == ids.result)
                .unwrap()
                + 1;
            wrong.blocks[0].insts.splice(at..at, [high, corrupt]);
            assert!(source_bound_frame(&source, &wrong).is_err());
            let obligation = refuted(
                &source,
                &machine,
                &wrong,
                1,
                1,
                "noncanonical-x0-upper-bits",
            );
            assert_eq!(
                evaluate(&obligation, 1, 1),
                (EvalResult::Bv(1), EvalResult::Bv((1 << 32) | 1))
            );
        }
    }
}

#[test]
fn only_live_cmp_cset_copies_and_reaching_flag_dependencies_receive_credit() {
    for bits in [32, 64] {
        let (source, mut machine, ids) = fixture(bits, 32, IntCC::SignedLessThan, 11);
        let dead_before = machine.push_inst(MachInst::new(M::CmpRR, vec![r(9, bits), r(9, bits)]));
        let dead_set_before =
            machine.push_inst(MachInst::new(M::CSet, vec![r(12, 32), O::Imm(11)]));
        let at = machine.blocks[0]
            .insts
            .iter()
            .position(|&id| id == ids.cmp)
            .unwrap();
        machine.blocks[0]
            .insts
            .splice(at..at, [dead_before, dead_set_before]);
        let dead_after = machine.push_inst(MachInst::new(M::CmpRR, vec![r(10, bits), r(10, bits)]));
        let dead_set_after = machine.push_inst(MachInst::new(M::CSet, vec![r(12, 32), O::Imm(11)]));
        let at = machine.blocks[0]
            .insts
            .iter()
            .position(|&id| id == ids.cset)
            .unwrap()
            + 1;
        machine.blocks[0]
            .insts
            .splice(at..at, [dead_after, dead_set_after]);
        let frame = source_bound_frame(&source, &machine)
            .expect("dead flags and predicates leave the return intact");
        let body = SourceBoundBody::bind(&frame).expect("bounded raw predicate body");
        for live in [ids.left, ids.right, ids.cmp, ids.cset, ids.result] {
            assert!(body.credits(live), "live dependency {live:?}");
        }
        for dead in [
            ids.stale_result,
            ids.dead_copy,
            dead_before,
            dead_set_before,
            dead_after,
            dead_set_after,
        ] {
            assert!(
                !body.credits(dead),
                "overwritten/unobserved dependency {dead:?}"
            );
        }
        assert_eq!(
            evaluate(body.obligation(), 7, 23),
            (EvalResult::Bv(1), EvalResult::Bv(1))
        );
    }
}

#[test]
fn predicate_raw_model_refuses_missing_flags_unsupported_writers_and_malformed_operands() {
    let (source, machine, ids) = fixture(64, 64, IntCC::SignedLessThan, 11);
    for mutation in 0..11 {
        let mut wrong = machine.clone();
        match mutation {
            0 => wrong.insts[ids.cmp.0 as usize] = MachInst::new(M::Nop, vec![]),
            1 => wrong.insts[ids.cmp.0 as usize].operands[0] = r(14, 64),
            2 => wrong.insts[ids.cmp.0 as usize].operands[1] = r(10, 32),
            3 => wrong.insts[ids.cset.0 as usize].operands[1] = O::Imm(14),
            4 => wrong.insts[ids.cset.0 as usize].operands[1] = O::Imm(-1),
            5 => wrong.insts[ids.cset.0 as usize].operands[0] = O::Special(SpecialReg::SP),
            6 => {
                wrong.insts[ids.cmp.0 as usize] =
                    MachInst::new(M::CmpRI, vec![r(9, 64), O::Imm(4096)])
            }
            7 => wrong.insts[ids.cset.0 as usize]
                .operands
                .pop()
                .map(|_| ())
                .unwrap(),
            8 => {
                let unknown_flags = wrong.push_inst(MachInst::new(
                    M::AddsRR,
                    vec![r(12, 64), r(9, 64), r(10, 64)],
                ));
                let at = wrong.blocks[0]
                    .insts
                    .iter()
                    .position(|&id| id == ids.cset)
                    .unwrap();
                wrong.blocks[0].insts.insert(at, unknown_flags);
            }
            9 => {
                wrong.insts[ids.cmp.0 as usize] =
                    MachInst::new(M::CmpRI, vec![O::Special(SpecialReg::XZR), O::Imm(0)])
            }
            _ => {
                wrong.blocks[0].insts.pop();
            }
        }
        assert!(
            raw_body(
                &source,
                &wrong,
                wrong.blocks[0].insts.clone(),
                [InstId(0), InstId(1), InstId(3)]
            )
            .is_none(),
            "malformed/unsupported case {mutation} must fail closed; this is not residual refutation credit"
        );
    }
}

#[test]
fn predicate_source_domain_and_raw_tree_resource_limits_fail_closed() {
    let (source, machine, _) = fixture(64, 64, IntCC::SignedLessThan, 11);
    for mutation in 0..4 {
        let mut wrong = source.clone();
        match mutation {
            0 => wrong.signature.params[0] = Type::B1,
            1 => wrong.signature.params[1] = Type::I32,
            2 => wrong.signature.params = vec![Type::I64; 9],
            _ => {
                wrong
                    .blocks
                    .get_mut(&wrong.entry_block)
                    .unwrap()
                    .instructions[0]
                    .args[0] = Value(99)
            }
        }
        assert!(
            raw_body(
                &wrong,
                &machine,
                machine.blocks[0].insts.clone(),
                [InstId(0), InstId(1), InstId(3)]
            )
            .is_none(),
            "unsupported source case {mutation}"
        );
    }
    for bits in [32, 64] {
        let (mut source, mut machine, ids) = fixture(bits, 64, IntCC::Equal, 0);
        let mut instructions = Vec::new();
        let mut value = Value(0);
        // Repeated source doubling has a compact affine form, but expands
        // exponentially as a raw tree. Refuse before cloning beyond budget.
        for i in 0..13 {
            let result = Value(i + 2);
            instructions.push(Instruction {
                opcode: L::Iadd,
                args: vec![value, value],
                results: vec![result],
            });
            source.value_types.insert(result, ty(bits));
            value = result;
        }
        let predicate = Value(15);
        instructions.push(Instruction {
            opcode: L::Icmp { cond: IntCC::Equal },
            args: vec![value, Value(1)],
            results: vec![predicate],
        });
        instructions.push(Instruction {
            opcode: L::Return,
            args: vec![predicate],
            results: vec![],
        });
        source.value_types.insert(predicate, Type::B1);
        source
            .blocks
            .get_mut(&source.entry_block)
            .unwrap()
            .instructions = instructions;
        let shift = machine.push_inst(MachInst::new(
            M::LslRI,
            vec![r(9, bits), r(9, bits), O::Imm(13)],
        ));
        let at = machine.blocks[0]
            .insts
            .iter()
            .position(|&id| id == ids.cmp)
            .unwrap();
        machine.blocks[0].insts.insert(at, shift);
        let frame = source_bound_frame(&source, &machine)
            .expect("resource control is otherwise semantically supported");
        assert!(
            SourceBoundBody::bind(&frame).is_none(),
            "raw expansion must decline, never substitute an affine predicate"
        );
    }
}

#[test]
fn wrong_comparison_raw_residual_requires_an_independent_ay_counterexample() {
    use crate::ay_bridge::{AYConfig, AYResult, verify_with_cli_raw_attributed};
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_NO_SOLVER_SERVER", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            for bits in [32, 64] {
                let (source, machine, ids) = fixture(bits, 64, IntCC::SignedLessThan, 11);
                let mut wrong = machine.clone();
                wrong.insts[ids.cset.0 as usize].operands[1] = O::Imm(10);
                let obligation = refuted(
                    &source,
                    &machine,
                    &wrong,
                    7,
                    23,
                    "independent-cset-condition",
                );
                let outcome = verify_with_cli_raw_attributed(&obligation, &AYConfig::default());
                assert!(
                    matches!(outcome.result, AYResult::CounterExample(_)),
                    "i{bits}: wrong raw comparison needs an AY counterexample, not structural refusal: {:?}",
                    outcome.result
                );
                println!(
                    "A64_RAW_PREDICATE_AY_COUNTEREXAMPLE bits={bits} result={} provenance={:?}",
                    outcome.result,
                    outcome.provenance()
                );
            }
        },
    );
}

#[test]
fn comparison_raw_obligations_require_positive_independent_ay_clean_replay() {
    use crate::function_request::FunctionDischargeContext;
    use crate::provenance_xcheck::ProvenanceXCheckMode;
    use crate::verify::VerificationResult;
    use crate::{FunctionVerifier, VerificationConfig};
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_REFINE_SOLVER", "1"),
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            let verifier = FunctionVerifier::with_config(VerificationConfig::for_proof_promotion());
            let request = verifier.capture_request_with_mode(ProvenanceXCheckMode::Enforce);
            for bits in [32, 64] {
                for (cond, cc) in CONDITIONS {
                    let (source, machine, _) = fixture(bits, 64, cond, cc);
                    let frame =
                        source_bound_frame(&source, &machine).expect("matching comparison frame");
                    let body = SourceBoundBody::bind(&frame).expect("raw comparison owner");
                    println!(
                        "A64_RAW_PREDICATE_REPLAY_QUERY bits={bits} cond={cond:?} smt2={}",
                        serde_json::to_string(&crate::serialize_to_smt2(body.obligation()))
                            .unwrap()
                    );
                    let result = FunctionDischargeContext::new(&request).a64_body(&body);
                    assert!(
                        matches!(result, Some(VerificationResult::Valid)),
                        "required independent AY/Clean replay i{bits}/{cond:?}: {result:?}; concrete evaluation is not substitute proof evidence"
                    );
                }
            }
        },
    );
}
