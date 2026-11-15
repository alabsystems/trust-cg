// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Raw source/machine select equations are checked independently here. Concrete
//! agreement and structural refusal are not proof evidence; the positive gate
//! separately requires fresh AY/Clean replay of the exact raw obligation.

use super::{SourceBoundBody, raw_body};
use crate::lowering_proof::ProofObligation;
use crate::smt::{EvalEnv, EvalResult};
use crate::source_bound_frame::source_bound_frame;
use std::collections::HashSet;
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

const INPUTS: [u64; 12] = [
    0,
    1,
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

#[derive(Clone, Copy, Debug)]
enum Route {
    Direct,
    Materialized(u32),
}

#[derive(Clone, Copy)]
struct Ids {
    inputs: [InstId; 4],
    stale_result: InstId,
    dead_copy: InstId,
    cmp: InstId,
    bool_set: Option<InstId>,
    bool_cmp: Option<InstId>,
    select: InstId,
    result: InstId,
}

fn r(index: u16, bits: u32) -> O {
    O::PReg(PReg::new(index + if bits == 32 { 32 } else { 0 }))
}

fn copy(bits: u32) -> M {
    if bits == 32 { M::MOVWrr } else { M::MOVXrr }
}

fn ty(bits: u32) -> Type {
    if bits == 32 { Type::I32 } else { Type::I64 }
}

fn inst(opcode: L, args: &[u32], result: Option<u32>) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(Value).collect(),
        results: result.into_iter().map(Value).collect(),
    }
}

/// Four independent ABI inputs, a canonical B1 comparison, and integer
/// Select. Modifiers are expressed by real wrapping source arithmetic on the
/// false arm, never inferred from the machine opcode when building the query.
fn fixture(
    bits: u32,
    condition: IntCC,
    cc: i64,
    selector: IntCC,
    operation: M,
    route: Route,
) -> (Function, MachFunction, Ids) {
    let (_, mut machine) = crate::source_bound_alu::tests::fixture(bits, M::AddRR, r(1, bits));
    let integer = ty(bits);
    let mut source = Function::new(
        "raw_integer_select",
        Signature {
            params: vec![integer.clone(); 4],
            returns: vec![integer.clone()],
        },
    );
    let params = (0..4)
        .map(|i| (Value(i), integer.clone()))
        .collect::<Vec<_>>();
    source.value_types.extend(params.iter().cloned());
    source.value_types.insert(Value(4), Type::B1);
    let mut instructions = vec![inst(L::Icmp { cond: condition }, &[0, 1], Some(4))];
    let false_value = match operation {
        M::Csel => 3,
        M::Csinc | M::Csinv | M::Csneg => {
            let constant = match operation {
                M::Csinc => 1,
                M::Csinv => -1,
                _ => 0,
            };
            instructions.push(inst(
                L::Iconst {
                    ty: integer.clone(),
                    imm: constant,
                },
                &[],
                Some(5),
            ));
            instructions.push(inst(
                if operation == M::Csinc {
                    L::Iadd
                } else {
                    L::Isub
                },
                if operation == M::Csinc {
                    &[3, 5]
                } else {
                    &[5, 3]
                },
                Some(6),
            ));
            source.value_types.insert(Value(5), integer.clone());
            source.value_types.insert(Value(6), integer.clone());
            6
        }
        _ => panic!("not a conditional-select fixture operation"),
    };
    let result_value = if false_value == 3 { 5 } else { 7 };
    instructions.push(inst(
        L::Select { cond: selector },
        &[4, 2, false_value],
        Some(result_value),
    ));
    instructions.push(inst(L::Return, &[result_value], None));
    source.value_types.insert(Value(result_value), integer);
    source.blocks.insert(
        source.entry_block,
        BasicBlock {
            params,
            instructions,
            ..Default::default()
        },
    );
    machine.name.clone_from(&source.name);
    let machine_type = if bits == 32 {
        MachineType::I32
    } else {
        MachineType::I64
    };
    machine.signature.params = vec![machine_type.clone(); 4];
    machine.signature.returns = vec![machine_type];
    let inputs = std::array::from_fn(|i| {
        machine.push_inst(MachInst::new(
            copy(bits),
            vec![r(i as u16 + 9, bits), r(i as u16, bits)],
        ))
    });
    let stale_result = machine.push_inst(MachInst::new(copy(bits), vec![r(13, bits), r(1, bits)]));
    let dead_copy = machine.push_inst(MachInst::new(copy(bits), vec![r(14, bits), r(0, bits)]));
    machine.insts[2] = MachInst::new(M::CmpRR, vec![r(9, bits), r(10, bits)]);
    let mut chain = vec![InstId(0), InstId(1)];
    chain.extend(inputs);
    chain.extend([stale_result, dead_copy, InstId(2)]);
    let (bool_set, bool_cmp, select_cc) = match route {
        Route::Direct => (None, None, cc ^ i64::from(selector == IntCC::Equal)),
        Route::Materialized(carrier) => {
            let set = machine.push_inst(MachInst::new(M::CSet, vec![r(15, carrier), O::Imm(cc)]));
            let cmp = machine.push_inst(MachInst::new(M::CmpRI, vec![r(15, carrier), O::Imm(0)]));
            chain.extend([set, cmp]);
            (Some(set), Some(cmp), i64::from(selector == IntCC::NotEqual))
        }
    };
    let select = machine.push_inst(MachInst::new(
        operation,
        vec![r(13, bits), r(11, bits), r(12, bits), O::Imm(select_cc)],
    ));
    let result = machine.push_inst(MachInst::new(copy(bits), vec![r(0, bits), r(13, bits)]));
    chain.extend([select, result, InstId(3), InstId(4)]);
    machine.blocks[0].insts = chain;
    (
        source,
        machine,
        Ids {
            inputs,
            stale_result,
            dead_copy,
            cmp: InstId(2),
            bool_set,
            bool_cmp,
            select,
            result,
        },
    )
}

fn low(value: u64, bits: u32) -> u64 {
    if bits == 32 {
        value as u32 as u64
    } else {
        value
    }
}

fn predicate(condition: IntCC, bits: u32, a: u64, b: u64) -> bool {
    let (a, b) = (low(a, bits), low(b, bits));
    let (sa, sb) = if bits == 32 {
        (a as i32 as i64, b as i32 as i64)
    } else {
        (a as i64, b as i64)
    };
    match condition {
        IntCC::Equal => a == b,
        IntCC::NotEqual => a != b,
        IntCC::SignedLessThan => sa < sb,
        IntCC::SignedGreaterThanOrEqual => sa >= sb,
        IntCC::SignedGreaterThan => sa > sb,
        IntCC::SignedLessThanOrEqual => sa <= sb,
        IntCC::UnsignedLessThan => a < b,
        IntCC::UnsignedGreaterThanOrEqual => a >= b,
        IntCC::UnsignedGreaterThan => a > b,
        IntCC::UnsignedLessThanOrEqual => a <= b,
    }
}

fn expected(bits: u32, condition: IntCC, selector: IntCC, operation: M, input: [u64; 4]) -> u64 {
    let [a, b, yes, no] = input;
    let take_then = predicate(condition, bits, a, b) ^ (selector == IntCC::Equal);
    low(
        if take_then {
            yes
        } else {
            match operation {
                M::Csel => no,
                M::Csinc => no.wrapping_add(1),
                M::Csinv => !no,
                M::Csneg => 0u64.wrapping_sub(no),
                _ => unreachable!(),
            }
        },
        bits,
    )
}

fn evaluate(obligation: &ProofObligation, input: [u64; 4]) -> (EvalResult, EvalResult) {
    let mut env = EvalEnv::default();
    for (i, value) in input.into_iter().enumerate() {
        env.insert(format!("abi_x{i}"), value);
    }
    (
        obligation.trust_ir_expr.eval(&env),
        obligation.aarch64_expr.eval(&env),
    )
}

fn raw(source: &Function, machine: &MachFunction) -> (ProofObligation, HashSet<InstId>) {
    raw_body(
        source,
        machine,
        machine.blocks[0].insts.clone(),
        [InstId(0), InstId(1), InstId(3)],
    )
    .expect("supported wrong sequence must construct an independent raw semantic residual")
}

fn refuted(
    source: &Function,
    correct: &MachFunction,
    wrong: &MachFunction,
    input: [u64; 4],
    label: &str,
) -> ProofObligation {
    let (correct, _) = raw(source, correct);
    let (wrong, _) = raw(source, wrong);
    assert!(
        !wrong.is_degenerate(),
        "{label}: raw identity supplies no residual"
    );
    assert_ne!(
        crate::serialize_to_smt2(&correct),
        crate::serialize_to_smt2(&wrong),
        "{label}: machine mutation must change the actual query"
    );
    let (source_value, machine_value) = evaluate(&wrong, input);
    assert_eq!(
        source_value,
        evaluate(&correct, input).0,
        "{label}: machine mutation must not rewrite source semantics"
    );
    assert_ne!(
        source_value, machine_value,
        "{label}: {input:?} must refute the raw residual; structural refusal is insufficient"
    );
    println!(
        "A64_RAW_SELECT_COUNTEREXAMPLE mutation={label} input={input:?} source={source_value:?} machine={machine_value:?}"
    );
    wrong
}

fn insert_before(machine: &mut MachFunction, at: InstId, inserted: &[InstId]) {
    let index = machine.blocks[0]
        .insts
        .iter()
        .position(|&id| id == at)
        .unwrap();
    machine.blocks[0]
        .insts
        .splice(index..index, inserted.iter().copied());
}

#[test]
fn raw_select_covers_all_comparisons_eq_ne_and_direct_materialized_conditions() {
    let mut cases = 0;
    for bits in [32, 64] {
        for (condition, cc) in CONDITIONS {
            for selector in [IntCC::Equal, IntCC::NotEqual] {
                for route in [
                    Route::Direct,
                    Route::Materialized(32),
                    Route::Materialized(64),
                ] {
                    let (source, machine, ids) =
                        fixture(bits, condition, cc, selector, M::Csel, route);
                    let frame = source_bound_frame(&source, &machine)
                        .expect("matching four-input select frame");
                    let body = SourceBoundBody::bind(&frame).expect("raw integer select owner");
                    assert_eq!(
                        body.category(),
                        crate::proof_database::ProofCategory::Arithmetic
                    );
                    let obligation = body.obligation();
                    assert!(!obligation.is_degenerate());
                    assert_eq!(obligation.trust_ir_expr.bv_width(), bits);
                    assert_eq!(obligation.aarch64_expr.bv_width(), bits);
                    assert_eq!(
                        obligation.inputs,
                        (0..4)
                            .map(|i| (format!("abi_x{i}"), 64))
                            .collect::<Vec<_>>()
                    );
                    let mut live = ids.inputs.into_iter().collect::<HashSet<_>>();
                    live.extend([ids.cmp, ids.select, ids.result]);
                    live.extend(ids.bool_set);
                    live.extend(ids.bool_cmp);
                    let (_, actual) = raw(&source, &machine);
                    assert_eq!(
                        actual, live,
                        "i{bits}/{condition:?}/{selector:?}/{route:?}: exact dependency slice"
                    );
                    for id in live {
                        assert!(body.credits(id));
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
                        assert!(!body.credits(id), "dead/envelope dependency {id:?}");
                    }
                    for a in INPUTS {
                        for b in INPUTS {
                            for (yes, no) in
                                [(111, 222), (u64::MAX, 0), ((1 << 32) + 17, (1 << 63) + 29)]
                            {
                                let input = [a, b, yes, no];
                                let want = EvalResult::Bv(expected(
                                    bits,
                                    condition,
                                    selector,
                                    M::Csel,
                                    input,
                                ));
                                assert_eq!(
                                    evaluate(obligation, input),
                                    (want.clone(), want),
                                    "i{bits}/{condition:?}/{selector:?}/{route:?}/{input:?}"
                                );
                            }
                        }
                    }
                    let query = crate::serialize_to_smt2(obligation);
                    assert!(
                        query.contains("bvsub"),
                        "machine condition must retain actual CMP subtraction/flags"
                    );
                    assert!(
                        query.contains("ite"),
                        "raw integer select must retain its ITE"
                    );
                    if bits == 32 {
                        assert!(
                            query.contains("zero_extend 32"),
                            "W copies must clear their X aliases' upper bits"
                        );
                    }
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 120);
}

#[test]
fn raw_conditional_select_modifiers_transform_only_false_arm_with_wrapping() {
    let mut cases = 0;
    for bits in [32, 64] {
        for operation in [M::Csel, M::Csinc, M::Csinv, M::Csneg] {
            for selector in [IntCC::Equal, IntCC::NotEqual] {
                for route in [Route::Direct, Route::Materialized(32)] {
                    let (source, machine, ids) =
                        fixture(bits, IntCC::SignedLessThan, 11, selector, operation, route);
                    let frame = source_bound_frame(&source, &machine)
                        .expect("matching transformed false arm");
                    let body = SourceBoundBody::bind(&frame).expect("raw modifier semantics");
                    assert!(body.credits(ids.select));
                    for (a, b) in [(7, 23), (23, 7)] {
                        for yes in INPUTS {
                            for no in INPUTS {
                                let input = [a, b, yes, no];
                                let want = EvalResult::Bv(expected(
                                    bits,
                                    IntCC::SignedLessThan,
                                    selector,
                                    operation,
                                    input,
                                ));
                                assert_eq!(
                                    evaluate(body.obligation(), input),
                                    (want.clone(), want),
                                    "i{bits}/{operation:?}/{selector:?}/{route:?}/{input:?}"
                                );
                            }
                        }
                    }
                    if operation != M::Csel {
                        assert!(
                            crate::serialize_to_smt2(body.obligation()).contains("zero_extend 1"),
                            "source false-arm arithmetic must retain widened wrapping"
                        );
                    }
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 32);
}

#[test]
fn select_conditions_arms_cmp_flags_destinations_and_return_routes_have_raw_counterexamples() {
    for bits in [32, 64] {
        let (source, machine, ids) = fixture(
            bits,
            IntCC::SignedLessThan,
            11,
            IntCC::NotEqual,
            M::Csel,
            Route::Direct,
        );
        for mutation in 0..10 {
            let mut wrong = machine.clone();
            let mut input = [7, 23, 111, 222];
            let label = match mutation {
                0 => {
                    wrong.insts[ids.select.0 as usize].operands[3] = O::Imm(10);
                    "select-wrong-condition"
                }
                1 => {
                    wrong.insts[ids.select.0 as usize].operands.swap(1, 2);
                    "select-swapped-arms"
                }
                2 => {
                    wrong.insts[ids.select.0 as usize].operands[1] = r(12, bits);
                    "select-wrong-true-arm"
                }
                3 => {
                    input = [23, 7, 111, 222];
                    wrong.insts[ids.select.0 as usize].operands[2] = r(11, bits);
                    "select-wrong-false-arm"
                }
                4 => {
                    wrong.insts[ids.cmp.0 as usize].operands.swap(0, 1);
                    "select-cmp-swapped-operands"
                }
                5 => {
                    wrong.insts[ids.cmp.0 as usize].operands[0] = r(10, bits);
                    "select-cmp-wrong-lhs"
                }
                6 => {
                    let clobber =
                        wrong.push_inst(MachInst::new(M::CmpRR, vec![r(10, bits), r(9, bits)]));
                    insert_before(&mut wrong, ids.select, &[clobber]);
                    "select-reaches-overwriting-cmp"
                }
                7 => {
                    wrong.insts[ids.select.0 as usize].operands[0] = r(14, bits);
                    "select-wrong-destination"
                }
                8 => {
                    wrong.insts[ids.result.0 as usize].operands[1] = r(12, bits);
                    "select-wrong-return-route"
                }
                _ => {
                    let clobber =
                        wrong.push_inst(MachInst::new(copy(bits), vec![r(13, bits), r(12, bits)]));
                    insert_before(&mut wrong, ids.result, &[clobber]);
                    "select-overwritten-result"
                }
            };
            assert!(
                source_bound_frame(&source, &wrong).is_err(),
                "independent frame checker must also reject {label}"
            );
            refuted(&source, &machine, &wrong, input, label);
        }
        for operation in [M::Csinc, M::Csinv, M::Csneg] {
            let mut wrong = machine.clone();
            wrong.insts[ids.select.0 as usize].opcode = operation;
            assert!(source_bound_frame(&source, &wrong).is_err());
            refuted(
                &source,
                &machine,
                &wrong,
                [23, 7, 111, 5],
                "select-wrong-false-arm-operation",
            );
        }
    }
}

#[test]
fn materialized_boolean_select_consumes_actual_cset_and_boolean_zero_comparison() {
    for bits in [32, 64] {
        for carrier in [32, 64] {
            let (source, machine, ids) = fixture(
                bits,
                IntCC::SignedLessThan,
                11,
                IntCC::NotEqual,
                M::Csel,
                Route::Materialized(carrier),
            );
            for mutation in 0..3 {
                let mut wrong = machine.clone();
                let (input, label) = match mutation {
                    0 => {
                        wrong.insts[ids.bool_set.unwrap().0 as usize].operands[1] = O::Imm(10);
                        ([7, 23, 111, 222], "select-materialized-wrong-cset")
                    }
                    1 => {
                        wrong.insts[ids.bool_cmp.unwrap().0 as usize].operands[1] = O::Imm(1);
                        ([7, 23, 111, 222], "select-materialized-cmp-one-not-zero")
                    }
                    _ => {
                        wrong.insts[ids.bool_cmp.unwrap().0 as usize].operands[0] = r(14, carrier);
                        (
                            [23, 7, 111, 222],
                            "select-materialized-wrong-boolean-register",
                        )
                    }
                };
                assert!(source_bound_frame(&source, &wrong).is_err());
                refuted(&source, &machine, &wrong, input, label);
            }
        }
    }
}

#[test]
fn cmp_select_and_copy_width_mutations_preserve_full_abi_counterexamples() {
    let (source, machine, ids) = fixture(
        64,
        IntCC::UnsignedLessThan,
        3,
        IntCC::NotEqual,
        M::Csel,
        Route::Direct,
    );
    let mut wrong = machine.clone();
    wrong.insts[ids.cmp.0 as usize].operands = vec![r(9, 32), r(10, 32)];
    assert!(source_bound_frame(&source, &wrong).is_err());
    refuted(
        &source,
        &machine,
        &wrong,
        [(1 << 32) + 1, 2, 111, 222],
        "select-cmp-x-to-w-width",
    );
    let mut wrong = machine.clone();
    wrong.insts[ids.select.0 as usize].operands = vec![r(13, 32), r(11, 32), r(12, 32), O::Imm(3)];
    assert!(source_bound_frame(&source, &wrong).is_err());
    refuted(
        &source,
        &machine,
        &wrong,
        [1, 2, (1 << 32) + 111, 222],
        "select-x-to-w-width",
    );
    for id in [ids.inputs[2], ids.result] {
        let mut wrong = machine.clone();
        wrong.insts[id.0 as usize].opcode = M::MOVWrr;
        assert!(source_bound_frame(&source, &wrong).is_err());
        refuted(
            &source,
            &machine,
            &wrong,
            [1, 2, (1 << 32) + 111, 222],
            "select-live-copy-x-to-w-width",
        );
    }
    let (source, mut machine, ids) = fixture(
        32,
        IntCC::UnsignedLessThan,
        3,
        IntCC::NotEqual,
        M::Csel,
        Route::Direct,
    );
    // Incoming X0/X1 retain upper bits: comparing W0/W1 directly makes the
    // W->X mutation genuinely different, unlike already zeroed W9/W10 copies.
    machine.insts[ids.cmp.0 as usize].operands = vec![r(0, 32), r(1, 32)];
    let frame = source_bound_frame(&source, &machine).expect("direct incoming W compare");
    let body = SourceBoundBody::bind(&frame).unwrap();
    let input = [(1 << 32) + 1, 2, (1 << 63) + 111, (1 << 32) + 222];
    assert_eq!(
        evaluate(body.obligation(), input),
        (EvalResult::Bv(111), EvalResult::Bv(111))
    );
    let mut wrong = machine.clone();
    wrong.insts[ids.cmp.0 as usize].operands = vec![r(0, 64), r(1, 64)];
    assert!(source_bound_frame(&source, &wrong).is_err());
    let obligation = refuted(
        &source,
        &machine,
        &wrong,
        input,
        "select-incoming-cmp-w-to-x-width",
    );
    assert_eq!(
        evaluate(&obligation, input),
        (EvalResult::Bv(111), EvalResult::Bv(222))
    );
}

#[test]
fn select_aliases_read_both_arms_before_write_and_track_only_live_dependencies() {
    for bits in [32, 64] {
        for destination in [11, 12] {
            let (source, mut machine, ids) = fixture(
                bits,
                IntCC::SignedLessThan,
                11,
                IntCC::NotEqual,
                M::Csneg,
                Route::Materialized(32),
            );
            machine.insts[ids.select.0 as usize].operands[0] = r(destination, bits);
            machine.insts[ids.result.0 as usize].operands[1] = r(destination, bits);
            let dead_cmp = machine.push_inst(MachInst::new(M::CmpRR, vec![r(9, bits), r(9, bits)]));
            let dead_set = machine.push_inst(MachInst::new(M::CSet, vec![r(16, 32), O::Imm(11)]));
            insert_before(&mut machine, ids.cmp, &[dead_cmp, dead_set]);
            let late_cmp =
                machine.push_inst(MachInst::new(M::CmpRR, vec![r(10, bits), r(10, bits)]));
            let late_select = machine.push_inst(MachInst::new(
                M::Csel,
                vec![r(17, bits), r(9, bits), r(10, bits), O::Imm(0)],
            ));
            insert_before(&mut machine, ids.result, &[late_cmp, late_select]);
            let frame = source_bound_frame(&source, &machine)
                .expect("aliasing select and dead condition writes leave return intact");
            let body = SourceBoundBody::bind(&frame).expect("bounded raw aliasing select");
            let mut live = ids.inputs.into_iter().collect::<HashSet<_>>();
            live.extend([
                ids.cmp,
                ids.bool_set.unwrap(),
                ids.bool_cmp.unwrap(),
                ids.select,
                ids.result,
            ]);
            assert_eq!(raw(&source, &machine).1, live);
            for dead in [
                dead_cmp,
                dead_set,
                late_cmp,
                late_select,
                ids.stale_result,
                ids.dead_copy,
            ] {
                assert!(!body.credits(dead), "dead/overwritten dependency {dead:?}");
            }
            for input in [[7, 23, u64::MAX, 5], [23, 7, 111, 1 << 63]] {
                let want = EvalResult::Bv(expected(
                    bits,
                    IntCC::SignedLessThan,
                    IntCC::NotEqual,
                    M::Csneg,
                    input,
                ));
                assert_eq!(evaluate(body.obligation(), input), (want.clone(), want));
            }
        }
    }
}

#[test]
fn select_raw_model_fails_closed_on_malformed_or_unsupported_source_and_machine_forms() {
    let (source, machine, ids) = fixture(
        64,
        IntCC::SignedLessThan,
        11,
        IntCC::NotEqual,
        M::Csel,
        Route::Direct,
    );
    for mutation in 0..9 {
        let mut wrong = machine.clone();
        match mutation {
            0 => wrong.insts[ids.cmp.0 as usize] = MachInst::new(M::Nop, vec![]),
            1 => wrong.insts[ids.select.0 as usize].operands[1] = r(17, 64),
            2 => wrong.insts[ids.select.0 as usize].operands[2] = r(12, 32),
            3 => wrong.insts[ids.select.0 as usize].operands[3] = O::Imm(14),
            4 => wrong.insts[ids.select.0 as usize].operands[3] = O::Imm(-1),
            5 => wrong.insts[ids.select.0 as usize].operands[0] = O::Special(SpecialReg::SP),
            6 => {
                wrong.insts[ids.select.0 as usize].operands.pop();
            }
            7 => {
                let unknown_flags = wrong.push_inst(MachInst::new(
                    M::AddsRR,
                    vec![r(14, 64), r(9, 64), r(10, 64)],
                ));
                insert_before(&mut wrong, ids.select, &[unknown_flags]);
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
            "unsupported/malformed machine case {mutation}: refusal is not residual proof credit"
        );
    }
    for mutation in 0..7 {
        let mut wrong = source.clone();
        match mutation {
            0 => wrong.signature.params[0] = Type::B1,
            1 => wrong.signature.params[1] = Type::I32,
            2 => wrong.signature.returns = vec![Type::B1],
            3 => {
                wrong
                    .blocks
                    .get_mut(&wrong.entry_block)
                    .unwrap()
                    .instructions[1]
                    .opcode = L::Select {
                    cond: IntCC::SignedLessThan,
                }
            }
            4 => {
                wrong
                    .blocks
                    .get_mut(&wrong.entry_block)
                    .unwrap()
                    .instructions[1]
                    .args[0] = Value(0)
            }
            5 => {
                wrong
                    .blocks
                    .get_mut(&wrong.entry_block)
                    .unwrap()
                    .instructions[1]
                    .args[1] = Value(4)
            }
            _ => {
                wrong
                    .blocks
                    .get_mut(&wrong.entry_block)
                    .unwrap()
                    .instructions[1]
                    .args
                    .pop();
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
            "unsupported/malformed source case {mutation}"
        );
    }
}

#[test]
fn select_raw_tree_and_instruction_resource_budgets_decline_without_normalizing() {
    for bits in [32, 64] {
        let (mut source, mut machine, ids) = fixture(
            bits,
            IntCC::Equal,
            0,
            IntCC::NotEqual,
            M::Csel,
            Route::Direct,
        );
        let mut prefix = Vec::new();
        let mut value = 0;
        for result in 6..19 {
            prefix.push(inst(L::Iadd, &[value, value], Some(result)));
            source.value_types.insert(Value(result), ty(bits));
            value = result;
        }
        let block = source.blocks.get_mut(&source.entry_block).unwrap();
        block.instructions[0].args[0] = Value(value);
        block.instructions.splice(0..0, prefix);
        let shift = machine.push_inst(MachInst::new(
            M::LslRI,
            vec![r(9, bits), r(9, bits), O::Imm(13)],
        ));
        insert_before(&mut machine, ids.cmp, &[shift]);
        let frame = source_bound_frame(&source, &machine)
            .expect("compact affine select remains supported outside raw expansion budget");
        assert!(
            SourceBoundBody::bind(&frame).is_none(),
            "source raw tree must decline beyond budget, never substitute its compact affine form"
        );

        let (source, mut machine, ids) = fixture(
            bits,
            IntCC::Equal,
            0,
            IntCC::NotEqual,
            M::Csel,
            Route::Direct,
        );
        let mut dead_doubling = Vec::new();
        for _ in 0..13 {
            dead_doubling.push(machine.push_inst(MachInst::new(
                M::AddRR,
                vec![r(14, bits), r(14, bits), r(14, bits)],
            )));
        }
        insert_before(&mut machine, ids.cmp, &dead_doubling);
        let frame = source_bound_frame(&source, &machine)
            .expect("dead expanded machine tree leaves select return intact");
        assert!(
            SourceBoundBody::bind(&frame).is_none(),
            "machine raw budget must apply even to uncredited computations"
        );
    }
    let (mut source, machine, _) =
        fixture(64, IntCC::Equal, 0, IntCC::NotEqual, M::Csel, Route::Direct);
    let mut copies = Vec::new();
    for value in 6..263 {
        copies.push(inst(L::Copy, &[0], Some(value)));
        source.value_types.insert(Value(value), Type::I64);
    }
    source
        .blocks
        .get_mut(&source.entry_block)
        .unwrap()
        .instructions
        .splice(0..0, copies);
    assert!(
        raw_body(
            &source,
            &machine,
            machine.blocks[0].insts.clone(),
            [InstId(0), InstId(1), InstId(3)]
        )
        .is_none(),
        "bounded source instruction domain must fail closed"
    );
}

#[test]
fn select_aggregate_arm_budget_is_checked_before_combining_supported_raw_arms() {
    for bits in [32, 64] {
        let (mut source, mut machine, ids) = fixture(
            bits,
            IntCC::Equal,
            0,
            IntCC::NotEqual,
            M::Csel,
            Route::Direct,
        );
        let mut prefix = Vec::new();
        let mut next = 6;
        let mut arms = [2, 3];
        // Each raw arm remains below 4096 nodes (2556 at I64, 3068 at
        // I32), but their union plus the condition exceeds the limit. The
        // frame's affine arms remain small and exact.
        for arm in &mut arms {
            for _ in 0..9 {
                prefix.push(inst(L::Iadd, &[*arm, *arm], Some(next)));
                source.value_types.insert(Value(next), ty(bits));
                *arm = next;
                next += 1;
            }
        }
        let block = source.blocks.get_mut(&source.entry_block).unwrap();
        block.instructions[1].args[1] = Value(arms[0]);
        block.instructions[1].args[2] = Value(arms[1]);
        block.instructions.splice(1..1, prefix);
        let shifts = [11, 12].map(|arm| {
            machine.push_inst(MachInst::new(
                M::LslRI,
                vec![r(arm, bits), r(arm, bits), O::Imm(9)],
            ))
        });
        insert_before(&mut machine, ids.select, &shifts);
        let frame = source_bound_frame(&source, &machine)
            .expect("both compact affine arms are otherwise supported");
        assert!(
            SourceBoundBody::bind(&frame).is_none(),
            "aggregate select tree must decline, never normalize its arms"
        );
    }
}

#[test]
fn wrong_select_condition_requires_an_independent_admitted_ay_counterexample() {
    use crate::ay_bridge::{AYConfig, AYResult, verify_with_cli_raw_attributed};
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_NO_SOLVER_SERVER", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            for bits in [32, 64] {
                let (source, machine, ids) = fixture(
                    bits,
                    IntCC::SignedLessThan,
                    11,
                    IntCC::NotEqual,
                    M::Csel,
                    Route::Direct,
                );
                let mut wrong = machine.clone();
                wrong.insts[ids.select.0 as usize].operands[3] = O::Imm(10);
                let obligation = refuted(
                    &source,
                    &machine,
                    &wrong,
                    [7, 23, 111, 222],
                    "independent-select-condition",
                );
                let outcome = verify_with_cli_raw_attributed(&obligation, &AYConfig::default());
                assert!(
                    matches!(outcome.result, AYResult::CounterExample(_)),
                    "i{bits}: wrong raw select requires actual AY SAT counterexample, not structural refusal: {:?}",
                    outcome.result
                );
                println!(
                    "A64_RAW_SELECT_AY_COUNTEREXAMPLE bits={bits} result={} provenance={:?}",
                    outcome.result,
                    outcome.provenance()
                );
            }
        },
    );
}

#[test]
fn select_raw_obligations_require_positive_independent_ay_clean_replay() {
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
                for (condition, cc) in CONDITIONS {
                    let (source, machine, _) =
                        fixture(bits, condition, cc, IntCC::NotEqual, M::Csel, Route::Direct);
                    let frame =
                        source_bound_frame(&source, &machine).expect("matching select frame");
                    let body = SourceBoundBody::bind(&frame).expect("raw select owner");
                    println!(
                        "A64_RAW_SELECT_REPLAY_QUERY bits={bits} cond={condition:?} smt2={}",
                        serde_json::to_string(&crate::serialize_to_smt2(body.obligation()))
                            .unwrap()
                    );
                    let result = FunctionDischargeContext::new(&request).a64_body(&body);
                    assert!(
                        matches!(result, Some(VerificationResult::Valid)),
                        "required independent AY/Clean select replay i{bits}/{condition:?}: {result:?}; concrete evaluation is not substitute proof evidence"
                    );
                }
            }
        },
    );
}
