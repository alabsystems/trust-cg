// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Original four-block source and allocated control/dataflow, not the frame
//! normalizer's Select. Concrete controls and AY SAT refutations are distinct
//! from the strict positive AY/Clean gate, which must never skip a proof failure.

use super::{MAX_NODES, Registers, SourceBoundBody, SourceValue, Term, Word, raw_control_body};
use crate::lowering_proof::ProofObligation;
use crate::proof_database::ProofCategory;
use crate::smt::{EvalEnv, EvalResult, SmtExpr as E, SmtSort};
use crate::source_bound_frame::{RawControl, SourceBoundFrame, source_bound_frame};
use std::collections::{HashMap, HashSet};
use trust_cg_ir::function::{MachBlock, Signature as MachineSignature, Type as MachineType};
use trust_cg_ir::regs::{PReg, SpecialReg, X29, X30};
use trust_cg_ir::{AArch64Opcode as M, BlockId, InstId, MachFunction, MachInst, MachOperand as O};
use trust_cg_lower::Type;
use trust_cg_lower::function::{BasicBlock, Function, Signature};
use trust_cg_lower::instructions::{Block, Instruction, IntCC, Opcode as L, Value};

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
const ARMS: [(u64, u64); 8] = [
    (0, 0),
    (1, 7),
    (u64::MAX, 1),
    (i32::MAX as u64, 1),
    ((1 << 32) + 111, (1 << 32) + 222),
    (1 << 63, u64::MAX),
    (u64::MAX, u64::MAX),
    (111, 222),
];

#[derive(Clone, Copy, Debug)]
enum Route {
    Direct,
    Materialized { carrier: u32, zero: bool },
}
const ROUTES: [Route; 5] = [
    Route::Direct,
    Route::Materialized {
        carrier: 32,
        zero: false,
    },
    Route::Materialized {
        carrier: 64,
        zero: false,
    },
    Route::Materialized {
        carrier: 32,
        zero: true,
    },
    Route::Materialized {
        carrier: 64,
        zero: true,
    },
];

#[derive(Clone, Copy)]
struct Ids {
    inputs: [InstId; 4],
    stale: InstId,
    dead: InstId,
    cmp: InstId,
    cset: Option<InstId>,
    branch: InstId,
    arm_copies: [InstId; 2],
    arm_results: [InstId; 2],
    result: InstId,
    restore: InstId,
    ret: InstId,
}

fn r(index: u16, bits: u32) -> O {
    O::PReg(PReg::new(index + if bits == 32 { 32 } else { 0 }))
}
fn ty(bits: u32) -> Type {
    if bits == 32 { Type::I32 } else { Type::I64 }
}
fn copy(bits: u32) -> M {
    if bits == 32 { M::MOVWrr } else { M::MOVXrr }
}
fn lir(opcode: L, args: &[u32], output: Option<u32>) -> Instruction {
    Instruction {
        opcode,
        args: args.iter().copied().map(Value).collect(),
        results: output.into_iter().map(Value).collect(),
    }
}
fn push(machine: &mut MachFunction, opcode: M, operands: Vec<O>) -> InstId {
    machine.push_inst(MachInst::new(opcode, operands))
}

/// if a cmp b { copy(c+d)-7 } else { copy(d-c)+11 }. Both arms define
/// their own merge value; the original CFG is never replaced by a Select.
fn fixture(bits: u32, condition: IntCC, cc: i64, route: Route) -> (Function, MachFunction, Ids) {
    let integer = ty(bits);
    let mut source = Function::new(
        "raw_control_diamond",
        Signature {
            params: vec![integer.clone(); 4],
            returns: vec![integer.clone()],
        },
    );
    let entry = BasicBlock {
        params: (0..4).map(|n| (Value(n), integer.clone())).collect(),
        instructions: vec![
            lir(L::Icmp { cond: condition }, &[0, 1], Some(4)),
            lir(
                L::Brif {
                    cond: Value(4),
                    then_dest: Block(1),
                    else_dest: Block(2),
                },
                &[4],
                None,
            ),
        ],
        ..Default::default()
    };
    let arm = |mut instructions: Vec<Instruction>| {
        instructions.push(lir(L::Jump { dest: Block(3) }, &[], None));
        BasicBlock {
            instructions,
            ..Default::default()
        }
    };
    source.blocks.insert(Block(0), entry);
    source.blocks.insert(
        Block(1),
        arm(vec![
            lir(
                L::Iconst {
                    ty: integer.clone(),
                    imm: 7,
                },
                &[],
                Some(5),
            ),
            lir(L::Iadd, &[2, 3], Some(6)),
            lir(L::Copy, &[6], Some(7)),
            lir(L::Isub, &[7, 5], Some(12)),
        ]),
    );
    source.blocks.insert(
        Block(2),
        arm(vec![
            lir(
                L::Iconst {
                    ty: integer.clone(),
                    imm: 11,
                },
                &[],
                Some(8),
            ),
            lir(L::Isub, &[3, 2], Some(9)),
            lir(L::Copy, &[9], Some(10)),
            lir(L::Iadd, &[10, 8], Some(12)),
        ]),
    );
    source.blocks.insert(
        Block(3),
        BasicBlock {
            params: vec![(Value(12), integer.clone())],
            instructions: vec![lir(L::Return, &[12], None)],
            ..Default::default()
        },
    );
    source.block_order = (0..4).map(Block).collect();
    for n in (0..=10).chain([12]) {
        source
            .value_types
            .insert(Value(n), if n == 4 { Type::B1 } else { integer.clone() });
    }

    let machine_type = if bits == 32 {
        MachineType::I32
    } else {
        MachineType::I64
    };
    let mut machine = MachFunction::new(
        source.name.clone(),
        MachineSignature::new(vec![machine_type.clone(); 4], vec![machine_type]),
    );
    let frame = |offset| {
        vec![
            O::PReg(X29),
            O::PReg(X30),
            O::Special(SpecialReg::SP),
            O::Imm(offset),
        ]
    };
    let mut prefix = vec![
        push(&mut machine, M::StpPreIndex, frame(-16)),
        push(
            &mut machine,
            M::AddRI,
            vec![O::PReg(X29), O::Special(SpecialReg::SP), O::Imm(0)],
        ),
    ];
    let inputs = std::array::from_fn(|n| {
        push(
            &mut machine,
            copy(bits),
            vec![r(n as u16 + 9, bits), r(n as u16, bits)],
        )
    });
    prefix.extend(inputs);
    let stale = push(&mut machine, copy(bits), vec![r(13, bits), r(10, bits)]);
    let cmp = push(&mut machine, M::CmpRR, vec![r(9, bits), r(10, bits)]);
    // This dead copy lies after CMP: replacing it with another CMP must
    // replace reaching NZCV, not silently reuse the source comparison.
    let dead = push(&mut machine, copy(bits), vec![r(14, bits), r(9, bits)]);
    prefix.extend([stale, cmp, dead]);
    let (cset, opcode, operand, taken, other) = match route {
        Route::Direct => (None, M::BCond, O::Imm(cc), 1, 2),
        Route::Materialized { carrier, zero } => {
            let id = push(&mut machine, M::CSet, vec![r(15, carrier), O::Imm(cc)]);
            prefix.push(id);
            (
                Some(id),
                if zero { M::Cbz } else { M::Cbnz },
                r(15, carrier),
                if zero { 2 } else { 1 },
                if zero { 1 } else { 2 },
            )
        }
    };
    let branch = push(
        &mut machine,
        opcode,
        vec![operand, O::Block(BlockId(taken))],
    );
    prefix.extend([
        branch,
        push(&mut machine, M::B, vec![O::Block(BlockId(other))]),
    ]);
    let mut arm_copies = [InstId(0); 2];
    let mut arm_results = [InstId(0); 2];
    let mut paths = Vec::new();
    for which in 0..2 {
        let arithmetic = push(
            &mut machine,
            if which == 0 { M::AddRR } else { M::SubRR },
            if which == 0 {
                vec![r(16, bits), r(11, bits), r(12, bits)]
            } else {
                vec![r(16, bits), r(12, bits), r(11, bits)]
            },
        );
        arm_copies[which] = push(&mut machine, copy(bits), vec![r(17, bits), r(16, bits)]);
        arm_results[which] = push(
            &mut machine,
            if which == 0 { M::SubRI } else { M::AddRI },
            vec![
                r(13, bits),
                r(17, bits),
                O::Imm(if which == 0 { 7 } else { 11 }),
            ],
        );
        paths.push(vec![
            arithmetic,
            arm_copies[which],
            arm_results[which],
            push(&mut machine, M::B, vec![O::Block(BlockId(3))]),
        ]);
    }
    let result = push(&mut machine, copy(bits), vec![r(0, bits), r(13, bits)]);
    let restore = push(&mut machine, M::LdpPostIndex, frame(16));
    let ret = push(&mut machine, M::Ret, vec![O::PReg(X30)]);
    let block = |insts, preds: &[u32], succs: &[u32]| MachBlock {
        insts,
        preds: preds.iter().copied().map(BlockId).collect(),
        succs: succs.iter().copied().map(BlockId).collect(),
        loop_depth: 0,
    };
    machine.blocks = vec![
        block(prefix, &[], &[1, 2]),
        block(paths.remove(0), &[0], &[3]),
        block(paths.remove(0), &[0], &[3]),
        block(vec![result, restore, ret], &[1, 2], &[]),
    ];
    machine.block_order = (0..4).map(BlockId).collect();
    (
        source,
        machine,
        Ids {
            inputs,
            stale,
            dead,
            cmp,
            cset,
            branch,
            arm_copies,
            arm_results,
            result,
            restore,
            ret,
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
fn arm_value(bits: u32, take_then: bool, c: u64, d: u64) -> u64 {
    let (c, d) = (low(c, bits), low(d, bits));
    low(
        if take_then {
            c.wrapping_add(d).wrapping_sub(7)
        } else {
            d.wrapping_sub(c).wrapping_add(11)
        },
        bits,
    )
}
fn env(input: [u64; 4]) -> EvalEnv {
    let mut env = EvalEnv::default();
    for (i, value) in input.into_iter().enumerate() {
        env.insert(format!("abi_x{i}"), value);
    }
    env
}
fn evaluate(obligation: &ProofObligation, input: [u64; 4]) -> (EvalResult, EvalResult) {
    let env = env(input);
    (
        obligation.trust_ir_expr.eval(&env),
        obligation.aarch64_expr.eval(&env),
    )
}
fn registers() -> Registers {
    let mut registers = Registers(std::array::from_fn(|_| None));
    for (i, register) in registers.0[..4].iter_mut().enumerate() {
        *register = Some(Word {
            term: Term::leaf(E::var(format!("abi_x{i}"), 64)),
            slice: HashSet::new(),
        });
    }
    registers
}

/// Each actual path also leaves the complete X0 ABI word correct. For i32
/// this checks the upper half is zero, not merely equality of low result bits.
fn full_abi_paths(frame: &SourceBoundFrame<'_>, bits: u32, route: Route, input: [u64; 4]) {
    let RawControl::Diamond { prefix, paths, .. } = frame.raw_control().unwrap() else {
        panic!("not a diamond")
    };
    let mut registers = registers();
    let mut flags = None;
    let mut credited = HashSet::new();
    assert!(
        !super::machine_run(
            frame.machine(),
            &prefix,
            frame.envelope_instructions(),
            &mut registers,
            &mut flags,
            &mut credited
        )
        .unwrap()
    );
    let true_first = !matches!(route, Route::Materialized { zero: true, .. });
    for (index, path) in paths.into_iter().enumerate() {
        let mut branch_registers = registers.clone();
        let mut branch_flags = flags.clone();
        assert!(
            super::machine_run(
                frame.machine(),
                &path,
                frame.envelope_instructions(),
                &mut branch_registers,
                &mut branch_flags,
                &mut credited
            )
            .unwrap()
        );
        let returned = branch_registers.read(&r(0, 64), 64, false).unwrap();
        assert_eq!(
            returned.term.expr.eval(&env(input)),
            EvalResult::Bv(arm_value(
                bits,
                (index == 0) == true_first,
                input[2],
                input[3]
            ))
        );
    }
}

/// The control comes from the ORIGINAL checked frame. Thus a supported wrong
/// instruction must produce a raw residual, not pass through frame rejection.
fn refuted(
    source: &Function,
    correct: &MachFunction,
    wrong: &MachFunction,
    input: [u64; 4],
    label: &str,
) -> ProofObligation {
    let frame = source_bound_frame(source, correct).expect("original valid frame");
    let correct = SourceBoundBody::bind(&frame).expect("original raw owner");
    let (wrong, _) = raw_control_body(
        source,
        wrong,
        frame.raw_control().unwrap(),
        frame.envelope_instructions(),
    )
    .unwrap_or_else(|| panic!("{label}: supported mutation must reach raw model"));
    assert_ne!(
        crate::serialize_to_smt2(correct.obligation()),
        crate::serialize_to_smt2(&wrong),
        "{label}: actual raw query changed"
    );
    let (source_value, machine_value) = evaluate(&wrong, input);
    assert_eq!(
        source_value,
        evaluate(correct.obligation(), input).0,
        "{label}: machine cannot rewrite source"
    );
    assert_ne!(
        source_value, machine_value,
        "{label}/{input:?}: raw counterexample required"
    );
    println!(
        "A64_RAW_DIAMOND_COUNTEREXAMPLE mutation={label} input={input:?} source={source_value:?} machine={machine_value:?}"
    );
    wrong
}

#[test]
fn original_diamond_all_comparisons_and_actual_branch_routes_agree_on_full_abi_edges() {
    let mut cases = 0;
    for bits in [32, 64] {
        for (condition, cc) in CONDITIONS {
            for route in ROUTES {
                let (source, machine, ids) = fixture(bits, condition, cc, route);
                let frame = source_bound_frame(&source, &machine)
                    .expect("original arithmetic diamond frame");
                let body = SourceBoundBody::bind(&frame).expect("raw original diamond");
                assert_eq!(source.blocks.len(), 4);
                assert_eq!(body.category(), ProofCategory::Arithmetic);
                assert_eq!(
                    body.obligation().inputs,
                    (0..4)
                        .map(|i| (format!("abi_x{i}"), 64))
                        .collect::<Vec<_>>()
                );
                assert!(body.obligation().preconditions.is_empty());
                assert!(!body.obligation().is_degenerate());
                assert_eq!(
                    body.obligation().trust_ir_expr.sort(),
                    SmtSort::BitVec(bits)
                );
                assert_eq!(body.obligation().aarch64_expr.sort(), SmtSort::BitVec(bits));
                let mut live = ids.inputs.into_iter().collect::<HashSet<_>>();
                live.extend([
                    ids.cmp,
                    ids.branch,
                    ids.arm_copies[0],
                    ids.arm_copies[1],
                    ids.result,
                ]);
                live.extend(ids.cset);
                let (_, credited) = raw_control_body(
                    &source,
                    &machine,
                    frame.raw_control().unwrap(),
                    frame.envelope_instructions(),
                )
                .unwrap();
                assert_eq!(credited, live, "only exact live control/copy dependencies");
                for dead in [
                    ids.stale,
                    ids.dead,
                    ids.arm_results[0],
                    ids.arm_results[1],
                    ids.restore,
                    ids.ret,
                    InstId(0),
                    InstId(1),
                ] {
                    assert!(!body.credits(dead), "uncredited row {dead:?}");
                }
                for a in INPUTS {
                    for b in INPUTS {
                        for (c, d) in ARMS {
                            let input = [a, b, c, d];
                            let want = EvalResult::Bv(arm_value(
                                bits,
                                predicate(condition, bits, a, b),
                                c,
                                d,
                            ));
                            assert_eq!(
                                evaluate(body.obligation(), input),
                                (want.clone(), want),
                                "i{bits}/{condition:?}/{route:?}/{input:?}"
                            );
                        }
                    }
                }
                for (c, d) in ARMS {
                    full_abi_paths(&frame, bits, route, [7, 23, c, d]);
                }
                let query = crate::serialize_to_smt2(body.obligation());
                assert!(
                    query.contains("zero_extend 1"),
                    "original wrapping arms were normalized away"
                );
                if bits == 32 {
                    assert!(
                        query.contains("zero_extend 32"),
                        "W writes must clear upper ABI bits"
                    );
                }
                cases += 1;
            }
        }
    }
    assert_eq!(cases, 100);
}

#[test]
fn raw_diamond_refutes_condition_operands_stale_flags_arm_and_merge_return_mutations() {
    for bits in [32, 64] {
        let (source, machine, ids) = fixture(bits, IntCC::SignedLessThan, 11, Route::Direct);
        for mutation in 0..10 {
            let mut wrong = machine.clone();
            let mut input = [7, 23, 111, 222];
            let label = match mutation {
                0 => {
                    wrong.insts[ids.branch.0 as usize].operands[0] = O::Imm(10);
                    "branch-condition"
                }
                1 => {
                    wrong.insts[ids.cmp.0 as usize].operands.swap(0, 1);
                    "cmp-operands"
                }
                2 => {
                    wrong.insts[ids.cmp.0 as usize].operands[0] = r(10, bits);
                    "cmp-lhs"
                }
                3 => {
                    wrong.insts[ids.arm_results[0].0 as usize].opcode = M::AddRI;
                    "then-arm-operation"
                }
                4 => {
                    input = [23, 7, 111, 222];
                    wrong.insts[ids.arm_results[1].0 as usize].opcode = M::SubRI;
                    "else-arm-operation"
                }
                5 => {
                    wrong.insts[ids.arm_results[0].0 as usize].operands[0] = r(14, bits);
                    "then-merge-destination"
                }
                6 => {
                    wrong.insts[ids.result.0 as usize].operands[1] = r(12, bits);
                    "return-input-route"
                }
                7 => {
                    wrong.insts[ids.result.0 as usize].operands[1] = r(16, bits);
                    "return-pre-arm-route"
                }
                8 => {
                    wrong.insts[ids.dead.0 as usize] =
                        MachInst::new(M::CmpRR, vec![r(10, bits), r(9, bits)]);
                    "reaching-overwritten-nzcv"
                }
                _ => {
                    wrong.insts[ids.inputs[2].0 as usize].operands[1] = r(3, bits);
                    "live-arm-input-copy"
                }
            };
            assert!(
                source_bound_frame(&source, &wrong).is_err(),
                "frame also refuses {label}"
            );
            refuted(&source, &machine, &wrong, input, label);
        }
        let mut wrong = machine.clone();
        let width = if bits == 64 { 32 } else { 64 };
        wrong.insts[ids.cmp.0 as usize].operands = vec![r(9, width), r(10, width)];
        let input = if bits == 64 {
            [(1 << 32) + 1, 2, 111, 222]
        } else {
            [(1 << 31) + 1, 2, 111, 222]
        };
        refuted(&source, &machine, &wrong, input, "comparison-width");
        if bits == 64 {
            wrong = machine.clone();
            wrong.insts[ids.result.0 as usize].opcode = M::MOVWrr;
            refuted(
                &source,
                &machine,
                &wrong,
                [7, 23, (1 << 32) + 111, 222],
                "return-copy-width",
            );
        }
        let mut swapped = source.clone();
        swapped.blocks.get_mut(&Block(0)).unwrap().instructions[1].opcode = L::Brif {
            cond: Value(4),
            then_dest: Block(2),
            else_dest: Block(1),
        };
        let frame = source_bound_frame(&source, &machine).unwrap();
        let good = SourceBoundBody::bind(&frame).unwrap();
        let (wrong, _) = raw_control_body(
            &swapped,
            &machine,
            frame.raw_control().unwrap(),
            frame.envelope_instructions(),
        )
        .expect("supported original source arm swap");
        assert_ne!(
            crate::serialize_to_smt2(good.obligation()),
            crate::serialize_to_smt2(&wrong)
        );
        assert_eq!(
            evaluate(&wrong, [7, 23, 111, 222]).1,
            evaluate(good.obligation(), [7, 23, 111, 222]).1
        );
        assert_ne!(
            evaluate(&wrong, [7, 23, 111, 222]).0,
            evaluate(&wrong, [7, 23, 111, 222]).1,
            "source arm choice must come from original CFG"
        );
    }
}

#[test]
fn raw_materialized_diamond_observes_cset_cbz_cbnz_and_exact_boolean_register() {
    for bits in [32, 64] {
        for route in ROUTES.into_iter().skip(1) {
            let (source, machine, ids) = fixture(bits, IntCC::SignedLessThan, 11, route);
            let Route::Materialized { carrier, .. } = route else {
                unreachable!()
            };
            for mutation in 0..3 {
                let mut wrong = machine.clone();
                let label = match mutation {
                    0 => {
                        wrong.insts[ids.cset.unwrap().0 as usize].operands[1] = O::Imm(10);
                        "materialized-cset-condition"
                    }
                    1 => {
                        let branch = &mut wrong.insts[ids.branch.0 as usize];
                        branch.opcode = if branch.opcode == M::Cbz {
                            M::Cbnz
                        } else {
                            M::Cbz
                        };
                        "cbz-cbnz-polarity"
                    }
                    _ => {
                        wrong.insts[ids.branch.0 as usize].operands[0] = r(14, carrier);
                        "branch-boolean-register"
                    }
                };
                refuted(&source, &machine, &wrong, [23, 7, 111, 222], label);
            }
        }
    }
}

#[test]
fn raw_diamond_declines_missing_flags_bad_source_merge_and_missing_return() {
    let (source, machine, ids) = fixture(64, IntCC::SignedLessThan, 11, Route::Direct);
    let frame = source_bound_frame(&source, &machine).unwrap();
    for mutation in 0..4 {
        let mut wrong = machine.clone();
        match mutation {
            0 => wrong.insts[ids.cmp.0 as usize] = MachInst::new(M::Nop, vec![]),
            1 => {
                wrong.insts[ids.dead.0 as usize] =
                    MachInst::new(M::AddsRR, vec![r(14, 64), r(9, 64), r(10, 64)])
            }
            2 => wrong.insts[ids.branch.0 as usize].operands[0] = O::Imm(14),
            _ => wrong.insts[ids.ret.0 as usize] = MachInst::new(M::Nop, vec![]),
        }
        assert!(
            raw_control_body(
                &source,
                &wrong,
                frame.raw_control().unwrap(),
                frame.envelope_instructions()
            )
            .is_none(),
            "unsupported machine control {mutation}"
        );
    }
    for mutation in 0..3 {
        let mut wrong = source.clone();
        match mutation {
            0 => wrong.blocks.get_mut(&Block(3)).unwrap().instructions[0].args = vec![Value(7)],
            1 => wrong.blocks.get_mut(&Block(3)).unwrap().params = vec![(Value(7), Type::I64)],
            _ => wrong.blocks.get_mut(&Block(0)).unwrap().instructions[1].args = vec![Value(0)],
        }
        assert!(
            raw_control_body(
                &wrong,
                &machine,
                frame.raw_control().unwrap(),
                frame.envelope_instructions()
            )
            .is_none(),
            "malformed original merge/condition {mutation}"
        );
    }
}

#[test]
fn aggregate_source_and_machine_state_budgets_decline_before_diamond_forks() {
    for bits in [32, 64] {
        let (mut source, machine, _) = fixture(bits, IntCC::SignedLessThan, 11, Route::Direct);
        let mut prefix = Vec::new();
        let mut input = 0;
        for output in 20..28 {
            prefix.push(lir(L::Iadd, &[input, input], Some(output)));
            source.value_types.insert(Value(output), ty(bits));
            input = output;
        }
        source
            .blocks
            .get_mut(&Block(0))
            .unwrap()
            .instructions
            .splice(1..1, prefix);
        let mut values = HashMap::new();
        for n in 0..4 {
            let input = Term::leaf(E::var(format!("abi_x{n}"), 64));
            values.insert(
                Value(n),
                SourceValue {
                    term: if bits == 32 {
                        input.unary(1, |e| e.extract(31, 0)).unwrap()
                    } else {
                        input
                    },
                    boolean: false,
                },
            );
        }
        let entry = &source.blocks[&Block(0)].instructions;
        assert!(
            super::source_run(
                &entry[..entry.len() - 1],
                &ty(bits),
                bits,
                false,
                &mut values
            )
            .unwrap()
            .is_none()
        );
        assert!(values.values().all(|v| v.term.nodes <= MAX_NODES));
        assert!(values.values().map(|v| v.term.nodes).sum::<usize>() * 2 > MAX_NODES);
        let frame = source_bound_frame(&source, &machine)
            .expect("dead source arithmetic stays affine-supported");
        assert!(
            SourceBoundBody::bind(&frame).is_none(),
            "aggregate source state, not individual operation, must refuse the fork"
        );

        let (source, mut machine, ids) = fixture(bits, IntCC::SignedLessThan, 11, Route::Direct);
        let mut doubling = Vec::new();
        for _ in 0..if bits == 32 { 8 } else { 10 } {
            doubling.push(push(
                &mut machine,
                M::AddRR,
                vec![r(14, bits), r(14, bits), r(14, bits)],
            ));
        }
        let at = machine.blocks[0]
            .insts
            .iter()
            .position(|&id| id == ids.branch)
            .unwrap();
        machine.blocks[0].insts.splice(at..at, doubling);
        let frame = source_bound_frame(&source, &machine)
            .expect("dead machine arithmetic stays affine-supported");
        let RawControl::Diamond { prefix, .. } = frame.raw_control().unwrap() else {
            panic!("not a diamond")
        };
        let mut registers = registers();
        let mut flags = None;
        let mut credited = HashSet::new();
        assert!(
            !super::machine_run(
                &machine,
                &prefix,
                frame.envelope_instructions(),
                &mut registers,
                &mut flags,
                &mut credited
            )
            .unwrap()
        );
        assert!(
            registers
                .0
                .iter()
                .flatten()
                .all(|w| w.term.nodes <= MAX_NODES)
        );
        let nodes = registers
            .0
            .iter()
            .flatten()
            .map(|w| w.term.nodes)
            .sum::<usize>()
            + flags.as_ref().unwrap().nodes;
        assert!(nodes * 2 > MAX_NODES);
        assert!(
            SourceBoundBody::bind(&frame).is_none(),
            "aggregate machine state must refuse before either raw path clone"
        );
    }
}

#[test]
fn wrong_raw_diamond_condition_has_an_actual_ay_sat_counterexample() {
    use crate::ay_bridge::{AYConfig, AYResult, verify_with_cli_raw_attributed};
    crate::env_lock::with_env_overrides(
        &[
            ("TCG_NO_PROOF_CACHE", "1"),
            ("TCG_NO_SOLVER_SERVER", "1"),
            ("TCG_BLOCKING_IDENTITY", "1"),
        ],
        || {
            for bits in [32, 64] {
                let (source, machine, ids) =
                    fixture(bits, IntCC::SignedLessThan, 11, Route::Direct);
                let mut wrong = machine.clone();
                wrong.insts[ids.branch.0 as usize].operands[0] = O::Imm(10);
                let obligation = refuted(
                    &source,
                    &machine,
                    &wrong,
                    [7, 23, 111, 222],
                    "independent-ay-branch-condition",
                );
                let outcome = verify_with_cli_raw_attributed(&obligation, &AYConfig::default());
                assert!(
                    matches!(outcome.result, AYResult::CounterExample(_)),
                    "i{bits}: actual AY SAT counterexample required: {:?}",
                    outcome.result
                );
                println!(
                    "A64_RAW_DIAMOND_AY_COUNTEREXAMPLE bits={bits} result={} provenance={:?}",
                    outcome.result,
                    outcome.provenance()
                );
            }
        },
    );
}

#[test]
fn diamond_raw_obligations_require_positive_independent_ay_clean_replay() {
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
                    for route in ROUTES {
                        let (source, machine, _) = fixture(bits, condition, cc, route);
                        let frame = source_bound_frame(&source, &machine)
                            .expect("matching original diamond frame");
                        let body =
                            SourceBoundBody::bind(&frame).expect("original diamond raw owner");
                        println!(
                            "A64_RAW_DIAMOND_REPLAY_QUERY bits={bits} cond={condition:?} route={route:?} smt2={}",
                            serde_json::to_string(&crate::serialize_to_smt2(body.obligation()))
                                .unwrap()
                        );
                        let result = FunctionDischargeContext::new(&request).a64_body(&body);
                        assert!(
                            matches!(result, Some(VerificationResult::Valid)),
                            "required independent AY/Clean diamond replay i{bits}/{condition:?}/{route:?}: {result:?}; no unavailable-proof skip and concrete agreement is not proof evidence"
                        );
                    }
                }
            }
        },
    );
}

#[path = "source_bound_body_scalar_arm_tests.rs"]
mod scalar_arm_tests;
