// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression matrix for the SSA-071 positional anti-swap boundary.
//!
//! A computed value may legitimately update one loop slot from another slot's
//! invariant value. Identity-preserving cross-slot routing is still a misthread,
//! and a computed cross-slot value is still a misthread when its source slot also
//! changes on the same back-edge. These fixtures keep those three cases distinct.

use trust_cg_verify::ssa_loop_complete::{SsaViolation, check_function};
use trust_ir::{
    BinOp, Block, BlockId, Constant, FuncId, FuncTyId, Function, ICmpOp, Inst, InstrNode, Ty,
    ValueId,
};

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn push_add(block: &mut Block, result: u32, lhs: ValueId, rhs: ValueId) -> ValueId {
    let result = v(result);
    block.body.push(
        InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs,
            rhs,
        })
        .with_result(result),
    );
    result
}

fn push_copy(block: &mut Block, result: u32, operand: ValueId) -> ValueId {
    let result = v(result);
    block.body.push(
        InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand,
        })
        .with_result(result),
    );
    result
}

/// Build a three-slot natural loop. Slots 0 and 1 are the values under test;
/// slot 2 is an ordinary counter that guarantees a changing back-edge.
fn loop_with_back_args(
    build_values: impl FnOnce(&mut Block, ValueId) -> (ValueId, ValueId),
) -> Function {
    let mut function = Function::new(FuncId::new(0), "anti_swap", FuncTyId::new(0), b(0));

    let mut entry = Block::new(b(0));
    for (result, value) in [(0, 0), (1, 7), (2, 0)] {
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(value),
            })
            .with_result(v(result)),
        );
    }
    entry.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(0), v(1), v(2)],
    }));

    let mut header = Block::new(b(1))
        .with_param(v(10), Ty::I32)
        .with_param(v(11), Ty::I32)
        .with_param(v(12), Ty::I32);
    header.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(4),
        })
        .with_result(v(13)),
    );
    header.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            ty: Ty::I32,
            lhs: v(12),
            rhs: v(13),
        })
        .with_result(v(14)),
    );
    header.body.push(InstrNode::new(Inst::CondBr {
        cond: v(14),
        then_target: b(2),
        then_args: vec![],
        else_target: b(3),
        else_args: vec![],
    }));

    let mut latch = Block::new(b(2));
    latch.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(20)),
    );
    let (slot_0_arg, slot_1_arg) = build_values(&mut latch, v(20));
    let next_counter = push_add(&mut latch, 29, v(12), v(20));
    latch.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![slot_0_arg, slot_1_arg, next_counter],
    }));

    let mut exit = Block::new(b(3));
    exit.body.push(InstrNode::new(Inst::Return {
        values: vec![v(10), v(11)],
    }));

    function.blocks = vec![entry, header, latch, exit];
    function
}

fn assert_slot_misthreaded(function: &Function, slot: usize, arg: ValueId) {
    let violations = check_function(function).expect_err("cross-slot route must fail closed");
    assert!(
        violations.iter().any(|violation| matches!(
            violation,
            SsaViolation::LoopCarriedSlotMisthreaded {
                header,
                latch,
                slot: actual_slot,
                arg: actual_arg,
                ..
            } if *header == b(1)
                && *latch == b(2)
                && *actual_slot == slot
                && *actual_arg == arg
        )),
        "expected slot {slot} / arg {arg:?} misthread, got {violations:?}"
    );
}

#[test]
fn accepts_computed_update_from_unchanged_other_phi() {
    let function = loop_with_back_args(|latch, one| {
        // Slot 0's fresh update reads slot 1, while slot 1 is invariant.
        let slot_0_next = push_add(latch, 21, v(11), one);
        (slot_0_next, v(11))
    });
    assert!(
        check_function(&function).is_ok(),
        "a computed update from an invariant other phi is not an identity misroute: {:?}",
        check_function(&function)
    );
}

#[test]
fn rejects_verbatim_cross_slot_value_even_when_source_is_unchanged() {
    let function = loop_with_back_args(|_latch, _one| (v(11), v(11)));
    assert_slot_misthreaded(&function, 0, v(11));
}

#[test]
fn rejects_copy_chain_cross_slot_value_even_when_source_is_unchanged() {
    let function = loop_with_back_args(|latch, _one| {
        let first_copy = push_copy(latch, 21, v(11));
        let second_copy = push_copy(latch, 22, first_copy);
        (second_copy, v(11))
    });
    assert_slot_misthreaded(&function, 0, v(22));
}

#[test]
fn rejects_computed_cross_slot_value_when_source_slot_changes() {
    let function = loop_with_back_args(|latch, one| {
        let slot_1_next = push_add(latch, 21, v(11), one);
        let crossed_computation = push_add(latch, 22, v(11), one);
        (crossed_computation, slot_1_next)
    });
    assert_slot_misthreaded(&function, 0, v(22));
}

#[test]
fn classic_computed_swap_stays_rejected() {
    let function = loop_with_back_args(|latch, one| {
        let slot_0_next = push_add(latch, 21, v(10), one);
        let slot_1_next = push_add(latch, 22, v(11), one);
        (slot_1_next, slot_0_next)
    });
    assert_slot_misthreaded(&function, 0, v(22));
    assert_slot_misthreaded(&function, 1, v(21));
}

#[test]
fn own_slot_computed_updates_stay_accepted() {
    let function = loop_with_back_args(|latch, one| {
        let slot_0_next = push_add(latch, 21, v(10), one);
        let slot_1_next = push_add(latch, 22, v(11), one);
        (slot_0_next, slot_1_next)
    });
    assert!(check_function(&function).is_ok());
}

#[test]
fn stale_unchanged_slot_with_dead_update_stays_rejected() {
    let function = loop_with_back_args(|latch, one| {
        let _dead_slot_0_update = push_add(latch, 21, v(10), one);
        (v(10), v(11))
    });
    let violations = check_function(&function).expect_err("stale dead update must fail closed");
    assert!(
        violations.iter().any(|violation| matches!(
            violation,
            SsaViolation::LoopCarriedValueNotThreaded {
                value,
                def_block,
                header,
                latch,
            } if *value == v(21)
                && *def_block == b(2)
                && *header == b(1)
                && *latch == b(2)
        )),
        "expected dead slot-0 update to be rejected, got {violations:?}"
    );
}

/// The `overflowing_pow` shape: an in-loop `if` joins slot 0's possibly-updated
/// value into a join-block param `q`, and the latch threads `q | t`, where `t`
/// is computed from slot 1 (which also changes). `q | t` is slot 0's own next
/// value; `q` merges only slot-0 values.
fn loop_with_join(
    join_slot_0: impl FnOnce(&mut Block, ValueId) -> ValueId,
    latch_slot_0: impl FnOnce(&mut Block, ValueId, ValueId) -> ValueId,
) -> Function {
    loop_with_join_routed(join_slot_0, latch_slot_0, |s0, s1, counter| {
        vec![s0, s1, counter]
    })
}

/// [`loop_with_join`] with the back-edge argument list chosen by `back` from
/// (slot 0's next value, slot 1's next value, the counter's next value).
fn loop_with_join_routed(
    join_slot_0: impl FnOnce(&mut Block, ValueId) -> ValueId,
    latch_slot_0: impl FnOnce(&mut Block, ValueId, ValueId) -> ValueId,
    back: impl FnOnce(ValueId, ValueId, ValueId) -> Vec<ValueId>,
) -> Function {
    let mut function = Function::new(FuncId::new(0), "join_slot", FuncTyId::new(0), b(0));

    let mut entry = Block::new(b(0));
    for (result, value) in [(0, 0), (1, 7), (2, 0)] {
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(value),
            })
            .with_result(v(result)),
        );
    }
    entry.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: vec![v(0), v(1), v(2)],
    }));

    // Header: `if counter < 4 { then } else { exit }`.
    let mut header = Block::new(b(1))
        .with_param(v(10), Ty::I32)
        .with_param(v(11), Ty::I32)
        .with_param(v(12), Ty::I32);
    header.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(4),
        })
        .with_result(v(13)),
    );
    header.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Slt,
            ty: Ty::I32,
            lhs: v(12),
            rhs: v(13),
        })
        .with_result(v(14)),
    );
    header.body.push(InstrNode::new(Inst::CondBr {
        cond: v(14),
        then_target: b(2),
        then_args: vec![],
        else_target: b(5),
        else_args: vec![],
    }));

    // Diamond head: `if slot1 == counter { update } else { keep }`.
    let mut head = Block::new(b(2));
    head.body.push(
        InstrNode::new(Inst::ICmp {
            op: ICmpOp::Eq,
            ty: Ty::I32,
            lhs: v(11),
            rhs: v(12),
        })
        .with_result(v(20)),
    );
    head.body.push(InstrNode::new(Inst::CondBr {
        cond: v(20),
        then_target: b(3),
        then_args: vec![],
        else_target: b(4),
        else_args: vec![v(10)],
    }));

    let mut update = Block::new(b(3));
    let updated = join_slot_0(&mut update, v(12));
    update.body.push(InstrNode::new(Inst::Br {
        target: b(4),
        args: vec![updated],
    }));

    // Join + latch: `q` is the merged slot-0 value.
    let mut latch = Block::new(b(4)).with_param(v(40), Ty::I32);
    latch.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(1),
        })
        .with_result(v(41)),
    );
    let slot_1_next = push_add(&mut latch, 42, v(11), v(11));
    let slot_0_next = latch_slot_0(&mut latch, v(40), slot_1_next);
    let next_counter = push_add(&mut latch, 49, v(12), v(41));
    latch.body.push(InstrNode::new(Inst::Br {
        target: b(1),
        args: back(slot_0_next, slot_1_next, next_counter),
    }));

    let mut exit = Block::new(b(5));
    exit.body.push(InstrNode::new(Inst::Return {
        values: vec![v(10), v(11)],
    }));

    function.blocks = vec![entry, header, head, update, latch, exit];
    function
}

#[test]
fn own_slot_update_through_an_in_loop_join_is_accepted() {
    let function = loop_with_join(
        |update, counter| push_add(update, 30, v(10), counter),
        |latch, q, t| push_add(latch, 43, q, t),
    );
    assert!(
        check_function(&function).is_ok(),
        "`q + t` with `q` merging slot 0's values is slot 0's next value: {:?}",
        check_function(&function)
    );
}

#[test]
fn cross_slot_value_after_an_in_loop_join_stays_rejected() {
    // Slot 0 threads a value computed only from the CHANGED slot 1, while the
    // join merges slot 0's values into a param the latch then ignores.
    let function = loop_with_join(
        |update, counter| push_add(update, 30, v(10), counter),
        |latch, _q, t| push_add(latch, 43, t, v(41)),
    );
    assert_slot_misthreaded_at(&function, 4, 0, v(43));
}

#[test]
fn join_merging_another_slots_update_does_not_become_that_slots_variable() {
    // The join param `q` merges `p0 + p2` (which reads the counter) with `p0`,
    // so it is slot 0's variable, not the counter's. Routing slot 0's next
    // value `q + t` into the counter slot is a misthread; the same route
    // without the join is rejected too.
    let through_join = loop_with_join_routed(
        |update, counter| push_add(update, 30, v(10), counter),
        |latch, q, t| push_add(latch, 43, q, t),
        |s0, s1, _counter| vec![s0, s1, s0],
    );
    assert_slot_misthreaded_at(&through_join, 4, 2, v(43));
    let straight_line = loop_with_join_routed(
        |update, counter| push_add(update, 30, v(10), counter),
        |latch, _q, t| push_add(latch, 43, v(10), t),
        |s0, s1, _counter| vec![s0, s1, s0],
    );
    assert_slot_misthreaded_at(&straight_line, 4, 2, v(43));
}

fn assert_slot_misthreaded_at(function: &Function, latch_block: u32, slot: usize, arg: ValueId) {
    let violations = check_function(function).expect_err("cross-slot route must fail closed");
    assert!(
        violations.iter().any(|violation| matches!(
            violation,
            SsaViolation::LoopCarriedSlotMisthreaded {
                header,
                latch,
                slot: actual_slot,
                arg: actual_arg,
                ..
            } if *header == b(1)
                && *latch == b(latch_block)
                && *actual_slot == slot
                && *actual_arg == arg
        )),
        "expected slot {slot} / arg {arg:?} misthread, got {violations:?}"
    );
}
