// trust-cg-verify/trust_ir_mid_tv_selbr_tests.rs - tests of the select-branch checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! An early-exit loop's `switch zext(select c, 1, 0)` becomes `condbr c`;
//! an `Option<&T>` niche test (`switch select(p == 0, trunc p, 1)` on `p`
//! the address of `select c, slot + 4, null`) becomes `condbr p == 0`, then
//! `condbr c` (the slot address is not null), and the load through the
//! select under the branch reads the slot address. Each target agrees with
//! its source in the reference interpreter. Refused: a condition that does
//! not decide the scrutinee, an address past its slot, a parameter's
//! address (not known non-null), an equality with a value that is not a
//! constant, a terminator already branching on the condition, a forward in
//! a block no edge on the condition guards, a forward on a select of
//! another condition, a chain the witness miscounts, a name that is not
//! fresh, a target with the arms swapped, a forward guarded only by an
//! edge into the entry block (the call enters it too), and a `condbr` on a
//! condition defined in a block that does not dominate the terminator (the
//! evaluator decided the scrutinee through the value the equality pins).
//!
//! The witness types (`SelectBranchWitness`, `SelectTerminator`,
//! `SelectForward`, `MAX_FORWARD_CHAIN`, the `PassWitness::SelectBranch`
//! variant and `MidTvError::NotSelectBranch`) are provisional surfaces
//! pending the owner's sign-off (`docs/wasm32_perf_roadmap.md`, "Pending
//! owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, run_samples,
    seeded_inputs,
};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"selbr\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn f(m: &Module) -> &Function {
    m.functions.iter().find(|f| f.name == "f").expect("f")
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// `f(a, n)`: `acc += i` for `i` from `a` while `i <= n & 15`, the test
/// spelled as the bridge spells an exhausted-flag loop's: a `switch` on the
/// `zext` of a `select` of `1` and `0`.
const EARLY_EXIT: &str = "functy.0 = (u32, u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = const u32 0\n\
\x20   %20 = const u32 15\n\
\x20   %21 = and u32 %1, %20\n\
\x20   br bb1(%2, %0)\n\
bb1(%3: u32, %4: u32):\n\
\x20   %5 = icmp ule u32 %4, %21\n\
\x20   %6 = const u8 1\n\
\x20   %7 = const u8 0\n\
\x20   %8 = select u8 %5, %6, %7\n\
\x20   %9 = zext u8 %8 to i32\n\
\x20   switch %9 [ 0: bb3 default: bb2 ]\n\
bb2:\n\
\x20   %10 = add u32 %3, %4\n\
\x20   %11 = const u32 1\n\
\x20   %12 = add u32 %4, %11\n\
\x20   br bb1(%10, %12)\n\
bb3:\n\
\x20   ret %3\n\
}\n";

/// `f(a)`: a 4-halfword slot holds `a`'s halves and two constants; `k = a &
/// 3`; the niche of `if k < 2 { Some(&slot[2]) } else { None }` is tested as
/// the bridge tests it, and `Some` loads through it. `{off}` is the byte
/// offset of the address in the slot.
fn niche(off: &str, base: &str) -> String {
    format!(
        "functy.0 = (u32, ptr) -> (u32)\n\n\
fn @f(functy.0) {{\n\
bb0(%0: u32, %40: ptr):\n\
\x20   %1 = alloca (u16, u16, u16, u16), align 2\n\
\x20   %30 = trunc u32 %0 to u16\n\
\x20   store u16 %30, ptr %1\n\
\x20   %31 = const i32 2\n\
\x20   %32 = gep u8, ptr %1, %31\n\
\x20   store u16 %30, ptr %32\n\
\x20   %33 = const u16 7\n\
\x20   %34 = const i32 4\n\
\x20   %35 = gep u8, ptr %1, %34\n\
\x20   store u16 %33, ptr %35\n\
\x20   %36 = const i32 6\n\
\x20   %37 = gep u8, ptr %1, %36\n\
\x20   store u16 %33, ptr %37\n\
\x20   br bb1\n\
bb1:\n\
\x20   %3 = const u32 3\n\
\x20   %4 = and u32 %0, %3\n\
\x20   %5 = const u32 2\n\
\x20   %6 = icmp ult u32 %4, %5\n\
\x20   %7 = ptrtoint ptr {base} to i32\n\
\x20   %8 = const i32 {off}\n\
\x20   %9 = add i32 %7, %8\n\
\x20   %10 = inttoptr i32 %9 to ptr\n\
\x20   %11 = const i32 0\n\
\x20   %12 = inttoptr i32 %11 to ptr\n\
\x20   %13 = select ptr %6, %10, %12\n\
\x20   %14 = ptrtoint ptr %13 to i32\n\
\x20   %15 = inttoptr i32 %14 to ptr\n\
\x20   %16 = ptrtoint ptr %15 to u64\n\
\x20   %17 = const u64 0\n\
\x20   %18 = icmp eq u64 %16, %17\n\
\x20   %19 = trunc u64 %16 to i32\n\
\x20   %20 = const i32 1\n\
\x20   %21 = select i32 %18, %19, %20\n\
\x20   switch %21 [ 0: bb3 1: bb2 default: bb4 ]\n\
bb2:\n\
\x20   %22 = inttoptr i32 %14 to ptr\n\
\x20   %23 = load u16, ptr %22\n\
\x20   %24 = zext u16 %23 to u32\n\
\x20   ret %24\n\
bb3:\n\
\x20   %25 = const u32 99\n\
\x20   ret %25\n\
bb4:\n\
\x20   unreachable\n\
}}\n"
    )
}

fn terminator(block: u32, cond: u32) -> SelectTerminator {
    SelectTerminator {
        block: b(block),
        cond: v(cond),
    }
}

fn agrees(m: &Module, src: &Function, out: &Function) {
    let inputs = seeded_inputs(m, src, 32, 64, 3).unwrap_or_else(|| {
        // A pointer parameter has no seeded value; the tests' pointer is
        // never read on the path the inputs take.
        panic!("seeded inputs")
    });
    let (a, _) = run_samples(m, src, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(m, out, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

fn refused(m: &Module, w: &SelectBranchWitness, why: &str) {
    match rebuild_select_branch(m, 32, f(m), w) {
        Err(MidTvError::NotSelectBranch { why: found, .. }) => {
            assert!(found.contains(why), "refused for `{found}`, not `{why}`");
        }
        other => panic!("not refused: {:?}", other.map(|_| ())),
    }
}

#[test]
fn an_early_exit_switch_on_a_select_becomes_a_branch_and_agrees() {
    let m = module(EARLY_EXIT);
    let src = f(&m);
    let w = SelectBranchWitness {
        terminators: vec![terminator(1, 5)],
        removed_blocks: Vec::new(),
        forwards: Vec::new(),
    };
    let (out, verdict) = rebuild_select_branch(&m, 32, src, &w).expect("accepted");
    assert_eq!(verdict.refinements, 1);
    check_pass(&m, 32, src, &out, &PassWitness::SelectBranch(w)).expect("check_pass");
    let term = &out.blocks[1].body.last().expect("terminator").inst;
    assert!(
        matches!(term, Inst::CondBr { cond, then_target, else_target, .. }
            if *cond == v(5) && *then_target == b(2) && *else_target == b(3)),
        "{out}"
    );
    agrees(&m, src, &out);
}

/// The niche program's two terminator steps and the forward, accepted.
fn niche_witness() -> SelectBranchWitness {
    SelectBranchWitness {
        terminators: vec![terminator(1, 18), terminator(1, 6)],
        removed_blocks: vec![b(4)],
        forwards: vec![SelectForward {
            block: b(2),
            index: 0,
            operand: v(14),
            cond: v(6),
            values: vec![v(900)],
        }],
    }
}

#[test]
fn a_niche_test_on_a_slot_address_becomes_a_branch_and_the_load_reads_the_slot() {
    let text = niche("4", "%1")
        .replace("(u32, ptr) -> (u32)", "(u32) -> (u32)")
        .replace("bb0(%0: u32, %40: ptr):", "bb0(%0: u32):");
    let m = module(&text);
    let src = f(&m);
    let w = niche_witness();
    let (out, verdict) = rebuild_select_branch(&m, 32, src, &w).expect("accepted");
    assert_eq!((verdict.refinements, verdict.exact), (2, 2));
    assert!(
        out.blocks.iter().all(|blk| blk.id != b(4)),
        "the dead default goes"
    );
    check_pass(&m, 32, src, &out, &PassWitness::SelectBranch(w)).expect("check_pass");
    let term = &out.blocks[1].body.last().expect("terminator").inst;
    assert!(
        matches!(term, Inst::CondBr { cond, then_target, else_target, .. }
            if *cond == v(6) && *then_target == b(2) && *else_target == b(3)),
        "{out}"
    );
    // The load's address is the slot address's integer, not the select's.
    assert!(
        matches!(&out.blocks[2].body[0].inst, Inst::Cast { op: CastOp::PtrToInt, operand, .. }
            if *operand == v(10)),
        "{out}"
    );
    agrees(&m, src, &out);
}

#[test]
fn steps_the_evaluator_does_not_decide_are_refused() {
    let plain = |t: &str| {
        t.replace("(u32, ptr) -> (u32)", "(u32) -> (u32)")
            .replace("bb0(%0: u32, %40: ptr):", "bb0(%0: u32):")
    };
    let only = |terms: Vec<SelectTerminator>| SelectBranchWitness {
        terminators: terms,
        removed_blocks: Vec::new(),
        forwards: Vec::new(),
    };
    // The control: both steps accepted.
    let m = module(&plain(&niche("4", "%1")));
    rebuild_select_branch(&m, 32, f(&m), &niche_witness()).expect("control");
    // The slot condition alone decides the niche test too.
    rebuild_select_branch(&m, 32, f(&m), &only(vec![terminator(1, 6)])).expect("one step");
    // A condition the scrutinee does not depend on.
    let m = module(&plain(&niche("4", "%1")).replace(
        "%6 = icmp ult u32 %4, %5\n",
        "%6 = icmp ult u32 %4, %5\n    %42 = icmp ugt u32 %0, %5\n",
    ));
    refused(&m, &only(vec![terminator(1, 42)]), "not decided");
    // The address is past the slot's 8 bytes: not known non-null.
    let m = module(&plain(&niche("12", "%1")));
    refused(
        &m,
        &only(vec![terminator(1, 18), terminator(1, 6)]),
        "not decided when the condition is true",
    );
    // A parameter's address is not known non-null.
    let m = module(&niche("4", "%40"));
    refused(
        &m,
        &only(vec![terminator(1, 18), terminator(1, 6)]),
        "not decided when the condition is true",
    );
    // An equality with a value that is not a constant pins nothing.
    let m = module(&plain(&niche("4", "%1")).replace(
        "%18 = icmp eq u64 %16, %17",
        "%41 = zext u32 %0 to u64\n    %18 = icmp eq u64 %16, %41",
    ));
    refused(&m, &only(vec![terminator(1, 18)]), "not decided");
    // A terminator already branching on the condition.
    let m = module(EARLY_EXIT);
    let w = only(vec![terminator(1, 5)]);
    let (once, _) = rebuild_select_branch(&m, 32, f(&m), &w).expect("first");
    let mut again = m.clone();
    let at = again
        .functions
        .iter()
        .position(|g| g.name == "f")
        .expect("f");
    again.functions[at] = once;
    refused(&again, &w, "already branches");
}

#[test]
fn forwards_off_their_guard_are_refused() {
    let m = module(
        &niche("4", "%1")
            .replace("(u32, ptr) -> (u32)", "(u32) -> (u32)")
            .replace("bb0(%0: u32, %40: ptr):", "bb0(%0: u32):"),
    );
    let mut w = niche_witness();
    // Without the terminator steps, no edge on `%6` guards `bb2`.
    let unguarded = SelectBranchWitness {
        terminators: Vec::new(),
        removed_blocks: Vec::new(),
        forwards: w.forwards.clone(),
    };
    // A block the rewrites leave reachable is not removed.
    let mut reach = niche_witness();
    reach.removed_blocks = vec![b(3)];
    assert!(matches!(
        rebuild_select_branch(&m, 32, f(&m), &reach),
        Err(MidTvError::ReachableBlockRemoved { .. })
    ));
    refused(&m, &unguarded, "no edge on the condition");
    // A select of another condition.
    w.forwards[0].cond = v(18);
    refused(&m, &w, "no edge on the condition");
    // The chain miscounted.
    let mut w = niche_witness();
    w.forwards[0].values.push(v(901));
    refused(&m, &w, "the chain has 1 instructions");
    // A name that is not fresh.
    let mut w = niche_witness();
    w.forwards[0].values = vec![v(23)];
    refused(&m, &w, "not fresh");
    // An instruction that does not read the operand.
    let mut w = niche_witness();
    w.forwards[0].index = 1;
    refused(&m, &w, "does not read the operand");
    // A target with the arms swapped is not the claimed rewrite.
    let src = f(&m);
    let w = niche_witness();
    let (mut out, _) = rebuild_select_branch(&m, 32, src, &w).expect("accepted");
    if let Some(Inst::CondBr {
        then_target,
        else_target,
        ..
    }) = out.blocks[1].body.last_mut().map(|n| &mut n.inst)
    {
        std::mem::swap(then_target, else_target);
    }
    assert!(matches!(
        check_pass(&m, 32, src, &out, &PassWitness::SelectBranch(w)),
        Err(MidTvError::TargetDiffers { .. })
    ));
}

/// `f(x)`: `select x == 0, x, (select x == 77, 0, x)`, returned along the
/// `else` edge of `condbr x == 0`, whose `then` edge re-enters the entry.
const ENTRY_GUARD: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %2 = const u32 0\n\
\x20   %3 = icmp eq u32 %1, %2\n\
\x20   %20 = const u32 77\n\
\x20   %21 = icmp eq u32 %1, %20\n\
\x20   %22 = select u32 %21, %2, %1\n\
\x20   %6 = select u32 %3, %1, %22\n\
\x20   %9 = const u32 1\n\
\x20   %10 = add u32 %6, %2\n\
\x20   condbr %3, bb0(%9), bb1(%10)\n\
bb1(%11: u32):\n\
\x20   ret %11\n\
}\n";

#[test]
fn an_edge_into_the_entry_guards_no_forward() {
    let m = module(ENTRY_GUARD);
    // The `add` reading `%6` in the entry, which the `then` edge alone
    // enters among the edges; the call enters it with any `x`.
    let w = SelectBranchWitness {
        terminators: Vec::new(),
        removed_blocks: Vec::new(),
        forwards: vec![SelectForward {
            block: b(0),
            index: 7,
            operand: v(6),
            cond: v(3),
            values: Vec::new(),
        }],
    };
    refused(&m, &w, "no edge on the condition guards the block");
    // The control: a block other than the entry that one edge enters, the
    // `then` edge of `condbr x == 0`, is guarded by it.
    let guarded = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb8(%1: u32):\n\
\x20   %2 = const u32 0\n\
\x20   %3 = icmp eq u32 %1, %2\n\
\x20   %20 = const u32 77\n\
\x20   %21 = icmp eq u32 %1, %20\n\
\x20   %22 = select u32 %21, %2, %1\n\
\x20   %6 = select u32 %3, %1, %22\n\
\x20   condbr %3, bb0, bb1(%1)\n\
bb0:\n\
\x20   %10 = add u32 %6, %2\n\
\x20   br bb1(%10)\n\
bb1(%11: u32):\n\
\x20   ret %11\n\
}\n",
    );
    let w = SelectBranchWitness {
        terminators: Vec::new(),
        removed_blocks: Vec::new(),
        forwards: vec![SelectForward {
            block: b(0),
            index: 0,
            operand: v(6),
            cond: v(3),
            values: Vec::new(),
        }],
    };
    let src = f(&guarded);
    let (out, verdict) = rebuild_select_branch(&guarded, 32, src, &w).expect("the control");
    assert_eq!(verdict.exact, 1);
    agrees(&guarded, src, &out);
}

#[test]
fn a_condition_defined_off_the_terminators_dominators_is_refused() {
    // `%6 = icmp eq %2, 7` is defined in `bb1` only; assuming it true pins
    // `%2` to 7 and the `switch` in `bb2` takes `bb4`, assuming it false
    // reads `%2` as 5 and takes `bb3`. A `condbr %6` in `bb2` would read
    // `%6` where it is not defined.
    let text = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %2 = const u32 5\n\
\x20   %3 = const u32 0\n\
\x20   %4 = icmp eq u32 %1, %3\n\
\x20   condbr %4, bb1, bb2\n\
bb1:\n\
\x20   %5 = const u32 7\n\
\x20   %6 = icmp eq u32 %2, %5\n\
\x20   %20 = zext bool %6 to u32\n\
\x20   ret %20\n\
bb2:\n\
\x20   switch %2 [ 5: bb3 7: bb4 default: bb4 ]\n\
bb3:\n\
\x20   %7 = const u32 1\n\
\x20   ret %7\n\
bb4:\n\
\x20   %8 = const u32 2\n\
\x20   ret %8\n\
}\n";
    let w = SelectBranchWitness {
        terminators: vec![terminator(2, 6)],
        removed_blocks: Vec::new(),
        forwards: Vec::new(),
    };
    refused(&module(text), &w, "does not dominate");
    // The control: the condition defined in the entry, which dominates
    // `bb2`.
    let hoisted = text
        .replace(
            "\x20   %5 = const u32 7\n\x20   %6 = icmp eq u32 %2, %5\n",
            "",
        )
        .replace(
            "\x20   %4 = icmp eq u32 %1, %3\n",
            "\x20   %4 = icmp eq u32 %1, %3\n\x20   %5 = const u32 7\n\
             \x20   %6 = icmp eq u32 %2, %5\n",
        );
    let m = module(&hoisted);
    let src = f(&m);
    let (out, _) = rebuild_select_branch(&m, 32, src, &w).expect("the control");
    agrees(&m, src, &out);
}
