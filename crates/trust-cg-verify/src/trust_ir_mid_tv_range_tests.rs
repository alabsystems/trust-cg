// trust-cg-verify/trust_ir_mid_tv_range_tests.rs - tests of the range rules' checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Each rule is accepted where its premises hold and decide it, and refused
//! (the negative controls) where it is applied outside its precondition: a
//! premise narrower than the derived fact, premises that contain the fact
//! but do not decide the rule (every rule, each refused by its own
//! decision), a reachable block removed, a target beyond the witness. The
//! rewritten functions agree with their sources in the interpreter. The
//! compare and overflow decisions agree with brute force on every pair of
//! intervals at small widths, and the guard index agrees with the
//! dominator-path walk on every small tree. The lemmas hold on every input
//! at small widths and their controls fail (in-process enumeration); `ay`
//! refutes no lemma and no accepted rewrite's obligation, and refutes every
//! control (its UNSAT answers are counted, certified or not, and an
//! `unknown` proves nothing).

use std::collections::BTreeSet;

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, run_samples,
    seeded_inputs,
};
use super::*;
use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay};
use crate::lowering_proof::{
    ProofObligation, VerificationConfig, verify_by_evaluation_with_config,
};
use crate::verify::VerificationResult;

const HEADER: &str = "; TrustIr text format v1\nmodule \"range\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn func<'m>(module: &'m Module, name: &str) -> &'m Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .expect("function")
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

fn premise(value: u32, lo: u128, hi: u128) -> RangePremise {
    RangePremise {
        value: v(value),
        lo,
        hi,
    }
}

fn rewrite(block: u32, index: usize, rule: RangeRule, premises: &[RangePremise]) -> RangeRewrite {
    RangeRewrite {
        block: b(block),
        index,
        rule,
        premises: premises.to_vec(),
    }
}

fn witness(rewrites: Vec<RangeRewrite>, removed: &[u32]) -> PassWitness {
    PassWitness::Range(RangeWitness {
        rewrites,
        removed_blocks: removed.iter().map(|&n| b(n)).collect(),
        invariants: Vec::new(),
    })
}

/// `src` with the instruction at `(block position, index)` replaced by
/// `nodes`.
fn with(src: &Function, block: usize, index: usize, nodes: Vec<Inst>) -> Function {
    let mut out = src.clone();
    let node = out.blocks[block].body.remove(index);
    let results = node.results.clone();
    for (k, inst) in nodes.into_iter().enumerate().rev() {
        let mut n = node.clone();
        n.inst = inst;
        n.results = match results.len() {
            2 => vec![results[k]],
            _ => results.clone(),
        };
        out.blocks[block].body.insert(index, n);
    }
    out
}

fn bool_const(value: bool) -> Inst {
    Inst::Const {
        ty: Ty::Bool,
        value: Constant::Bool(value),
    }
}

/// The source and target agree in the interpreter on seeded inputs.
fn agree(m: &Module, source: &Function, target: &Function) {
    let inputs = seeded_inputs(m, source, 32, 64, 11).expect("scalar parameters");
    let (a, _) = run_samples(m, source, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(m, target, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

// ---------------------------------------------------------------------------
// icmp
// ---------------------------------------------------------------------------

/// A masked index checked against the table length: the bounds check of
/// `t[i & 63]` for a 64-entry table.
fn masked(mask: u32) -> String {
    format!(
        "functy.0 = (u32) -> (bool)\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: u32):\n\
         \x20   %1 = const u32 {mask}\n\
         \x20   %2 = and u32 %0, %1\n\
         \x20   %3 = const u32 64\n\
         \x20   %4 = icmp ult u32 %2, %3\n\
         \x20   ret %4\n\
         }}\n"
    )
}

#[test]
fn a_masked_index_check_folds_to_true() {
    let src = module(&masked(63));
    let f = func(&src, "f");
    let target = with(f, 0, 3, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(
            0,
            3,
            RangeRule::ICmp,
            &[premise(2, 0, 63), premise(3, 64, 64)],
        )],
        &[],
    );
    let verdict = check_pass(&src, 32, f, &target, &w).expect("the mask decides the compare");
    assert_eq!((verdict.exact, verdict.refinements), (1, 0));
    agree(&src, f, &target);
}

#[test]
fn negative_control_a_premise_narrower_than_the_fact_is_refused() {
    // The mask is 127: the index may reach the bound.
    let src = module(&masked(127));
    let f = func(&src, "f");
    let target = with(f, 0, 3, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(
            0,
            3,
            RangeRule::ICmp,
            &[premise(2, 0, 63), premise(3, 64, 64)],
        )],
        &[],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(
        matches!(
            err,
            MidTvError::RangePremise {
                derived: Some((0, 127)),
                ..
            }
        ),
        "{err}"
    );
}

#[test]
fn negative_control_premises_that_do_not_decide_the_compare_are_refused() {
    let src = module(&masked(127));
    let f = func(&src, "f");
    let target = with(f, 0, 3, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(
            0,
            3,
            RangeRule::ICmp,
            &[premise(2, 0, 127), premise(3, 64, 64)],
        )],
        &[],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangeUndecided { .. }), "{err}");
}

#[test]
fn negative_control_a_wrong_constant_is_refused() {
    let src = module(&masked(63));
    let f = func(&src, "f");
    let target = with(f, 0, 3, vec![bool_const(false)]);
    let w = witness(
        vec![rewrite(
            0,
            3,
            RangeRule::ICmp,
            &[premise(2, 0, 63), premise(3, 64, 64)],
        )],
        &[],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::TargetDiffers { .. }), "{err}");
}

/// The fact rows through extensions, shifts, remainders, subtraction and
/// `select`, and the signed predicates.
const ROWS: &str = "functy.0 = (u32, u8, i32) -> (bool, bool, bool, bool, bool, bool, bool)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32, %1: u8, %2: i32):\n\
    \x20   %3 = zext u8 %1 to usize\n\
    \x20   %4 = const usize 256\n\
    \x20   %5 = icmp ult usize %3, %4\n\
    \x20   %6 = const u32 24\n\
    \x20   %7 = lshr u32 %0, %6\n\
    \x20   %8 = const u32 255\n\
    \x20   %9 = icmp ule u32 %7, %8\n\
    \x20   %10 = const u32 10\n\
    \x20   %11 = urem u32 %0, %10\n\
    \x20   %12 = const u32 9\n\
    \x20   %13 = icmp ugt u32 %11, %12\n\
    \x20   %14 = zext u8 %1 to u32\n\
    \x20   %15 = const u32 300\n\
    \x20   %16 = sub u32 %15, %14\n\
    \x20   %17 = const u32 45\n\
    \x20   %18 = icmp uge u32 %16, %17\n\
    \x20   %19 = select u32 %5, %14, %17\n\
    \x20   %20 = icmp eq u32 %19, %15\n\
    \x20   %21 = zext u8 %1 to i32\n\
    \x20   %22 = const i32 -1\n\
    \x20   %23 = icmp sgt i32 %21, %22\n\
    \x20   %24 = trunc u32 %14 to u16\n\
    \x20   %25 = sext u16 %24 to i64\n\
    \x20   %26 = const i64 256\n\
    \x20   %27 = icmp slt i64 %25, %26\n\
    \x20   ret %5, %9, %13, %18, %20, %23, %27\n\
    }\n";

#[test]
fn each_fact_row_decides_its_compare() {
    let src = module(ROWS);
    let f = func(&src, "f");
    let all_ones = u128::from(u32::MAX);
    // (index, premises, outcome): zext to usize, lshr by a constant, urem
    // by a constant, a non-wrapping difference, a select on a decided
    // condition (its arm %14, not the hull with 45), a signed compare
    // against -1, trunc then sext.
    let cases: [(usize, [RangePremise; 2], bool); 7] = [
        (2, [premise(3, 0, 255), premise(4, 256, 256)], true),
        (6, [premise(7, 0, 255), premise(8, 255, 255)], true),
        (10, [premise(11, 0, 9), premise(12, 9, 9)], false),
        (15, [premise(16, 45, 300), premise(17, 45, 45)], true),
        (17, [premise(19, 0, 255), premise(15, 300, 300)], false),
        (
            20,
            [premise(21, 0, 255), premise(22, all_ones, all_ones)],
            true,
        ),
        (24, [premise(25, 0, 255), premise(26, 256, 256)], true),
    ];
    let mut rewrites = Vec::new();
    let mut target = f.clone();
    for (index, premises, outcome) in &cases {
        target.blocks[0].body[*index].inst = bool_const(*outcome);
        rewrites.push(rewrite(0, *index, RangeRule::ICmp, premises));
    }
    let w = witness(rewrites, &[]);
    check_pass(&src, 32, f, &target, &w).expect("every row decides its compare");
    agree(&src, f, &target);
}

// ---------------------------------------------------------------------------
// overflow
// ---------------------------------------------------------------------------

fn overflow(op: &str, ty: &str, lhs: &str, rhs: &str) -> String {
    format!(
        "functy.0 = (u16, u16) -> ({ty}, bool)\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: u16, %1: u16):\n\
         \x20   %2 = zext u16 %0 to {ty}\n\
         \x20   %3 = zext u16 %1 to {ty}\n\
         \x20   %4 = const {ty} {lhs}\n\
         \x20   %5 = add {ty} %2, %4\n\
         \x20   %6 = const {ty} {rhs}\n\
         \x20   %7 = add {ty} %3, %6\n\
         \x20   %8, %9 = {op}.overflow {ty} %5, %7\n\
         \x20   ret %8, %9\n\
         }}\n"
    )
}

fn overflow_case(
    op: &str,
    ty: &str,
    (lhs, rhs): (u32, u32),
    rule: RangeRule,
    binop: BinOp,
    premises: [(u128, u128); 2],
) -> (Module, Function, PassWitness) {
    let src = module(&overflow(op, ty, &lhs.to_string(), &rhs.to_string()));
    let f = func(&src, "f").clone();
    let ty = if ty == "u32" { Ty::U32 } else { Ty::I32 };
    let target = with(
        &f,
        0,
        6,
        vec![
            Inst::BinOp {
                op: binop,
                ty,
                lhs: v(5),
                rhs: v(7),
            },
            bool_const(false),
        ],
    );
    let w = witness(
        vec![rewrite(
            0,
            6,
            rule,
            &[
                premise(5, premises[0].0, premises[0].1),
                premise(7, premises[1].0, premises[1].1),
            ],
        )],
        &[],
    );
    (src, target, w)
}

#[test]
fn overflow_rules_drop_impossible_flags() {
    let m = 65535u128;
    for (op, ty, offsets, rule, binop, premises) in [
        (
            "add",
            "u32",
            (0, 1),
            RangeRule::AddOverflow,
            BinOp::Add,
            [(0, m), (1, m + 1)],
        ),
        (
            "sub",
            "u32",
            (70000, 0),
            RangeRule::SubOverflow,
            BinOp::Sub,
            [(70000, 70000 + m), (0, m)],
        ),
        (
            "mul",
            "u32",
            (0, 0),
            RangeRule::MulOverflow,
            BinOp::Mul,
            [(0, m), (0, m)],
        ),
        (
            "add",
            "i32",
            (0, 0),
            RangeRule::AddOverflow,
            BinOp::Add,
            [(0, m), (0, m)],
        ),
        (
            "sub",
            "i32",
            (0, 0),
            RangeRule::SubOverflow,
            BinOp::Sub,
            [(0, m), (0, m)],
        ),
    ] {
        let (src, target, w) = overflow_case(op, ty, offsets, rule, binop, premises);
        let f = func(&src, "f");
        let verdict =
            check_pass(&src, 32, f, &target, &w).unwrap_or_else(|e| panic!("{op} {ty}: {e}"));
        assert_eq!(verdict.exact, 1);
        agree(&src, f, &target);
    }
}

#[test]
fn negative_control_an_overflow_outside_its_precondition_is_refused() {
    let m = 65535u128;
    // u32: 65535 * 65538 overflows; claimed with the true premises, the rule
    // is undecided.
    let (src, target, w) = overflow_case(
        "mul",
        "u32",
        (0, 3),
        RangeRule::MulOverflow,
        BinOp::Mul,
        [(0, m), (3, m + 3)],
    );
    let err = check_pass(&src, 32, func(&src, "f"), &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangeUndecided { .. }), "{err}");
    // A premise narrower than the derived fact is refused.
    let (src, target, w) = overflow_case(
        "mul",
        "u32",
        (0, 3),
        RangeRule::MulOverflow,
        BinOp::Mul,
        [(0, m), (3, 4)],
    );
    let err = check_pass(&src, 32, func(&src, "f"), &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangePremise { .. }), "{err}");
    // An unsigned difference that may borrow.
    let (src, target, w) = overflow_case(
        "sub",
        "u32",
        (100, 0),
        RangeRule::SubOverflow,
        BinOp::Sub,
        [(100, 100 + m), (0, m)],
    );
    let err = check_pass(&src, 32, func(&src, "f"), &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangeUndecided { .. }), "{err}");
    // A signed sum past i32::MAX.
    let (src, target, w) = overflow_case(
        "add",
        "i32",
        (0x7fff_0000, 0),
        RangeRule::AddOverflow,
        BinOp::Add,
        [(0x7fff_0000, 0x7fff_0000 + m), (0, m)],
    );
    let err = check_pass(&src, 32, func(&src, "f"), &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangeUndecided { .. }), "{err}");
    // The rule named for another operation.
    let (src, target, w) = overflow_case(
        "add",
        "u32",
        (0, 1),
        RangeRule::MulOverflow,
        BinOp::Add,
        [(0, m), (1, m + 1)],
    );
    let err = check_pass(&src, 32, func(&src, "f"), &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangeUndecided { .. }), "{err}");
}

// ---------------------------------------------------------------------------
// select, assert, condbr
// ---------------------------------------------------------------------------

/// A saturating add in the bridge's shape, its flag fed to a `select` and to
/// a branch through `icmp eq bool %flag, false` (the bridge's lowering of
/// `assert(!flag)`), and an `assert` of the same condition.
const FLAGS: &str = "functy.0 = (u8, u8) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u8, %1: u8):\n\
    \x20   %2 = zext u8 %0 to u32\n\
    \x20   %3 = zext u8 %1 to u32\n\
    \x20   %4, %5 = add.overflow u32 %2, %3\n\
    \x20   %6 = const u32 4294967295\n\
    \x20   %7 = select u32 %5, %6, %4\n\
    \x20   %8 = const bool false\n\
    \x20   %9 = icmp eq bool %5, %8\n\
    \x20   assert %9\n\
    \x20   condbr %9, bb1, bb2\n\
    bb1:\n\
    \x20   ret %7\n\
    bb2:\n\
    \x20   %10 = const u32 0\n\
    \x20   ret %10\n\
    }\n";

fn flags_rewrites(drop_condition: bool) -> Vec<RangeRewrite> {
    let mut rewrites = vec![
        rewrite(
            0,
            2,
            RangeRule::AddOverflow,
            &[premise(2, 0, 255), premise(3, 0, 255)],
        ),
        rewrite(0, 4, RangeRule::Select, &[premise(5, 0, 0)]),
        rewrite(0, 6, RangeRule::ICmp, &[premise(5, 0, 0), premise(8, 0, 0)]),
        rewrite(0, 7, RangeRule::Assert, &[premise(9, 1, 1)]),
    ];
    if !drop_condition {
        rewrites.push(rewrite(0, 8, RangeRule::CondBr, &[premise(9, 1, 1)]));
    }
    rewrites
}

fn flags_target(src: &Function, fold_branch: bool, remove: bool) -> Function {
    let mut t = src.clone();
    let body = &mut t.blocks[0].body;
    if fold_branch {
        body[8].inst = Inst::Br {
            target: b(1),
            args: vec![],
        };
    }
    body.remove(7);
    body[6].inst = bool_const(true);
    body[4].inst = Inst::Copy {
        ty: Ty::U32,
        operand: v(4),
    };
    let node = body.remove(2);
    let mut flag = node.clone();
    flag.inst = bool_const(false);
    flag.results = vec![v(5)];
    let mut value = node;
    value.inst = Inst::BinOp {
        op: BinOp::Add,
        ty: Ty::U32,
        lhs: v(2),
        rhs: v(3),
    };
    value.results = vec![v(4)];
    body.insert(2, flag);
    body.insert(2, value);
    if remove {
        t.blocks.retain(|block| block.id != b(2));
    }
    t
}

#[test]
fn a_decided_flag_folds_the_select_the_assert_and_the_branch() {
    let src = module(FLAGS);
    let f = func(&src, "f");
    let target = flags_target(f, true, true);
    let w = witness(flags_rewrites(false), &[2]);
    let verdict = check_pass(&src, 32, f, &target, &w).expect("the flag is decided");
    assert_eq!((verdict.exact, verdict.refinements), (6, 0));
    agree(&src, f, &target);
    let PassWitness::Range(rw) = &w else {
        unreachable!()
    };
    let counts = rw.counts();
    assert_eq!(counts.get("add_overflow"), Some(&1));
    assert_eq!(counts.get("removed_block"), Some(&1));
}

#[test]
fn negative_control_a_reachable_block_removal_is_refused() {
    let src = module(FLAGS);
    let f = func(&src, "f");
    // The branch stays, so bb2 is reachable.
    let target = flags_target(f, false, true);
    let w = witness(flags_rewrites(true), &[2]);
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(
        matches!(err, MidTvError::ReachableBlockRemoved { .. }),
        "{err}"
    );
}

#[test]
fn negative_control_an_undecided_condition_is_refused() {
    // The operands are full u32s: the flag is not decided, and neither the
    // select nor the assert may fold on it.
    let text = FLAGS.replace("%2 = zext u8 %0 to u32", "%2 = const u32 4294967295");
    let src = module(&text);
    let f = func(&src, "f");
    let target = flags_target(f, true, true);
    let w = witness(flags_rewrites(false), &[2]);
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(
        matches!(
            err,
            MidTvError::RangeUndecided { .. } | MidTvError::RangePremise { .. }
        ),
        "{err}"
    );
    // A select on an undecided condition.
    let w = witness(
        vec![rewrite(0, 4, RangeRule::Select, &[premise(5, 0, 1)])],
        &[],
    );
    let mut t = f.clone();
    t.blocks[0].body[4].inst = Inst::Copy {
        ty: Ty::U32,
        operand: v(4),
    };
    let err = check_pass(&src, 32, f, &t, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangePremise { .. }), "{err}");
    // An assert claimed on a condition decided false.
    let src = module(FLAGS);
    let f = func(&src, "f");
    let w = witness(
        vec![rewrite(0, 7, RangeRule::Assert, &[premise(9, 0, 0)])],
        &[],
    );
    let mut t = f.clone();
    t.blocks[0].body.remove(7);
    let err = check_pass(&src, 32, f, &t, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangePremise { .. }), "{err}");
}

/// A condition whose derived fact is `[0, 1]` (`%6`, a compare the mask
/// does not decide) and one whose fact is `[0, 0]` (`%8`), read by a
/// `select`, two `assert`s and a `condbr`.
const UNDECIDED: &str = "functy.0 = (u32, u32, u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32, %1: u32, %2: u32):\n\
    \x20   %3 = const u32 127\n\
    \x20   %4 = and u32 %0, %3\n\
    \x20   %5 = const u32 64\n\
    \x20   %6 = icmp ult u32 %4, %5\n\
    \x20   %7 = select u32 %6, %1, %2\n\
    \x20   %8 = icmp ugt u32 %4, %3\n\
    \x20   assert %6\n\
    \x20   assert %8\n\
    \x20   condbr %6, bb1, bb2\n\
    bb1:\n\
    \x20   ret %7\n\
    bb2:\n\
    \x20   ret %1\n\
    }\n";

/// `err` is the rule's own refusal `why`, not a premise refusal.
fn undecided_because(err: &MidTvError, expected: &str) {
    match err {
        MidTvError::RangeUndecided { why, .. } => assert_eq!(*why, expected, "{err}"),
        other => panic!("expected RangeUndecided({expected}), got {other}"),
    }
}

/// Each condition rule claimed with a premise that CONTAINS the derived
/// fact, so the premise check passes and the rule's own decision refuses:
/// a `select`, `assert` and `condbr` on a `[0, 1]` condition, and an
/// `assert` of a condition decided false.
#[test]
fn negative_control_each_condition_rule_refuses_an_undecided_condition() {
    let src = module(UNDECIDED);
    let f = func(&src, "f");
    // select %6 claimed as its then arm.
    let mut t = f.clone();
    t.blocks[0].body[4].inst = Inst::Copy {
        ty: Ty::U32,
        operand: v(1),
    };
    let w = witness(
        vec![rewrite(0, 4, RangeRule::Select, &[premise(6, 0, 1)])],
        &[],
    );
    let err = check_pass(&src, 32, f, &t, &w).unwrap_err();
    undecided_because(&err, "the condition is not decided");
    // assert %6 removed.
    let mut t = f.clone();
    t.blocks[0].body.remove(6);
    let w = witness(
        vec![rewrite(0, 6, RangeRule::Assert, &[premise(6, 0, 1)])],
        &[],
    );
    let err = check_pass(&src, 32, f, &t, &w).unwrap_err();
    undecided_because(&err, "the condition is not decided true");
    // assert %8 removed: its condition is decided, but false.
    let mut t = f.clone();
    t.blocks[0].body.remove(7);
    let w = witness(
        vec![rewrite(0, 7, RangeRule::Assert, &[premise(8, 0, 0)])],
        &[],
    );
    let err = check_pass(&src, 32, f, &t, &w).unwrap_err();
    undecided_because(&err, "the condition is not decided true");
    // condbr %6 folded to its then edge, with and without removing bb2.
    for removed in [&[][..], &[2][..]] {
        let mut t = f.clone();
        t.blocks[0].body[8].inst = Inst::Br {
            target: b(1),
            args: vec![],
        };
        if !removed.is_empty() {
            t.blocks.retain(|block| block.id != b(2));
        }
        let w = witness(
            vec![rewrite(0, 8, RangeRule::CondBr, &[premise(6, 0, 1)])],
            removed,
        );
        let err = check_pass(&src, 32, f, &t, &w).unwrap_err();
        undecided_because(&err, "the condition is not decided");
    }
}

/// A signed compare on an interval that crosses the sign boundary is not
/// decided, though the premise contains the derived fact; the same compare
/// on an interval that stays negative is.
#[test]
fn negative_control_a_signed_compare_across_the_sign_boundary_is_refused() {
    let text = "functy.0 = (i32) -> (bool, bool)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = const i32 -1\n\
        \x20   %2 = and i32 %0, %1\n\
        \x20   %3 = const i32 0\n\
        \x20   %4 = icmp slt i32 %2, %3\n\
        \x20   %5 = const i32 -8\n\
        \x20   %6 = icmp slt i32 %5, %1\n\
        \x20   ret %4, %6\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let all_ones = u128::from(u32::MAX);
    let target = with(f, 0, 3, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(
            0,
            3,
            RangeRule::ICmp,
            &[premise(2, 0, all_ones), premise(3, 0, 0)],
        )],
        &[],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    undecided_because(&err, "the premises do not decide the compare");
    // -8 <s -1: two negative intervals decide it.
    let target = with(f, 0, 5, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(
            0,
            5,
            RangeRule::ICmp,
            &[
                premise(5, all_ones - 7, all_ones - 7),
                premise(1, all_ones, all_ones),
            ],
        )],
        &[],
    );
    check_pass(&src, 32, f, &target, &w).expect("two negative constants compare");
    agree(&src, f, &target);
}

/// The raw values of a width read signed.
fn signed_at(raw: u128, bits: u32) -> i128 {
    if (raw >> (bits - 1)) & 1 == 1 {
        raw as i128 - (1i128 << bits)
    } else {
        raw as i128
    }
}

fn icmp_brute(op: ICmpOp, bits: u32, x: u128, y: u128) -> bool {
    let (sx, sy) = (signed_at(x, bits), signed_at(y, bits));
    match op {
        ICmpOp::Eq => x == y,
        ICmpOp::Ne => x != y,
        ICmpOp::Ult => x < y,
        ICmpOp::Ule => x <= y,
        ICmpOp::Ugt => x > y,
        ICmpOp::Uge => x >= y,
        ICmpOp::Slt => sx < sy,
        ICmpOp::Sle => sx <= sy,
        ICmpOp::Sgt => sx > sy,
        ICmpOp::Sge => sx >= sy,
    }
}

/// Every interval of raw values at `bits`.
fn intervals(bits: u32) -> Vec<Iv> {
    let top = mask(bits);
    let mut out = Vec::new();
    for lo in 0..=top {
        for hi in lo..=top {
            out.push(Iv { lo, hi, bits });
        }
    }
    out
}

/// The checker's compare decision against brute force, on every pair of
/// intervals at widths 1 to 4 and every predicate: a decision is the
/// outcome of every pair of values (sound), and every unsigned compare, and
/// every signed one whose intervals stay on one side of the sign boundary,
/// that all pairs agree on is decided (complete there).
#[test]
fn the_compare_decision_agrees_with_brute_force_at_small_widths() {
    const OPS: [ICmpOp; 10] = [
        ICmpOp::Eq,
        ICmpOp::Ne,
        ICmpOp::Ult,
        ICmpOp::Ule,
        ICmpOp::Ugt,
        ICmpOp::Uge,
        ICmpOp::Slt,
        ICmpOp::Sle,
        ICmpOp::Sgt,
        ICmpOp::Sge,
    ];
    let mut decided = 0usize;
    for bits in 1..=4u32 {
        let all = intervals(bits);
        for op in OPS {
            let signed = matches!(op, ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge);
            for &a in &all {
                for &b in &all {
                    let mut outcomes = [false; 2];
                    for x in a.lo..=a.hi {
                        for y in b.lo..=b.hi {
                            outcomes[usize::from(icmp_brute(op, bits, x, y))] = true;
                        }
                    }
                    let truth = match outcomes {
                        [false, true] => Some(true),
                        [true, false] => Some(false),
                        _ => None,
                    };
                    let claim = decide_icmp(op, bits, a, b);
                    if let Some(c) = claim {
                        decided += 1;
                        assert_eq!(truth, Some(c), "{op:?} at {bits}: {a:?} {b:?}");
                    }
                    let one_sided = !signed
                        || (bits >= 2
                            && signed_interval(a).is_some()
                            && signed_interval(b).is_some());
                    if one_sided {
                        assert_eq!(claim, truth, "{op:?} at {bits}: {a:?} {b:?} (incomplete)");
                    }
                }
            }
        }
    }
    assert!(decided > 0);
}

/// The checker's overflow decision against brute force on every pair of
/// intervals at widths 2 to 4: when it says no pair overflows, none does
/// (the interpreter's flags: the exact result outside the type's range), and
/// for unsigned operations it says so whenever none does.
#[test]
fn the_overflow_decision_agrees_with_brute_force_at_small_widths() {
    let mut excluded = 0usize;
    for bits in 2..=4u32 {
        let all = intervals(bits);
        for op in [
            OverflowOp::AddOverflow,
            OverflowOp::SubOverflow,
            OverflowOp::MulOverflow,
        ] {
            for signed in [false, true] {
                for &a in &all {
                    for &b in &all {
                        let mut any = false;
                        for x in a.lo..=a.hi {
                            for y in b.lo..=b.hi {
                                let (x, y) = if signed {
                                    (signed_at(x, bits), signed_at(y, bits))
                                } else {
                                    (x as i128, y as i128)
                                };
                                let exact = match op {
                                    OverflowOp::AddOverflow => x + y,
                                    OverflowOp::SubOverflow => x - y,
                                    OverflowOp::MulOverflow => x * y,
                                };
                                let (min, max) = if signed {
                                    (-(1i128 << (bits - 1)), (1i128 << (bits - 1)) - 1)
                                } else {
                                    (0, (1i128 << bits) - 1)
                                };
                                any |= exact < min || exact > max;
                            }
                        }
                        let claim = cannot_overflow(op, bits, signed, a, b);
                        if claim {
                            excluded += 1;
                            assert!(!any, "{op:?} signed={signed} at {bits}: {a:?} {b:?}");
                        }
                        if !signed {
                            assert_eq!(claim, !any, "{op:?} at {bits}: {a:?} {b:?} (incomplete)");
                        }
                    }
                }
            }
        }
    }
    assert!(excluded > 0);
}

#[test]
fn negative_control_a_target_beyond_the_witness_is_refused() {
    let src = module(FLAGS);
    let f = func(&src, "f");
    let target = flags_target(f, true, true);
    // The witness omits the assert's removal.
    let mut rewrites = flags_rewrites(false);
    rewrites.remove(3);
    let err = check_pass(&src, 32, f, &target, &witness(rewrites, &[2])).unwrap_err();
    assert!(matches!(err, MidTvError::TargetDiffers { .. }), "{err}");
}

// ---------------------------------------------------------------------------
// Solver obligations and lemmas
// ---------------------------------------------------------------------------

fn ay() -> AYConfig {
    AYConfig::default().with_timeout(30_000)
}

/// What `ay` said about an obligation that must hold.
#[derive(Debug, Default)]
struct Answers {
    /// UNSAT with a proof the independent checker certified.
    certified: usize,
    /// UNSAT whose proof the checker cannot certify (`SolverUnsat`, or AY's
    /// own certificate header naming unproved steps).
    uncertified: usize,
    /// No verdict (an `unknown` of any reason, a timeout): never counted
    /// as a proof.
    unanswered: Vec<String>,
}

impl Answers {
    /// Record `result`; a counterexample or a solver error fails the test.
    fn record(&mut self, name: &str, result: AYResult) {
        match result {
            AYResult::Verified => self.certified += 1,
            AYResult::SolverUnsat => self.uncertified += 1,
            AYResult::Unknown(reason) if reason.starts_with("incomplete AY proof certificate:") => {
                self.uncertified += 1;
            }
            AYResult::Unknown(reason) => self.unanswered.push(format!("{name}: {reason}")),
            AYResult::Timeout => self.unanswered.push(format!("{name}: timeout")),
            AYResult::CounterExample(cex) => panic!("{name}: the solver refutes it: {cex:?}"),
            AYResult::Error(why) => panic!("{name}: the solver did not run: {why}"),
        }
    }

    fn unsat(&self) -> usize {
        self.certified + self.uncertified
    }
}

/// The control must be refuted by the solver.
fn refuted(obligation: &ProofObligation) {
    match verify_with_ay(obligation, &ay()) {
        AYResult::CounterExample(_) => {}
        other => panic!("{}: not refuted: {other}", obligation.name),
    }
}

/// Every lemma holds on every input at 3 bits (and the extension and `and`
/// rows at 4 and 6 bits, where their inputs fit the enumeration), and every
/// control fails on some input: exhaustive, in process, independent of the
/// solver.
#[test]
fn every_fact_row_and_decision_holds_exhaustively_and_its_control_fails() {
    let config = VerificationConfig {
        exhaustive_threshold: 10,
        ..VerificationConfig::default()
    };
    let mut checked = 0usize;
    for bits in [3u32, 4, 6] {
        let lemmas = range_fact_lemmas(bits);
        assert_eq!(lemmas.len(), 35);
        for lemma in &lemmas {
            if crate::lowering_proof::exhaustive_input_count(&lemma.obligation, &config).is_none() {
                assert!(bits > 3, "{} is not enumerable at 3 bits", lemma.name);
                continue;
            }
            assert!(
                matches!(
                    verify_by_evaluation_with_config(&lemma.obligation, &config),
                    VerificationResult::Valid
                ),
                "{}",
                lemma.obligation.name
            );
            assert!(
                matches!(
                    verify_by_evaluation_with_config(&lemma.control, &config),
                    VerificationResult::Invalid { .. }
                ),
                "{}",
                lemma.control.name
            );
            checked += 1;
        }
    }
    assert!(checked >= 35 + 2 * 4, "{checked} lemmas enumerated");
}

/// At 8 bits the solver refutes no lemma and refutes every control. Its
/// UNSAT answers are counted, certified or not; an `unknown` or a timeout
/// proves nothing and is listed.
#[test]
fn the_solver_refutes_no_lemma_and_every_control() {
    let mut answers = Answers::default();
    for lemma in range_fact_lemmas(8) {
        answers.record(
            &lemma.obligation.name,
            verify_with_ay(&lemma.obligation, &ay()),
        );
        refuted(&lemma.control);
    }
    eprintln!(
        "range lemmas at 8 bits: {} UNSAT ({} certified), unanswered: {:#?}",
        answers.unsat(),
        answers.certified,
        answers.unanswered
    );
    assert!(answers.unsat() > 0, "the solver answered no lemma");
}

/// The obligation of every accepted rewrite: the solver refutes none, and
/// refutes the obligation of a rewrite outside its premises.
#[test]
fn rewrite_obligations_are_not_refuted_and_their_controls_are() {
    let mut obligations = Vec::new();
    let src = module(&masked(63));
    let PassWitness::Range(w) = witness(
        vec![rewrite(
            0,
            3,
            RangeRule::ICmp,
            &[premise(2, 0, 63), premise(3, 64, 64)],
        )],
        &[],
    ) else {
        unreachable!()
    };
    obligations.extend(range_obligations(32, func(&src, "f"), &w).expect("encodes"));
    let src = module(FLAGS);
    let PassWitness::Range(w) = witness(flags_rewrites(false), &[2]) else {
        unreachable!()
    };
    obligations.extend(range_obligations(32, func(&src, "f"), &w).expect("encodes"));
    let src = module(ROWS);
    let PassWitness::Range(w) = witness(
        vec![
            rewrite(
                0,
                20,
                RangeRule::ICmp,
                &[premise(21, 0, 255), premise(22, 0xffff_ffff, 0xffff_ffff)],
            ),
            rewrite(
                0,
                24,
                RangeRule::ICmp,
                &[premise(25, 0, 255), premise(26, 256, 256)],
            ),
        ],
        &[],
    ) else {
        unreachable!()
    };
    obligations.extend(range_obligations(32, func(&src, "f"), &w).expect("encodes"));
    assert_eq!(obligations.len(), 8);
    let mut answers = Answers::default();
    for obligation in &obligations {
        answers.record(&obligation.name, verify_with_ay(obligation, &ay()));
    }
    eprintln!(
        "range rewrite obligations: {} UNSAT ({} certified), unanswered: {:#?}",
        answers.unsat(),
        answers.certified,
        answers.unanswered
    );
    assert!(answers.unsat() > 0, "the solver answered no obligation");

    // The overflow rule claimed on operands that may overflow, and a select
    // claimed on an undecided condition.
    let m = 65535u128;
    let (src, _, w) = overflow_case(
        "mul",
        "u32",
        (0, 3),
        RangeRule::MulOverflow,
        BinOp::Mul,
        [(0, m), (3, m + 3)],
    );
    let PassWitness::Range(w) = w else {
        unreachable!()
    };
    let mut controls = range_obligations(32, func(&src, "f"), &w).expect("encodes");
    let src = module(FLAGS);
    let PassWitness::Range(w) = witness(
        vec![rewrite(0, 4, RangeRule::Select, &[premise(5, 0, 1)])],
        &[],
    ) else {
        unreachable!()
    };
    controls.extend(range_obligations(32, func(&src, "f"), &w).expect("encodes"));
    for control in &controls {
        refuted(control);
    }
}

#[test]
fn the_rules_name_their_evidence() {
    let names: Vec<&str> = RangeRule::ALL.iter().map(|r| r.as_str()).collect();
    assert_eq!(
        names,
        [
            "icmp",
            "add_overflow",
            "sub_overflow",
            "mul_overflow",
            "select",
            "assert",
            "condbr",
            "icmp_implied",
            "switch"
        ]
    );
}

// ---------------------------------------------------------------------------
// Dominating conditions, implied compares, invariants and switch
// ---------------------------------------------------------------------------

fn witness_with(
    rewrites: Vec<RangeRewrite>,
    removed: &[u32],
    invariants: &[(u32, u32, u128, u128)],
) -> PassWitness {
    PassWitness::Range(RangeWitness {
        rewrites,
        removed_blocks: removed.iter().map(|&n| b(n)).collect(),
        invariants: invariants
            .iter()
            .map(|&(block, param, lo, hi)| RangeInvariant {
                block: b(block),
                param: v(param),
                lo,
                hi,
            })
            .collect(),
    })
}

/// `x < 10` on the edge into `bb1` (and `x >= 10` into `bb2`); `bb3` joins
/// both. Each block compares `x < 16` at index 1.
const GUARDED: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 10\n\
    \x20   %2 = icmp ult u32 %0, %1\n\
    \x20   condbr %2, bb1, bb2\n\
    bb1:\n\
    \x20   %3 = const u32 16\n\
    \x20   %4 = icmp ult u32 %0, %3\n\
    \x20   br bb3(%4)\n\
    bb2:\n\
    \x20   %5 = const u32 16\n\
    \x20   %6 = icmp ult u32 %0, %5\n\
    \x20   br bb3(%6)\n\
    bb3(%7: bool):\n\
    \x20   %8 = const u32 16\n\
    \x20   %9 = icmp ult u32 %0, %8\n\
    \x20   %10 = zext bool %7 to u32\n\
    \x20   %11 = zext bool %9 to u32\n\
    \x20   %12 = add u32 %10, %11\n\
    \x20   ret %12\n\
    }\n";

#[test]
fn a_guard_bounds_a_value_in_the_blocks_its_edge_dominates() {
    let src = module(GUARDED);
    let f = func(&src, "f");
    let target = with(f, 1, 1, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(
            1,
            1,
            RangeRule::ICmp,
            &[premise(0, 0, 9), premise(3, 16, 16)],
        )],
        &[],
    );
    check_pass(&src, 32, f, &target, &w).expect("x < 10 decides x < 16");
    agree(&src, f, &target);
}

#[test]
fn negative_control_a_fact_used_across_a_join_is_refused() {
    let src = module(GUARDED);
    let f = func(&src, "f");
    let target = with(f, 3, 1, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(
            3,
            1,
            RangeRule::ICmp,
            &[premise(0, 0, 9), premise(8, 16, 16)],
        )],
        &[],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(
        matches!(err, MidTvError::RangePremise { derived: None, .. }),
        "{err}"
    );
}

#[test]
fn negative_control_a_guard_that_does_not_dominate_is_refused() {
    // `bb2` is entered by the other edge: there `x >= 10`.
    let src = module(GUARDED);
    let f = func(&src, "f");
    let target = with(f, 2, 1, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(
            2,
            1,
            RangeRule::ICmp,
            &[premise(0, 0, 9), premise(5, 16, 16)],
        )],
        &[],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(
        matches!(
            err,
            MidTvError::RangePremise {
                derived: Some((10, 0xffff_ffff)),
                ..
            }
        ),
        "{err}"
    );
}

/// `a < b` and its two edges.
const IMPLIED: &str = "functy.0 = (u32, u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32, %1: u32):\n\
    \x20   %2 = icmp ult u32 %0, %1\n\
    \x20   condbr %2, bb1, bb2\n\
    bb1:\n\
    \x20   %3 = icmp ugt u32 %1, %0\n\
    \x20   %4 = zext bool %3 to u32\n\
    \x20   ret %4\n\
    bb2:\n\
    \x20   %5 = icmp ult u32 %0, %1\n\
    \x20   %6 = icmp eq u32 %0, %1\n\
    \x20   %7 = zext bool %5 to u32\n\
    \x20   %8 = zext bool %6 to u32\n\
    \x20   %9 = add u32 %7, %8\n\
    \x20   ret %9\n\
    }\n";

#[test]
fn a_dominating_compare_decides_one_of_the_same_operands() {
    let src = module(IMPLIED);
    let f = func(&src, "f");
    let target = with(
        &with(f, 1, 0, vec![bool_const(true)]),
        2,
        0,
        vec![bool_const(false)],
    );
    let w = witness(
        vec![
            rewrite(1, 0, RangeRule::ICmpImplied, &[]),
            rewrite(2, 0, RangeRule::ICmpImplied, &[]),
        ],
        &[],
    );
    check_pass(&src, 32, f, &target, &w).expect("a < b decides b > a, and a >= b decides a < b");
    agree(&src, f, &target);
}

#[test]
fn negative_controls_of_the_implied_compare() {
    let src = module(IMPLIED);
    let f = func(&src, "f");
    // `a >= b` does not decide `a == b`.
    let target = with(f, 2, 1, vec![bool_const(false)]);
    let w = witness(vec![rewrite(2, 1, RangeRule::ICmpImplied, &[])], &[]);
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    undecided_because(&err, "no dominating compare decides the compare");
    // The wrong constant.
    let target = with(f, 1, 0, vec![bool_const(false)]);
    let w = witness(vec![rewrite(1, 0, RangeRule::ICmpImplied, &[])], &[]);
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::TargetDiffers { .. }), "{err}");
    // Premises the rule does not read.
    let target = with(f, 1, 0, vec![bool_const(true)]);
    let w = witness(
        vec![rewrite(1, 0, RangeRule::ICmpImplied, &[premise(0, 0, 1)])],
        &[],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    undecided_because(&err, "the premises do not name the rule's operands");
}

/// A counted loop `for i in 0..(x & 15)` whose exit block compares `i <
/// 17`: only the induction range `[0, 15]` decides it. `wrap` counts while
/// `i <= x` for an unknown `x`: its step may wrap.
const COUNTED: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 15\n\
    \x20   %2 = and u32 %0, %1\n\
    \x20   %3 = const u32 0\n\
    \x20   br bb1(%3)\n\
    bb1(%4: u32):\n\
    \x20   %5 = icmp ult u32 %4, %2\n\
    \x20   condbr %5, bb2, bb3\n\
    bb2:\n\
    \x20   %6 = const u32 1\n\
    \x20   %7 = add u32 %4, %6\n\
    \x20   br bb1(%7)\n\
    bb3:\n\
    \x20   %10 = const u32 17\n\
    \x20   %11 = icmp ult u32 %4, %10\n\
    \x20   %12 = zext bool %11 to u32\n\
    \x20   ret %12\n\
    }\n\n\
    fn @wrap(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %3 = const u32 0\n\
    \x20   br bb1(%3)\n\
    bb1(%4: u32):\n\
    \x20   %5 = icmp ule u32 %4, %0\n\
    \x20   condbr %5, bb2, bb3\n\
    bb2:\n\
    \x20   %6 = const u32 1\n\
    \x20   %7 = add u32 %4, %6\n\
    \x20   %8 = const u32 4\n\
    \x20   %9 = icmp ult u32 %0, %8\n\
    \x20   condbr %9, bb1(%7), bb3\n\
    bb3:\n\
    \x20   %10 = const u32 17\n\
    \x20   %11 = icmp ult u32 %4, %10\n\
    \x20   %12 = zext bool %11 to u32\n\
    \x20   ret %12\n\
    }\n";

fn exit_compare(name: &str, invariant: (u128, u128)) -> (Module, Function, PassWitness) {
    let src = module(COUNTED);
    let f = func(&src, name).clone();
    let target = with(&f, 3, 1, vec![bool_const(true)]);
    let w = witness_with(
        vec![rewrite(
            3,
            1,
            RangeRule::ICmp,
            &[premise(4, invariant.0, invariant.1), premise(10, 17, 17)],
        )],
        &[],
        &[(1, 4, invariant.0, invariant.1)],
    );
    (src, target, w)
}

#[test]
fn an_induction_range_holds_at_entry_and_after_the_step() {
    let (src, target, w) = exit_compare("f", (0, 15));
    let f = func(&src, "f");
    check_pass(&src, 32, f, &target, &w).expect("i stays in [0, 15]");
    agree(&src, f, &target);
    // Without the invariant the exit edge's `i >= n` leaves `i` anywhere.
    let PassWitness::Range(mut bare) = w else {
        unreachable!()
    };
    bare.invariants.clear();
    let err = check_pass(&src, 32, f, &target, &PassWitness::Range(bare)).unwrap_err();
    assert!(
        matches!(
            err,
            MidTvError::RangePremise {
                derived: Some((0, 0xffff_ffff)),
                ..
            }
        ),
        "{err}"
    );
}

fn invariant_because(err: &MidTvError, expected: &str) {
    match err {
        MidTvError::RangeInvariant { why, .. } => assert_eq!(*why, expected, "{err}"),
        other => panic!("expected a refused invariant, got {other}"),
    }
}

#[test]
fn negative_control_an_invariant_the_step_leaves_is_refused() {
    // The back edge passes `i + 1` in `[1, 15]`.
    let (src, target, w) = exit_compare("f", (0, 14));
    let err = check_pass(&src, 32, func(&src, "f"), &target, &w).unwrap_err();
    invariant_because(&err, "an edge passes an argument outside the interval");
    // The entry passes 0.
    let (src, target, w) = exit_compare("f", (1, 15));
    let err = check_pass(&src, 32, func(&src, "f"), &target, &w).unwrap_err();
    invariant_because(&err, "an edge passes an argument outside the interval");
}

#[test]
fn negative_control_a_step_that_can_wrap_is_refused() {
    // Under `i <= x` with `x` unknown, `i` may be `u32::MAX`, and `i + 1`
    // wraps: it has no interval, so no claim on `i` closes.
    let (src, target, w) = exit_compare("wrap", (0, 0xffff_ffff));
    let err = check_pass(&src, 32, func(&src, "wrap"), &target, &w).unwrap_err();
    invariant_because(&err, "an argument has no interval");
    // A narrower claim is broken by the step itself.
    let (src, target, w) = exit_compare("wrap", (0, 15));
    let err = check_pass(&src, 32, func(&src, "wrap"), &target, &w).unwrap_err();
    invariant_because(&err, "an edge passes an argument outside the interval");
}

#[test]
fn negative_control_a_malformed_invariant_is_refused() {
    let src = module(COUNTED);
    let f = func(&src, "f");
    for (claim, why) in [
        ((0, 0, 0, 15), "the block is the entry or unreachable"),
        ((1, 2, 0, 15), "the value is not a parameter of the block"),
        (
            (1, 4, 0, 1u128 << 40),
            "the interval is empty or outside the type",
        ),
        ((1, 4, 9, 3), "the interval is empty or outside the type"),
    ] {
        let w = witness_with(Vec::new(), &[], &[claim]);
        let err = check_pass(&src, 32, f, f, &w).unwrap_err();
        invariant_because(&err, why);
    }
    let w = witness_with(Vec::new(), &[], &[(1, 4, 0, 15), (1, 4, 0, 15)]);
    let err = check_pass(&src, 32, f, f, &w).unwrap_err();
    invariant_because(&err, "the parameter is claimed twice or defined twice");
}

/// A `switch` on `x & 1` with cases 0 and 1 and a default.
const SWITCHED: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 1\n\
    \x20   %2 = and u32 %0, %1\n\
    \x20   switch %2 [ 0: bb1 1: bb2 default: bb3 ]\n\
    bb1:\n\
    \x20   %3 = const u32 10\n\
    \x20   ret %3\n\
    bb2:\n\
    \x20   %4 = const u32 20\n\
    \x20   ret %4\n\
    bb3:\n\
    \x20   %5 = const u32 30\n\
    \x20   ret %5\n\
    }\n";

fn switch_target(src: &Function, last: Inst, removed: &[u32]) -> Function {
    let mut out = with(src, 0, 2, vec![last]);
    out.blocks.retain(|blk| !removed.contains(&blk.id.index()));
    out
}

fn switch_to(cases: &[(i128, u32)], default: u32) -> Inst {
    Inst::Switch {
        value: v(2),
        default: b(default),
        default_args: Vec::new(),
        cases: cases
            .iter()
            .map(|&(c, t)| trust_ir::SwitchCase {
                value: Constant::Int(c),
                target: b(t),
                args: Vec::new(),
            })
            .collect(),
        exhaustive_enum_unreachable: false,
    }
}

#[test]
fn a_switch_covering_its_interval_loses_its_default() {
    let src = module(SWITCHED);
    let f = func(&src, "f");
    let target = switch_target(f, switch_to(&[(0, 1)], 2), &[3]);
    let w = witness(
        vec![rewrite(0, 2, RangeRule::Switch, &[premise(2, 0, 1)])],
        &[3],
    );
    check_pass(&src, 32, f, &target, &w).expect("[0, 1] covers both cases");
    agree(&src, f, &target);
}

#[test]
fn negative_controls_of_the_switch_rule() {
    let src = module(SWITCHED);
    let f = func(&src, "f");
    // A case inside the interval dropped.
    let target = switch_target(
        f,
        Inst::Br {
            target: b(1),
            args: Vec::new(),
        },
        &[2, 3],
    );
    let w = witness(
        vec![rewrite(0, 2, RangeRule::Switch, &[premise(2, 0, 1)])],
        &[2, 3],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(
        matches!(
            err,
            MidTvError::TargetDiffers { .. } | MidTvError::ReachableBlockRemoved { .. }
        ),
        "{err}"
    );
    // A premise narrower than the fact.
    let w = witness(
        vec![rewrite(0, 2, RangeRule::Switch, &[premise(2, 0, 0)])],
        &[2, 3],
    );
    let err = check_pass(&src, 32, f, &target, &w).unwrap_err();
    assert!(matches!(err, MidTvError::RangePremise { .. }), "{err}");
    // An interval that excludes nothing.
    let w = witness(
        vec![rewrite(0, 2, RangeRule::Switch, &[premise(2, 0, 7)])],
        &[],
    );
    let err = check_pass(&src, 32, f, f, &w).unwrap_err();
    undecided_because(&err, "the interval excludes no case and not the default");
}

// ---------------------------------------------------------------------------
// The guard and implication decisions against brute force
// ---------------------------------------------------------------------------

const PREDICATES: [ICmpOp; 10] = [
    ICmpOp::Eq,
    ICmpOp::Ne,
    ICmpOp::Ult,
    ICmpOp::Ule,
    ICmpOp::Ugt,
    ICmpOp::Uge,
    ICmpOp::Slt,
    ICmpOp::Sle,
    ICmpOp::Sgt,
    ICmpOp::Sge,
];

/// The checker's narrowing of every pair of intervals at widths 1 to 4, for
/// every predicate, is the hull of each side's values that have a partner
/// (exact; a signed predicate at one bit narrows nothing, which is sound).
#[test]
fn the_guard_narrowing_is_the_exact_hull_at_small_widths() {
    let mut checked = 0usize;
    for bits in 1..=4u32 {
        for op in PREDICATES {
            let signed_op = matches!(op, ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge);
            for a in intervals(bits) {
                for bb in intervals(bits) {
                    let mut xs: Option<(u128, u128)> = None;
                    let mut ys: Option<(u128, u128)> = None;
                    for x in a.lo..=a.hi {
                        for y in bb.lo..=bb.hi {
                            if icmp_brute(op, bits, x, y) {
                                xs = Some(xs.map_or((x, x), |(l, h)| (l.min(x), h.max(x))));
                                ys = Some(ys.map_or((y, y), |(l, h)| (l.min(y), h.max(y))));
                            }
                        }
                    }
                    let got = narrow_by(op, a, bb).map(|(x, y)| ((x.lo, x.hi), (y.lo, y.hi)));
                    if signed_op && bits == 1 {
                        assert_eq!(got, Some(((a.lo, a.hi), (bb.lo, bb.hi))));
                    } else {
                        assert_eq!(got, xs.zip(ys), "{op:?} at {bits} bits: {a:?} {bb:?}");
                    }
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 20_000, "{checked}");
}

/// The implication agrees with brute force: sound at widths 1 to 4, and
/// complete at widths 2 to 4.
#[test]
fn the_implication_agrees_with_brute_force_at_small_widths() {
    for bits in 1..=4u32 {
        let top = mask(bits);
        for known in PREDICATES {
            for query in PREDICATES {
                for swapped in [false, true] {
                    let mut outcomes = BTreeSet::new();
                    for x in 0..=top {
                        for y in 0..=top {
                            let holds = if swapped {
                                icmp_brute(known, bits, y, x)
                            } else {
                                icmp_brute(known, bits, x, y)
                            };
                            if holds {
                                outcomes.insert(icmp_brute(query, bits, x, y));
                            }
                        }
                    }
                    let got = implication(known, query, swapped);
                    if let Some(c) = got {
                        assert!(
                            outcomes.iter().all(|&o| o == c),
                            "{known:?} {query:?} {swapped} at {bits} bits"
                        );
                    }
                    if bits >= 2 && outcomes.len() == 1 {
                        assert_eq!(
                            got,
                            outcomes.first().copied(),
                            "{known:?} {query:?} {swapped}"
                        );
                    }
                }
            }
        }
    }
}

/// The obligations of the implied compares and the switch: the solver
/// refutes none, and refutes each one with its precondition dropped.
#[test]
fn the_implied_and_switch_obligations_are_not_refuted_and_their_controls_are() {
    let mut obligations = Vec::new();
    let src = module(IMPLIED);
    let PassWitness::Range(w) = witness(
        vec![
            rewrite(1, 0, RangeRule::ICmpImplied, &[]),
            rewrite(2, 0, RangeRule::ICmpImplied, &[]),
        ],
        &[],
    ) else {
        unreachable!()
    };
    obligations.extend(range_obligations(32, func(&src, "f"), &w).expect("encodes"));
    let src = module(SWITCHED);
    let PassWitness::Range(w) = witness(
        vec![rewrite(0, 2, RangeRule::Switch, &[premise(2, 0, 1)])],
        &[3],
    ) else {
        unreachable!()
    };
    obligations.extend(range_obligations(32, func(&src, "f"), &w).expect("encodes"));
    assert_eq!(obligations.len(), 3);
    let config = VerificationConfig::default();
    let mut answers = Answers::default();
    for obligation in &obligations {
        assert!(
            !matches!(
                verify_by_evaluation_with_config(obligation, &config),
                VerificationResult::Invalid { .. }
            ),
            "{}",
            obligation.name
        );
        answers.record(&obligation.name, verify_with_ay(obligation, &ay()));
        let mut control = obligation.clone();
        control.preconditions.clear();
        refuted(&control);
    }
    eprintln!(
        "implied and switch obligations: {} UNSAT ({} certified), unanswered: {:#?}",
        answers.unsat(),
        answers.certified,
        answers.unanswered
    );
}

/// The guard index, its members added in an order where each block's
/// dominators come first, lists exactly the members on a block's dominator
/// path, nearest first, on every tree of up to seven nodes and every member
/// set and block; the dominance test agrees with the parent walk.
#[test]
fn the_guard_index_agrees_with_the_dominator_path_on_small_trees() {
    fn trees(n: usize) -> Vec<Vec<usize>> {
        let mut out = vec![vec![0]];
        for i in 1..n {
            let mut next = Vec::new();
            for t in &out {
                for p in 0..i {
                    let mut t = t.clone();
                    t.push(p);
                    next.push(t);
                }
            }
            out = next;
        }
        out
    }
    let path = |idom: &[usize], mut b: usize| {
        let mut up = vec![b];
        while b != 0 {
            b = idom[b];
            up.push(b);
        }
        up
    };
    let mut cases = 0usize;
    for n in 1..=7 {
        for idom in trees(n) {
            let order: Vec<usize> = (0..n).collect();
            let tree = tree_numbers(&order, &idom, 0);
            for a in 0..n {
                for b in 0..n {
                    assert_eq!(dominates(&tree, a, b), path(&idom, b).contains(&a));
                }
            }
            for mask in 0u32..(1 << n) {
                let mut index = GuardIndex::default();
                for m in (0..n).filter(|i| mask & (1 << i) != 0) {
                    index.add(&tree, m);
                }
                for at in 0..n {
                    let expected: Vec<usize> = path(&idom, at)
                        .into_iter()
                        .filter(|b| mask & (1 << b) != 0)
                        .collect();
                    let listed: Vec<usize> = index.over(&tree, at).collect();
                    assert_eq!(listed, expected, "idom {idom:?}, mask {mask:#b}, at {at}");
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 695_482);
}
