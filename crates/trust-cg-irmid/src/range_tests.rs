// trust-cg-irmid/range_tests.rs - the range rules' path-sensitive facts
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The range rules' facts from dominating branches, block-parameter
//! invariants (loop induction ranges) and `switch` folding: each fold is
//! made where its fact holds and kept by the checker and the interpreter
//! differential; a fact is not used across a join another edge reaches, a
//! step that can wrap gets no induction range, and a lying pass (an
//! invariant an edge breaks, a case inside the interval dropped) is rolled
//! back and counted. The refinement and implication decisions agree with
//! brute force at small widths, the guard index lists the dominator-path
//! guards of every block of every small tree, and functions of some 3,600
//! blocks with deep guard chains fold and check within a time bound. The
//! witness types this reads (`RangeWitness::invariants`, `RangeInvariant`,
//! the `icmp_implied` and `switch` rules) are provisional surfaces pending
//! the owner's sign-off.

use trust_cg_verify::trust_ir_mid_tv::{
    PassWitness, RangeInvariant, RangeRewrite, RangeRule, RangeWitness,
};
use trust_ir::{BlockId, Constant, Function, ICmpOp, Inst, Module, ValueId};

use crate::manager;
use crate::passes::range::{RANGE_SOURCES, RangeSources, decisions};
use crate::passes::{self, MidPass, PassContext};
use crate::{IrmidReport, MidConfig, PassStats, optimize_module};

const HEADER: &str = "; TrustIr text format v1\nmodule \"irmid\"\n\
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

fn insts(func: &Function) -> Vec<&Inst> {
    func.blocks
        .iter()
        .flat_map(|b| &b.body)
        .map(|n| &n.inst)
        .collect()
}

fn range_stats(report: &IrmidReport) -> PassStats {
    report
        .passes
        .iter()
        .find(|p| p.name == "range")
        .cloned()
        .unwrap_or_default()
}

/// The range pass alone on `name`, with `sources` on this thread.
fn range_with(sources: RangeSources, m: &Module, name: &str) -> Option<RangeWitness> {
    RANGE_SOURCES.with(|s| s.set(sources));
    let cx = PassContext {
        module: m,
        pointer_bits: 32,
    };
    let out = passes::RangeRules.run(&cx, func(m, name));
    RANGE_SOURCES.with(|s| s.set(RangeSources::ALL));
    out.map(|(_, w)| match w {
        PassWitness::Range(w) => w,
        _ => panic!("range witness"),
    })
}

fn rules(w: &Option<RangeWitness>, rule: &str) -> usize {
    w.as_ref()
        .and_then(|w| w.counts().get(rule).copied())
        .unwrap_or(0)
}

const NONE: RangeSources = RangeSources {
    guards: false,
    invariants: false,
    switch: false,
};

/// The optimized module, with no rollback and the differential run.
fn optimized(m: &Module) -> (Module, IrmidReport) {
    let (out, report) = optimize_module(m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.tv.samples_compared > 0, "{:?}", report.tv);
    (out, report)
}

// ---------------------------------------------------------------------------
// Dominating conditions
// ---------------------------------------------------------------------------

/// `x < 10` guards a block whose bounds check `x < 16` it decides; a block
/// both edges reach (`join`) keeps the same check.
const GUARDS: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @guard(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 10\n\
    \x20   %2 = icmp ult u32 %0, %1\n\
    \x20   condbr %2, bb1, bb3\n\
    bb1:\n\
    \x20   %3 = const u32 16\n\
    \x20   %4 = icmp ult u32 %0, %3\n\
    \x20   condbr %4, bb2, bb4\n\
    bb2:\n\
    \x20   %5 = const u32 3\n\
    \x20   %6 = mul u32 %0, %5\n\
    \x20   ret %6\n\
    bb4:\n\
    \x20   %7 = const u32 99\n\
    \x20   ret %7\n\
    bb3:\n\
    \x20   %8 = const u32 0\n\
    \x20   ret %8\n\
    }\n\n\
    fn @join(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 10\n\
    \x20   %2 = icmp ult u32 %0, %1\n\
    \x20   condbr %2, bb1, bb2\n\
    bb1:\n\
    \x20   br bb2\n\
    bb2:\n\
    \x20   %3 = const u32 16\n\
    \x20   %4 = icmp ult u32 %0, %3\n\
    \x20   condbr %4, bb3, bb4\n\
    bb3:\n\
    \x20   ret %0\n\
    bb4:\n\
    \x20   %5 = const u32 99\n\
    \x20   ret %5\n\
    }\n";

#[test]
fn a_dominating_check_decides_a_bounds_check_and_its_panic_arm_goes() {
    let m = module(GUARDS);
    let w = range_with(RangeSources::ALL, &m, "guard");
    assert_eq!(rules(&w, "icmp"), 1, "{w:?}");
    assert_eq!(rules(&w, "condbr"), 1, "{w:?}");
    assert_eq!(rules(&w, "removed_block"), 1, "{w:?}");
    // Without the guard's facts nothing decides it.
    assert!(range_with(NONE, &m, "guard").is_none());

    let (out, report) = optimized(&m);
    let stats = range_stats(&report);
    assert_eq!(stats.rules.get("icmp"), Some(&1), "{stats:?}");
    let f = func(&out, "guard");
    assert_eq!(
        insts(f)
            .iter()
            .filter(|i| matches!(i, Inst::CondBr { .. }))
            .count(),
        1,
        "only the guard is left: {f:#?}"
    );
}

#[test]
fn negative_control_a_fact_is_not_used_across_a_join() {
    let m = module(GUARDS);
    assert!(range_with(RangeSources::ALL, &m, "join").is_none());
    let (out, _) = optimized(&m);
    assert_eq!(
        insts(func(&out, "join"))
            .iter()
            .filter(|i| matches!(i, Inst::CondBr { .. }))
            .count(),
        2
    );
}

/// `a < b` decides `a <= b` and `b > a` below it, and `a == b` on its
/// `false` edge.
const IMPLIED: &str = "functy.0 = (u32, u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32, %1: u32):\n\
    \x20   %2 = icmp ult u32 %0, %1\n\
    \x20   condbr %2, bb1, bb3\n\
    bb1:\n\
    \x20   %3 = icmp ule u32 %0, %1\n\
    \x20   %4 = icmp ugt u32 %1, %0\n\
    \x20   condbr %3, bb2, bb4\n\
    bb2:\n\
    \x20   %6 = sub u32 %1, %0\n\
    \x20   %5 = zext bool %4 to u32\n\
    \x20   %10 = add u32 %6, %5\n\
    \x20   ret %10\n\
    bb4:\n\
    \x20   %7 = const u32 7\n\
    \x20   ret %7\n\
    bb3:\n\
    \x20   %8 = icmp eq u32 %1, %0\n\
    \x20   %9 = zext bool %8 to u32\n\
    \x20   ret %9\n\
    }\n";

#[test]
fn a_dominating_compare_decides_the_same_operands_compare() {
    let m = module(IMPLIED);
    let w = range_with(RangeSources::ALL, &m, "f").expect("implied compares");
    // `ule` and `ugt` below the true edge; `eq` is not decided on the
    // false edge (`a >= b` allows `a == b`).
    assert_eq!(w.counts().get("icmp_implied"), Some(&2), "{w:?}");
    assert_eq!(w.counts().get("condbr"), Some(&1), "{w:?}");
    let (out, report) = optimized(&m);
    assert_eq!(
        range_stats(&report).rules.get("icmp_implied"),
        Some(&2),
        "{:?}",
        range_stats(&report)
    );
    assert_eq!(
        func(&out, "f").blocks.len(),
        3,
        "the `false` arm is gone, a lone successor merged"
    );
}

// ---------------------------------------------------------------------------
// Loop induction ranges
// ---------------------------------------------------------------------------

/// A 4 x 4 nest in the bridge's shape (k10_matrix's `matmul4`): the inner
/// header carries the outer index as a parameter, and the bounds check of
/// `i * 4 + k < 16` needs both induction ranges; the outer step's overflow
/// check needs the guard.
const NEST: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @nest(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 0\n\
    \x20   br bb1(%1, %0)\n\
    bb1(%2: u32, %3: u32):\n\
    \x20   %4 = const u32 4\n\
    \x20   %5 = icmp ult u32 %2, %4\n\
    \x20   condbr %5, bb2, bb7\n\
    bb2:\n\
    \x20   %6 = const u32 1\n\
    \x20   %7, %30 = add.overflow u32 %2, %6\n\
    \x20   condbr %30, bb9, bb10\n\
    bb10:\n\
    \x20   %8 = const u32 0\n\
    \x20   br bb3(%2, %8, %3)\n\
    bb3(%20: u32, %9: u32, %10: u32):\n\
    \x20   %11 = const u32 4\n\
    \x20   %12 = icmp ult u32 %9, %11\n\
    \x20   condbr %12, bb4, bb6\n\
    bb4:\n\
    \x20   %13 = const u32 4\n\
    \x20   %14 = mul u32 %20, %13\n\
    \x20   %15 = add u32 %14, %9\n\
    \x20   %16 = const u32 16\n\
    \x20   %17 = icmp ult u32 %15, %16\n\
    \x20   condbr %17, bb5, bb8\n\
    bb5:\n\
    \x20   %18 = mul u32 %10, %16\n\
    \x20   %19 = add u32 %18, %15\n\
    \x20   %21 = const u32 1\n\
    \x20   %22 = add u32 %9, %21\n\
    \x20   br bb3(%20, %22, %19)\n\
    bb6:\n\
    \x20   br bb1(%7, %10)\n\
    bb7:\n\
    \x20   ret %3\n\
    bb8:\n\
    \x20   %23 = const u32 99999\n\
    \x20   ret %23\n\
    bb9:\n\
    \x20   %24 = const u32 88888\n\
    \x20   ret %24\n\
    }\n";

#[test]
fn induction_ranges_decide_a_nested_bounds_check() {
    let m = module(NEST);
    let all = range_with(RangeSources::ALL, &m, "nest").expect("folds");
    assert_eq!(rules(&Some(all.clone()), "icmp"), 1, "{all:?}");
    assert_eq!(rules(&Some(all.clone()), "add_overflow"), 1, "{all:?}");
    assert_eq!(rules(&Some(all.clone()), "condbr"), 2, "{all:?}");
    assert_eq!(rules(&Some(all.clone()), "removed_block"), 2, "{all:?}");
    let claimed = |v: u32| {
        all.invariants
            .iter()
            .find(|i| i.param == ValueId::new(v))
            .map(|i| (i.lo, i.hi))
    };
    assert_eq!(claimed(2), Some((0, 4)), "outer index: {all:?}");
    assert_eq!(claimed(20), Some((0, 3)), "the outer index carried inward");
    assert_eq!(claimed(9), Some((0, 4)), "inner index");
    // The guard alone decides the overflow, not the bounds check.
    let guards_only = range_with(
        RangeSources {
            invariants: false,
            ..RangeSources::ALL
        },
        &m,
        "nest",
    );
    assert_eq!(rules(&guards_only, "add_overflow"), 1, "{guards_only:?}");
    assert_eq!(rules(&guards_only, "icmp"), 0, "{guards_only:?}");

    let (out, report) = optimized(&m);
    let stats = range_stats(&report);
    assert_eq!(stats.rules.get("icmp"), Some(&1), "{stats:?}");
    let f = func(&out, "nest");
    assert!(
        !insts(f).iter().any(|i| matches!(i, Inst::Overflow { .. })),
        "{f:#?}"
    );
    // With the bounds check gone both loops have constant trip counts, and
    // full unrolling replaces them with their iterations.
    assert_eq!(
        insts(f)
            .iter()
            .filter(|i| matches!(i, Inst::CondBr { .. }))
            .count(),
        0,
        "the two loop tests are unrolled away: {f:#?}"
    );
    let unroll = report.passes.iter().find(|p| p.name == "unroll").unwrap();
    assert_eq!(unroll.functions_changed, 1, "{unroll:?}");
}

/// A signed counter `i < n` with `n` in `[0, 100]`: the guard bounds `i`
/// only once the induction range says it is non-negative, and then decides
/// the step's signed overflow.
const SIGNED: &str = "functy.0 = (i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = const i32 100\n\
    \x20   %2 = and i32 %0, %1\n\
    \x20   %3 = const i32 0\n\
    \x20   br bb1(%3)\n\
    bb1(%4: i32):\n\
    \x20   %5 = icmp slt i32 %4, %2\n\
    \x20   condbr %5, bb2, bb3\n\
    bb2:\n\
    \x20   %6 = const i32 1\n\
    \x20   %7, %8 = add.overflow i32 %4, %6\n\
    \x20   condbr %8, bb4, bb5\n\
    bb5:\n\
    \x20   br bb1(%7)\n\
    bb4:\n\
    \x20   %9 = const i32 -1\n\
    \x20   ret %9\n\
    bb3:\n\
    \x20   ret %4\n\
    }\n";

#[test]
fn a_signed_induction_range_decides_its_step() {
    let m = module(SIGNED);
    let w = range_with(RangeSources::ALL, &m, "f");
    assert_eq!(rules(&w, "add_overflow"), 1, "{w:?}");
    let without = range_with(
        RangeSources {
            invariants: false,
            ..RangeSources::ALL
        },
        &m,
        "f",
    );
    assert_eq!(rules(&without, "add_overflow"), 0, "{without:?}");
    let (out, _) = optimized(&m);
    assert!(
        !insts(func(&out, "f"))
            .iter()
            .any(|i| matches!(i, Inst::Overflow { .. }))
    );
}

/// `for i in 0..=n` with `n` unknown: `i + 1` can wrap, so the step keeps
/// its overflow check and `i` gets no interval below `u32::MAX + 1`.
const WRAPS: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 0\n\
    \x20   br bb1(%1)\n\
    bb1(%2: u32):\n\
    \x20   %3 = icmp ule u32 %2, %0\n\
    \x20   condbr %3, bb2, bb3\n\
    bb2:\n\
    \x20   %4 = const u32 1\n\
    \x20   %5, %6 = add.overflow u32 %2, %4\n\
    \x20   condbr %6, bb4, bb5\n\
    bb5:\n\
    \x20   %7 = const u32 3\n\
    \x20   %8 = icmp ult u32 %0, %7\n\
    \x20   condbr %8, bb1(%5), bb3\n\
    bb4:\n\
    \x20   %9 = const u32 77\n\
    \x20   ret %9\n\
    bb3:\n\
    \x20   ret %2\n\
    }\n";

#[test]
fn negative_control_a_step_that_can_wrap_keeps_its_check() {
    let m = module(WRAPS);
    let w = range_with(RangeSources::ALL, &m, "f");
    assert_eq!(rules(&w, "add_overflow"), 0, "{w:?}");
    let (out, _) = optimize_module(&m, &MidConfig::wasm32());
    assert!(
        insts(func(&out, "f"))
            .iter()
            .any(|i| matches!(i, Inst::Overflow { .. }))
    );
}

/// A pass that claims `i` of [`WRAPS`] stays in `[0, 3]` and folds the
/// overflow under it. Every execution keeps `i` there (the back edge is
/// taken only while `n < 3`), but the claim is not inductive on the facts:
/// under it the back edge passes `i + 1` in `[1, 4]`. The checker refuses
/// the invariant and the manager rolls the rewrite back.
struct LyingInvariant;

impl MidPass for LyingInvariant {
    fn name(&self) -> &'static str {
        "range"
    }

    fn run(&self, _cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let mut out = func.clone();
        let bb2 = out.blocks.iter().position(|b| b.id == BlockId::new(2))?;
        let node = out.blocks[bb2].body.get(1)?.clone();
        let Inst::Overflow { ty, lhs, rhs, .. } = node.inst.clone() else {
            return None;
        };
        let mut add = node.clone();
        add.inst = Inst::BinOp {
            op: trust_ir::BinOp::Add,
            ty,
            lhs,
            rhs,
        };
        add.results = vec![node.results[0]];
        let mut flag = node.clone();
        flag.inst = Inst::Const {
            ty: trust_ir::Ty::Bool,
            value: Constant::Bool(false),
        };
        flag.results = vec![node.results[1]];
        out.blocks[bb2].body.splice(1..=1, [add, flag]);
        let premise = |v: ValueId, lo, hi| trust_cg_verify::trust_ir_mid_tv::RangePremise {
            value: v,
            lo,
            hi,
        };
        let witness = RangeWitness {
            rewrites: vec![RangeRewrite {
                block: BlockId::new(2),
                index: 1,
                rule: RangeRule::AddOverflow,
                premises: vec![premise(lhs, 0, 3), premise(rhs, 1, 1)],
            }],
            removed_blocks: Vec::new(),
            invariants: vec![RangeInvariant {
                block: BlockId::new(1),
                param: ValueId::new(2),
                lo: 0,
                hi: 3,
            }],
        };
        Some((out, PassWitness::Range(witness)))
    }
}

#[test]
fn negative_control_an_invariant_an_edge_breaks_is_rolled_back() {
    let m = module(WRAPS);
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&LyingInvariant]);
    assert_eq!(out, m, "the snapshot stays");
    assert_eq!(report.rollback_count(), 1);
    let reason = &report.rollbacks[0].reason;
    assert!(
        reason.starts_with("witness:") && reason.contains("range invariant"),
        "{reason}"
    );
    let stats = range_stats(&report);
    assert_eq!(stats.rules_rolled_back.get("add_overflow"), Some(&1));
    assert_eq!(stats.rules_rolled_back.get("param_interval"), Some(&1));
}

// ---------------------------------------------------------------------------
// switch
// ---------------------------------------------------------------------------

const SWITCHES: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @two(functy.0) {\n\
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
    }\n\n\
    fn @narrow(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 3\n\
    \x20   %2 = and u32 %0, %1\n\
    \x20   switch %2 [ 0: bb1 5: bb2 7: bb2 default: bb3 ]\n\
    bb1:\n\
    \x20   %3 = const u32 10\n\
    \x20   ret %3\n\
    bb2:\n\
    \x20   %4 = const u32 20\n\
    \x20   ret %4\n\
    bb3:\n\
    \x20   ret %2\n\
    }\n\n\
    fn @decided(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 8\n\
    \x20   %2 = icmp ult u32 %0, %1\n\
    \x20   condbr %2, bb4, bb3\n\
    bb4:\n\
    \x20   %6 = const u32 2\n\
    \x20   %7 = lshr u32 %0, %6\n\
    \x20   %8 = const u32 1\n\
    \x20   %9 = add u32 %7, %8\n\
    \x20   switch %9 [ 0: bb1 5: bb2 default: bb3 ]\n\
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

#[test]
fn a_switch_drops_the_cases_and_the_default_its_interval_excludes() {
    let m = module(SWITCHES);
    for (name, removed) in [("two", 1), ("narrow", 1), ("decided", 2)] {
        let w = range_with(RangeSources::ALL, &m, name);
        assert_eq!(rules(&w, "switch"), 1, "{name}: {w:?}");
        assert_eq!(rules(&w, "removed_block"), removed, "{name}: {w:?}");
    }
    let (out, report) = optimized(&m);
    let stats = range_stats(&report);
    assert_eq!(stats.rules.get("switch"), Some(&3), "{stats:?}");
    let terminators = |name: &str| -> Vec<Inst> {
        func(&out, name)
            .blocks
            .iter()
            .filter_map(|b| b.body.last())
            .filter(|n| matches!(n.inst, Inst::Switch { .. } | Inst::Br { .. }))
            .map(|n| n.inst.clone())
            .collect()
    };
    // `two`: `[0, 1]` is covered, so case 1 becomes the default.
    let two = terminators("two");
    let [Inst::Switch { default, cases, .. }] = two.as_slice() else {
        panic!("{two:?}");
    };
    assert_eq!((*default, cases.len()), (BlockId::new(2), 1));
    // `narrow`: `[0, 3]` drops 5 and 7 and keeps the default.
    let narrow = terminators("narrow");
    let [Inst::Switch { default, cases, .. }] = narrow.as_slice() else {
        panic!("{narrow:?}");
    };
    assert_eq!((*default, cases.len()), (BlockId::new(3), 1));
    // `decided`: `x < 8` leaves `(x >> 2) + 1` in `[1, 2]`: only the
    // default.
    assert!(
        !insts(func(&out, "decided"))
            .iter()
            .any(|i| matches!(i, Inst::Switch { .. }))
    );
}

/// A pass that drops case `1` of `two`, inside the interval `[0, 1]`.
struct LyingSwitch;

impl MidPass for LyingSwitch {
    fn name(&self) -> &'static str {
        "range"
    }

    fn run(&self, _cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        if func.name != "two" {
            return None;
        }
        let mut out = func.clone();
        let last = out.blocks[0].body.last_mut()?;
        let Inst::Switch { value, cases, .. } = &mut last.inst else {
            return None;
        };
        cases.retain(|c| c.value != Constant::Int(1));
        let value = *value;
        let witness = RangeWitness {
            rewrites: vec![RangeRewrite {
                block: BlockId::new(0),
                index: 2,
                rule: RangeRule::Switch,
                premises: vec![trust_cg_verify::trust_ir_mid_tv::RangePremise {
                    value,
                    lo: 0,
                    hi: 1,
                }],
            }],
            removed_blocks: Vec::new(),
            invariants: Vec::new(),
        };
        Some((out, PassWitness::Range(witness)))
    }
}

#[test]
fn negative_control_a_case_inside_the_interval_dropped_is_rolled_back() {
    let m = module(SWITCHES);
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&LyingSwitch]);
    assert_eq!(out, m, "the snapshot stays");
    assert_eq!(report.rollback_count(), 1);
    assert!(
        report.rollbacks[0].reason.starts_with("witness:"),
        "{:?}",
        report.rollbacks
    );
    assert_eq!(
        range_stats(&report).rules_rolled_back.get("switch"),
        Some(&1)
    );
}

// ---------------------------------------------------------------------------
// The decisions against brute force
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

fn signed(raw: u128, bits: u32) -> i128 {
    if raw >= 1 << (bits - 1) {
        raw as i128 - (1i128 << bits)
    } else {
        raw as i128
    }
}

fn compare(op: ICmpOp, bits: u32, x: u128, y: u128) -> bool {
    let (sx, sy) = (signed(x, bits), signed(y, bits));
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

/// The refinement of every pair of intervals at widths 1 to 4, for every
/// predicate, is the hull of each side's values that have a partner (exact;
/// a signed predicate at one bit refines nothing, which is sound).
#[test]
fn the_refinement_is_the_exact_hull_at_small_widths() {
    let mut checked = 0usize;
    for bits in 1..=4u32 {
        let top = (1u128 << bits) - 1;
        let intervals: Vec<(u128, u128)> = (0..=top)
            .flat_map(|lo| (lo..=top).map(move |hi| (lo, hi)))
            .collect();
        for op in PREDICATES {
            let signed_op = matches!(op, ICmpOp::Slt | ICmpOp::Sle | ICmpOp::Sgt | ICmpOp::Sge);
            for &a in &intervals {
                for &b in &intervals {
                    let mut xs: Option<(u128, u128)> = None;
                    let mut ys: Option<(u128, u128)> = None;
                    for x in a.0..=a.1 {
                        for y in b.0..=b.1 {
                            if compare(op, bits, x, y) {
                                xs = Some(xs.map_or((x, x), |(l, h)| (l.min(x), h.max(x))));
                                ys = Some(ys.map_or((y, y), |(l, h)| (l.min(y), h.max(y))));
                            }
                        }
                    }
                    let got = decisions::refine(op, bits, a, b);
                    if signed_op && bits == 1 {
                        assert_eq!(got, Some((a, b)), "{op:?} at one bit");
                    } else {
                        let want = xs.zip(ys);
                        assert_eq!(got, want, "{op:?} {bits} bits on {a:?} {b:?}");
                    }
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 20_000, "{checked}");
}

/// The implication table agrees with brute force: sound at widths 1 to 4,
/// and it decides everything brute force decides at widths 2 to 4.
#[test]
fn the_implication_agrees_with_brute_force_at_small_widths() {
    for bits in 1..=4u32 {
        let top = 1u128 << bits;
        for known in PREDICATES {
            for query in PREDICATES {
                for swapped in [false, true] {
                    let mut outcomes = std::collections::BTreeSet::new();
                    for x in 0..top {
                        for y in 0..top {
                            let premise = if swapped {
                                compare(known, bits, y, x)
                            } else {
                                compare(known, bits, x, y)
                            };
                            if premise {
                                outcomes.insert(compare(query, bits, x, y));
                            }
                        }
                    }
                    let got = decisions::implied(known, query, swapped);
                    if let Some(c) = got {
                        assert!(
                            outcomes.iter().all(|&o| o == c),
                            "{known:?} {query:?} {swapped} at {bits} bits: {c} but {outcomes:?}"
                        );
                    }
                    if bits >= 2 && outcomes.len() == 1 {
                        assert_eq!(
                            got,
                            outcomes.iter().next().copied(),
                            "{known:?} {query:?} {swapped} at {bits} bits"
                        );
                    }
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Compile time on deep guard chains
// ---------------------------------------------------------------------------

/// `n` sequential early exits `if x * k == y { return x * k }`, each followed
/// by the bounds check `y & 63 < 64` with a panic arm: a guard chain `2n`
/// deep, every guard naming `y`.
fn sequential_guards(n: usize) -> String {
    let mut s = String::from(
        "functy.0 = (u32, u32) -> (u32)\n\nfn @seq(functy.0) {\n\
         bb0(%0: u32, %1: u32):\n    br bb1\n",
    );
    let (mut v, mut b) = (2, 1);
    for i in 0..n {
        let (test, exit, check, panic, next) = (b, b + 1, b + 2, b + 3, b + 4);
        let (k, m, c, c63, t, c64, u, p) = (v, v + 1, v + 2, v + 3, v + 4, v + 5, v + 6, v + 7);
        s += &format!(
            "bb{test}:\n    %{k} = const u32 {}\n    %{m} = mul u32 %0, %{k}\n    \
             %{c} = icmp eq u32 %{m}, %1\n    condbr %{c}, bb{exit}, bb{check}\n\
             bb{exit}:\n    ret %{m}\n\
             bb{check}:\n    %{c63} = const u32 63\n    %{t} = and u32 %1, %{c63}\n    \
             %{c64} = const u32 64\n    %{u} = icmp ult u32 %{t}, %{c64}\n    \
             condbr %{u}, bb{next}, bb{panic}\n\
             bb{panic}:\n    %{p} = const u32 7\n    ret %{p}\n",
            2 * i + 1
        );
        v += 8;
        b += 4;
    }
    s + &format!("bb{b}:\n    ret %0\n}}\n")
}

/// `n` nested tests `x + i > y`; below the nest, each level's join reads `y`
/// in the bounds check `y & 63 < 64`. The join's nearest dominating guard
/// naming `y` lies above a sibling subtree `n` guards deep, all naming `y`.
fn nested_guards(n: usize) -> String {
    let (join, cont, panic) = (100_000, 200_000, 300_000);
    let mut s = String::from(
        "functy.0 = (u32, u32) -> (u32)\n\nfn @deep(functy.0) {\n\
         bb0(%0: u32, %1: u32):\n    br bb1\n",
    );
    let mut v = 2;
    for i in 0..n {
        let (k, a, c) = (v, v + 1, v + 2);
        s += &format!(
            "bb{}:\n    %{k} = const u32 {i}\n    %{a} = add u32 %0, %{k}\n    \
             %{c} = icmp ugt u32 %{a}, %1\n    condbr %{c}, bb{}, bb{}(%{a})\n",
            1 + i,
            2 + i,
            join + i
        );
        v += 3;
    }
    s += &format!("bb{}:\n    br bb{}(%0)\n", 1 + n, join + n - 1);
    for i in (0..n).rev() {
        let (p, c63, t, c64, u) = (v, v + 1, v + 2, v + 3, v + 4);
        v += 5;
        let next = match i {
            0 => format!("ret %{p}"),
            _ => format!("br bb{}(%{p})", join + i - 1),
        };
        s += &format!(
            "bb{}(%{p}: u32):\n    %{c63} = const u32 63\n    %{t} = and u32 %1, %{c63}\n    \
             %{c64} = const u32 64\n    %{u} = icmp ult u32 %{t}, %{c64}\n    \
             condbr %{u}, bb{}, bb{}\nbb{}:\n    {next}\nbb{}:\n    ret %1\n",
            join + i,
            cont + i,
            panic + i,
            cont + i,
            panic + i
        );
    }
    s + "}\n"
}

/// A function of about 3,600 blocks with a guard chain 1,800 deep (or a
/// nest 900 deep whose joins read below it) is folded and checked in time
/// linear in its size: a fact or relation lookup does not walk the
/// dominator path. Each step has a bound some fifty times its debug-build
/// cost on an idle host; a lookup walking the chain took seconds per step.
#[test]
fn deep_guard_chains_are_folded_and_checked_without_walking_the_chain() {
    let bound = std::time::Duration::from_secs(10);
    for (name, text) in [
        ("seq", sequential_guards(900)),
        ("deep", nested_guards(900)),
    ] {
        let m = module(&text);
        let source = func(&m, name);
        assert!(source.blocks.len() > 3_000, "{}", source.blocks.len());
        let cx = PassContext {
            module: &m,
            pointer_bits: 32,
        };
        let start = std::time::Instant::now();
        let (target, witness) = passes::RangeRules.run(&cx, source).expect("rewrites");
        let pass = start.elapsed();
        let PassWitness::Range(w) = &witness else {
            panic!("range witness");
        };
        assert_eq!(
            w.counts().get("condbr"),
            Some(&900),
            "{name}: {:?}",
            w.counts()
        );
        assert_eq!(w.removed_blocks.len(), 900, "{name}");
        let start = std::time::Instant::now();
        trust_cg_verify::trust_ir_mid_tv::check_pass(&m, 32, source, &target, &witness)
            .unwrap_or_else(|e| panic!("{name}: {e}"));
        let check = start.elapsed();
        assert!(
            pass < bound && check < bound,
            "{name}: pass {pass:?}, check {check:?}"
        );
    }
}

/// The guard index lists exactly the members on the dominator path of a
/// block, nearest first, on every tree of up to seven nodes (as parent
/// arrays) and every member set and block.
#[test]
fn the_guard_index_lists_the_dominator_path_members_nearest_first() {
    fn trees(n: usize) -> Vec<Vec<usize>> {
        // Node `i` (1..n) takes any parent below it.
        let mut out = vec![Vec::new()];
        for i in 1..n {
            out = out
                .into_iter()
                .flat_map(|t: Vec<usize>| {
                    (0..i).map(move |p| {
                        let mut t = t.clone();
                        t.push(p);
                        t
                    })
                })
                .collect();
        }
        out
    }
    let mut cases = 0usize;
    for n in 1..=7 {
        for parent in trees(n) {
            for mask in 0u32..(1 << n) {
                let members: Vec<usize> = (0..n).filter(|i| mask & (1 << i) != 0).collect();
                for at in 0..n {
                    let mut naive = Vec::new();
                    let mut b = at;
                    loop {
                        if members.contains(&b) {
                            naive.push(b);
                        }
                        if b == 0 {
                            break;
                        }
                        b = parent[b - 1];
                    }
                    let index = decisions::dominating_members(&parent, &members, at);
                    assert_eq!(
                        index, naive,
                        "tree {parent:?}, members {members:?}, at {at}"
                    );
                    cases += 1;
                }
            }
        }
    }
    assert_eq!(cases, 695_482);
}
