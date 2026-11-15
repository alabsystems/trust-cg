// trust-cg-verify/trust_ir_mid_tv_bounded_tests.rs - tests of the interval-bounded unrolling checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A loop over a 4-element slot whose trip count is `min(4, k % 5)` (the
//! minimum spelled as the bridge spells it, a join of the two arms) is
//! unrolled to 4 copies that keep their exit tests, and to 5; so is the
//! same loop when its exit test is `Zip::next`'s niche (`switch` on a
//! `select` of the element address and `null`). Each target agrees with its
//! source in the reference interpreter. Refused: a bound the intervals do
//! not prove (`k % 9` trips), a bound one short, a bound read from memory
//! the body writes, a trip count bounded only by another loop's induction
//! variable, a value of the loop read after it outside an exit block, a
//! zero bound, names that are not fresh or counted wrong, a bound read
//! from an entry block parameter's edges alone (an edge back into the entry
//! passes `2`; the call passes any value), and a loop whose header is the
//! entry block, entered from outside only by an unreachable block (the call
//! enters it too, with any argument).
//!
//! The witness types (`BoundedUnrollWitness`, `BoundedUnrollLoop`,
//! `MAX_BOUNDED_TRIPS` and the `PassWitness::BoundedUnroll` variant) are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, run_samples,
    seeded_inputs,
};
use super::*;
use trust_ir::Module;

const HEADER: &str = "; TrustIr text format v1\nmodule \"bounded\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn f(m: &Module) -> &Function {
    m.functions.iter().find(|f| f.name == "f").expect("f")
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// The slot `[1, 2, 3, 4]` of `u16`, then `n = min(4, k % {modulus})` and
/// `acc = acc * 100 + slot[i]` for `i < n`. `{test}` is the header's exit
/// test on `%19` (`i`) and `%15` (`n`), ending in a branch to `bb6` (stay)
/// or `bb7` (leave).
fn program(modulus: &str, test: &str, tail: &str) -> String {
    format!(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {{\n\
bb0(%0: u32):\n\
\x20   %1 = alloca (u16, u16, u16, u16), align 2\n\
\x20   %2 = const u16 1\n\
\x20   store u16 %2, ptr %1\n\
\x20   %3 = const i32 2\n\
\x20   %4 = gep u8, ptr %1, %3\n\
\x20   %5 = const u16 2\n\
\x20   store u16 %5, ptr %4\n\
\x20   %6 = const i32 4\n\
\x20   %7 = gep u8, ptr %1, %6\n\
\x20   %8 = const u16 3\n\
\x20   store u16 %8, ptr %7\n\
\x20   %9 = const i32 6\n\
\x20   %40 = gep u8, ptr %1, %9\n\
\x20   %41 = const u16 4\n\
\x20   store u16 %41, ptr %40\n\
\x20   %10 = const u32 {modulus}\n\
\x20   %11 = urem u32 %0, %10\n\
\x20   %12 = const u32 4\n\
\x20   %13 = icmp ult u32 %12, %11\n\
\x20   condbr %13, bb2, bb3\n\
bb2:\n\
\x20   br bb4(%12)\n\
bb3:\n\
\x20   br bb4(%11)\n\
bb4(%14: u32):\n\
\x20   %15 = bitcast u32 %14 to i32\n\
\x20   %16 = const u32 0\n\
\x20   %17 = const i32 0\n\
\x20   br bb5(%16, %17)\n\
bb5(%18: u32, %19: i32):\n\
{test}\
bb6:\n\
\x20   %21 = ptrtoint ptr %1 to i32\n\
\x20   %22 = const i32 2\n\
\x20   %23 = mul i32 %19, %22\n\
\x20   %24 = add i32 %21, %23\n\
\x20   %25 = inttoptr i32 %24 to ptr\n\
\x20   %26 = load u16, ptr %25\n\
\x20   %27 = zext u16 %26 to u32\n\
\x20   %28 = const u32 100\n\
\x20   %29 = mul u32 %18, %28\n\
\x20   %30 = add u32 %29, %27\n\
\x20   %31 = const i32 1\n\
\x20   %32 = add i32 %19, %31\n\
\x20   br bb5(%30, %32)\n\
bb7:\n\
\x20   ret %18\n\
{tail}\
}}\n"
    )
}

const PLAIN: &str = "\x20   %20 = icmp ult i32 %19, %15\n\x20   condbr %20, bb6, bb7\n";

/// `Zip::next`'s niche: the element address or `null`, tested as the bridge
/// tests it.
const NICHE: &str = "\x20   %20 = icmp ult i32 %19, %15\n\
\x20   %50 = ptrtoint ptr %1 to i32\n\
\x20   %51 = const i32 2\n\
\x20   %52 = mul i32 %19, %51\n\
\x20   %53 = add i32 %50, %52\n\
\x20   %54 = inttoptr i32 %53 to ptr\n\
\x20   %55 = const i32 0\n\
\x20   %56 = inttoptr i32 %55 to ptr\n\
\x20   %57 = select ptr %20, %54, %56\n\
\x20   %58 = ptrtoint ptr %57 to u64\n\
\x20   %59 = const u64 0\n\
\x20   %60 = icmp eq u64 %58, %59\n\
\x20   %61 = trunc u64 %58 to i32\n\
\x20   %62 = const i32 1\n\
\x20   %63 = select i32 %60, %61, %62\n\
\x20   switch %63 [ 0: bb7 1: bb6 default: bb8 ]\n";

const NICHE_TAIL: &str = "bb8:\n\x20   unreachable\n";

/// The witness for `bound` copies of the loop at `bb5`, with
/// `header_values` results in the header: per copy three blocks (the
/// header, `bb6`, the exit block `bb7`) and the header's values, `bb6`'s
/// twelve, `bb7`'s none.
fn witness(bound: u32, header_values: u32) -> BoundedUnrollWitness {
    let per = header_values + 12;
    BoundedUnrollWitness {
        loops: vec![BoundedUnrollLoop {
            header: b(5),
            bound,
            blocks: (0..3 * bound).map(|i| b(900 + i)).collect(),
            values: (0..per * bound).map(|i| ValueId::new(1000 + i)).collect(),
        }],
    }
}

fn accepted_and_agrees(m: &Module, w: &BoundedUnrollWitness) -> Function {
    let src = f(m);
    let (out, verdict) = rebuild_bounded_unroll(32, src, w).expect("accepted");
    assert_eq!(verdict.exact, 1);
    check_pass(m, 32, src, &out, &PassWitness::BoundedUnroll(w.clone())).expect("check_pass");
    let inputs = seeded_inputs(m, src, 32, 64, 9).expect("scalar parameters");
    let mut inputs = inputs;
    for k in 0..10u32 {
        inputs.push(vec![
            trust_ir::InterpretValue::int(Ty::U32, i128::from(k)).expect("u32"),
        ]);
    }
    let (a, _) = run_samples(m, src, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(m, &out, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert_eq!(report.compared, inputs.len(), "every input is compared");
    out
}

fn refused(m: &Module, w: &BoundedUnrollWitness, why: &str) {
    match rebuild_bounded_unroll(32, f(m), w) {
        Err(MidTvError::NotLoopRewrite { why: found, .. }) => {
            assert!(found.contains(why), "refused for `{found}`, not `{why}`");
        }
        other => panic!("not refused: {:?}", other.map(|_| ())),
    }
}

#[test]
fn a_loop_bounded_by_its_trip_counts_interval_is_unrolled_to_the_bound() {
    let m = module(&program("5", PLAIN, ""));
    let out = accepted_and_agrees(&m, &witness(4, 1));
    // No back edge remains: every copy's header leaves or goes on.
    let header_reached = out
        .blocks
        .iter()
        .filter_map(|blk| blk.body.last())
        .flat_map(|n| n.inst.successor_edges())
        .filter(|e| e.target == b(5))
        .count();
    assert_eq!(
        header_reached, 1,
        "only the last copy enters the header\n{out}"
    );
    // A larger bound is exact too.
    accepted_and_agrees(&m, &witness(5, 1));
}

#[test]
fn a_zip_niche_exit_test_is_decided_on_the_bound_visit() {
    let m = module(&program("5", NICHE, NICHE_TAIL));
    accepted_and_agrees(&m, &witness(4, 15));
}

#[test]
fn bounds_the_intervals_do_not_prove_are_refused() {
    // The control.
    let m = module(&program("5", PLAIN, ""));
    rebuild_bounded_unroll(32, f(&m), &witness(4, 1)).expect("control");
    // `k % 9` without the minimum: the trip count reaches 8.
    let m =
        module(&program("9", PLAIN, "").replace("condbr %13, bb2, bb3", "condbr %13, bb3, bb3"));
    refused(&m, &witness(4, 1), "not decided on visit 4");
    // One short of the bound.
    let m = module(&program("5", PLAIN, ""));
    refused(&m, &witness(3, 1), "not decided on visit 3");
    // A zero bound.
    refused(&m, &witness(0, 1), "not in 1..=");
    // The bound read from memory the body writes: the header reloads it.
    let m = module(
        &program(
            "5",
            "\x20   %70 = load u32, ptr %71\n\x20   %72 = bitcast u32 %70 to i32\n\
             \x20   %20 = icmp ult i32 %19, %72\n\x20   condbr %20, bb6, bb7\n",
            "",
        )
        .replace(
            "\x20   %10 = const u32 5\n",
            "\x20   %71 = alloca (u32), align 4\n\x20   %10 = const u32 5\n",
        )
        .replace(
            "\x20   %16 = const u32 0\n",
            "\x20   store u32 %14, ptr %71\n\x20   %16 = const u32 0\n",
        )
        .replace(
            "\x20   br bb5(%30, %32)\n",
            "\x20   %73 = const u32 9\n\x20   store u32 %73, ptr %71\n\x20   br bb5(%30, %32)\n",
        ),
    );
    refused(&m, &witness(4, 3), "not decided on visit 4");
}

#[test]
fn a_bound_from_another_loops_induction_variable_is_refused() {
    // `n` is the induction variable of an outer loop over `0..k`: its
    // parameter's interval meets itself through the back edge.
    let m = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 0\n\
\x20   br bb1(%1, %1)\n\
bb1(%2: u32, %3: u32):\n\
\x20   %4 = icmp ult u32 %2, %0\n\
\x20   condbr %4, bb2, bb9\n\
bb2:\n\
\x20   %5 = const u32 0\n\
\x20   br bb5(%3, %5)\n\
bb5(%18: u32, %19: u32):\n\
\x20   %20 = icmp ult u32 %19, %2\n\
\x20   condbr %20, bb6, bb7\n\
bb6:\n\
\x20   %21 = add u32 %18, %19\n\
\x20   %22 = const u32 1\n\
\x20   %23 = add u32 %19, %22\n\
\x20   br bb5(%21, %23)\n\
bb7:\n\
\x20   %24 = const u32 1\n\
\x20   %25 = add u32 %2, %24\n\
\x20   br bb1(%25, %18)\n\
bb9:\n\
\x20   ret %3\n\
}\n",
    );
    let w = BoundedUnrollWitness {
        loops: vec![BoundedUnrollLoop {
            header: b(5),
            bound: 4,
            blocks: (0..8).map(|i| b(900 + i)).collect(),
            values: (0..16).map(|i| ValueId::new(1000 + i)).collect(),
        }],
    };
    refused(&m, &w, "not decided on visit 4");
}

#[test]
fn copies_off_their_shape_are_refused() {
    // A value of the loop read after it outside an exit block: `bb8`,
    // behind `bb7`, which reads nothing of the loop.
    let m = module(&program("5", PLAIN, "").replace(
        "bb7:\n\x20   ret %18\n",
        "bb7:\n\x20   br bb8\nbb8:\n\x20   ret %18\n",
    ));
    refused(&m, &witness(4, 1), "used outside it");
    // A name that is not fresh.
    let m = module(&program("5", PLAIN, ""));
    let mut w = witness(4, 1);
    w.loops[0].values[3] = ValueId::new(26);
    assert!(matches!(
        rebuild_bounded_unroll(32, f(&m), &w),
        Err(MidTvError::NotLoopRewrite { .. })
    ));
    // Values counted for another header.
    refused(&m, &witness(4, 2), "the witness names");
    // A target that drops the last copy's exit test is not the claimed
    // rewrite.
    let src = f(&m);
    let w = witness(4, 1);
    let (mut out, _) = rebuild_bounded_unroll(32, src, &w).expect("accepted");
    let last = out
        .blocks
        .iter_mut()
        .find(|blk| blk.id == b(900 + 9))
        .expect("the last header copy");
    if let Some(term) = last.body.last_mut()
        && let Inst::CondBr { then_target, .. } = &term.inst
    {
        term.inst = Inst::Br {
            target: *then_target,
            args: Vec::new(),
        };
    }
    assert!(matches!(
        check_pass(&m, 32, src, &out, &PassWitness::BoundedUnroll(w)),
        Err(MidTvError::TargetDiffers { .. })
    ));
}

#[test]
fn an_entry_parameter_has_its_types_range_whatever_edges_reenter_the_entry() {
    // `i < n` with `n` the entry's parameter; the only edge into the entry
    // passes `2`, and the call passes any `n` (`f(40)` runs 40 iterations).
    let m = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %2 = const u32 0\n\
\x20   br bb1(%2, %2)\n\
bb1(%3: u32, %4: u32):\n\
\x20   %5 = icmp ult u32 %3, %1\n\
\x20   condbr %5, bb2, bb3(%4)\n\
bb2:\n\
\x20   %6 = const u32 1\n\
\x20   %7 = add u32 %3, %6\n\
\x20   %30 = const u32 3\n\
\x20   %31 = mul u32 %4, %30\n\
\x20   %8 = xor u32 %31, %3\n\
\x20   %32 = const u32 2\n\
\x20   %33 = icmp uge u32 %7, %32\n\
\x20   %34 = const u32 40\n\
\x20   %35 = icmp ne u32 %1, %34\n\
\x20   %36 = and bool %33, %35\n\
\x20   condbr %36, bb3(%8), bb1(%7, %8)\n\
bb3(%12: u32):\n\
\x20   %9 = const u32 100000\n\
\x20   %10 = icmp eq u32 %12, %9\n\
\x20   condbr %10, bb4, bb5\n\
bb4:\n\
\x20   %11 = const u32 2\n\
\x20   br bb0(%11)\n\
bb5:\n\
\x20   ret %12\n\
}\n",
    );
    // Per copy: the header and `bb2`; the header's one value and `bb2`'s
    // ten.
    let w = BoundedUnrollWitness {
        loops: vec![BoundedUnrollLoop {
            header: b(1),
            bound: 2,
            blocks: (0..4).map(|i| b(900 + i)).collect(),
            values: (0..22).map(|i| ValueId::new(1000 + i)).collect(),
        }],
    };
    refused(&m, &w, "not decided on visit 2");
    // The control: with the bound read from a fresh entry's argument
    // through a block of its own, the edge's `2` is the only value.
    let fresh = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb9(%90: u32):\n\
\x20   %91 = const u32 2\n\
\x20   br bb0(%91)\n\
bb0(%1: u32):\n\
\x20   %2 = const u32 0\n\
\x20   br bb1(%2, %2)\n\
bb1(%3: u32, %4: u32):\n\
\x20   %5 = icmp ult u32 %3, %1\n\
\x20   condbr %5, bb2, bb3(%4)\n\
bb2:\n\
\x20   %6 = const u32 1\n\
\x20   %7 = add u32 %3, %6\n\
\x20   %30 = const u32 3\n\
\x20   %31 = mul u32 %4, %30\n\
\x20   %8 = xor u32 %31, %3\n\
\x20   %32 = const u32 2\n\
\x20   %33 = icmp uge u32 %7, %32\n\
\x20   %34 = const u32 40\n\
\x20   %35 = icmp ne u32 %1, %34\n\
\x20   %36 = and bool %33, %35\n\
\x20   condbr %36, bb3(%8), bb1(%7, %8)\n\
bb3(%12: u32):\n\
\x20   ret %12\n\
}\n",
    );
    rebuild_bounded_unroll(32, f(&fresh), &w).expect("the control is accepted");
}

/// `x == C` keeps `x + 7` in the loop at `bb0`. `{entry}` is the text before
/// the loop; `{tail}` follows it.
fn entry_loop(entry: &str, tail: &str) -> String {
    format!(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {{\n\
{entry}\
bb0(%1: u32):\n\
\x20   %2 = const u32 1515870810\n\
\x20   %8 = const u32 4294967295\n\
\x20   %9 = xor u32 %1, %8\n\
\x20   %10 = xor u32 %9, %8\n\
\x20   %3 = icmp eq u32 %10, %2\n\
\x20   condbr %3, bb1, bb2\n\
bb1:\n\
\x20   %4 = const u32 7\n\
\x20   %5 = add u32 %1, %4\n\
\x20   br bb0(%5)\n\
bb2:\n\
\x20   ret %1\n\
{tail}\
}}\n"
    )
}

#[test]
fn a_loop_headed_by_the_entry_block_has_no_preheader() {
    // The header is the entry, so its one reachable edge in is a back edge
    // and only the unreachable `bb9` enters it from outside. Its `C` is not
    // the loop's start value: the call passes any `x`, and `f(C)` is
    // `C + 7`, which the two copies the dead edge's `C` decides would make
    // `C`.
    let m = module(&entry_loop(
        "",
        "bb9:\n\x20   %6 = const u32 1515870810\n\x20   br bb0(%6)\n",
    ));
    // Per copy: the header, `bb1` and the exit block `bb2`; the header's
    // five values and `bb1`'s two.
    let w = BoundedUnrollWitness {
        loops: vec![BoundedUnrollLoop {
            header: b(0),
            bound: 2,
            blocks: (0..6).map(|i| b(900 + i)).collect(),
            values: (0..14).map(|i| ValueId::new(1000 + i)).collect(),
        }],
    };
    refused(&m, &w, "the header is the entry block");
    // The control: a fresh entry passing `C` is the preheader, and the same
    // witness is exact.
    let fresh = module(&entry_loop(
        "bb8(%80: u32):\n\x20   %81 = const u32 1515870810\n\x20   br bb0(%81)\n",
        "",
    ));
    accepted_and_agrees(&fresh, &w);
}
