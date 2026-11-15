// trust-cg-verify/trust_ir_mid_tv_unroll_tests.rs - tests of the full unrolling checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A counted loop and a pointer loop over a slot are unrolled exactly as
//! the module docs construct them, and agree with their sources in the
//! interpreter; the negative controls are refused: a trip count off by one
//! either way, a body over the bound, a trip count over the cap, a compare
//! the checker cannot decide, an irreducible region, a side exit whose
//! target reads a value of the body, an inner cycle, names that are not
//! fresh or not enough, and a loop whose header is the entry block, entered
//! from outside only by an unreachable block (the call enters it too).
//!
//! The witness types (`UnrollWitness`, `UnrollLoop`, `PassWitness::Unroll`)
//! are provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, run_samples,
    seeded_inputs,
};
use super::*;
use trust_ir::Module;

const HEADER: &str = "; TrustIr text format v1\nmodule \"unroll\"\n\
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

fn witness(header: u32, trips: u32, blocks: u32, values: u32) -> PassWitness {
    PassWitness::Unroll(UnrollWitness {
        loops: vec![UnrollLoop {
            header: BlockId::new(header),
            trips,
            blocks: (100..100 + blocks).map(BlockId::new).collect(),
            values: (100..100 + values).map(ValueId::new).collect(),
        }],
    })
}

fn rebuild(m: &Module, f: &Function, w: &PassWitness) -> Result<Function, MidTvError> {
    let PassWitness::Unroll(uw) = w else {
        unreachable!()
    };
    let (out, _) = rebuild_unroll(32, m, f, uw)?;
    check_pass(m, 32, f, &out, w)?;
    Ok(out)
}

fn agree(m: &Module, source: &Function, target: &Function) {
    let inputs = seeded_inputs(m, source, 32, 64, 11).expect("scalar parameters");
    let (a, _) = run_samples(m, source, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(m, target, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

fn refused(m: &Module, w: &PassWitness, why: &str) {
    match rebuild(m, func(m, "f"), w) {
        Err(MidTvError::NotLoopRewrite { why: got, .. }) => {
            assert!(got.contains(why), "refused for `{got}`, expected `{why}`");
        }
        other => panic!("expected a refusal containing `{why}`, got {other:?}"),
    }
}

/// `acc = acc * x + i` for `i` in `0..4`.
const COUNTED: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 0\n\
\x20   %2 = const u32 0\n\
\x20   br bb1(%1, %2)\n\
bb1(%10: u32, %11: u32):\n\
\x20   %12 = const u32 4\n\
\x20   %13 = icmp ult u32 %10, %12\n\
\x20   condbr %13, bb2, bb3\n\
bb2:\n\
\x20   %14 = mul u32 %11, %0\n\
\x20   %15 = add u32 %14, %10\n\
\x20   %16 = const u32 1\n\
\x20   %17 = add u32 %10, %16\n\
\x20   br bb1(%17, %15)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

/// [`COUNTED`] unrolled, as the module docs construct it.
const COUNTED_UNROLLED: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 0\n\
\x20   %2 = const u32 0\n\
\x20   br bb100\n\
bb100:\n\
\x20   %100 = const u32 4\n\
\x20   br bb101\n\
bb101:\n\
\x20   %101 = mul u32 %2, %0\n\
\x20   %102 = add u32 %101, %1\n\
\x20   %103 = const u32 1\n\
\x20   %104 = add u32 %1, %103\n\
\x20   br bb102\n\
bb102:\n\
\x20   %105 = const u32 4\n\
\x20   br bb103\n\
bb103:\n\
\x20   %106 = mul u32 %102, %0\n\
\x20   %107 = add u32 %106, %104\n\
\x20   %108 = const u32 1\n\
\x20   %109 = add u32 %104, %108\n\
\x20   br bb104\n\
bb104:\n\
\x20   %110 = const u32 4\n\
\x20   br bb105\n\
bb105:\n\
\x20   %111 = mul u32 %107, %0\n\
\x20   %112 = add u32 %111, %109\n\
\x20   %113 = const u32 1\n\
\x20   %114 = add u32 %109, %113\n\
\x20   br bb106\n\
bb106:\n\
\x20   %115 = const u32 4\n\
\x20   br bb107\n\
bb107:\n\
\x20   %116 = mul u32 %112, %0\n\
\x20   %117 = add u32 %116, %114\n\
\x20   %118 = const u32 1\n\
\x20   %119 = add u32 %114, %118\n\
\x20   br bb1(%119, %117)\n\
bb1(%10: u32, %11: u32):\n\
\x20   %12 = const u32 4\n\
\x20   %13 = icmp ult u32 %10, %12\n\
\x20   br bb3\n\
bb3:\n\
\x20   ret %11\n\
}\n";

fn edited(text: &str, edit: &[(&str, &str)]) -> Module {
    let mut text = text.to_string();
    for (from, to) in edit {
        assert!(text.contains(from), "{from}");
        text = text.replace(from, to);
    }
    module(&text)
}

#[test]
fn a_counted_loop_becomes_its_four_iterations() {
    let src = module(COUNTED);
    let f = func(&src, "f");
    let w = witness(1, 4, 8, 20);
    let out = rebuild(&src, f, &w).expect("accepted");
    let expected = module(COUNTED_UNROLLED);
    assert_eq!(&out, func(&expected, "f"));
    let PassWitness::Unroll(uw) = &w else {
        unreachable!()
    };
    // The copies drop the exit compare: a refinement.
    let (_, verdict) = rebuild_unroll(32, &src, f, uw).expect("accepted");
    assert_eq!((verdict.exact, verdict.refinements), (0, 1));
    agree(&src, f, &out);
}

#[test]
fn a_trip_count_off_by_one_is_refused() {
    let src = module(COUNTED);
    refused(&src, &witness(1, 5, 10, 25), "the trip count is 4, not 5");
    refused(&src, &witness(1, 3, 6, 15), "the trip count is 4, not 3");
}

#[test]
fn names_that_are_not_fresh_or_not_enough_are_refused() {
    let src = module(COUNTED);
    refused(&src, &witness(1, 4, 8, 19), "the copies define 20");
    refused(&src, &witness(1, 4, 7, 20), "the copies need 8");
    let mut w = witness(1, 4, 8, 20);
    if let PassWitness::Unroll(uw) = &mut w {
        uw.loops[0].values[3] = ValueId::new(15);
    }
    refused(&src, &w, "is not fresh");
    let mut w = witness(1, 4, 8, 20);
    if let PassWitness::Unroll(uw) = &mut w {
        uw.loops[0].blocks[2] = BlockId::new(2);
    }
    refused(&src, &w, "is not fresh");
}

#[test]
fn a_bound_the_checker_cannot_decide_is_refused() {
    let m = edited(
        COUNTED,
        &[("%13 = icmp ult u32 %10, %12", "%13 = icmp ult u32 %10, %0")],
    );
    refused(&m, &witness(1, 4, 8, 20), "not decided");
}

#[test]
fn a_trip_count_over_the_cap_is_refused() {
    let m = edited(COUNTED, &[("%12 = const u32 4", "%12 = const u32 40")]);
    refused(&m, &witness(1, 40, 80, 200), "more than 32");
}

#[test]
fn a_body_over_the_bound_is_refused() {
    // Thirty iterations of a body of more than 34 instructions.
    let mut body = String::new();
    for k in 0..36 {
        body.push_str(&format!("\x20   %{} = add u32 %15, %0\n", 9000 + k));
    }
    let m = edited(
        COUNTED,
        &[
            ("%12 = const u32 4", "%12 = const u32 30"),
            (
                "\x20   %16 = const u32 1\n",
                &format!("{body}\x20   %16 = const u32 1\n"),
            ),
        ],
    );
    refused(&m, &witness(1, 30, 60, 30 * 41), "over the bound");
}

#[test]
fn an_irreducible_region_is_refused() {
    // A second entry into the body.
    let m = edited(
        COUNTED,
        &[(
            "\x20   br bb1(%1, %2)\n",
            "\x20   %3 = icmp eq u32 %0, %1\n\x20   condbr %3, bb1(%1, %2), bb2\n",
        )],
    );
    match rebuild(&m, func(&m, "f"), &witness(1, 4, 8, 20)) {
        Err(MidTvError::NotLoopRewrite { .. }) => {}
        other => panic!("expected a refusal, got {other:?}"),
    }
}

#[test]
fn a_side_exit_joining_a_use_of_the_header_is_refused() {
    // The side exit reaches `bb6`, which also follows the header's exit and
    // reads the header's `%11`: in the copies no single definition of it
    // dominates `bb6`.
    let m = edited(
        COUNTED,
        &[
            (
                "\x20   %17 = add u32 %10, %16\n\x20   br bb1(%17, %15)\n",
                "\x20   %17 = add u32 %10, %16\n\x20   %18 = icmp eq u32 %15, %0\n\x20   condbr %18, bb4, bb5\nbb5:\n\x20   br bb1(%17, %15)\nbb4:\n\x20   br bb6\n",
            ),
            (
                "bb3:\n\x20   ret %11\n",
                "bb3:\n\x20   br bb6\nbb6:\n\x20   ret %11\n",
            ),
        ],
    );
    refused(&m, &witness(1, 4, 12, 24), "used outside it");
}

#[test]
fn a_side_exit_into_an_exit_block_is_copied_with_each_iteration() {
    // `bb4`, entered by the side exit alone, reads `%15`: each copy takes
    // its own `bb4`.
    let m = edited(
        COUNTED,
        &[(
            "\x20   %17 = add u32 %10, %16\n\x20   br bb1(%17, %15)\n",
            "\x20   %17 = add u32 %10, %16\n\x20   %18 = icmp eq u32 %15, %0\n\x20   condbr %18, bb4, bb5\nbb5:\n\x20   br bb1(%17, %15)\nbb4:\n\x20   %19 = add u32 %15, %16\n\x20   ret %19\n",
        )],
    );
    let f = func(&m, "f");
    // Per copy: H, bb2, bb5, bb4; values: %12, %14..%18, %19.
    let out = rebuild(&m, f, &witness(1, 4, 16, 28)).expect("accepted");
    assert!(out.blocks.iter().all(|b| b.id != BlockId::new(4)));
    agree(&m, f, &out);
}

#[test]
fn an_inner_cycle_is_refused() {
    let m = edited(
        COUNTED,
        &[(
            "\x20   %17 = add u32 %10, %16\n\x20   br bb1(%17, %15)\n",
            "\x20   %17 = add u32 %10, %16\n\x20   br bb4\nbb4:\n\x20   %18 = icmp eq u32 %0, %16\n\x20   condbr %18, bb4, bb5\nbb5:\n\x20   br bb1(%17, %15)\n",
        )],
    );
    refused(&m, &witness(1, 4, 16, 28), "inner cycle");
}

/// The sum of a four-element slot through a pointer induction variable
/// (`p != end` as `==` on the exit edge), the bridge's integer addresses.
const POINTER: &str = "functy.0 = (u32) -> (u32)\n\n\
type ty.0 = u32\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = alloca [ty.0 x 4], align 4\n\
\x20   store u32 %0, ptr %1\n\
\x20   %20 = const i32 4\n\
\x20   %21 = gep inbounds u8, ptr %1, %20\n\
\x20   %22 = const u32 7\n\
\x20   store u32 %22, ptr %21\n\
\x20   %23 = const i32 8\n\
\x20   %24 = gep inbounds u8, ptr %1, %23\n\
\x20   store u32 %0, ptr %24\n\
\x20   %25 = const i32 12\n\
\x20   %26 = gep inbounds u8, ptr %1, %25\n\
\x20   store u32 %22, ptr %26\n\
\x20   %2 = ptrtoint ptr %1 to i32\n\
\x20   %3 = const i32 16\n\
\x20   %4 = add i32 %2, %3\n\
\x20   %5 = const u32 0\n\
\x20   br bb1(%2, %5)\n\
bb1(%10: i32, %11: u32):\n\
\x20   %12 = icmp eq i32 %10, %4\n\
\x20   condbr %12, bb3, bb2\n\
bb2:\n\
\x20   %13 = inttoptr i32 %10 to ptr\n\
\x20   %14 = load u32, ptr %13\n\
\x20   %15 = add u32 %11, %14\n\
\x20   %16 = const i32 4\n\
\x20   %17 = add i32 %10, %16\n\
\x20   br bb1(%17, %15)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

#[test]
fn a_pointer_loop_over_a_slot_is_unrolled_on_a_shared_root() {
    let src = module(POINTER);
    let f = func(&src, "f");
    // Per copy: H (nothing but the dropped compare), bb2 (five values).
    let out = rebuild(&src, f, &witness(1, 4, 8, 20)).expect("accepted");
    agree(&src, f, &out);
    refused(&src, &witness(1, 3, 6, 15), "the trip count is 4");
    // A bound of another root is not decided.
    let m = edited(POINTER, &[("%4 = add i32 %2, %3", "%4 = add i32 %3, %3")]);
    refused(&m, &witness(1, 4, 8, 20), "not decided");
}

/// `x == C` (`{test}`) keeps `x + 7` in the loop at `bb0`. `{entry}` is the
/// text before the loop; `{tail}` follows it.
fn entry_loop(entry: &str, test: &str, tail: &str) -> Module {
    module(&format!(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {{\n\
{entry}\
bb0(%1: u32):\n\
\x20   %2 = const u32 1515870810\n\
{test}\
bb1:\n\
\x20   %4 = const u32 7\n\
\x20   %5 = add u32 %1, %4\n\
\x20   br bb0(%5)\n\
bb2:\n\
\x20   ret %1\n\
{tail}\
}}\n"
    ))
}

#[test]
fn a_loop_headed_by_the_entry_block_has_no_preheader() {
    // The header is the entry: its one reachable edge in is a back edge and
    // only the unreachable `bb9` enters it from outside. With the dead
    // edge's `C` as the start value the trip count would be 1, but the call
    // passes any `x`.
    const DEAD: &str = "bb9:\n\x20   %6 = const u32 1515870810\n\x20   br bb0(%6)\n";
    const FRESH: &str = "bb8(%80: u32):\n\x20   %81 = const u32 1515870810\n\x20   br bb0(%81)\n";
    for test in [
        "\x20   %3 = icmp eq u32 %1, %2\n\x20   condbr %3, bb1, bb2\n",
        "\x20   %3 = icmp ne u32 %1, %2\n\x20   condbr %3, bb2, bb1\n",
    ] {
        // One trip: the header's constant (the copy drops the exit compare)
        // and the body's two values.
        let w = witness(0, 1, 2, 3);
        refused(
            &entry_loop("", test, DEAD),
            &w,
            "the header is the entry block",
        );
        // The control: a fresh entry passing `C` is the preheader.
        let fresh = entry_loop(FRESH, test, "");
        let out = rebuild(&fresh, func(&fresh, "f"), &w).expect("the control is accepted");
        agree(&fresh, func(&fresh, "f"), &out);
    }
}
