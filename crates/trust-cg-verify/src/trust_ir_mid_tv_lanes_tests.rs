// trust-cg-verify/trust_ir_mid_tv_lanes_tests.rs - tests of the lane-load checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! An array load whose lanes are read in the rustc bridge's
//! declared-aggregate spelling gains a scalar load per lane read, the reads
//! becoming copies, and the target agrees with the source run in the
//! differential's view (`u32`, `i8` and `u64` lanes, a lane read twice, a
//! lane at the end of the array, the array load's result kept for another
//! use). Refused: a volatile load, a load of a struct, an array of arrays, a
//! lane past the length, a lane claimed twice, a read of another value, a
//! read declared at another type, a read of an unclaimed lane, a name that
//! is not fresh and an empty claim. A target whose lane load reads the
//! wrong offset is not the claimed rewrite, and the differential sees it.
//!
//! The witness types (`LaneLoadWitness`, `LaneLoad`, `LaneRead`, the
//! `PassWitness::LaneLoad` variant and `MidTvError::NotLaneLoad`) are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, SampleOutcome, check_pass, compare_samples,
    interpretable, interpretable_module, run_samples, seeded_inputs,
};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"lanes\"\n\
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

/// Three `u32` lanes `a`, `b`, `a ^ b` stored into a slot, the slot loaded
/// as `[u32 x 3]` (`%10`, `{volatile}`), lanes 2 and 0 read (`%11`, `%12`)
/// and lane 2 again (`%13`); the result is `%11 * 7 + %12 - %13 + lane 1`.
fn program(volatile: &str) -> String {
    format!(
        "type ty.0 = u32\n\n\
functy.0 = (u32, u32) -> (u32)\n\n\
fn @f(functy.0) {{\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 3], align 4\n\
\x20   store u32 %0, ptr %2\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   store u32 %1, ptr %4\n\
\x20   %5 = const usize 8\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   %7 = xor u32 %0, %1\n\
\x20   store u32 %7, ptr %6\n\
\x20   %10 = {volatile}load [ty.0 x 3], ptr %2\n\
\x20   %11 = extractfield [ty.0 x 3] %10, 2\n\
\x20   %12 = extractfield [ty.0 x 3] %10, 0\n\
\x20   %13 = extractfield [ty.0 x 3] %10, 2\n\
\x20   %14 = extractfield [ty.0 x 3] %10, 1\n\
\x20   %15 = const u32 7\n\
\x20   %16 = mul u32 %11, %15\n\
\x20   %17 = add u32 %16, %12\n\
\x20   %18 = sub u32 %17, %13\n\
\x20   %19 = add u32 %18, %14\n\
\x20   ret %19\n\
}}\n"
    )
}

fn lane(field: u32, base: u32) -> LaneRead {
    LaneRead {
        field,
        index: v(base),
        address: v(base + 1),
        value: v(base + 2),
    }
}

/// Lanes 2, 0 and 1 of `%10`, read by `%11`..`%14`.
fn witness() -> LaneLoadWitness {
    LaneLoadWitness {
        loads: vec![LaneLoad {
            array: v(10),
            lanes: vec![lane(2, 100), lane(0, 103), lane(1, 106)],
            reads: vec![v(11), v(12), v(13), v(14)],
        }],
    }
}

/// The source and the target run in the differential's view (each spelled
/// in the interpreter's typed form, as the mid-end's manager runs them).
fn viewed_runs(
    m: &Module,
    src: &Function,
    out: &Function,
) -> (Vec<SampleOutcome>, Vec<SampleOutcome>) {
    let view = interpretable_module(m);
    let inputs = seeded_inputs(m, src, 32, 64, 7).expect("scalar parameters");
    let sv = interpretable(&view, src).unwrap_or_else(|| src.clone());
    let tv = interpretable(&view, out).unwrap_or_else(|| out.clone());
    let (a, _) = run_samples(&view, &sv, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&view, &tv, &inputs, DifferentialBudget::default());
    (a, t)
}

/// The rewrite on `m` checked, and run against the source in the view.
fn accepted_and_agrees(m: &Module, w: &LaneLoadWitness) -> Function {
    let src = f(m);
    let (out, verdict) = rebuild_lane_load(m, src, w).expect("accepted");
    assert_eq!(verdict.exact, w.rewrite_count());
    check_pass(m, 32, src, &out, &PassWitness::LaneLoad(w.clone())).expect("check_pass");
    let (a, t) = viewed_runs(m, src, &out);
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
    out
}

#[test]
fn an_array_load_read_lane_by_lane_becomes_scalar_loads_and_agrees() {
    let m = module(&program(""));
    let out = accepted_and_agrees(&m, &witness());
    let body = &out.blocks[0].body;
    // The lane loads follow the array load, the reads are copies.
    let at = body
        .iter()
        .position(|n| n.results == [v(10)])
        .expect("array load kept");
    assert!(matches!(
        body[at + 3].inst,
        Inst::Load { ty: Ty::U32, ptr, align: Some(1), .. } if ptr == v(101)
    ));
    assert!(matches!(
        body[at + 1].inst,
        Inst::Const {
            value: Constant::Int(8),
            ..
        }
    ));
    for (read, lane_value) in [(11, 102), (12, 105), (13, 102), (14, 108)] {
        let node = body.iter().find(|n| n.results == [v(read)]).expect("read");
        assert_eq!(
            node.inst,
            Inst::Copy {
                ty: Ty::U32,
                operand: v(lane_value)
            }
        );
    }
}

#[test]
fn typed_array_elements_are_checked_at_their_constant_indices() {
    let text = program("")
        .replace(
            "%11 = extractfield [ty.0 x 3] %10, 2",
            "%30 = const usize 2\n    %11 = extractelement u32 %10, %30",
        )
        .replace(
            "%12 = extractfield [ty.0 x 3] %10, 0",
            "%31 = const usize 0\n    %12 = extractelement u32 %10, %31",
        )
        .replace(
            "%13 = extractfield [ty.0 x 3] %10, 2",
            "%13 = extractelement u32 %10, %30",
        )
        .replace(
            "%14 = extractfield [ty.0 x 3] %10, 1",
            "%32 = const usize 1\n    %14 = extractelement u32 %10, %32",
        );
    let m = module(&text);
    assert!(trust_ir_build::validate_module(&m).is_empty());
    accepted_and_agrees(&m, &witness());
    for bad in [
        text.replace("extractelement u32 %10, %30", "extractelement i32 %10, %30"),
        text.replace("%30 = const usize 2", "%30 = const usize 3"),
        text.replace("%30 = const usize 2", "%30 = const isize -1"),
        text.replace("%30 = const usize 2", "%30 = copy u32 %0"),
    ] {
        let invalid = module(&bad);
        assert!(rebuild_lane_load(&invalid, f(&invalid), &witness()).is_err());
    }
    let mut forged = witness();
    forged.loads[0].lanes[0].field = 1;
    assert!(rebuild_lane_load(&m, f(&m), &forged).is_err());
}

#[test]
fn byte_and_word_lanes_and_a_kept_array_value_agree() {
    // An `i8` array: lanes 0 and 7; a `u64` array's lane 1; the `i8`
    // array value also passed on whole (kept by the rewrite).
    let text = "type ty.0 = i8\ntype ty.1 = u64\n\n\
functy.0 = (u32, u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca [ty.1 x 2], align 8\n\
\x20   %3 = zext u32 %0 to u64\n\
\x20   store u64 %3, ptr %2\n\
\x20   %4 = const usize 8\n\
\x20   %5 = gep u8, ptr %2, %4\n\
\x20   %6 = zext u32 %1 to u64\n\
\x20   %7 = const u64 40\n\
\x20   %8 = shl u64 %6, %7\n\
\x20   store u64 %8, ptr %5\n\
\x20   %10 = load [ty.0 x 8], ptr %2\n\
\x20   %11 = extractfield [ty.0 x 8] %10, 0\n\
\x20   %12 = extractfield [ty.0 x 8] %10, 7\n\
\x20   %13 = load [ty.1 x 2], ptr %2\n\
\x20   %14 = extractfield [ty.1 x 2] %13, 1\n\
\x20   %15 = alloca [ty.0 x 8], align 1\n\
\x20   store [ty.0 x 8] %10, ptr %15\n\
\x20   %16 = load u32, ptr %15\n\
\x20   %17 = sext i8 %11 to u32\n\
\x20   %18 = sext i8 %12 to u32\n\
\x20   %19 = trunc u64 %14 to u32\n\
\x20   %20 = add u32 %17, %18\n\
\x20   %21 = xor u32 %20, %19\n\
\x20   %22 = add u32 %21, %16\n\
\x20   ret %22\n\
}\n";
    let m = module(text);
    let w = LaneLoadWitness {
        loads: vec![
            LaneLoad {
                array: v(10),
                lanes: vec![lane(0, 100), lane(7, 103)],
                reads: vec![v(11), v(12)],
            },
            LaneLoad {
                array: v(13),
                lanes: vec![lane(1, 106)],
                reads: vec![v(14)],
            },
        ],
    };
    let out = accepted_and_agrees(&m, &w);
    let body = &out.blocks[0].body;
    assert!(body.iter().any(|n| n.results == [v(10)]), "array load kept");
    assert!(
        body.iter()
            .any(|n| n.results == [v(107)]
                && matches!(n.inst, Inst::GEP { base, .. } if base == v(2)))
    );
}

#[test]
fn claims_off_the_form_are_refused() {
    let refused = |m: &Module, w: &LaneLoadWitness| {
        assert!(
            matches!(
                rebuild_lane_load(m, f(m), w),
                Err(MidTvError::NotLaneLoad { .. })
            ),
            "{w:?}"
        );
    };
    let m = module(&program(""));
    let edit = |f: &dyn Fn(&mut LaneLoad)| {
        let mut w = witness();
        f(&mut w.loads[0]);
        w
    };
    // A volatile array load (a strict load: the lanes cannot be read again).
    refused(&module(&program("volatile ")), &witness());
    // A lane past the array's length.
    refused(&m, &edit(&|l| l.lanes[2].field = 3));
    // A lane claimed twice.
    refused(&m, &edit(&|l| l.lanes[2].field = 2));
    // A read of another value (a lane's own arithmetic).
    refused(&m, &edit(&|l| l.reads.push(v(16))));
    // A read whose lane is not claimed.
    refused(&m, &edit(&|l| l.lanes.truncate(2)));
    // A name that is not fresh.
    refused(&m, &edit(&|l| l.lanes[0].value = v(19)));
    // The claimed array is not a load.
    refused(&m, &edit(&|l| l.array = v(7)));
    // Nothing claimed.
    refused(&m, &LaneLoadWitness::default());
    refused(&m, &edit(&|l| l.reads.clear()));
    // A read declared at another type (a reinterpreting read).
    let m2 = module(
        &program("")
            .replace(
                "%13 = extractfield [ty.0 x 3] %10, 2",
                "%13 = extractfield [ty.1 x 3] %10, 2",
            )
            .replace("type ty.0 = u32\n", "type ty.0 = u32\ntype ty.1 = i32\n"),
    );
    refused(&m2, &witness());
    // An array of arrays (a lane that is not a scalar), and a struct load.
    let nested = "type ty.0 = u32\ntype ty.1 = [ty.0 x 2]\n\n\
functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %2 = alloca [ty.1 x 2], align 4\n\
\x20   store u32 %0, ptr %2\n\
\x20   %10 = load [ty.1 x 2], ptr %2\n\
\x20   %11 = extractfield [ty.1 x 2] %10, 0\n\
\x20   ret %0\n\
}\n";
    let one = LaneLoadWitness {
        loads: vec![LaneLoad {
            array: v(10),
            lanes: vec![lane(0, 100)],
            reads: vec![v(11)],
        }],
    };
    refused(&module(nested), &one);
    let record = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %2 = alloca (u32, u32), align 4\n\
\x20   store u32 %0, ptr %2\n\
\x20   %10 = load (u32, u32), ptr %2\n\
\x20   %11 = extractfield (u32, u32) %10, 0\n\
\x20   ret %11\n\
}\n";
    refused(&module(record), &one);
}

#[test]
fn a_lane_loaded_from_the_wrong_offset_is_refused_and_disagrees() {
    let m = module(&program(""));
    let src = f(&m);
    let w = witness();
    let (mut out, _) = rebuild_lane_load(&m, src, &w).expect("accepted");
    // Lane 2's offset spelled 4 (lane 1's bytes).
    for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if node.results == [v(100)] {
            node.inst = Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(4),
            };
        }
    }
    assert!(matches!(
        check_pass(&m, 32, src, &out, &PassWitness::LaneLoad(w)),
        Err(MidTvError::TargetDiffers { .. })
    ));
    let (a, t) = viewed_runs(&m, src, &out);
    assert!(compare_samples(&a, &t).mismatch.is_some());
}
