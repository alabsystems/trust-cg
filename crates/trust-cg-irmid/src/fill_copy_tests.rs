// trust-cg-irmid/fill_copy_tests.rs - the round-16 rewrites over the pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Over the wasm32 pipeline, each kept by its checker and compared by the
//! interpreter differential, except the unauthenticated fill-call rewrite
//! which is withheld and keeps both byte-uniform and other imported calls:
//! a packed struct built in a frame slot and copied byte by byte into an
//! out-pointer is stored into the out-pointer field by field; the bridge's
//! sign-reinterpreting `copy` is respelled as a `bitcast`; a callee whose
//! only slot is a temporary it promotes is spliced into its caller's loop
//! (a spliced slot may not go there); and an iterator's state copied out of
//! the slot it was built in, then stepped in a loop through a `select` of
//! its own reload, leaves memory. The pass names `fill_call`, `byte_copy`
//! and `retype_copy` and the witness types are provisional surfaces pending
//! the owner's sign-off (`docs/wasm32_perf_roadmap.md`, "Pending owner
//! sign-off").

use trust_ir::{Function, Inst, Module, Ty};

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

fn stats(report: &IrmidReport, name: &str) -> PassStats {
    report
        .passes
        .iter()
        .find(|p| p.name == name)
        .cloned()
        .unwrap_or_default()
}

fn compared(report: &IrmidReport, name: &str) -> usize {
    report.tv.by_pass.get(name).map_or(0, |c| c.compared)
}

fn count(f: &Function, pred: impl Fn(&Inst) -> bool) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| pred(&n.inst))
        .count()
}

/// `[v; 20]` of `u32` filled by the bridge's helper, then words 0, 7 and 19
/// read back and mixed with the argument.
const FILL: &str = "type ty.0 = i32\n\n\
functy.0 = (ptr, i64, i32) -> ()\n\
functy.1 = (u32) -> (u32)\n\n\
fn @__trustcg_array_fill_i32(functy.0) {\n}\n\n\
fn @f(functy.1) {\n\
bb0(%0: u32):\n\
\x20   %1 = alloca [ty.0 x 20], align 4\n\
\x20   %2 = const i64 0\n\
\x20   %3 = const i32 20\n\
\x20   call @func.0(%1, %2, %3)\n\
\x20   %4 = const usize 28\n\
\x20   %5 = gep u8, ptr %1, %4\n\
\x20   store u32 %0, ptr %5\n\
\x20   %6 = load u32, ptr %1\n\
\x20   %7 = load u32, ptr %5\n\
\x20   %8 = const usize 76\n\
\x20   %9 = gep u8, ptr %1, %8\n\
\x20   %10 = load u32, ptr %9\n\
\x20   %11 = add u32 %6, %7\n\
\x20   %12 = xor u32 %11, %10\n\
\x20   ret %12\n\
}\n";

#[test]
fn unauthenticated_array_fill_calls_are_withheld_and_retained() {
    let m = module(FILL);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(report.passes_withheld["fill_call"].contains("source-bound helper"));
    assert_eq!(stats(&report, "fill_call").functions_changed, 0);
    assert_eq!(compared(&report, "fill_call"), 0);
    let f = func(&out, "f");
    assert_eq!(count(f, |i| matches!(i, Inst::Call { .. })), 1, "{f}");
    assert_eq!(count(f, |i| matches!(i, Inst::MemSet { .. })), 0, "{f}");
    // A differing-byte value likewise leaves the actual external call intact.
    let m = module(&FILL.replace("%2 = const i64 0", "%2 = const i64 16909060"));
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(stats(&report, "fill_call").functions_changed, 0);
    assert!(report.passes_withheld["fill_call"].contains("source-bound helper"));
    assert_eq!(
        count(func(&out, "f"), |i| matches!(i, Inst::Call { .. })),
        1
    );
}

/// A packed `{ a: u8, x: f64, b: u16, y: f32 }` built in the 15-byte slot
/// `%2` and copied byte by byte into the out-pointer `%0`, as the bridge
/// lowers `fn mk(k: u32, x: f64) -> Packed`.
fn packed() -> String {
    let mut copy = String::new();
    for i in 0..15u32 {
        let n = 100 + 5 * i;
        copy.push_str(&format!(
            "\x20   %{n} = const usize {i}\n\x20   %{a} = gep u8, ptr %2, %{n}\n\
             \x20   %{l} = load i8, ptr %{a}\n\x20   %{b} = gep u8, ptr %0, %{n}\n\
             \x20   store i8 %{l}, ptr %{b}\n",
            a = n + 1,
            l = n + 2,
            b = n + 3,
        ));
    }
    format!(
        "type ty.0 = u8\n\n\
functy.0 = (ptr, u32, f64) -> ()\n\n\
fn @mk(functy.0) {{\n\
bb0(%0: ptr, %1: u32, %3: f64):\n\
\x20   %2 = alloca [ty.0 x 15], align 1\n\
\x20   %4 = trunc u32 %1 to u8\n\
\x20   store u8 %4, ptr %2\n\
\x20   %5 = const usize 1\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   store f64 %3, ptr %6\n\
\x20   %7 = const usize 9\n\
\x20   %8 = gep u8, ptr %2, %7\n\
\x20   %9 = trunc u32 %1 to u16\n\
\x20   store u16 %9, ptr %8\n\
\x20   %10 = const usize 11\n\
\x20   %11 = gep u8, ptr %2, %10\n\
\x20   %12 = fptrunc f64 %3 to f32\n\
\x20   store f32 %12, ptr %11\n\
{copy}\
\x20   ret\n\
}}\n"
    )
}

#[test]
fn a_packed_struct_is_stored_into_its_out_pointer_field_by_field() {
    let m = module(&packed());
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(stats(&report, "byte_copy").functions_changed >= 1);
    assert!(
        compared(&report, "byte_copy") >= 1,
        "{:?}",
        report.tv.by_pass
    );
    let f = func(&out, "mk");
    assert_eq!(count(f, |i| matches!(i, Inst::Load { .. })), 0, "{f}");
    assert_eq!(count(f, |i| matches!(i, Inst::MemCopy { .. })), 0, "{f}");
    assert_eq!(count(f, |i| matches!(i, Inst::Store { .. })), 4, "{f}");
    assert_eq!(count(f, |i| matches!(i, Inst::Alloca { .. })), 0, "{f}");
}

/// `g` reads an `i32` and returns it through the bridge's
/// sign-reinterpreting `copy u32`; `f` calls it in a loop.
const REINTERPRET: &str = "functy.0 = (i32) -> (u32)\n\
functy.1 = (i32) -> (u32)\n\n\
fn @g.tcg.crate.0000000000000001(functy.0) {\n\
\x20   ; #visibility: hidden\n\
bb0(%0: i32):\n\
\x20   %1 = const i32 3\n\
\x20   %2 = mul i32 %0, %1\n\
\x20   %3 = copy u32 %2\n\
\x20   ret %3\n\
}\n\n\
fn @f(functy.1) {\n\
bb0(%0: i32):\n\
\x20   %1 = const i32 0\n\
\x20   %2 = const u32 0\n\
\x20   br bb1(%1, %2)\n\
bb1(%3: i32, %4: u32):\n\
\x20   %5 = icmp slt i32 %3, %0\n\
\x20   condbr %5, bb2, bb3\n\
bb2:\n\
\x20   %6 = call @func.0(%3)\n\
\x20   %7 = add u32 %4, %6\n\
\x20   %8 = const i32 1\n\
\x20   %9 = add i32 %3, %8\n\
\x20   br bb1(%9, %7)\n\
bb3:\n\
\x20   ret %4\n\
}\n";

#[test]
fn a_sign_reinterpreting_copy_is_respelled_before_its_callee_is_spliced() {
    let m = module(REINTERPRET);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(stats(&report, "retype_copy").functions_changed >= 1);
    let reinterpreting = |f: &Function| {
        count(
            f,
            |i| matches!(i, Inst::Copy { ty: Ty::U32, operand } if f.blocks.iter().flat_map(|b| &b.body).any(|n| n.results == [*operand] && matches!(n.inst, Inst::BinOp { ty: Ty::I32, .. }))),
        )
    };
    for name in ["f", "g.tcg.crate.0000000000000001"] {
        let f = func(&out, name);
        assert_eq!(reinterpreting(f), 0, "{f}");
    }
    let f = func(&out, "f");
    assert_eq!(count(f, |i| matches!(i, Inst::Call { .. })), 0, "{f}");
}

/// `h` packs its two arguments into a temporary pair and returns their
/// difference through it; `f` calls it in a loop.
const TEMP: &str = "type ty.0 = i32\n\n\
functy.0 = (i32, i32) -> (i32)\n\
functy.1 = (i32) -> (i32)\n\n\
fn @h.tcg.crate.0000000000000001(functy.0) {\n\
\x20   ; #visibility: hidden\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   store i32 %0, ptr %2\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   store i32 %1, ptr %4\n\
\x20   %5 = load i32, ptr %2\n\
\x20   %6 = load i32, ptr %4\n\
\x20   %7 = sub i32 %5, %6\n\
\x20   ret %7\n\
}\n\n\
fn @f(functy.1) {\n\
bb0(%0: i32):\n\
\x20   %1 = const i32 0\n\
\x20   br bb1(%1, %1)\n\
bb1(%3: i32, %4: i32):\n\
\x20   %5 = icmp slt i32 %3, %0\n\
\x20   condbr %5, bb2, bb3\n\
bb2:\n\
\x20   %6 = call @func.0(%3, %4)\n\
\x20   %8 = const i32 1\n\
\x20   %9 = add i32 %3, %8\n\
\x20   br bb1(%9, %6)\n\
bb3:\n\
\x20   ret %4\n\
}\n";

#[test]
fn a_callee_temporary_is_promoted_before_the_callee_is_spliced_into_a_loop() {
    let m = module(TEMP);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert_eq!(count(f, |i| matches!(i, Inst::Call { .. })), 0, "{f}");
    assert_eq!(count(f, |i| matches!(i, Inst::Alloca { .. })), 0, "{f}");
}

/// An iterator's state `(index, len)` built in `%1`, copied as one word
/// into `%6`, then stepped in a loop through a `select` of its own reload.
const ITER: &str = "type ty.0 = i32\n\n\
functy.0 = (u32) -> (i32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = alloca [ty.0 x 2], align 8\n\
\x20   %2 = const i32 0\n\
\x20   store i32 %2, ptr %1\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %1, %3\n\
\x20   %20 = const u32 7\n\
\x20   %21 = and u32 %0, %20\n\
\x20   %5 = bitcast u32 %21 to i32\n\
\x20   store i32 %5, ptr %4\n\
\x20   %6 = alloca i64, align 8\n\
\x20   %7 = load i64, ptr %1\n\
\x20   store i64 %7, ptr %6\n\
\x20   %10 = gep u8, ptr %6, %3\n\
\x20   br bb1(%2)\n\
bb1(%8: i32):\n\
\x20   %9 = load i32, ptr %6\n\
\x20   %11 = load i32, ptr %10\n\
\x20   %12 = icmp slt i32 %9, %11\n\
\x20   %13 = const i32 1\n\
\x20   %14 = add i32 %9, %13\n\
\x20   %15 = select i32 %12, %14, %9\n\
\x20   store i32 %15, ptr %6\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %16 = mul i32 %8, %13\n\
\x20   %17 = add i32 %16, %9\n\
\x20   br bb1(%17)\n\
bb3:\n\
\x20   ret %8\n\
}\n";

#[test]
fn an_iterator_state_stepped_through_its_own_reload_leaves_memory() {
    let m = module(ITER);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(compared(&report, "sroa") >= 1, "{:?}", report.tv.by_pass);
    let f = func(&out, "f");
    assert_eq!(count(f, |i| matches!(i, Inst::Alloca { .. })), 0, "{f}");
    assert_eq!(
        count(f, |i| matches!(i, Inst::Load { .. } | Inst::Store { .. })),
        0,
        "{f}"
    );
}
