// trust-cg-irmid/sroa_bool_tests.rs - a bool field read as a byte
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Scalar replacement of a one-byte field written and read both as `bool`
//! and as a one-byte integer (the bridge's whole-lane copy of a record's
//! `bool` field, `RangeInclusive::exhausted`, reads it as `i8`): the field
//! is carried as the integer, the `bool` store becomes its `zext` and the
//! `bool` load the nonzero test, kept by the checker and the interpreter
//! differential over the pipeline; a two-byte field read as `bool` stays in
//! memory. The witness fields this drives (`SroaLoad::via` naming the
//! zero) are provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use trust_ir::{Function, ICmpOp, Inst, Module};

use crate::{MidConfig, optimize_module};

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

/// `RangeInclusive<u8>`'s `exhausted` flag in a three-byte slot: written
/// as `bool`, copied as `i8` into a second slot, read there as `i8` and as
/// `bool` in a loop that sets it.
const RANGE: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = alloca i8\n\
\x20   %2 = alloca i8\n\
\x20   %3 = const bool 0\n\
\x20   store bool %3, ptr %1\n\
\x20   %4 = load i8, ptr %1\n\
\x20   store i8 %4, ptr %2\n\
\x20   %5 = const u32 0\n\
\x20   br bb1(%5)\n\
bb1(%6: u32):\n\
\x20   %7 = load bool, ptr %2\n\
\x20   condbr %7, bb3, bb2\n\
bb2:\n\
\x20   %8 = const u32 7\n\
\x20   %9 = and u32 %0, %8\n\
\x20   %10 = icmp uge u32 %6, %9\n\
\x20   store bool %10, ptr %2\n\
\x20   %11 = const u32 1\n\
\x20   %12 = add u32 %6, %11\n\
\x20   br bb1(%12)\n\
bb3:\n\
\x20   %13 = load i8, ptr %2\n\
\x20   %14 = zext i8 %13 to u32\n\
\x20   %15 = add u32 %6, %14\n\
\x20   ret %15\n\
}\n";

fn slots(f: &Function) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| matches!(n.inst, Inst::Alloca { .. }))
        .count()
}

#[test]
fn a_bool_flag_copied_as_a_byte_leaves_memory() {
    let m = module(RANGE);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert_eq!(slots(f), 0, "{f}");
    assert!(
        f.blocks.iter().flat_map(|b| &b.body).any(|n| matches!(
            n.inst,
            Inst::ICmp {
                op: ICmpOp::Ne,
                ty: trust_ir::Ty::I8,
                ..
            }
        )),
        "{f}"
    );
    let tv = report.tv.by_pass.get("sroa").expect("candidates");
    assert!(tv.compared >= 1, "{tv:?}");
}

#[test]
fn a_bool_read_of_a_wider_field_stays_in_memory() {
    // The second slot is an `i16` written whole and read as a `bool` at its
    // first byte: a part access of a two-byte field, not the byte rule.
    let text = RANGE
        .replace("%2 = alloca i8", "%2 = alloca i16")
        .replace(
            "store i8 %4, ptr %2",
            "%40 = sext i8 %4 to i16\n\x20   store i16 %40, ptr %2",
        )
        .replace(
            "%13 = load i8, ptr %2\n\x20   %14 = zext i8 %13 to u32",
            "%13 = load i16, ptr %2\n\x20   %14 = zext i16 %13 to u32",
        );
    let m = module(&text);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(slots(func(&out, "f")), 1);
}
