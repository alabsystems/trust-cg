// crates/trust-cg-eqsat/tests/engine_round_trip.rs - body -> graph -> body on hand-written functions
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! `round_trip` always elaborates (no rules), so these tests exercise the
//! reader, extraction, placement and the operand remap on straight-line
//! code, a diamond, a loop with block arguments, calls/loads/stores and
//! copies. Each output must validate (trust-ir-build) and behave like the
//! input on the reference interpreter at boundary inputs.

#![allow(clippy::unwrap_used, clippy::expect_used, clippy::panic)]

mod engine_common;

use engine_common::{assert_same_behaviour, function, module};
use trust_cg_eqsat::round_trip;
use trust_ir::Inst;

fn check(text: &str, name: &str) -> trust_ir::Function {
    let module = module(text);
    let input = function(&module, name);
    let output = round_trip(&module, input).unwrap_or_else(|d| panic!("declined: {d}"));
    assert_eq!(output.name, input.name);
    assert_eq!(output.blocks.len(), input.blocks.len());
    assert_same_behaviour(&module, input, &output, 400);
    // Idempotent shape: a second round trip changes nothing.
    let module2 = engine_common::substitute(&module, &output);
    let again = round_trip(&module2, function(&module2, name)).unwrap();
    assert_eq!(again, output);
    output
}

const STRAIGHT: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (i32, i32) -> (i32)

fn @f(functy.0) {
bb0(%0: i32, %1: i32):
    %2 = xor i32 %0, %1
    %3 = const i32 7
    %4 = add i32 %2, %3
    %5 = mul i32 %4, %4
    %6 = sub i32 %5, %2
    %7 = add i32 %2, %3
    %8 = rotl i32 %7, %6
    %9 = ctpop i32 %8
    %10 = icmp slt i32 %9, %3
    %11 = select i32 %10, %8, %6
    ret %11
}
"#;

#[test]
fn straight_line() {
    let output = check(STRAIGHT, "f");
    // `%7` is `%4` again: hash-consing merges them (one add fewer).
    let adds = output.blocks[0]
        .body
        .iter()
        .filter(|n| {
            matches!(
                n.inst,
                Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ..
                }
            )
        })
        .count();
    assert_eq!(adds, 1);
}

const DIAMOND: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (u8, u8) -> (u8)

fn @f(functy.0) {
bb0(%0: u8, %1: u8):
    %2 = icmp ult u8 %0, %1
    %3 = xor u8 %0, %1
    condbr %2, bb1, bb2
bb1:
    %4 = const u8 3
    %5 = add u8 %3, %4
    %6 = mul u8 %5, %3
    br bb3(%6)
bb2:
    %7 = const u8 3
    %8 = add u8 %3, %7
    %9 = sub u8 %8, %3
    br bb3(%9)
bb3(%10: u8):
    %11 = add u8 %3, %10
    ret %11
}
"#;

#[test]
fn diamond() {
    let output = check(DIAMOND, "f");
    // The arms' nodes have their only leaf (`%3`) in bb0, so they are placed
    // there (a graph node is total); the two arms' `add %3, 3` are separate
    // graph nodes (the hash-cons map is scoped by the dominator tree) but
    // emit one instruction. Each arm keeps only its branch.
    for block in [1usize, 2] {
        assert_eq!(output.blocks[block].body.len(), 1, "block {block}");
    }
    let adds = output
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| {
            matches!(
                n.inst,
                Inst::BinOp {
                    op: trust_ir::BinOp::Add,
                    ..
                }
            )
        })
        .count();
    // The hoisted `add %3, 3` and the skeleton `add %3, %10` (a block
    // parameter operand keeps it in the skeleton).
    assert_eq!(adds, 2);
}

const LOOP: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (u32, u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: u32):
    %2 = const u32 0
    %3 = and u32 %1, %1
    %4 = const u32 15
    %5 = and u32 %3, %4
    br bb1(%2, %0)
bb1(%6: u32, %7: u32):
    %8 = add u32 %7, %6
    %9 = const u32 1
    %10 = add u32 %6, %9
    %11 = icmp ult u32 %10, %5
    %12 = copy u32 %8
    condbr %11, bb1(%10, %12), bb2
bb2:
    %13 = const u32 0
    %14 = copy u32 %13
    %15 = add u32 %12, %14
    ret %15
}
"#;

#[test]
fn loop_with_block_arguments() {
    let output = check(LOOP, "f");
    // Copies are see-through: none is emitted.
    assert!(
        output
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .all(|n| !matches!(n.inst, Inst::Copy { .. }))
    );
}

const MEMORY: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (i64) -> (i64)

functy.1 = (i64, i64) -> (i64)

fn @g(functy.0) {
bb0(%0: i64):
    %1 = const i64 3
    %2 = mul i64 %0, %1
    ret %2
}

fn @f(functy.1) {
bb0(%0: i64, %1: i64):
    %2 = alloca i64
    %3 = const i64 5
    %4 = add i64 %0, %3
    store i64 %4, ptr %2
    %5 = load i64, ptr %2
    %6 = call @func.0(%5)
    %7 = copy i64 %6
    %8 = xor i64 %7, %1
    %9 = add i64 %0, %3
    %10 = sub i64 %8, %9
    store i64 %10, ptr %2
    %11 = load i64, ptr %2
    %12 = copy i64 %11
    ret %12
}
"#;

#[test]
fn calls_loads_stores_and_copies() {
    let output = check(MEMORY, "f");
    let kinds: Vec<&str> = output.blocks[0]
        .body
        .iter()
        .filter_map(|n| match n.inst {
            Inst::Alloca { .. } => Some("alloca"),
            Inst::Store { .. } => Some("store"),
            Inst::Load { .. } => Some("load"),
            Inst::Call { .. } => Some("call"),
            Inst::Return { .. } => Some("ret"),
            _ => None,
        })
        .collect();
    assert_eq!(
        kinds,
        ["alloca", "store", "load", "call", "store", "load", "ret"]
    );
}

const BOOLS: &str = r#"; TrustIr text format v1
module "m"

functy.0 = (bool, i16, i16) -> (i16)

fn @f(functy.0) {
bb0(%0: bool, %1: i16, %2: i16):
    %3 = icmp sle i16 %1, %2
    %4 = const bool true
    %5 = bxor bool %3, %4
    %6 = band bool %5, %3
    %7 = icmp eq bool %6, %3
    %8 = select i16 %7, %1, %2
    %9 = sext i16 %8 to i64
    %10 = trunc i64 %9 to i8
    %11 = zext i8 %10 to i16
    %12 = select i16 %0, %11, %8
    ret %12
}
"#;

#[test]
fn booleans_casts_and_selects() {
    check(BOOLS, "f");
}
