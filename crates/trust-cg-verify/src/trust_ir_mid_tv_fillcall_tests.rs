// trust-cg-verify/trust_ir_mid_tv_fillcall_tests.rs - tests of the fill-call checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The former width/value/position fixtures remain refusal controls: neither
//! their name nor their signature authenticates an external helper. The early
//! custody refusal is not evidence for the old detailed rewrite guards.
//! Forged byte/count targets refuse, and the differential retains the actual
//! declaration rather than inventing a loop. Empty witnesses change nothing.

use trust_ir::{Constant, Inst, InstrNode, Ty};

use super::super::{MidTvError, PassWitness, check_pass, interpretable_module};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"fillcall\"\n\
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

/// The position of the helper call in [`program`]'s entry block.
const CALL: usize = 58;

fn witness(count: u32, byte: u32) -> FillCallWitness {
    FillCallWitness {
        rewrites: vec![FillCall {
            block: BlockId::new(0),
            index: CALL,
            count: v(count),
            byte: v(byte),
        }],
    }
}

/// A 40-byte slot whose ten words hold `a`, `b`, `a + b`, `a + 2b`, ...;
/// the helper `__trustcg_array_fill_{width}` fills `count` elements from
/// byte `at` with `value`; then the last two words take `a ^ b` and `a + b`,
/// and the result folds the slot's ten words.
fn program(width: &str, value: &str, count: &str, at: u32) -> String {
    let mut init = String::new();
    for word in 0..8u32 {
        // Words 2..9: `a + (word + 1) * b`, each a constant, a product, a
        // sum, an offset, an address and a store (6 instructions).
        init.push_str(&format!(
            "\x20   %{k} = const u32 {f}\n\x20   %{p} = mul u32 %1, %{k}\n\x20   \
             %{s} = add u32 %0, %{p}\n\x20   %{o} = const usize {off}\n\x20   \
             %{g} = gep u8, ptr %2, %{o}\n\x20   store u32 %{s}, ptr %{g}\n",
            k = 200 + 5 * word,
            p = 201 + 5 * word,
            s = 202 + 5 * word,
            o = 203 + 5 * word,
            g = 204 + 5 * word,
            f = word + 1,
            off = 8 + 4 * word,
        ));
    }
    let mut fold = String::new();
    let mut acc = 20;
    for word in 0..10u32 {
        fold.push_str(&format!(
            "\x20   %{a} = const usize {o}\n\x20   %{b} = gep u8, ptr %2, %{a}\n\
             \x20   %{c} = load u32, ptr %{b}\n",
            a = 30 + 3 * word,
            b = 31 + 3 * word,
            c = 32 + 3 * word,
            o = 4 * word,
        ));
        let next = 70 + 2 * word;
        fold.push_str(&format!(
            "\x20   %{m} = mul u32 %{acc}, %21\n\x20   %{next} = xor u32 %{m}, %{c}\n",
            m = 71 + 2 * word,
            c = 32 + 3 * word,
        ));
        acc = next;
    }
    format!(
        "functy.0 = (ptr, i64, i32) -> ()\n\
functy.1 = (u32, u32) -> (u32)\n\n\
fn @__trustcg_array_fill_{width}(functy.0) {{\n}}\n\n\
fn @f(functy.1) {{\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca (u32, u32, u32, u32, u32, u32, u32, u32, u32, u32), align 4\n\
\x20   store u32 %0, ptr %2\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   store u32 %1, ptr %4\n\
{init}\
\x20   %5 = const usize {at}\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   %7 = ptrtoptr ptr %6 to *mut u8\n\
\x20   %8 = {value}\n\
\x20   %9 = {count}\n\
\x20   call @func.0(%7, %8, %9)\n\
\x20   %10 = const usize 32\n\
\x20   %11 = gep u8, ptr %2, %10\n\
\x20   %12 = xor u32 %0, %1\n\
\x20   store u32 %12, ptr %11\n\
\x20   %13 = const usize 36\n\
\x20   %14 = gep u8, ptr %2, %13\n\
\x20   %15 = add u32 %0, %1\n\
\x20   store u32 %15, ptr %14\n\
\x20   %20 = const u32 17\n\
\x20   %21 = const u32 31\n\
{fold}\
\x20   ret %{acc}\n\
}}\n"
    )
}

fn assert_refused(m: &Module, w: &FillCallWitness, target: &Function) {
    let snapshot = m.clone();
    let error = check_pass(m, 32, f(m), target, &PassWitness::FillCall(w.clone()))
        .expect_err("a proposed rewrite cannot authenticate a helper declaration");
    assert!(matches!(
        error,
        MidTvError::NotFillCall { ref why, .. } if why.contains("source-bound helper")
    ));
    assert_eq!(m, &snapshot, "refusal must preserve the complete source");
}

fn forged_target(m: &Module, byte: i128, bytes: i128) -> Function {
    let mut target = f(m).clone();
    let Inst::Call { args, .. } = &target.blocks[0].body[CALL].inst else {
        panic!("the original fixture retains its actual call");
    };
    let destination = args[0];
    let count = InstrNode::new(Inst::Const {
        ty: Ty::Usize,
        value: Constant::Int(bytes),
    })
    .with_result(v(100));
    let fill = InstrNode::new(Inst::Const {
        ty: Ty::U8,
        value: Constant::Int(byte),
    })
    .with_result(v(101));
    let store = InstrNode::new(Inst::MemSet {
        dst: destination,
        byte: v(101),
        bytes: v(100),
    });
    target.blocks[0]
        .body
        .splice(CALL..=CALL, [count, fill, store]);
    target
}

#[test]
fn formerly_uniform_fills_refuse_without_a_source_bound_helper() {
    // (width, value, count, at, the byte, the byte count)
    let cases: [(&str, &str, &str, u32, i128, i128); 7] = [
        ("i32", "const i64 0", "const i32 6", 8, 0, 24),
        ("i8", "const i64 171", "const i32 13", 9, 0xab, 13),
        ("i16", "const i64 257", "const i32 5", 6, 1, 10),
        ("i64", "const i64 -1", "const i32 3", 8, 0xff, 24),
        ("i32", "const i64 4294967295", "const i32 2", 13, 0xff, 8),
        // The old proposed truncating fill case: no declaration body is inferred.
        ("i32", "const i64 4294967296", "const i32 4", 12, 0, 16),
        ("i64", "const i64 0", "const i32 0", 8, 0, 0),
    ];
    for (width, value, count, at, byte, bytes) in cases {
        let m = module(&program(width, value, count, at));
        assert_refused(&m, &witness(100, 101), &forged_target(&m, byte, bytes));
        let view = interpretable_module(&m);
        assert_eq!(view.functions[0], m.functions[0]);
        assert!(view.functions[0].is_declaration());
    }
}

#[test]
fn calls_off_the_helper_form_are_refused() {
    let refused = |m: &Module, w: &FillCallWitness| {
        assert!(
            matches!(
                rebuild_fill_call(m, 32, f(m), w),
                Err(MidTvError::NotFillCall { .. })
            ),
            "{w:?}"
        );
    };
    let base = program("i32", "const i64 0", "const i32 4", 8);
    let w = witness(100, 101);
    // Even the old byte-uniform control has no authenticated helper body.
    refused(&module(&base), &w);
    // A helper the module defines (its body runs).
    refused(
        &module(&base.replace(
            "fn @__trustcg_array_fill_i32(functy.0) {\n}",
            "fn @__trustcg_array_fill_i32(functy.0) {\nbb0(%0: ptr, %1: i64, %2: i32):\n    ret\n}",
        )),
        &w,
    );
    // A declaration of another name.
    refused(
        &module(&base.replace("__trustcg_array_fill_i32", "__trustcg_array_fill_i24")),
        &w,
    );
    // Not the helper's signature: an unsigned count, an `i32` value, a result.
    refused(
        &module(
            &base
                .replace("(ptr, i64, i32) -> ()", "(ptr, i64, u32) -> ()")
                .replace("const i32 4", "const u32 4"),
        ),
        &w,
    );
    refused(
        &module(
            &base
                .replace("(ptr, i64, i32) -> ()", "(ptr, i32, i32) -> ()")
                .replace("const i64 0", "const i32 0"),
        ),
        &w,
    );
    refused(
        &module(
            &base
                .replace("(ptr, i64, i32) -> ()", "(ptr, i64, i32) -> (i32)")
                .replace("    call @func.0(", "    %99 = call @func.0("),
        ),
        &w,
    );
    // A runtime count, a runtime value, a negative count.
    refused(
        &module(&base.replace("%9 = const i32 4", "%9 = bitcast u32 %1 to i32")),
        &w,
    );
    refused(
        &module(&base.replace("%8 = const i64 0", "%8 = zext u32 %1 to i64")),
        &w,
    );
    refused(&module(&base.replace("const i32 4", "const i32 -1")), &w);
    // An element whose bytes differ (`[0x0102_0304; 4]`).
    refused(
        &module(&base.replace("const i64 0", "const i64 16909060")),
        &w,
    );
    // A byte count past the 32-bit pointer width.
    refused(
        &module(
            &program("i64", "const i64 0", "const i32 0", 8)
                .replace("const i32 0", "const i32 2147483647"),
        ),
        &w,
    );
    let m = module(&base);
    // Not the call: the instruction after it.
    refused(
        &m,
        &FillCallWitness {
            rewrites: vec![FillCall {
                block: BlockId::new(0),
                index: CALL + 1,
                count: v(100),
                byte: v(101),
            }],
        },
    );
    // No such block.
    refused(
        &m,
        &FillCallWitness {
            rewrites: vec![FillCall {
                block: BlockId::new(9),
                index: CALL,
                count: v(100),
                byte: v(101),
            }],
        },
    );
    // Rewritten twice.
    let mut twice = witness(100, 101);
    twice.rewrites.push(FillCall {
        block: BlockId::new(0),
        index: 10,
        count: v(102),
        byte: v(103),
    });
    refused(&m, &twice);
    // A name that is not fresh.
    refused(&m, &witness(2, 101));
    refused(&m, &witness(100, 100));
}

#[test]
fn a_forged_fill_byte_refuses_without_helper_authority() {
    let m = module(&program("i8", "const i64 7", "const i32 6", 8));
    assert_refused(&m, &witness(100, 101), &forged_target(&m, 8, 6));
}

#[test]
fn a_short_fill_has_no_invented_differential_or_witness_authority() {
    let m = module(&program("i32", "const i64 0", "const i32 6", 8));
    assert_refused(&m, &witness(100, 101), &forged_target(&m, 0, 20));
    let view = interpretable_module(&m);
    assert_eq!(view.functions[0], m.functions[0]);
    assert!(view.functions[0].is_declaration());
}

#[test]
fn an_empty_fill_witness_is_only_exact_identity() {
    let m = module(&program("i32", "const i64 0", "const i32 6", 8));
    let empty = FillCallWitness::default();
    let (out, verdict) = rebuild_fill_call(&m, 32, f(&m), &empty).unwrap();
    assert_eq!(&out, f(&m));
    assert_eq!(verdict.exact, 0);
    assert_eq!(verdict.refinements, 0);
    check_pass(&m, 32, f(&m), &out, &PassWitness::FillCall(empty)).unwrap();
}
