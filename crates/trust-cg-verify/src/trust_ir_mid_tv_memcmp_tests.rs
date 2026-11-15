// trust-cg-verify/trust_ir_mid_tv_memcmp_tests.rs - tests of the comparison-call checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A call of the `memcmp` or `bcmp` declaration with a constant count of 0
//! to 16 becomes loads and compares, and the target agrees with the source
//! run in a test view that gives the declaration the C library's byte loop
//! (the differential's own view does not, OD-164's merge boundary; the
//! default profile withholds the rewrite) for every count from 0 to 16 read by a zero test,
//! counts 0 and 1 whose result is read whole (its sign), operands that
//! overlap or are one pointer, and `bcmp`. Refused: a count past the
//! bound, a run-time count, a count of another type, a result whose sign
//! is read when more than one byte is compared, a callee the module
//! defines under the name, another prototype (a 16-bit count, a 64-bit
//! result), fresh values one short or one too many (a count off by one), a
//! name that is not fresh, and an empty claim. The expansion of one byte
//! more or one byte less than the call compares is not the claimed
//! rewrite, and the differential sees it on a pair that differs in the
//! byte it misses; so are one byte compared as a signed char, and the
//! chunks' xor replaced by an and.
//!
//! The witness types (`MemCmpWitness`, `MemCmp`, `MAX_MEMCMP_BYTES`, the
//! `PassWitness::MemCmp` variant, `MidTvError::NotMemCmp`) and the view's
//! comparison body are provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, SampleOutcome, check_pass, compare_samples,
    interpretable, run_samples, seeded_inputs,
};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"memcmp\"\n\
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

/// The values the expansion of `k` bytes names (module documentation).
fn fresh_count(k: u64) -> usize {
    match k {
        0 => 0,
        1 => 4,
        _ => {
            let parts = chunks(k);
            let wide = if parts.iter().any(|&(_, w)| w == 8) {
                8
            } else {
                4
            };
            let widened = parts.iter().filter(|&&(_, w)| w != wide).count();
            parts.len() * 6 + widened + (parts.len() - 1) + 2
        }
    }
}

fn witness(k: u64) -> MemCmpWitness {
    MemCmpWitness {
        rewrites: vec![MemCmp {
            value: v(40),
            fresh: (0..fresh_count(k)).map(|i| v(100 + i as u32)).collect(),
        }],
    }
}

/// Two 24-byte slots `A` (`%2`) and `B` (`%3`) holding the same three words
/// of `a` and `b` (`a ^ b` last); then `B`'s byte `at` is xored with `a & 1`
/// (so the bytes differ there for odd `a`) and its byte `at2` with `b & 1`.
/// The call `%40 = {callee}(A + {pa}, B + {pb}, {count})`; the result is
/// `{read}` of `%40` (`%41`), zero-extended or kept as the `u32` result.
fn program(callee: &str, at: u32, at2: u32, pa: u32, pb: &str, count: &str, read: &str) -> String {
    format!(
        "type ty.0 = u64\n\n\
functy.0 = (ptr, ptr, i32) -> (i32)\n\
functy.1 = (u32, u32) -> (u32)\n\n\
fn @{callee}(functy.0) {{\n}}\n\n\
fn @f(functy.1) {{\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 3], align 8\n\
\x20   %3 = alloca [ty.0 x 3], align 8\n\
\x20   %4 = zext u32 %0 to u64\n\
\x20   %5 = zext u32 %1 to u64\n\
\x20   %6 = const u64 1311768467294899695\n\
\x20   %7 = mul u64 %4, %6\n\
\x20   %8 = mul u64 %5, %6\n\
\x20   %9 = xor u64 %7, %8\n\
\x20   %10 = const usize 8\n\
\x20   %11 = const usize 16\n\
\x20   %12 = gep u8, ptr %2, %10\n\
\x20   %13 = gep u8, ptr %2, %11\n\
\x20   %14 = gep u8, ptr %3, %10\n\
\x20   %15 = gep u8, ptr %3, %11\n\
\x20   store u64 %7, ptr %2\n\
\x20   store u64 %8, ptr %12\n\
\x20   store u64 %9, ptr %13\n\
\x20   store u64 %7, ptr %3\n\
\x20   store u64 %8, ptr %14\n\
\x20   store u64 %9, ptr %15\n\
\x20   %16 = const usize {at}\n\
\x20   %17 = gep u8, ptr %3, %16\n\
\x20   %18 = load u8, ptr %17\n\
\x20   %19 = trunc u32 %0 to u8\n\
\x20   %20 = const u8 1\n\
\x20   %21 = and u8 %19, %20\n\
\x20   %22 = xor u8 %18, %21\n\
\x20   store u8 %22, ptr %17\n\
\x20   %23 = const usize {at2}\n\
\x20   %24 = gep u8, ptr %3, %23\n\
\x20   %25 = load u8, ptr %24\n\
\x20   %26 = trunc u32 %1 to u8\n\
\x20   %27 = and u8 %26, %20\n\
\x20   %28 = xor u8 %25, %27\n\
\x20   store u8 %28, ptr %24\n\
\x20   %29 = const usize {pa}\n\
\x20   %30 = gep u8, ptr %2, %29\n\
\x20   %31 = {pb}\n\
\x20   %32 = {count}\n\
\x20   %40 = call @func.0(%30, %31, %32)\n\
\x20   %33 = const i32 0\n\
\x20   {read}\n\
\x20   ret %42\n\
}}\n"
    )
}

/// A zero test of `%40` (`r == 0`) as the result.
const ZERO_TEST: &str = "%41 = icmp eq i32 %40, %33\n\x20   %42 = zext bool %41 to u32";
/// `%40` itself as the result (its sign read).
const WHOLE: &str = "%41 = add i32 %40, %33\n\x20   %42 = bitcast i32 %41 to u32";
/// `r < 0` as the result.
const SIGN: &str = "%41 = icmp slt i32 %40, %33\n\x20   %42 = zext bool %41 to u32";

/// `memcmp(A + 0, B + 0, k)`, the bytes differing at `at` and `at2`.
fn compare(k: u64, at: u32, at2: u32, read: &str) -> Module {
    module(&program(
        "memcmp",
        at,
        at2,
        0,
        "gep u8, ptr %3, %29",
        &format!("const i32 {k}"),
        read,
    ))
}

fn viewed_runs(
    m: &Module,
    src: &Function,
    out: &Function,
) -> (Vec<SampleOutcome>, Vec<SampleOutcome>) {
    let view = super::super::harness::interpretable_module_with_c_compare(m);
    let inputs = seeded_inputs(m, src, 32, 64, 11).expect("scalar parameters");
    let sv = interpretable(&view, src).unwrap_or_else(|| src.clone());
    let tv = interpretable(&view, out).unwrap_or_else(|| out.clone());
    let (a, _) = run_samples(&view, &sv, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&view, &tv, &inputs, DifferentialBudget::default());
    (a, t)
}

/// The rewrite on `m` checked, the call gone, and the target run against
/// the source in the view: they agree, and some inputs are compared.
fn accepted_and_agrees(m: &Module, w: &MemCmpWitness) -> Function {
    let src = f(m);
    let (out, verdict) = rebuild_mem_cmp(m, 32, src, w).expect("accepted");
    assert_eq!(verdict.exact, w.rewrites.len());
    check_pass(m, 32, src, &out, &PassWitness::MemCmp(w.clone())).expect("check_pass");
    assert!(
        !out.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Call { .. })),
        "the call is gone"
    );
    let (a, t) = viewed_runs(m, src, &out);
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
    out
}

#[test]
fn every_count_up_to_the_bound_becomes_loads_and_agrees() {
    for k in 0..=MAX_MEMCMP_BYTES {
        // The bytes differ at the last compared byte (or the first) when
        // `a` (or `b`) is odd.
        let last = u32::try_from(k.max(1) - 1).unwrap();
        let m = compare(k, last, 0, ZERO_TEST);
        let out = accepted_and_agrees(&m, &witness(k));
        if k >= 2 {
            let loads = out
                .blocks
                .iter()
                .flat_map(|b| &b.body)
                .filter(|n| matches!(n.inst, Inst::Load { align: Some(1), .. }))
                .count();
            assert_eq!(loads, 2 * chunks(k).len(), "k = {k}");
        }
    }
}

#[test]
fn a_whole_result_of_zero_or_one_byte_agrees() {
    for k in [0, 1] {
        accepted_and_agrees(&compare(k, 0, 0, WHOLE), &witness(k));
        accepted_and_agrees(&compare(k, 0, 0, SIGN), &witness(k));
    }
}

#[test]
fn overlapping_operands_and_bcmp_agree() {
    // `memcmp(A + 1, A + 8, 8)`: the ranges overlap in byte 8.
    let m = module(&program(
        "memcmp",
        3,
        5,
        1,
        "gep u8, ptr %2, %10",
        "const i32 8",
        ZERO_TEST,
    ));
    accepted_and_agrees(&m, &witness(8));
    // One pointer for both.
    let m = module(&program(
        "memcmp",
        3,
        5,
        0,
        "copy ptr %30",
        "const i32 5",
        ZERO_TEST,
    ));
    accepted_and_agrees(&m, &witness(5));
    // `bcmp`, three bytes.
    let m = module(&program(
        "bcmp",
        2,
        0,
        0,
        "gep u8, ptr %3, %29",
        "const i32 3",
        ZERO_TEST,
    ));
    accepted_and_agrees(&m, &witness(3));
}

#[test]
fn calls_off_the_form_are_refused() {
    let refused = |m: &Module, w: &MemCmpWitness| {
        assert!(
            matches!(
                rebuild_mem_cmp(m, 32, f(m), w),
                Err(MidTvError::NotMemCmp { .. })
            ),
            "{w:?}"
        );
    };
    // A count past the bound.
    refused(&compare(17, 0, 0, ZERO_TEST), &witness(17));
    // A run-time count, and a count of another type than the parameter's.
    let runtime = module(
        &program(
            "memcmp",
            0,
            0,
            0,
            "gep u8, ptr %3, %29",
            "const i32 8\n\x20   %44 = bitcast u32 %1 to i32\n\x20   %45 = and i32 %44, %32",
            ZERO_TEST,
        )
        .replace("call @func.0(%30, %31, %32)", "call @func.0(%30, %31, %45)"),
    );
    refused(&runtime, &witness(8));
    let unsigned = module(&program(
        "memcmp",
        0,
        0,
        0,
        "gep u8, ptr %3, %29",
        "const u32 4",
        ZERO_TEST,
    ));
    refused(&unsigned, &witness(4));
    // The sign read when more than one byte is compared.
    refused(&compare(2, 0, 0, SIGN), &witness(2));
    refused(&compare(4, 0, 0, WHOLE), &witness(4));
    // A callee the module defines under the name.
    let defined = module(
        &program(
            "memcmp",
            0,
            0,
            0,
            "gep u8, ptr %3, %29",
            "const i32 4",
            ZERO_TEST,
        )
        .replace(
            "fn @memcmp(functy.0) {\n}",
            "fn @memcmp(functy.0) {\nbb0(%0: ptr, %1: ptr, %2: i32):\n    ret %2\n}",
        ),
    );
    refused(&defined, &witness(4));
    // Other prototypes: a 16-bit count, a 64-bit result.
    let narrow = module(
        &program(
            "memcmp",
            0,
            0,
            0,
            "gep u8, ptr %3, %29",
            "const i16 4",
            ZERO_TEST,
        )
        .replace(
            "functy.0 = (ptr, ptr, i32) -> (i32)",
            "functy.0 = (ptr, ptr, i16) -> (i32)",
        ),
    );
    refused(&narrow, &witness(4));
    let wide = module(
        &program(
            "memcmp",
            0,
            0,
            0,
            "gep u8, ptr %3, %29",
            "const i32 4",
            "%41 = const u32 0\n\x20   %42 = copy u32 %41",
        )
        .replace(
            "functy.0 = (ptr, ptr, i32) -> (i32)",
            "functy.0 = (ptr, ptr, i32) -> (i64)",
        ),
    );
    refused(&wide, &witness(4));
    // Fresh values one too many or one short (a count off by one).
    let m = compare(4, 3, 0, ZERO_TEST);
    let mut w = witness(4);
    w.rewrites[0].fresh.push(v(99));
    refused(&m, &w);
    let mut w = witness(4);
    w.rewrites[0].fresh.pop();
    refused(&m, &w);
    // A name that is not fresh, the call claimed twice, nothing claimed.
    let mut w = witness(4);
    w.rewrites[0].fresh[2] = v(9);
    refused(&m, &w);
    let mut w = witness(4);
    w.rewrites.push(w.rewrites[0].clone());
    refused(&m, &w);
    refused(&m, &MemCmpWitness::default());
    // Not a call.
    let mut w = witness(4);
    w.rewrites[0].value = v(9);
    refused(&m, &w);
}

/// `target` is not the claimed rewrite of `m`, and the view's runs tell it
/// apart from the source.
fn refused_and_disagrees(m: &Module, w: &MemCmpWitness, target: &Function) {
    let src = f(m);
    assert!(matches!(
        check_pass(m, 32, src, target, &PassWitness::MemCmp(w.clone())),
        Err(MidTvError::TargetDiffers { .. })
    ));
    let (a, t) = viewed_runs(m, src, target);
    assert!(compare_samples(&a, &t).mismatch.is_some());
}

#[test]
fn a_count_off_by_one_and_a_signed_byte_disagree() {
    // One byte short: the bytes differ only in the last one, which the
    // target leaves out.
    let m = compare(5, 4, 4, ZERO_TEST);
    let short = compare(4, 4, 4, ZERO_TEST);
    let (target, _) = rebuild_mem_cmp(&short, 32, f(&short), &witness(4)).expect("accepted");
    refused_and_disagrees(&m, &witness(5), &target);
    // One byte more: the bytes differ only in the byte after them.
    let m = compare(4, 4, 4, ZERO_TEST);
    let long = compare(5, 4, 4, ZERO_TEST);
    let (target, _) = rebuild_mem_cmp(&long, 32, f(&long), &witness(5)).expect("accepted");
    refused_and_disagrees(&m, &witness(4), &target);
    // One byte compared as signed chars: the result's sign flips when one
    // byte is at least 0x80 and the other is not (the differing byte here
    // has its top bit flipped too).
    let m = module(
        &program(
            "memcmp",
            0,
            0,
            0,
            "gep u8, ptr %3, %29",
            "const i32 1",
            SIGN,
        )
        .replace("%20 = const u8 1", "%20 = const u8 129"),
    );
    let w = witness(1);
    let (mut target, _) = rebuild_mem_cmp(&m, 32, f(&m), &w).expect("accepted");
    for node in target.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::Cast {
            op, src_ty: Ty::U8, ..
        } = &mut node.inst
        {
            *op = CastOp::SExt;
        }
    }
    refused_and_disagrees(&m, &w, &target);
    // The chunks' xor replaced by an and.
    let m = compare(8, 6, 0, ZERO_TEST);
    let w = witness(8);
    let (mut target, _) = rebuild_mem_cmp(&m, 32, f(&m), &w).expect("accepted");
    for node in target.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::BinOp {
            op: op @ BinOp::Xor,
            ..
        } = &mut node.inst
        {
            *op = BinOp::And;
        }
    }
    refused_and_disagrees(&m, &w, &target);
}
