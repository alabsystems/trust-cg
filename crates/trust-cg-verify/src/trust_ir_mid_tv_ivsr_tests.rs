// trust-cg-verify/trust_ir_mid_tv_ivsr_tests.rs - tests of the strength reduction checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! An element address `slot + i * 8` (and `+ 16`) of a counted loop becomes
//! a pointer induction variable exactly as the module docs construct it,
//! and agrees with its source in the interpreter; the negative controls are
//! refused: a scale, offset or root the value does not read as, a value
//! that is not linear in the variable, a variable stepping by a value that
//! is not a constant, an initial value that may be poison, a strand type of
//! another width, names that are not fresh, and too few initial values.
//!
//! The witness types (`IvSrWitness`, `IvSrLoop`, `IvSrStrand`, `IvSrUse`,
//! `PassWitness::IvSr`) are provisional surfaces pending the owner's
//! sign-off (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, run_samples,
    seeded_inputs,
};
use super::*;
use trust_ir::Module;

const HEADER: &str = "; TrustIr text format v1\nmodule \"ivsr\"\n\
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

/// The sum of `%x * 1..=8` stored in a slot, read back by index.
const SUM: &str = "functy.0 = (u64, u32) -> (u64)\n\n\
type ty.0 = u64\n\n\
fn @f(functy.0) {\n\
bb0(%0: u64, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 8], align 8\n\
\x20   store u64 %0, ptr %2\n\
\x20   %30 = const i32 8\n\
\x20   %31 = gep inbounds u8, ptr %2, %30\n\
\x20   store u64 %0, ptr %31\n\
\x20   %32 = const i32 16\n\
\x20   %33 = gep inbounds u8, ptr %2, %32\n\
\x20   store u64 %0, ptr %33\n\
\x20   %34 = const i32 24\n\
\x20   %35 = gep inbounds u8, ptr %2, %34\n\
\x20   store u64 %0, ptr %35\n\
\x20   %36 = const i32 32\n\
\x20   %37 = gep inbounds u8, ptr %2, %36\n\
\x20   store u64 %0, ptr %37\n\
\x20   %38 = const i32 40\n\
\x20   %39 = gep inbounds u8, ptr %2, %38\n\
\x20   store u64 %0, ptr %39\n\
\x20   %3 = const u32 5\n\
\x20   %4 = and u32 %1, %3\n\
\x20   %5 = const u32 0\n\
\x20   %6 = const u64 0\n\
\x20   br bb1(%5, %6)\n\
bb1(%10: u32, %11: u64):\n\
\x20   %12 = icmp ult u32 %10, %4\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = ptrtoint ptr %2 to i32\n\
\x20   %14 = bitcast u32 %10 to i32\n\
\x20   %15 = const i32 8\n\
\x20   %16 = mul i32 %14, %15\n\
\x20   %17 = add i32 %13, %16\n\
\x20   %18 = inttoptr i32 %17 to ptr\n\
\x20   %19 = load u64, ptr %18\n\
\x20   %20 = add u64 %11, %19\n\
\x20   %21 = add i32 %17, %32\n\
\x20   %22 = inttoptr i32 %21 to ptr\n\
\x20   %23 = load u64, ptr %22\n\
\x20   %24 = add u64 %20, %23\n\
\x20   %25 = const u32 1\n\
\x20   %26 = add u32 %10, %25\n\
\x20   br bb1(%26, %24)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

/// [`SUM`] with `%17` and `%21` on one strand, as the module docs build it.
const SUM_REDUCED: &str = "functy.0 = (u64, u32) -> (u64)\n\n\
type ty.0 = u64\n\n\
fn @f(functy.0) {\n\
bb0(%0: u64, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 8], align 8\n\
\x20   store u64 %0, ptr %2\n\
\x20   %30 = const i32 8\n\
\x20   %31 = gep inbounds u8, ptr %2, %30\n\
\x20   store u64 %0, ptr %31\n\
\x20   %32 = const i32 16\n\
\x20   %33 = gep inbounds u8, ptr %2, %32\n\
\x20   store u64 %0, ptr %33\n\
\x20   %34 = const i32 24\n\
\x20   %35 = gep inbounds u8, ptr %2, %34\n\
\x20   store u64 %0, ptr %35\n\
\x20   %36 = const i32 32\n\
\x20   %37 = gep inbounds u8, ptr %2, %36\n\
\x20   store u64 %0, ptr %37\n\
\x20   %38 = const i32 40\n\
\x20   %39 = gep inbounds u8, ptr %2, %38\n\
\x20   store u64 %0, ptr %39\n\
\x20   %3 = const u32 5\n\
\x20   %4 = and u32 %1, %3\n\
\x20   %5 = const u32 0\n\
\x20   %6 = const u64 0\n\
\x20   %100 = bitcast u32 %5 to i32\n\
\x20   %101 = const i32 8\n\
\x20   %102 = mul i32 %100, %101\n\
\x20   %103 = ptrtoint ptr %2 to i32\n\
\x20   %104 = add i32 %102, %103\n\
\x20   br bb1(%5, %6, %104)\n\
bb1(%10: u32, %11: u64, %200: i32):\n\
\x20   %12 = icmp ult u32 %10, %4\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = ptrtoint ptr %2 to i32\n\
\x20   %14 = bitcast u32 %10 to i32\n\
\x20   %15 = const i32 8\n\
\x20   %16 = mul i32 %14, %15\n\
\x20   %17 = copy i32 %200\n\
\x20   %18 = inttoptr i32 %17 to ptr\n\
\x20   %19 = load u64, ptr %18\n\
\x20   %20 = add u64 %11, %19\n\
\x20   %107 = const i32 16\n\
\x20   %21 = add i32 %200, %107\n\
\x20   %22 = inttoptr i32 %21 to ptr\n\
\x20   %23 = load u64, ptr %22\n\
\x20   %24 = add u64 %20, %23\n\
\x20   %25 = const u32 1\n\
\x20   %26 = add u32 %10, %25\n\
\x20   %105 = const i32 8\n\
\x20   %106 = add i32 %200, %105\n\
\x20   br bb1(%26, %24, %106)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

fn strand(
    scale: u128,
    roots: &[(u32, u128)],
    ty: Ty,
    uses: &[(u32, u128, Option<u32>)],
) -> IvSrStrand {
    IvSrStrand {
        param: v(200),
        ty,
        iv: v(10),
        scale,
        roots: roots.iter().map(|(r, b)| (v(*r), *b)).collect(),
        init: (100..105).map(v).collect(),
        step: vec![v(105), v(106)],
        uses: uses
            .iter()
            .map(|(value, offset, constant)| IvSrUse {
                value: v(*value),
                offset: *offset,
                constant: constant.map(v),
            })
            .collect(),
    }
}

fn witness(s: IvSrStrand) -> PassWitness {
    PassWitness::IvSr(IvSrWitness {
        loops: vec![IvSrLoop {
            header: BlockId::new(1),
            strands: vec![s],
        }],
    })
}

fn good() -> IvSrStrand {
    strand(8, &[(2, 1)], Ty::I32, &[(17, 0, None), (21, 16, Some(107))])
}

fn rebuild(m: &Module, w: &PassWitness) -> Result<Function, MidTvError> {
    let PassWitness::IvSr(iw) = w else {
        unreachable!()
    };
    let (out, _) = rebuild_ivsr(32, f(m), iw)?;
    check_pass(m, 32, f(m), &out, w)?;
    Ok(out)
}

fn agree(m: &Module, target: &Function) {
    let source = f(m);
    let inputs = seeded_inputs(m, source, 32, 64, 9).expect("scalar parameters");
    let (a, _) = run_samples(m, source, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(m, target, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

fn refused(m: &Module, w: &PassWitness, why: &str) {
    match rebuild(m, w) {
        Err(MidTvError::NotLoopRewrite { why: got, .. }) => {
            assert!(got.contains(why), "refused for `{got}`, expected `{why}`");
        }
        other => panic!("expected a refusal containing `{why}`, got {other:?}"),
    }
}

#[test]
fn element_addresses_become_a_pointer_induction_variable() {
    let src = module(SUM);
    let out = rebuild(&src, &witness(good())).expect("accepted");
    let expected = module(SUM_REDUCED);
    assert_eq!(&out, f(&expected));
    agree(&src, &out);
}

#[test]
fn a_scale_offset_or_root_the_value_does_not_read_as_is_refused() {
    let src = module(SUM);
    let w = witness(strand(4, &[(2, 1)], Ty::I32, &[(17, 0, None)]));
    refused(&src, &w, "is not the strand's scale");
    let w = witness(strand(8, &[(2, 1)], Ty::I32, &[(21, 8, Some(107))]));
    refused(&src, &w, "is not the strand's scale");
    let w = witness(strand(8, &[], Ty::I32, &[(17, 0, None)]));
    refused(&src, &w, "is not the strand's scale");
    let w = witness(strand(8, &[(2, 2)], Ty::I32, &[(17, 0, None)]));
    refused(&src, &w, "is not the strand's scale");
    // A zero offset that names a constant.
    let w = witness(strand(8, &[(2, 1)], Ty::I32, &[(17, 0, Some(107))]));
    refused(&src, &w, "is not the strand's scale");
}

#[test]
fn a_value_that_is_not_linear_is_refused() {
    let src = module(SUM);
    let w = witness(strand(8, &[(2, 1)], Ty::U64, &[(19, 0, None)]));
    refused(&src, &w, "as wide as the induction variable");
    let m = module(&SUM.replace("%16 = mul i32 %14, %15", "%16 = mul i32 %14, %14"));
    refused(&m, &witness(good()), "is not linear");
}

#[test]
fn a_variable_stepping_by_a_non_constant_is_refused() {
    let m = module(&SUM.replace("%26 = add u32 %10, %25", "%26 = add u32 %10, %4"));
    refused(&m, &witness(good()), "does not step by a constant");
}

#[test]
fn an_initial_value_that_may_be_poison_is_refused() {
    let m = module(&SUM.replace("%5 = const u32 0", "%5 = undef u32"));
    refused(&m, &witness(good()), "may be poison");
}

#[test]
fn names_that_are_not_fresh_or_too_few_are_refused() {
    let src = module(SUM);
    let mut s = good();
    s.param = v(13);
    refused(&src, &witness(s), "is not fresh");
    let mut s = good();
    s.init.pop();
    refused(&src, &witness(s), "too few initial values");
    let mut s = good();
    s.init.push(v(108));
    refused(&src, &witness(s), "too many initial values");
}
