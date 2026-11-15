// trust-cg-verify/trust_ir_mid_tv_loop_tests.rs - tests of the loop passes' checkers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Each loop rewrite is accepted on the shape its checker states, and its
//! negative controls are refused: a load hoisted out of a loop with an
//! aliasing store, a trapping instruction that is not guaranteed to execute,
//! an operand computed in the loop, a parameter the loop changes, an
//! instruction or an invariant parameter whose operand has another type
//! than its form declares, an irreducible region; a reduction with a second
//! effect, a trip count that wraps under an extension, a step other than
//! one, a non-affine or possibly poison accumulator, a used overflow flag, a
//! second exit, an initial value, coefficient or bound of another type, and
//! values that are not fresh or more than the shared closed form defines.
//! Accepted rewrites agree with their sources in the interpreter on seeded
//! inputs. The closed form's lemmas hold on every input at small widths and
//! their controls fail; `ay` refutes no lemma and every control (an
//! `unknown` proves nothing).
//!
//! The witness types and `PassWitness::Licm` / `PassWitness::LoopCf` are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, run_samples,
    seeded_inputs,
};
use super::*;
use crate::ay_bridge::{AYConfig, AYResult, verify_with_ay};
use crate::lowering_proof::{VerificationConfig, verify_by_evaluation_with_config};
use crate::verify::VerificationResult;
use trust_ir::Module;

const HEADER: &str = "; TrustIr text format v1\nmodule \"loops\"\n\
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

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn b(n: u32) -> BlockId {
    BlockId::new(n)
}

/// `count` fresh values from `%100`.
fn fresh(count: u32) -> Vec<ValueId> {
    (100..100 + count).map(v).collect()
}

fn cf(header: u32, values: Vec<ValueId>) -> PassWitness {
    PassWitness::LoopCf(LoopCfWitness {
        loops: vec![LoopCfLoop {
            header: b(header),
            values,
        }],
    })
}

fn licm(header: u32, params: &[u32], hoisted: &[u32]) -> PassWitness {
    PassWitness::Licm(LicmWitness {
        loops: vec![LicmLoop {
            header: b(header),
            invariant_params: params.iter().map(|&n| v(n)).collect(),
            hoisted: hoisted.iter().map(|&n| v(n)).collect(),
        }],
    })
}

/// The function the checker rebuilds from `witness`, or its refusal.
fn rebuild(m: &Module, f: &Function, witness: &PassWitness) -> Result<Function, MidTvError> {
    let (out, _) = match witness {
        PassWitness::LoopCf(w) => rebuild_loop_cf(32, f, w)?,
        PassWitness::Licm(w) => rebuild_licm(m, 32, f, w)?,
        _ => unreachable!(),
    };
    check_pass(m, 32, f, &out, witness)?;
    Ok(out)
}

/// The source and target agree in the interpreter on seeded inputs.
fn agree(m: &Module, source: &Function, target: &Function) {
    let inputs = seeded_inputs(m, source, 32, 64, 7).expect("scalar parameters");
    let (a, _) = run_samples(m, source, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(m, target, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(
        report.compared > 0,
        "some inputs are compared: {report:?} {a:?}"
    );
}

fn refused(m: &Module, name: &str, witness: &PassWitness, why: &str) {
    let f = func(m, name);
    match rebuild(m, f, witness) {
        Err(MidTvError::NotLoopRewrite { why: got, .. }) => {
            assert!(got.contains(why), "refused for `{got}`, expected `{why}`");
        }
        other => panic!("expected a refusal containing `{why}`, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Closed-form induction
// ---------------------------------------------------------------------------

/// `(i0..hi).map(|i| i as u64).sum::<u64>()` with both ends masked, the
/// mid-end's form of `e_range_sum`: an invariant bound parameter, the
/// increment in the body, the sum through `add.overflow` with a dead flag
/// and a copy on the latch.
const SUM: &str = "functy.0 = (u32, u32) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = const u32 63\n\
\x20   %3 = and u32 %1, %2\n\
\x20   %4 = and u32 %0, %2\n\
\x20   %5 = const u64 0\n\
\x20   br bb1(%5, %3, %4)\n\
bb1(%10: u64, %11: u32, %12: u32):\n\
\x20   %13 = icmp ult u32 %12, %11\n\
\x20   condbr %13, bb2, bb3\n\
bb3:\n\
\x20   ret %10\n\
bb2:\n\
\x20   %14 = const u32 1\n\
\x20   %15 = add u32 %12, %14\n\
\x20   %16 = zext u32 %12 to u64\n\
\x20   %17, %18 = add.overflow u64 %10, %16\n\
\x20   br bb4\n\
bb4:\n\
\x20   %19 = copy u64 %17\n\
\x20   br bb1(%19, %11, %15)\n\
}\n";

/// The closed form of [`SUM`], instruction for instruction as the module
/// docs fix it.
const SUM_CLOSED: &str = "functy.0 = (u32, u32) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = const u32 63\n\
\x20   %3 = and u32 %1, %2\n\
\x20   %4 = and u32 %0, %2\n\
\x20   %5 = const u64 0\n\
\x20   %100 = icmp ult u32 %4, %3\n\
\x20   %101 = sub u32 %3, %4\n\
\x20   %102 = const u32 0\n\
\x20   %103 = select u32 %100, %101, %102\n\
\x20   %104 = zext u32 %103 to u64\n\
\x20   %105 = zext u32 %4 to u64\n\
\x20   %106 = const u64 1\n\
\x20   %107 = and u64 %104, %106\n\
\x20   %108 = sub u64 %104, %107\n\
\x20   %109 = lshr u64 %108, %106\n\
\x20   %110 = sub u64 %104, %106\n\
\x20   %111 = add u64 %110, %107\n\
\x20   %112 = mul u64 %109, %111\n\
\x20   %113 = mul u64 %104, %105\n\
\x20   %114 = add u64 %113, %112\n\
\x20   %115 = add u64 %5, %114\n\
\x20   %116 = add u32 %4, %103\n\
\x20   br bb1(%115, %3, %116)\n\
bb1(%10: u64, %11: u32, %12: u32):\n\
\x20   %13 = icmp ult u32 %12, %11\n\
\x20   br bb3\n\
bb3:\n\
\x20   ret %10\n\
}\n";

#[test]
fn a_counted_sum_becomes_its_closed_form() {
    let src = module(SUM);
    let f = func(&src, "f");
    let w = cf(1, fresh(17));
    let out = rebuild(&src, f, &w).expect("accepted");
    let expected = module(SUM_CLOSED);
    assert_eq!(&out, func(&expected, "f"));
    let PassWitness::LoopCf(lw) = &w else {
        unreachable!()
    };
    let (_, verdict) = rebuild_loop_cf(32, f, lw).expect("accepted");
    // `add.overflow`, `add` and `zext` inspect their operands.
    assert_eq!((verdict.exact, verdict.refinements), (0, 1));
    agree(&src, f, &out);
}

/// A loop over `u32` with an `!=` exit taken on the `else` edge, a weighted
/// term `i * 3` subtracted, a counter in `u64` and an invariant term.
const MIXED: &str = "functy.0 = (u32, u32, u32) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u32, %2: u32):\n\
\x20   %3 = const u32 255\n\
\x20   %4 = and u32 %0, %3\n\
\x20   %5 = add u32 %4, %1\n\
\x20   %6 = const u64 7\n\
\x20   br bb1(%1, %2, %6, %0)\n\
bb1(%10: u32, %11: u32, %12: u64, %13: u32):\n\
\x20   %14 = icmp eq u32 %10, %5\n\
\x20   condbr %14, bb3, bb2\n\
bb2:\n\
\x20   %15 = const u32 3\n\
\x20   %16 = mul u32 %10, %15\n\
\x20   %17 = sub u32 %11, %16\n\
\x20   %18 = const u64 1\n\
\x20   %19 = add u64 %18, %12\n\
\x20   %20 = add u32 %13, %2\n\
\x20   %21 = const u32 1\n\
\x20   %22 = add u32 %10, %21\n\
\x20   br bb1(%22, %17, %19, %20)\n\
bb3:\n\
\x20   %23 = zext u32 %11 to u64\n\
\x20   %24 = zext u32 %13 to u64\n\
\x20   %25 = xor u64 %23, %12\n\
\x20   %26 = xor u64 %25, %24\n\
\x20   ret %26\n\
}\n";

#[test]
fn a_wrapping_ne_loop_with_weighted_counted_and_invariant_terms_agrees() {
    let src = module(MIXED);
    let f = func(&src, "f");
    // n; i: 1; `-= i * 3`: 9 + const + mul + sub; `+= 1` at u64: zext and
    // add (a coefficient of one multiplies nothing); `+= %2`: mul, add.
    let w = cf(1, fresh(1 + 1 + 12 + 2 + 2));
    let out = rebuild(&src, f, &w).expect("accepted");
    assert_eq!(out.blocks.len(), 3);
    agree(&src, f, &out);
}

/// A signed loop accumulating the sign extension of its variable into `i64`.
const SIGNED: &str = "functy.0 = (i32, i32) -> (i64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: i32, %1: i32):\n\
\x20   %2 = const i32 127\n\
\x20   %3 = and i32 %1, %2\n\
\x20   %4 = const i32 64\n\
\x20   %5 = sub i32 %3, %4\n\
\x20   %6 = and i32 %0, %2\n\
\x20   %7 = sub i32 %6, %4\n\
\x20   %8 = const i64 -5\n\
\x20   br bb1(%7, %8)\n\
bb1(%10: i32, %11: i64):\n\
\x20   %12 = icmp sge i32 %10, %5\n\
\x20   condbr %12, bb3, bb2\n\
bb2:\n\
\x20   %13 = sext i32 %10 to i64\n\
\x20   %14 = add i64 %11, %13\n\
\x20   %15 = const i32 1\n\
\x20   %16 = add i32 %10, %15\n\
\x20   br bb1(%16, %14)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

#[test]
fn a_signed_loop_with_a_sign_extended_sum_agrees() {
    let src = module(SIGNED);
    let f = func(&src, "f");
    let w = cf(1, fresh(4 + 1 + 12));
    let out = rebuild(&src, f, &w).expect("accepted");
    agree(&src, f, &out);
}

/// Three `u64` accumulators of one `u32` loop: `+= i`, `+= 3 * i` and
/// `+= 1`, all through `zext`.
const SHARED: &str = "functy.0 = (u32, u32) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = const u32 63\n\
\x20   %3 = and u32 %1, %2\n\
\x20   %4 = and u32 %0, %2\n\
\x20   %5 = const u64 0\n\
\x20   %6 = zext u32 %0 to u64\n\
\x20   br bb1(%4, %5, %6, %5)\n\
bb1(%10: u32, %11: u64, %12: u64, %13: u64):\n\
\x20   %14 = icmp ult u32 %10, %3\n\
\x20   condbr %14, bb2, bb3\n\
bb2:\n\
\x20   %15 = zext u32 %10 to u64\n\
\x20   %16 = add u64 %11, %15\n\
\x20   %17 = const u64 3\n\
\x20   %18 = mul u64 %15, %17\n\
\x20   %19 = add u64 %12, %18\n\
\x20   %20 = const u64 1\n\
\x20   %21 = add u64 %13, %20\n\
\x20   %22 = const u32 1\n\
\x20   %23 = add u32 %10, %22\n\
\x20   br bb1(%23, %16, %19, %21)\n\
bb3:\n\
\x20   %24 = xor u64 %11, %12\n\
\x20   %25 = xor u64 %24, %13\n\
\x20   ret %25\n\
}\n";

#[test]
fn accumulators_of_one_type_share_the_trip_count_and_the_sum() {
    let src = module(SHARED);
    let f = func(&src, "f");
    // N: 4; i: 1; `+= i`: zext N, zext i0, the nine-instruction sum, add;
    // `+= 3 * i`: const, mul, add on the shared sum; `+= 1`: add on the
    // shared N.
    let w = cf(1, fresh(4 + 1 + 12 + 3 + 1));
    let out = rebuild(&src, f, &w).expect("accepted");
    let zexts = out.blocks[0]
        .body
        .iter()
        .filter(|n| {
            matches!(
                n.inst,
                Inst::Cast {
                    op: CastOp::ZExt,
                    ..
                }
            )
        })
        .count();
    // `%6`, `zext N` and `zext i0`, once each.
    assert_eq!(zexts, 3);
    agree(&src, f, &out);
    // A witness sized for one sum per accumulator is refused.
    refused(&src, "f", &cf(1, fresh(4 + 1 + 11 + 12 + 1)), "too many");
}

#[test]
fn values_of_another_type_are_refused_by_the_closed_form() {
    // An initial value of the bound's type for the `u64` sum (the source
    // faults at the header's binding; the closed form would add it).
    let m = sum_with(&[("br bb1(%5, %3, %4)", "br bb1(%3, %3, %4)")]);
    refused(&m, "f", &cf(1, fresh(17)), "does not have its type");
    // A `u32` coefficient of the `u64` sum, read only in the body (a loop
    // that runs zero times never reads it).
    let m = sum_with(&[(
        "%17, %18 = add.overflow u64 %10, %16",
        "%17, %18 = add.overflow u64 %10, %0",
    )]);
    refused(&m, "f", &cf(1, fresh(12)), "does not have its type");
    // A `u64` bound of the `u32` compare.
    let m = sum_with(&[("br bb1(%5, %3, %4)", "br bb1(%5, %5, %4)")]);
    refused(&m, "f", &cf(1, fresh(17)), "the bound does not have");
}

/// [`SUM`] with `edit` applied to its text.
fn sum_with(edit: &[(&str, &str)]) -> Module {
    let mut text = SUM.to_string();
    for (from, to) in edit {
        assert!(text.contains(from), "{from}");
        text = text.replace(from, to);
    }
    module(&text)
}

#[test]
fn a_reduction_with_a_second_effect_is_refused() {
    let m = sum_with(&[(
        "\x20   %19 = copy u64 %17\n",
        "\x20   %19 = copy u64 %17\n\x20   %30 = alloca u64\n\x20   store u64 %19, ptr %30\n",
    )]);
    refused(&m, "f", &cf(1, fresh(17)), "cannot drop");
}

#[test]
fn a_zero_extension_under_a_wrapping_exit_is_refused() {
    // `!=` lets the variable wrap: `zext(i0 + k)` is not `zext(i0) + k`.
    let m = sum_with(&[("icmp ult u32 %12, %11", "icmp ne u32 %12, %11")]);
    refused(&m, "f", &cf(1, fresh(17)), "not an affine accumulator");
}

#[test]
fn a_step_other_than_one_is_refused() {
    let m = sum_with(&[("%14 = const u32 1", "%14 = const u32 2")]);
    refused(&m, "f", &cf(1, fresh(17)), "does not step by + 1");
}

#[test]
fn a_geometric_accumulator_is_refused() {
    let m = sum_with(&[(
        "%17, %18 = add.overflow u64 %10, %16",
        "%30 = const u64 3\n\x20   %31 = mul u64 %10, %30\n\x20   %17, %18 = add.overflow u64 %31, %16",
    )]);
    refused(&m, "f", &cf(1, fresh(17)), "not an affine accumulator");
}

#[test]
fn a_used_overflow_flag_is_refused() {
    let m = sum_with(&[(
        "\x20   br bb4\n",
        "\x20   %30 = select u64 %18, %17, %16\n\x20   br bb4\n",
    )]);
    refused(&m, "f", &cf(1, fresh(17)), "not an affine accumulator");
}

#[test]
fn a_possibly_poison_initial_value_is_refused() {
    let m = sum_with(&[("%5 = const u64 0", "%5 = undef u64")]);
    refused(&m, "f", &cf(1, fresh(17)), "may be poison");
}

#[test]
fn a_second_exit_is_refused() {
    let m = sum_with(&[(
        "\x20   br bb4\n",
        "\x20   %30 = icmp eq u32 %12, %11\n\x20   condbr %30, bb3, bb4\n",
    )]);
    refused(&m, "f", &cf(1, fresh(17)), "leaves the loop");
}

#[test]
fn values_that_are_not_fresh_or_too_few_are_refused() {
    let src = module(SUM);
    let mut values = fresh(17);
    values[3] = v(13);
    refused(&src, "f", &cf(1, values), "not fresh");
    refused(&src, "f", &cf(1, fresh(16)), "too few");
    refused(&src, "f", &cf(1, fresh(18)), "too many");
}

/// Two blocks entering each other from the entry: a cycle with two entries
/// and no back edge by dominance.
const IRREDUCIBLE: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 0\n\
\x20   %2 = icmp eq u32 %0, %1\n\
\x20   condbr %2, bb1(%1), bb2(%1)\n\
bb1(%3: u32):\n\
\x20   %4 = const u32 1\n\
\x20   %5 = add u32 %3, %4\n\
\x20   %6 = icmp ult u32 %5, %0\n\
\x20   condbr %6, bb2(%5), bb3\n\
bb2(%7: u32):\n\
\x20   %8 = const u32 1\n\
\x20   %9 = add u32 %7, %8\n\
\x20   br bb1(%9)\n\
bb3:\n\
\x20   ret %5\n\
}\n";

#[test]
fn an_irreducible_cycle_is_refused_by_both_passes() {
    let m = module(IRREDUCIBLE);
    refused(&m, "f", &cf(1, fresh(5)), "no back edge");
    refused(&m, "f", &licm(1, &[], &[4]), "no back edge");
}

// ---------------------------------------------------------------------------
// Loop-invariant code motion
// ---------------------------------------------------------------------------

/// A loop reading `p[0]` in its header and `p[j * 4 + 1]` in its body, with
/// an invariant parameter `j`, a division by an invariant value and an
/// optional store through `p` (`STORE`).
fn invariant_loop(store: bool) -> String {
    let store = if store {
        "\x20   store u32 %16, ptr %0\n"
    } else {
        ""
    };
    format!(
        "functy.0 = (ptr, u32, u32) -> (u32)\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: ptr, %1: u32, %2: u32):\n\
         \x20   %3 = const u32 0\n\
         \x20   %4 = const u32 3\n\
         \x20   %5 = and u32 %1, %4\n\
         \x20   br bb1(%3, %3, %5)\n\
         bb1(%10: u32, %11: u32, %12: u32):\n\
         \x20   %13 = load u32, ptr %0\n\
         \x20   %14 = icmp ult u32 %10, %13\n\
         \x20   condbr %14, bb2, bb3\n\
         bb2:\n\
         \x20   %15 = const u32 4\n\
         \x20   %16 = mul u32 %12, %15\n\
         \x20   %17 = udiv u32 %10, %2\n\
         \x20   %18 = add u32 %11, %16\n\
         {store}\
         \x20   %19 = const u32 1\n\
         \x20   %20 = add u32 %10, %19\n\
         \x20   br bb1(%20, %18, %12)\n\
         bb3:\n\
         \x20   ret %11\n\
         }}\n"
    )
}

#[test]
fn invariant_parameters_constants_products_and_a_header_load_are_hoisted() {
    let src = module(&invariant_loop(false));
    let f = func(&src, "f");
    let out = rebuild(&src, f, &licm(1, &[12], &[13, 15, 16])).expect("accepted");
    // The parameter is gone, the three instructions end the preheader.
    assert_eq!(out.blocks[1].params.len(), 2);
    let pre: Vec<ValueId> = out.blocks[0]
        .body
        .iter()
        .filter_map(|n| n.results.first().copied())
        .collect();
    assert_eq!(pre, vec![v(3), v(4), v(5), v(13), v(15), v(16)]);
    assert!(matches!(
        &out.blocks[1].body[0].inst,
        Inst::ICmp { lhs, rhs, .. } if *lhs == v(10) && *rhs == v(13)
    ));
}

#[test]
fn a_division_by_a_constant_moved_with_it_is_speculatable() {
    let m = module(&invariant_loop(false).replace(
        "\x20   %18 = add u32 %11, %16\n",
        "\x20   %40 = const u32 5\n\x20   %41 = urem u32 %2, %40\n\x20   %18 = add u32 %41, %16\n",
    ));
    let f = func(&m, "f");
    rebuild(&m, f, &licm(1, &[], &[40, 41])).expect("accepted");
    // By zero it is not.
    let m = module(&invariant_loop(false).replace(
        "\x20   %18 = add u32 %11, %16\n",
        "\x20   %40 = const u32 0\n\x20   %41 = urem u32 %2, %40\n\x20   %18 = add u32 %41, %16\n",
    ));
    refused(&m, "f", &licm(1, &[], &[40, 41]), "neither speculatable");
}

#[test]
fn a_load_with_an_aliasing_store_in_the_loop_is_refused() {
    let m = module(&invariant_loop(true));
    refused(&m, "f", &licm(1, &[12], &[13]), "neither speculatable");
}

#[test]
fn a_trapping_instruction_not_guaranteed_to_execute_is_refused() {
    // `udiv` of invariant operands by a parameter that may be zero, in the
    // body: the loop may run zero times.
    let m = module(&invariant_loop(false).replace("udiv u32 %10, %2", "udiv u32 %5, %2"));
    refused(&m, "f", &licm(1, &[], &[17]), "neither speculatable");
}

#[test]
fn an_operand_computed_in_the_loop_is_refused() {
    let m = module(&invariant_loop(false));
    // `%16` reads the parameter `%12`, which is not claimed invariant.
    refused(&m, "f", &licm(1, &[], &[15, 16]), "defined in the loop");
}

#[test]
fn a_parameter_the_loop_changes_is_refused() {
    let m = module(&invariant_loop(false));
    refused(
        &m,
        "f",
        &licm(1, &[11], &[]),
        "does not pass %11 back unchanged",
    );
}

/// A loop whose body adds `%0 + %0` at `u32` only after its variable passes
/// 100; `ILL_TY` is `%0`'s type.
fn guarded_add(ill_ty: &str, form: &str) -> Module {
    module(&format!(
        "functy.0 = ({ill_ty}, u32) -> (u32)\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: {ill_ty}, %1: u32):\n\
         \x20   %2 = const u32 0\n\
         \x20   br bb1(%2, %2)\n\
         bb1(%10: u32, %11: u32):\n\
         \x20   %12 = icmp ult u32 %10, %1\n\
         \x20   condbr %12, bb2, bb3\n\
         bb2:\n\
         \x20   %13 = const u32 100\n\
         \x20   %14 = icmp ugt u32 %10, %13\n\
         \x20   condbr %14, bb4, bb5(%11)\n\
         bb4:\n\
         \x20   %15 = {form}\n\
         \x20   %16 = add u32 %11, %15\n\
         \x20   br bb5(%16)\n\
         bb5(%17: u32):\n\
         \x20   %18 = const u32 1\n\
         \x20   %19 = add u32 %10, %18\n\
         \x20   br bb1(%19, %17)\n\
         bb3:\n\
         \x20   ret %11\n\
         }}\n"
    ))
}

#[test]
fn an_ill_typed_instruction_is_not_speculatable() {
    // Well typed, the add moves out of the guarded block and agrees.
    let m = guarded_add("u32", "add u32 %0, %0");
    let f = func(&m, "f");
    let out = rebuild(&m, f, &licm(1, &[], &[15])).expect("accepted");
    agree(&m, f, &out);
    // On an `i32` operand the interpreter faults where the add runs, and
    // the source may never run it.
    for form in [
        "add u32 %0, %0",
        "copy u32 %0",
        "zext u16 %0 to u32",
        "bitcast u64 %0 to u32",
        "select u32 %0, %1, %1",
    ] {
        let m = guarded_add("i32", form);
        refused(&m, "f", &licm(1, &[], &[15]), "neither speculatable");
    }
    // A narrowing `zext` and a widening `trunc` are not conversions the
    // form admits.
    for form in ["zext u64 %0 to u32", "trunc u16 %0 to u32"] {
        let ty = if form.contains("u64") { "u64" } else { "u16" };
        let m = guarded_add(ty, form);
        refused(&m, "f", &licm(1, &[], &[15]), "neither speculatable");
    }
}

/// A loop of `%1` iterations whose body, guarded by `%0 != g`, adds
/// `%15 = {op} {ty} %0, %3` with `%3 = const {ty} {k}` defined before it.
fn guarded_division(ty: &str, op: &str, k: &str, g: &str) -> Module {
    module(&format!(
        "functy.0 = ({ty}, u32) -> ({ty})\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: {ty}, %1: u32):\n\
         \x20   %2 = const u32 0\n\
         \x20   %3 = const {ty} {k}\n\
         \x20   %4 = const {ty} 0\n\
         \x20   br bb1(%2, %4)\n\
         bb1(%10: u32, %11: {ty}):\n\
         \x20   %12 = icmp ult u32 %10, %1\n\
         \x20   condbr %12, bb2, bb3\n\
         bb2:\n\
         \x20   %13 = const {ty} {g}\n\
         \x20   %14 = icmp ne {ty} %0, %13\n\
         \x20   condbr %14, bb4, bb5(%11)\n\
         bb4:\n\
         \x20   %15 = {op} {ty} %0, %3\n\
         \x20   %16 = add {ty} %11, %15\n\
         \x20   br bb5(%16)\n\
         bb5(%17: {ty}):\n\
         \x20   %18 = const u32 1\n\
         \x20   %19 = add u32 %10, %18\n\
         \x20   br bb1(%19, %17)\n\
         bb3:\n\
         \x20   ret %11\n\
         }}\n"
    ))
}

#[test]
fn a_divisor_is_read_at_the_operations_width() {
    // The interpreter masks a constant to its width and divides signed
    // whatever the type's signedness: `sdiv u32 x, 4294967295` divides by
    // -1, which overflows on 0x80000000 (the guard keeps the source from
    // dividing it), and `usize` 4294967296, which a 64-bit validator admits,
    // is 0 at wasm32's 32-bit pointer width.
    for (ty, op, k, g) in [
        ("u32", "sdiv", "4294967295", "2147483648"),
        ("u32", "srem", "4294967295", "2147483648"),
        ("u8", "sdiv", "255", "128"),
        ("usize", "udiv", "4294967296", "0"),
        ("usize", "urem", "4294967296", "0"),
        ("usize", "sdiv", "4294967296", "0"),
    ] {
        let m = guarded_division(ty, op, k, g);
        refused(&m, "f", &licm(1, &[], &[15]), "neither speculatable");
    }
    // Controls: divisors that are neither 0 nor all ones at the width move,
    // and agree with the interpreter (a `u32` -2, a `usize` 4294967297,
    // which is 1 at 32 bits).
    for (ty, op, k, g) in [
        ("u32", "sdiv", "4294967294", "2147483648"),
        ("u32", "udiv", "4294967295", "0"),
        ("usize", "udiv", "4294967297", "0"),
        ("i32", "sdiv", "7", "0"),
    ] {
        let m = guarded_division(ty, op, k, g);
        let f = func(&m, "f");
        let out = rebuild(&m, f, &licm(1, &[], &[15]))
            .unwrap_or_else(|e| panic!("{op} {ty} by {k}: {e:?}"));
        agree(&m, f, &out);
    }
}

#[test]
fn an_invariant_parameter_of_another_type_is_refused() {
    // The header binds `%12: u32` from the `ptr` parameter: the source
    // faults on entry, the parameter's removal would not.
    let text = invariant_loop(false).replace("br bb1(%3, %3, %5)", "br bb1(%3, %3, %0)");
    let m = module(&text);
    refused(&m, "f", &licm(1, &[12], &[]), "does not have its type");
}

#[test]
fn hoisting_agrees_in_the_interpreter() {
    // Scalar parameters only: the loop of `MIXED` with its invariant
    // parameter, its constant and the product hoisted.
    let src = module(MIXED);
    let f = func(&src, "f");
    let out = rebuild(&src, f, &licm(1, &[], &[15, 18])).expect("accepted");
    agree(&src, f, &out);
}

// ---------------------------------------------------------------------------
// Lemmas
// ---------------------------------------------------------------------------

/// Every lemma holds on every input at 3 and 4 bits, and every control fails
/// on some input: exhaustive, in process, independent of the solver.
#[test]
fn every_lemma_holds_exhaustively_and_its_control_fails() {
    let config = VerificationConfig {
        exhaustive_threshold: 10,
        ..VerificationConfig::default()
    };
    let mut checked = 0usize;
    for bits in [3u32, 4] {
        let lemmas = loop_cf_lemmas(bits);
        assert_eq!(lemmas.len(), 8);
        for lemma in &lemmas {
            assert!(
                crate::lowering_proof::exhaustive_input_count(&lemma.obligation, &config).is_some(),
                "{} is not enumerable",
                lemma.obligation.name
            );
            assert!(
                matches!(
                    verify_by_evaluation_with_config(&lemma.obligation, &config),
                    VerificationResult::Valid
                ),
                "{}",
                lemma.obligation.name
            );
            assert!(
                matches!(
                    verify_by_evaluation_with_config(&lemma.control, &config),
                    VerificationResult::Invalid { .. }
                ),
                "{}",
                lemma.control.name
            );
            checked += 1;
        }
    }
    assert_eq!(checked, 16);
}

/// At 8 bits the solver refutes no lemma and refutes every control. Its
/// UNSAT answers are counted, certified or not; an `unknown` or a timeout
/// proves nothing and is listed.
#[test]
fn the_solver_refutes_no_lemma_and_every_control() {
    let config = AYConfig::default().with_timeout(30_000);
    let (mut unsat, mut unanswered) = (0usize, Vec::new());
    for lemma in loop_cf_lemmas(8) {
        match verify_with_ay(&lemma.obligation, &config) {
            AYResult::Verified | AYResult::SolverUnsat => unsat += 1,
            // UNSAT whose proof the checker cannot certify.
            AYResult::Unknown(reason) if reason.starts_with("incomplete AY proof certificate:") => {
                unsat += 1;
            }
            AYResult::Unknown(reason) => unanswered.push(format!("{}: {reason}", lemma.name)),
            AYResult::Timeout => unanswered.push(format!("{}: timeout", lemma.name)),
            AYResult::CounterExample(cex) => {
                panic!("{}: the solver refutes it: {cex:?}", lemma.name)
            }
            AYResult::Error(why) => panic!("{}: the solver did not run: {why}", lemma.name),
        }
        match verify_with_ay(&lemma.control, &config) {
            AYResult::CounterExample(_) => {}
            other => panic!("{}: not refuted: {other}", lemma.control.name),
        }
    }
    eprintln!("loop lemmas at 8 bits: {unsat} UNSAT, unanswered: {unanswered:#?}");
    assert!(unsat > 0, "the solver answered no lemma");
}

// ---------------------------------------------------------------------------
// Invariant code motion, tier (b): loads beside disjoint stores
// ---------------------------------------------------------------------------

/// A load of slot `%1` in the header of a loop whose only write is
/// `{store}`, with a second slot `%2` (8 bytes) and a function `@g`.
fn disjoint_loop(store: &str) -> String {
    format!(
        "functy.0 = (u32, ptr) -> (u32)\n\n\
         functy.1 = () -> ()\n\n\
         type ty.0 = u32\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: u32, %3: ptr):\n\
         \x20   %1 = alloca [ty.0 x 2], align 4\n\
         \x20   %2 = alloca [ty.0 x 2], align 4\n\
         \x20   store u32 %0, ptr %1\n\
         \x20   %4 = const i32 4\n\
         \x20   %5 = gep inbounds u8, ptr %1, %4\n\
         \x20   store u32 %0, ptr %5\n\
         \x20   store u32 %0, ptr %2\n\
         \x20   %6 = gep inbounds u8, ptr %2, %4\n\
         \x20   %7 = ptrtoint ptr %1 to i32\n\
         \x20   %8 = const u32 0\n\
         \x20   br bb1(%8)\n\
         bb1(%10: u32):\n\
         \x20   %11 = load u32, ptr %1\n\
         \x20   %12 = const u32 4\n\
         \x20   %13 = icmp ult u32 %10, %12\n\
         \x20   condbr %13, bb2, bb3\n\
         bb2:\n\
         \x20   %14 = add u32 %10, %11\n\
         {store}\
         \x20   %15 = const u32 1\n\
         \x20   %16 = add u32 %10, %15\n\
         \x20   br bb1(%16)\n\
         bb3:\n\
         \x20   %17 = load u32, ptr %2\n\
         \x20   ret %17\n\
         }}\n\n\
         fn @g(functy.1) {{\n\
         bb0:\n\
         \x20   ret\n\
         }}\n"
    )
}

#[test]
fn a_load_beside_stores_to_another_slot_or_other_bytes_is_hoisted() {
    // Another slot.
    let m = module(&disjoint_loop("\x20   store u32 %14, ptr %2\n"));
    let f = func(&m, "f");
    let out = rebuild(&m, f, &licm(1, &[], &[11])).expect("accepted");
    assert!(matches!(
        out.blocks[0].body.iter().rev().nth(1).map(|n| &n.inst),
        Some(Inst::Load { .. })
    ));
    // Other bytes of the same slot, through the bridge's integer address.
    let m = module(&disjoint_loop(
        "\x20   %20 = const i32 4\n\x20   %21 = add i32 %7, %20\n\x20   %22 = inttoptr i32 %21 to ptr\n\x20   store u32 %14, ptr %22\n",
    ));
    let f = func(&m, "f");
    rebuild(&m, f, &licm(1, &[], &[11])).expect("accepted");
}

#[test]
fn a_load_beside_an_overlapping_or_unknown_writer_is_refused() {
    // The same bytes.
    let m = module(&disjoint_loop("\x20   store u32 %14, ptr %1\n"));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
    // Overlapping bytes through an integer address.
    let m = module(&disjoint_loop(
        "\x20   %20 = const i32 2\n\x20   %21 = add i32 %7, %20\n\x20   %22 = inttoptr i32 %21 to ptr\n\x20   store u32 %14, ptr %22\n",
    ));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
    // A store through an escaped pointer (an entry parameter).
    let m = module(&disjoint_loop("\x20   store u32 %14, ptr %3\n"));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
    // A call.
    let m = module(&disjoint_loop(
        "\x20   store u32 %14, ptr %2\n\x20   call @func.1()\n",
    ));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
    // An atomic store to another slot.
    let m = module(&disjoint_loop(
        "\x20   atomic_store seq_cst u32 %14, ptr %2\n",
    ));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
    // A store past its slot's end.
    let m = module(&disjoint_loop(
        "\x20   %20 = const i32 8\n\x20   %21 = gep inbounds u8, ptr %2, %20\n\x20   store u32 %14, ptr %21\n",
    ));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
}

/// A load of global `@a` through `%1 = global_addr @global.0` in the header
/// of a loop whose body is `{body}` (ending in the back edge's block), with
/// a second `%2 = global_addr @global.0` of the SAME global and `%3` the address of global `@b`; the
/// loop runs `%0 & 7` times.
fn globals_loop(body: &str) -> String {
    format!(
        "functy.0 = (u32) -> (u32)\n\n\
         type ty.0 = u8\n\n\
         global internal align(4) @a [ty.0 x 8] = bytes<0700000000000000>\n\n\
         global internal align(4) @b [ty.0 x 8] = bytes<0000000000000000>\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: u32):\n\
         \x20   %1 = global_addr @global.0\n\
         \x20   %2 = global_addr @global.0\n\
         \x20   %3 = global_addr @global.1\n\
         \x20   %5 = const u32 7\n\
         \x20   %6 = and u32 %0, %5\n\
         \x20   %8 = const u32 0\n\
         \x20   br bb1(%8, %8)\n\
         bb1(%10: u32, %30: u32):\n\
         \x20   %11 = load u32, ptr %1\n\
         \x20   %13 = icmp ult u32 %10, %6\n\
         \x20   condbr %13, bb2, bb3\n\
         bb2:\n\
         \x20   %14 = add u32 %30, %11\n\
         \x20   %15 = const u32 1\n\
         \x20   %16 = add u32 %10, %15\n\
         {body}\
         \x20   br bb1(%16, %14)\n\
         bb3:\n\
         \x20   ret %30\n\
         }}\n"
    )
}

#[test]
fn every_global_addr_of_one_global_names_the_same_allocation() {
    // Another global: disjoint, accepted.
    let m = module(&globals_loop("\x20   store u32 %16, ptr %3\n"));
    let f = func(&m, "f");
    let out = rebuild(&m, f, &licm(1, &[], &[11])).expect("accepted");
    agree(&m, f, &out);
    // Other bytes of the same global through its second `global_addr`.
    let m = module(&globals_loop(
        "\x20   %20 = const i32 4\n\x20   %21 = gep inbounds u8, ptr %2, %20\n\x20   store u32 %16, ptr %21\n",
    ));
    let f = func(&m, "f");
    let out = rebuild(&m, f, &licm(1, &[], &[11])).expect("accepted");
    agree(&m, f, &out);
    // Negative controls: the same bytes through the second `global_addr`
    // (the identity is the global, not the instruction computing its
    // address), overlapping bytes through it, and the same bytes stored
    // only on some iterations.
    let m = module(&globals_loop("\x20   store u32 %16, ptr %2\n"));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
    let m = module(&globals_loop(
        "\x20   %20 = const i32 2\n\x20   %21 = gep inbounds u8, ptr %2, %20\n\x20   store u32 %16, ptr %21\n",
    ));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
    let m = module(&globals_loop(
        "\x20   %20 = const u32 3\n\x20   %21 = icmp eq u32 %10, %20\n\x20   condbr %21, bb4, bb5\n\
         bb4:\n\x20   store u32 %16, ptr %2\n\x20   br bb5\n\
         bb5:\n",
    ));
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
}

#[test]
fn two_globals_sharing_a_name_are_one_allocation() {
    // A second module entry named `a` (two declarations of one symbol)
    // is not a distinct allocation.
    let text = globals_loop("\x20   %20 = global_addr @global.2\n\x20   store u32 %16, ptr %20\n")
        .replace(
            "fn @f(",
            "global internal align(4) @a [ty.0 x 8] = bytes<0000000000000000>\n\nfn @f(",
        );
    let m = module(&text);
    assert_eq!(m.globals[0].name, m.globals[2].name);
    refused(&m, "f", &licm(1, &[], &[11]), "neither speculatable");
}
