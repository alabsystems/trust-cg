// trust-cg-verify/trust_ir_mid_tv_fold_tests.rs - tests of the folding checkers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Constant folding is accepted for the value the interpreter computes, in
//! its canonical spelling, and refused for another constant, a division by
//! zero, an overflowing signed division, a shift by the width, an operand
//! that is not a constant or of another width; each simplification rule is
//! accepted on its form and refused off it (an operand that is not the
//! identity element, a mask that does not cover the extension, a
//! truncation to another type, parts that may overlap, a shift short of the
//! truncated width, a copy of another type; a masked rotate whose mask
//! keeps a bit the shift does not compute, with another use, by an amount
//! outside the width, or with a shift amount that is not fresh; a
//! reinterpreting copy's respelling of a copy of its own type, of another
//! width, naming another operand or of something that is not a copy).
//! Accepted rewrites agree with their sources in the interpreter (the
//! reinterpreting copy in the differential's view, which reads it as the
//! lane does). An integer constant spelled out of its type's range is
//! respelled in range (refused: another value, the unwrapped spelling, an
//! in-range constant); a copy of a pointer as another pointer type becomes
//! `ptrtoptr` (refused: an integer copied at another width); the operand
//! respelling turns a typed pointer comparison into one at `ptr` and a
//! `u32` bulk-memory count into a `usize` (a `zext`, or a constant), each
//! clearing trust-ir's validator's finding, and is refused off its form (a
//! comparison at `ptr`, the rule on another instruction or of the other
//! kind, names not fresh, a rewrite claimed twice, an empty claim, a count
//! already `usize`, signed or narrower); a narrowed count is not the
//! claimed rewrite and the view's run tells it apart. The respelling's
//! witness (`RespellWitness`, `Respell`, `RespellRule`,
//! `PassWitness::Respell`) is provisional too.
//!
//! The witness types (`ConstFoldWitness`, `SimplifyWitness` and their
//! elements, `PassWitness::ConstFold` / `PassWitness::Simplify`) are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, run_samples,
    seeded_inputs,
};
use super::*;
use trust_ir::Module;

const HEADER: &str = "; TrustIr text format v1\nmodule \"fold\"\n\
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

fn fold(folds: &[(u32, Constant)]) -> PassWitness {
    PassWitness::ConstFold(ConstFoldWitness {
        folds: folds
            .iter()
            .map(|(value, constant)| ConstFold {
                value: v(*value),
                constant: constant.clone(),
            })
            .collect(),
    })
}

fn simplify(rewrites: &[(u32, SimplifyRule, u32)]) -> PassWitness {
    PassWitness::Simplify(SimplifyWitness {
        rewrites: rewrites
            .iter()
            .map(|(value, rule, operand)| Simplify {
                value: v(*value),
                rule: *rule,
                operand: v(*operand),
            })
            .collect(),
    })
}

fn rebuild(m: &Module, w: &PassWitness) -> Result<Function, MidTvError> {
    let src = f(m);
    let (out, _) = match w {
        PassWitness::ConstFold(w) => rebuild_const_fold(32, src, w)?,
        PassWitness::Simplify(w) => rebuild_simplify(32, src, w)?,
        _ => unreachable!(),
    };
    check_pass(m, 32, src, &out, &w.clone())?;
    Ok(out)
}

fn agree(m: &Module, target: &Function) {
    let source = f(m);
    let inputs = seeded_inputs(m, source, 32, 64, 5).expect("scalar parameters");
    let (a, _) = run_samples(m, source, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(m, target, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

const ARITH: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 6\n\
\x20   %2 = bitcast u32 %1 to i32\n\
\x20   %3 = const i32 8\n\
\x20   %4 = mul i32 %2, %3\n\
\x20   %5 = const i32 -1\n\
\x20   %6 = sdiv i32 %4, %5\n\
\x20   %7 = const i32 0\n\
\x20   %8 = icmp slt i32 %6, %7\n\
\x20   %9 = zext bool %8 to u32\n\
\x20   %10 = add u32 %0, %9\n\
\x20   %11 = const u32 33\n\
\x20   %12 = shl u32 %0, %11\n\
\x20   %13 = const u32 0\n\
\x20   %14 = udiv u32 %1, %13\n\
\x20   %15 = trunc u32 %0 to u8\n\
\x20   ret %10\n\
}\n";

#[test]
fn constant_chains_fold_to_their_canonical_values() {
    // Without the shift and the division the source leaves undefined.
    let m = module(
        &ARITH
            .replace("%11 = const u32 33", "%11 = const u32 3")
            .replace("%13 = const u32 0", "%13 = const u32 2"),
    );
    let w = fold(&[
        (2, Constant::Int(6)),
        (4, Constant::Int(48)),
        (6, Constant::Int(-48)),
        (8, Constant::Bool(true)),
        (9, Constant::Int(1)),
    ]);
    let out = rebuild(&m, &w).expect("accepted");
    agree(&m, &out);
}

fn refused(m: &Module, w: &PassWitness) {
    match rebuild(m, w) {
        Err(MidTvError::NotConstantFold { .. } | MidTvError::NotSimplification { .. }) => {}
        other => panic!("expected a refusal, got {other:?}"),
    }
}

#[test]
fn folds_off_the_interpreters_value_or_definedness_are_refused() {
    let m = module(ARITH);
    // Another constant, or an unsigned spelling of a signed result.
    refused(&m, &fold(&[(2, Constant::Int(7))]));
    refused(
        &m,
        &fold(&[
            (2, Constant::Int(6)),
            (4, Constant::Int(48)),
            (6, Constant::Int(4294967248)),
        ]),
    );
    // A fold out of order: its operand is not yet a constant.
    refused(&m, &fold(&[(4, Constant::Int(48))]));
    // A shift by the width or more, a division by zero.
    refused(&m, &fold(&[(12, Constant::Int(0))]));
    refused(&m, &fold(&[(14, Constant::Int(0))]));
    // A non-constant operand.
    refused(&m, &fold(&[(10, Constant::Int(1))]));
    refused(&m, &fold(&[(15, Constant::Int(0))]));
    // A constant claimed twice.
    refused(&m, &fold(&[(2, Constant::Int(6)), (2, Constant::Int(6))]));
}

#[test]
fn an_overflowing_signed_division_is_not_folded() {
    let m = module(
        "functy.0 = () -> (i32)\n\n\
fn @f(functy.0) {\n\
bb0:\n\
\x20   %1 = const i32 -2147483648\n\
\x20   %2 = const i32 -1\n\
\x20   %3 = sdiv i32 %1, %2\n\
\x20   ret %3\n\
}\n",
    );
    refused(&m, &fold(&[(3, Constant::Int(-2147483648))]));
}

/// Scalar replacement's pair packing of two `u32`s in a `u64` and its
/// reads, with identity elements around it.
const PAIR: &str = "functy.0 = (u32, u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = zext u32 %0 to u64\n\
\x20   %3 = const u64 0\n\
\x20   %4 = or u64 %3, %2\n\
\x20   %5 = const u64 4294967295\n\
\x20   %6 = and u64 %4, %5\n\
\x20   %7 = zext u32 %1 to u64\n\
\x20   %8 = const u64 32\n\
\x20   %9 = shl u64 %7, %8\n\
\x20   %10 = or u64 %6, %9\n\
\x20   %11 = bitcast u64 %10 to i64\n\
\x20   %12 = bitcast i64 %11 to u64\n\
\x20   %13 = trunc u64 %12 to u32\n\
\x20   %14 = lshr u64 %12, %8\n\
\x20   %15 = trunc u64 %14 to u32\n\
\x20   %16 = const u32 1\n\
\x20   %17 = mul u32 %15, %16\n\
\x20   %18 = sub u32 %13, %17\n\
\x20   ret %18\n\
}\n";

#[test]
fn a_packed_pair_reads_back_its_parts() {
    let m = module(PAIR);
    let w = simplify(&[
        (4, SimplifyRule::Identity, 2),
        (6, SimplifyRule::MaskedExtension, 4),
        (12, SimplifyRule::BitcastRoundTrip, 10),
        (13, SimplifyRule::TruncLowPart, 6),
        (14, SimplifyRule::HighPart, 7),
        (15, SimplifyRule::TruncExtension, 1),
        (17, SimplifyRule::Identity, 15),
    ]);
    let out = rebuild(&m, &w).expect("accepted");
    agree(&m, &out);
    // The low part reads `%0` once more through its extension.
    let w2 = simplify(&[
        (4, SimplifyRule::Identity, 2),
        (6, SimplifyRule::MaskedExtension, 4),
        (12, SimplifyRule::BitcastRoundTrip, 10),
        (13, SimplifyRule::TruncLowPart, 6),
        (13, SimplifyRule::TruncExtension, 0),
    ]);
    let out = rebuild(&m, &w2).expect("accepted");
    agree(&m, &out);
}

#[test]
fn simplifications_off_their_form_are_refused() {
    let m = module(PAIR);
    // An operand that is not the identity element's partner.
    refused(&m, &simplify(&[(4, SimplifyRule::Identity, 3)]));
    // `sub 0, x` is not `x`.
    let m2 = module(&PAIR.replace("%18 = sub u32 %13, %17", "%18 = sub u32 %16, %13"));
    refused(&m2, &simplify(&[(18, SimplifyRule::Identity, 13)]));
    // A mask that does not cover the extension's bits.
    let m3 = module(&PAIR.replace("%5 = const u64 4294967295", "%5 = const u64 2147483647"));
    refused(
        &m3,
        &simplify(&[
            (4, SimplifyRule::Identity, 2),
            (6, SimplifyRule::MaskedExtension, 4),
        ]),
    );
    // Parts that may overlap: the low part is not known below `2^32`.
    let m4 = module(&PAIR.replace("%10 = or u64 %6, %9", "%10 = or u64 %4, %9"));
    refused(&m4, &simplify(&[(14, SimplifyRule::HighPart, 7)]));
    // A shift short of the truncated width.
    let m5 = module(&PAIR.replace("%8 = const u64 32", "%8 = const u64 16"));
    refused(&m5, &simplify(&[(13, SimplifyRule::TruncLowPart, 6)]));
    // A truncation back to another type than the extension's source.
    let m6 = module(
        &PAIR
            .replace(
                "%15 = trunc u64 %14 to u32",
                "%15 = trunc u64 %14 to i32\n\x20   %19 = bitcast i32 %15 to u32",
            )
            .replace("%17 = mul u32 %15, %16", "%17 = mul u32 %19, %16"),
    );
    refused(
        &m6,
        &simplify(&[
            (14, SimplifyRule::HighPart, 7),
            (15, SimplifyRule::TruncExtension, 1),
        ]),
    );
    // A rule named for another form.
    refused(&m, &simplify(&[(10, SimplifyRule::HighPart, 7)]));
}

/// Masked rotates: `%3 = rotl %0, 5` read only under masks below `2^5`
/// (`15`, and `31` with the operands swapped), and `%7 = rotl %1, 3` under
/// `15`, which keeps a bit from the rotate's low part.
const ROT: &str = "functy.0 = (u32, u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = const u32 5\n\
\x20   %3 = rotl u32 %0, %2\n\
\x20   %4 = const u32 15\n\
\x20   %5 = and u32 %3, %4\n\
\x20   %6 = const u32 3\n\
\x20   %7 = rotl u32 %1, %6\n\
\x20   %8 = and u32 %7, %4\n\
\x20   %9 = const u32 31\n\
\x20   %10 = and u32 %9, %3\n\
\x20   %11 = add u32 %5, %8\n\
\x20   %12 = add u32 %11, %10\n\
\x20   ret %12\n\
}\n";

#[test]
fn a_rotate_read_only_under_masks_of_its_top_bits_becomes_a_shift() {
    let m = module(ROT);
    let out = rebuild(&m, &simplify(&[(3, SimplifyRule::MaskedRotate, 20)])).expect("accepted");
    let body = &out.blocks[0].body;
    assert_eq!(body[1].results, vec![v(20)]);
    assert_eq!(
        body[1].inst,
        Inst::Const {
            ty: Ty::U32,
            value: Constant::Int(27)
        }
    );
    assert!(matches!(
        body[2].inst,
        Inst::BinOp {
            op: BinOp::LShr,
            rhs,
            ..
        } if rhs == v(20)
    ));
    agree(&m, &out);
}

#[test]
fn masked_rotates_off_their_form_are_refused() {
    let m = module(ROT);
    // A mask (15) keeping bit 3, which `rotl %1, 3` takes from the low part.
    refused(&m, &simplify(&[(7, SimplifyRule::MaskedRotate, 20)]));
    // A mask of `2^c` itself.
    let m2 = module(&ROT.replace("%9 = const u32 31", "%9 = const u32 32"));
    refused(&m2, &simplify(&[(3, SimplifyRule::MaskedRotate, 20)]));
    // A use that is not an `and`.
    let m3 = module(&ROT.replace(
        "\x20   ret %12\n",
        "\x20   %13 = add u32 %12, %3\n\x20   ret %13\n",
    ));
    refused(&m3, &simplify(&[(3, SimplifyRule::MaskedRotate, 20)]));
    // An amount that is the width (a rotate by it is the identity).
    let m4 = module(&ROT.replace("%2 = const u32 5", "%2 = const u32 32"));
    refused(&m4, &simplify(&[(3, SimplifyRule::MaskedRotate, 20)]));
    // A shift amount that is not fresh.
    refused(&m, &simplify(&[(3, SimplifyRule::MaskedRotate, 9)]));
    refused(&m, &simplify(&[(3, SimplifyRule::MaskedRotate, 1)]));
    // A rule named on another instruction.
    refused(&m, &simplify(&[(5, SimplifyRule::MaskedRotate, 20)]));
}

/// The rustc bridge's sign-reinterpreting copy: `copy u32` of an `i32`.
const REINTERPRET: &str = "functy.0 = (i32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: i32):\n\
\x20   %1 = const i32 7\n\
\x20   %2 = add i32 %0, %1\n\
\x20   %3 = copy u32 %2\n\
\x20   %4 = const u32 3\n\
\x20   %5 = mul u32 %3, %4\n\
\x20   %6 = copy u32 %5\n\
\x20   %7 = trunc i32 %0 to i16\n\
\x20   ret %5\n\
}\n";

#[test]
fn a_sign_reinterpreting_copy_becomes_a_bitcast() {
    let m = module(REINTERPRET);
    let out = rebuild(&m, &simplify(&[(3, SimplifyRule::ReinterpretCopy, 2)])).expect("accepted");
    let cast = out
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .find(|n| n.results == [v(3)])
        .expect("%3");
    assert!(matches!(
        &cast.inst,
        Inst::Cast {
            op: CastOp::Bitcast,
            src_ty: Ty::I32,
            dst_ty: Ty::U32,
            ..
        }
    ));
    // The source's copy is a type error to the interpreter itself; its view
    // reads it as the bitcast the lane moves the bits by, and the two agree.
    let view = super::super::interpretable_module(&m);
    let src = f(&m);
    let sv = super::super::interpretable(&view, src).unwrap_or_else(|| src.clone());
    let tv = super::super::interpretable(&view, &out).unwrap_or_else(|| out.clone());
    let inputs = seeded_inputs(&m, src, 32, 64, 5).expect("scalar parameters");
    let (a, _) = run_samples(&view, &sv, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&view, &tv, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

#[test]
fn reinterpretations_off_their_form_are_refused() {
    let m = module(REINTERPRET);
    let rule = SimplifyRule::ReinterpretCopy;
    // A copy of its own type.
    refused(&m, &simplify(&[(6, rule, 5)]));
    // An operand that is not the copied value.
    refused(&m, &simplify(&[(3, rule, 1)]));
    // Not a copy.
    refused(&m, &simplify(&[(5, rule, 3)]));
    // Another width: `copy u32` of an `i16`.
    let wide = module(&REINTERPRET.replace("%6 = copy u32 %5", "%6 = copy u32 %7"));
    refused(&wide, &simplify(&[(6, rule, 7)]));
}

/// `f(k)`: an 8-halfword slot's start `s` and the address `s + (k & 7) * 2`
/// spelled as the rustc bridge spells a slice's end (integer arithmetic
/// behind pointer casts); `(end - start) / 2` is the length, and a second
/// difference subtracts another slot's start. `{len}` is the length's
/// subtraction.
fn difference(len: &str) -> String {
    format!(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {{\n\
bb0(%0: u32):\n\
\x20   %1 = alloca (u16, u16, u16, u16, u16, u16, u16, u16), align 2\n\
\x20   %20 = alloca (u16, u16), align 2\n\
\x20   %2 = ptrtoptr ptr %1 to *mut u16\n\
\x20   %3 = ptrtoptr *mut u16 %2 to ptr\n\
\x20   %4 = ptrtoint ptr %3 to i32\n\
\x20   %5 = const u32 7\n\
\x20   %6 = and u32 %0, %5\n\
\x20   %7 = bitcast u32 %6 to i32\n\
\x20   %8 = const i32 2\n\
\x20   %9 = mul i32 %7, %8\n\
\x20   %10 = add i32 %4, %9\n\
\x20   %11 = inttoptr i32 %10 to ptr\n\
\x20   %12 = ptrtoptr ptr %11 to *const u16\n\
\x20   %13 = ptrtoptr *const u16 %12 to ptr\n\
\x20   %14 = ptrtoint ptr %13 to i32\n\
\x20   %15 = ptrtoptr ptr %1 to *const u16\n\
\x20   %16 = ptrtoptr *const u16 %15 to ptr\n\
\x20   %17 = ptrtoint ptr %16 to i32\n\
\x20   %21 = ptrtoint ptr %20 to i32\n\
\x20   %22 = const i64 3\n\
\x20   %23 = zext u32 %0 to i64\n\
\x20   %24 = add i64 %23, %22\n\
\x20   %25 = sub i64 %24, %23\n\
\x20   {len}\n\
\x20   %19 = udiv i32 %18, %8\n\
\x20   %26 = bitcast i32 %19 to u32\n\
\x20   ret %26\n\
}}\n"
    )
}

#[test]
fn a_pointer_difference_of_one_base_is_the_offset() {
    let m = module(&difference("%18 = sub i32 %14, %17"));
    let w = simplify(&[(18, SimplifyRule::PointerDifference, 9)]);
    let out = rebuild(&m, &w).expect("accepted");
    assert!(
        out.blocks[0].body.iter().any(|n| n.results == [v(18)]
            && n.inst
                == Inst::Copy {
                    ty: Ty::I32,
                    operand: v(9)
                }),
        "{out}"
    );
    agree(&m, &out);
    // The addend first, the base second.
    let m = module(
        &difference("%18 = sub i32 %14, %17")
            .replace("%10 = add i32 %4, %9", "%10 = add i32 %9, %4"),
    );
    agree(&m, &rebuild(&m, &w).expect("accepted, commuted"));
}

#[test]
fn pointer_differences_off_their_form_are_refused() {
    let w = simplify(&[(18, SimplifyRule::PointerDifference, 9)]);
    // Another slot's start is subtracted.
    refused(&module(&difference("%18 = sub i32 %14, %21")), &w);
    // The subtraction is reversed: start minus end.
    refused(&module(&difference("%18 = sub i32 %17, %14")), &w);
    // The operand is the base, not the offset.
    refused(
        &module(&difference("%18 = sub i32 %14, %17")),
        &simplify(&[(18, SimplifyRule::PointerDifference, 4)]),
    );
    // A subtraction wider than the pointer: `(x + 3) - x` at 64 bits is
    // not an address difference this rule reads.
    refused(
        &module(&difference("%18 = sub i32 %14, %17")),
        &simplify(&[(25, SimplifyRule::PointerDifference, 22)]),
    );
    // Not a subtraction.
    refused(&module(&difference("%18 = add i32 %14, %17")), &w);
}

// ---------------------------------------------------------------------------
// Round 17 stage B: out-of-range constants, pointer copies, respellings
// ---------------------------------------------------------------------------

/// Run `out` against the source of `m` in the differential's view: they
/// agree, and at least one input is compared.
fn agree_in_view(m: &Module, out: &Function) {
    let view = super::super::interpretable_module(m);
    let src = f(m);
    let sv = super::super::interpretable(&view, src).unwrap_or_else(|| src.clone());
    let tv = super::super::interpretable(&view, out).unwrap_or_else(|| out.clone());
    let inputs = seeded_inputs(m, src, 32, 64, 5).expect("scalar parameters");
    let (a, _) = run_samples(&view, &sv, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&view, &tv, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
}

/// `Option<Ordering>`'s `None` niche as the bridge spells it, `const i8
/// 254`, compared with the argument's low byte; and `const u16 65535`.
const NICHE: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const i8 254\n\
\x20   %2 = trunc u32 %0 to i8\n\
\x20   %3 = icmp eq i8 %2, %1\n\
\x20   %4 = zext bool %3 to u32\n\
\x20   %5 = const u16 65535\n\
\x20   %6 = sext i8 %1 to u32\n\
\x20   %7 = add u32 %4, %6\n\
\x20   ret %7\n\
}\n";

#[test]
fn an_integer_constant_out_of_its_range_is_respelled_in_range() {
    let m = module(NICHE);
    let out = rebuild(&m, &fold(&[(1, Constant::Int(-2))])).expect("accepted");
    agree(&m, &out);
    // trust-ir's validator reports the out-of-range spelling, not the other.
    let kinds = |func: &Function| {
        let mut m2 = m.clone();
        m2.functions[0] = func.clone();
        trust_ir_build::validate_module(&m2)
            .iter()
            .filter(|e| format!("{e:?}").starts_with("ConstTypeMismatch"))
            .count()
    };
    assert_eq!((kinds(f(&m)), kinds(&out)), (1, 0));
    // Refused: another value, the unwrapped spelling, an in-range constant.
    refused(&m, &fold(&[(1, Constant::Int(254))]));
    refused(&m, &fold(&[(1, Constant::Int(-1))]));
    refused(&m, &fold(&[(5, Constant::Int(-1))]));
}

/// `copy *mut u32` of a `*const u32` (the bridge reads a slice iterator's
/// `*const` lane as `*mut`), then a load through it.
const POINTER_COPY: &str = "type ty.0 = u32\n\n\
functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = alloca [ty.0 x 1], align 4\n\
\x20   store u32 %0, ptr %1\n\
\x20   %2 = ptrtoptr ptr %1 to *const u32\n\
\x20   %3 = copy *mut u32 %2\n\
\x20   %4 = load u32, ptr %3\n\
\x20   ret %4\n\
}\n";

#[test]
fn a_copy_of_a_pointer_as_another_pointer_type_becomes_ptrtoptr() {
    let m = module(POINTER_COPY);
    let rule = SimplifyRule::ReinterpretCopy;
    let out = rebuild(&m, &simplify(&[(3, rule, 2)])).expect("accepted");
    assert!(out.blocks[0].body.iter().any(|n| n.results == [v(3)]
        && matches!(
            &n.inst,
            Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::PtrConst(_),
                dst_ty: Ty::PtrMut(_),
                ..
            }
        )));
    agree_in_view(&m, &out);
    // Refused: an integer copied as another width (`copy u64` of a `u32`).
    let wide = module(&POINTER_COPY.replace(
        "\x20   ret %4\n",
        "\x20   %5 = ptrtoint ptr %1 to u32\n\x20   %6 = copy u64 %5\n\x20   ret %4\n",
    ));
    refused(&wide, &simplify(&[(6, rule, 5)]));
}

/// A slice-iterator-like comparison of two `*mut u32`s (`%5`, at
/// `{ty}`), and a `memcopy` of `%0 & 3` bytes (a `u32` count `%9`) and one
/// of 4 bytes (`%12`, constant) between two slots; `{count}` the second
/// copy's count type.
fn respell_program(ty: &str, count: &str) -> String {
    format!(
        "type ty.0 = u32\n\n\
functy.0 = (u32, u32) -> (u32)\n\n\
fn @f(functy.0) {{\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   store u32 %0, ptr %2\n\
\x20   %20 = const usize 4\n\
\x20   %21 = gep u8, ptr %2, %20\n\
\x20   store u32 %1, ptr %21\n\
\x20   %3 = ptrtoptr ptr %2 to {ty}\n\
\x20   %4 = ptrtoptr ptr %21 to {ty}\n\
\x20   %5 = icmp eq {ty} %3, %4\n\
\x20   %6 = alloca [ty.0 x 2], align 4\n\
\x20   %22 = const u32 0\n\
\x20   store u32 %22, ptr %6\n\
\x20   %7 = const u32 3\n\
\x20   %9 = and u32 %0, %7\n\
\x20   memcopy ptr %6, ptr %2, %9\n\
\x20   %12 = const {count} 4\n\
\x20   memcopy ptr %21, ptr %6, %12\n\
\x20   %13 = load u32, ptr %6\n\
\x20   %14 = zext bool %5 to u32\n\
\x20   %15 = add u32 %13, %14\n\
\x20   %16 = load u32, ptr %21\n\
\x20   %17 = xor u32 %15, %16\n\
\x20   ret %17\n\
}}\n"
    )
}

fn respell(rewrites: Vec<(u32, usize, RespellRule)>) -> RespellWitness {
    RespellWitness {
        rewrites: rewrites
            .into_iter()
            .map(|(block, index, rule)| Respell {
                block: BlockId::new(block),
                index,
                rule,
            })
            .collect(),
    }
}

/// The pointer comparison (node 7), the run-time copy (node 13) and the
/// constant copy (node 15) respelled.
fn all_three() -> RespellWitness {
    respell(vec![
        (
            0,
            7,
            RespellRule::PointerCompare {
                lhs: v(100),
                rhs: v(101),
            },
        ),
        (0, 13, RespellRule::ByteCount { count: v(102) }),
        (0, 15, RespellRule::ByteCount { count: v(103) }),
    ])
}

fn rebuild_respelled(m: &Module, w: &RespellWitness) -> Result<Function, MidTvError> {
    let src = f(m);
    let (out, verdict) = rebuild_respell(32, src, w)?;
    assert_eq!(verdict.exact, w.rewrites.len());
    check_pass(m, 32, src, &out, &PassWitness::Respell(w.clone()))?;
    Ok(out)
}

#[test]
fn typed_pointer_compares_and_u32_counts_are_respelled() {
    let m = module(&respell_program("*mut u32", "u32"));
    let out = rebuild_respelled(&m, &all_three()).expect("accepted");
    let body = &out.blocks[0].body;
    let compare = body.iter().find(|n| n.results == [v(5)]).expect("%5");
    assert!(matches!(
        compare.inst,
        Inst::ICmp { ty: Ty::Ptr, lhs, rhs, .. } if lhs == v(100) && rhs == v(101)
    ));
    let count = |id: u32| body.iter().find(|n| n.results == [v(id)]).expect("count");
    assert!(matches!(
        count(102).inst,
        Inst::Cast { op: CastOp::ZExt, dst_ty: Ty::Usize, operand, .. } if operand == v(9)
    ));
    assert_eq!(
        count(103).inst,
        Inst::Const {
            ty: Ty::Usize,
            value: Constant::Int(4)
        }
    );
    agree_in_view(&m, &out);
    // trust-ir's validator reports the three forms and none of the respellings.
    let findings = |func: &Function| {
        let mut m2 = m.clone();
        m2.functions[0] = func.clone();
        trust_ir_build::validate_module(&m2).len()
    };
    assert_eq!((findings(f(&m)), findings(&out)), (3, 0));
}

#[test]
fn respellings_off_their_form_are_refused() {
    let refused = |m: &Module, w: &RespellWitness| {
        assert!(
            matches!(
                rebuild_respelled(m, w),
                Err(MidTvError::NotSimplification { .. })
            ),
            "{w:?}"
        );
    };
    let m = module(&respell_program("*mut u32", "u32"));
    let one = |index: usize, rule: RespellRule| respell(vec![(0, index, rule)]);
    let compare = RespellRule::PointerCompare {
        lhs: v(100),
        rhs: v(101),
    };
    // A comparison at `ptr` already.
    let at_ptr = module(&respell_program("ptr", "u32"));
    refused(&at_ptr, &one(7, compare.clone()));
    // The rule on another instruction, a rule of the other kind.
    refused(&m, &one(6, compare.clone()));
    refused(&m, &one(7, RespellRule::ByteCount { count: v(102) }));
    refused(&m, &one(13, compare.clone()));
    // Names that are not fresh, a rewrite claimed twice, nothing claimed.
    refused(
        &m,
        &one(
            7,
            RespellRule::PointerCompare {
                lhs: v(2),
                rhs: v(101),
            },
        ),
    );
    refused(&m, &one(13, RespellRule::ByteCount { count: v(9) }));
    refused(
        &m,
        &respell(vec![(0, 7, compare.clone()), (0, 7, compare.clone())]),
    );
    refused(&m, &RespellWitness::default());
    // A count that is already a `usize`, and a signed or narrower count.
    for ty in ["usize", "i32", "u16"] {
        let other = module(&respell_program("*mut u32", ty));
        refused(&other, &one(15, RespellRule::ByteCount { count: v(103) }));
    }
}

#[test]
fn a_narrowed_respelled_count_is_refused_and_disagrees() {
    let m = module(&respell_program("*mut u32", "u32"));
    let w = all_three();
    let src = f(&m);
    let (mut out, _) = rebuild_respell(32, src, &w).expect("accepted");
    // The constant count read as one byte less.
    for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if node.results == [v(103)] {
            node.inst = Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(3),
            };
        }
    }
    assert!(matches!(
        check_pass(&m, 32, src, &out, &PassWitness::Respell(w)),
        Err(MidTvError::TargetDiffers { .. })
    ));
    let view = super::super::interpretable_module(&m);
    let sv = super::super::interpretable(&view, src).unwrap_or_else(|| src.clone());
    let tv = super::super::interpretable(&view, &out).unwrap_or_else(|| out.clone());
    let inputs = seeded_inputs(&m, src, 32, 64, 5).expect("scalar parameters");
    let (a, _) = run_samples(&view, &sv, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&view, &tv, &inputs, DifferentialBudget::default());
    assert!(compare_samples(&a, &t).mismatch.is_some());
}
