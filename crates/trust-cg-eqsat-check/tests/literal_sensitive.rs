// trust-cg-eqsat-check/tests/literal_sensitive.rs - operands trust-ir's validator reads through their defining instruction
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! docs/eqsat-tier-e.md section 2.5 "Literal-sensitive operands" and section
//! 8 item 2: trust-ir-build's validator decides some operands by the
//! instruction that defines them, not by their value, so an output whose
//! terms all check can still be a module the validator refuses. Each refused
//! output below was run through the pinned validator
//! (`eqsat_corpus_probe`): the input validates and the output does not, with
//! the message quoted at the test. Each accepted output validates.
//!
//! * The lane index of `ExtractElement` / `InsertElement` is range-checked
//!   only when a `Const` defines it (`const_int_values`); so are, by the
//!   contract, both `PtrFromParts` operands. A folded or copy-stripped `Const`
//!   there must be the input's own (equal) `Const`: class
//!   `literal_introduced`.
//! * A `Resume` operand defined by a literal is refused (rule (c)); the
//!   reader refuses that on each body (`malformed_body`).
//! * The selector of an `exhaustive` `Switch` is traced through `Copy` and
//!   widening casts to an enum's tag, and only then is the case set held to
//!   the enum: class `tag_provenance_changed`.
//! * A `Switch` counts as a handle-lane tag guard only when its selector is
//!   directly an `ExtractField { field: 0 }` (`HandleEnumGuards::new`), so a
//!   copy inserted in front of a selector the input reads directly from an
//!   `ExtractField` (any field, conservatively) is also class
//!   `tag_provenance_changed`.
//! * A module with refinement predicates has its consumption sites decided by
//!   forward fact propagation over the graph instructions themselves: class
//!   `refinement_predicates`.

mod common;

use common::*;
use trust_cg_eqsat_check::{Body, Registry, Rejection};

const RULES: &str = "\
(rule fold_add
  (direction equiv)
  (domain u32 u64 i32)
  (lhs (add (const ?a) (const ?b)))
  (rhs (eval add ?a ?b))
  (where))

(rule add_zero
  (direction equiv)
  (domain u32)
  (lhs (add ?x (const 0)))
  (rhs ?x)
  (where))

(rule mul_one
  (direction equiv)
  (domain u32)
  (lhs (mul ?x (const 1)))
  (rhs ?x)
  (where))
";

const I32: u8 = 0x12;

fn reg() -> Registry {
    Registry::parse(RULES).expect("rules parse")
}

/// `(add (const a) (const b))` folded to its sum at `ty`.
fn fold(reg: &Registry, ty: u8, a: u128, b: u128) -> Deriv {
    let mut d = Deriv::header("f").with_rule(reg, "fold_add");
    d.terms = vec![T::Const(ty, a), T::Const(ty, b)];
    d.proofs = vec![rule(0, ty, &[("a", 0), ("b", 1)], &[])];
    d.claims = vec![0];
    d
}

fn literal_introduced(r: &Result<trust_cg_eqsat_check::Verdict, Rejection>) -> (u32, usize, usize) {
    match r {
        Err(Rejection::LiteralIntroduced {
            block,
            ordinal,
            operand,
            ..
        }) => (*block, *ordinal, *operand),
        other => panic!("expected literal_introduced, got {other:?}"),
    }
}

// ------------------------------------------------------------ ExtractElement

const EE_IN: &str = "\
functy.0 = (<4 x u32>) -> (u32)

fn @f(functy.0) {
bb0(%0: <4 x u32>):
    %1 = const u32 4
    %2 = const u32 5
    %3 = add u32 %1, %2
    %4 = extractelement u32 %0, %3
    ret %4
}
";

/// Validator: "invalid extract_element: constant lane index 9 is out of range
/// for 4 lanes".
const EE_OUT: &str = "\
functy.0 = (<4 x u32>) -> (u32)

fn @f(functy.0) {
bb0(%0: <4 x u32>):
    %1 = const u32 4
    %2 = const u32 5
    %3 = const u32 9
    %4 = extractelement u32 %0, %3
    ret %4
}
";

/// The same fold with a see-through copy in front of the index: validates.
const EE_COPY_OUT: &str = "\
functy.0 = (<4 x u32>) -> (u32)

fn @f(functy.0) {
bb0(%0: <4 x u32>):
    %1 = const u32 4
    %2 = const u32 5
    %3 = const u32 9
    %5 = copy u32 %3
    %4 = extractelement u32 %0, %5
    ret %4
}
";

#[test]
fn folding_an_extractelement_index_into_a_const_is_refused() {
    let reg = reg();
    assert!(run(EE_IN, EE_IN, &Deriv::header("f"), &reg).is_ok());
    let r = run(EE_IN, EE_OUT, &fold(&reg, U32, 4, 5), &reg);
    assert_eq!(class(&r), "literal_introduced", "{r:?}");
    // bb0, skeleton #0 (the extractelement), operand 1 (the index).
    assert_eq!(literal_introduced(&r), (0, 0, 1));
}

#[test]
fn a_see_through_copy_before_the_folded_index_is_accepted() {
    let reg = reg();
    let v = run(EE_IN, EE_COPY_OUT, &fold(&reg, U32, 4, 5), &reg).expect("accepted");
    assert_eq!(v.changed_operands, 1);
}

/// The input reaches the index through a copy (the validator does not look
/// through it, so an out-of-range constant validates); removing the copy
/// keeps every term but exposes the constant. Validator on the output:
/// "constant lane index 9 is out of range for 4 lanes".
#[test]
fn removing_a_copy_in_front_of_an_index_constant_is_refused() {
    let input = "\
functy.0 = (<4 x u32>) -> (u32)

fn @f(functy.0) {
bb0(%0: <4 x u32>):
    %1 = const u32 9
    %2 = copy u32 %1
    %3 = extractelement u32 %0, %2
    ret %3
}
";
    let output = "\
functy.0 = (<4 x u32>) -> (u32)

fn @f(functy.0) {
bb0(%0: <4 x u32>):
    %1 = const u32 9
    %3 = extractelement u32 %0, %1
    ret %3
}
";
    let reg = reg();
    assert!(run(input, input, &Deriv::header("f"), &reg).is_ok());
    let r = run(input, output, &Deriv::header("f"), &reg);
    assert_eq!(literal_introduced(&r), (0, 0, 1));
}

/// An input whose index already is a `Const` keeps an equal `Const` (here a
/// renumbered one) while another operand is folded: accepted.
#[test]
fn an_index_that_already_is_the_same_const_is_accepted() {
    let input = "\
functy.0 = (<4 x u32>) -> (u32, u32)

fn @f(functy.0) {
bb0(%0: <4 x u32>):
    %1 = const u32 2
    %2 = extractelement u32 %0, %1
    %3 = const u32 4
    %4 = const u32 5
    %5 = add u32 %3, %4
    ret %2, %5
}
";
    let output = "\
functy.0 = (<4 x u32>) -> (u32, u32)

fn @f(functy.0) {
bb0(%0: <4 x u32>):
    %7 = const u32 2
    %2 = extractelement u32 %0, %7
    %5 = const u32 9
    ret %2, %5
}
";
    let reg = reg();
    let v = run(input, output, &fold(&reg, U32, 4, 5), &reg).expect("accepted");
    assert_eq!(v.changed_operands, 1);
    // The index constant may not change its value either: 3 is not the
    // input's `Const` (the term check refuses it first, unjustified).
    let other = output.replace("%7 = const u32 2", "%7 = const u32 3");
    assert!(run(input, &other, &fold(&reg, U32, 4, 5), &reg).is_err());
}

// ------------------------------------------------------------- InsertElement

const IE_IN: &str = "\
functy.0 = (<4 x u32>, u32) -> (<4 x u32>)

fn @f(functy.0) {
bb0(%0: <4 x u32>, %9: u32):
    %1 = const u32 4
    %2 = const u32 5
    %3 = add u32 %1, %2
    %4 = insertelement <4 x u32> %0, %3, %9
    ret %4
}
";

/// Validator: "invalid insert_element: constant lane index 9 is out of range
/// for 4 lanes".
const IE_OUT: &str = "\
functy.0 = (<4 x u32>, u32) -> (<4 x u32>)

fn @f(functy.0) {
bb0(%0: <4 x u32>, %9: u32):
    %1 = const u32 4
    %2 = const u32 5
    %3 = const u32 9
    %4 = insertelement <4 x u32> %0, %3, %9
    ret %4
}
";

#[test]
fn folding_an_insertelement_index_into_a_const_is_refused() {
    let reg = reg();
    assert!(run(IE_IN, IE_IN, &Deriv::header("f"), &reg).is_ok());
    let r = run(IE_IN, IE_OUT, &fold(&reg, U32, 4, 5), &reg);
    assert_eq!(literal_introduced(&r), (0, 0, 1));
    let with_copy = IE_OUT.replace(
        "    %4 = insertelement <4 x u32> %0, %3, %9\n",
        "    %5 = copy u32 %3\n    %4 = insertelement <4 x u32> %0, %5, %9\n",
    );
    assert!(run(IE_IN, &with_copy, &fold(&reg, U32, 4, 5), &reg).is_ok());
}

// -------------------------------------------------------------- PtrFromParts

const PFP_IN: &str = "\
functy.0 = (ptr) -> (fatptr<str>)

fn @f(functy.0) {
bb0(%0: ptr):
    %1 = const u64 4
    %2 = const u64 5
    %3 = add u64 %1, %2
    %4 = ptr_from_parts fatptr<str> ptr %0, u64 %3
    ret %4
}
";

/// The pinned validator passes `const_int_values` to the `PtrFromParts`
/// check but its arms read only types today, so this output validates; the
/// contract keeps the position literal-sensitive (fail-closed against a
/// validator that starts reading it), and the engine keeps a copy there.
const PFP_OUT: &str = "\
functy.0 = (ptr) -> (fatptr<str>)

fn @f(functy.0) {
bb0(%0: ptr):
    %1 = const u64 4
    %2 = const u64 5
    %3 = const u64 9
    %4 = ptr_from_parts fatptr<str> ptr %0, u64 %3
    ret %4
}
";

#[test]
fn folding_a_ptrfromparts_operand_into_a_const_is_refused() {
    let reg = reg();
    assert!(run(PFP_IN, PFP_IN, &Deriv::header("f"), &reg).is_ok());
    let r = run(PFP_IN, PFP_OUT, &fold(&reg, U64, 4, 5), &reg);
    // Operand 1: the metadata (operand 0 is the data pointer).
    assert_eq!(literal_introduced(&r), (0, 0, 1));
    let with_copy = PFP_OUT.replace(
        "    %4 = ptr_from_parts fatptr<str> ptr %0, u64 %3\n",
        "    %5 = copy u64 %3\n    %4 = ptr_from_parts fatptr<str> ptr %0, u64 %5\n",
    );
    assert!(run(PFP_IN, &with_copy, &fold(&reg, U64, 4, 5), &reg).is_ok());
}

// -------------------------------------------------------------------- Resume

/// The landing-pad block re-raises a value computed after the pad.
fn resume_body(pad_tail: &str) -> String {
    format!(
        "\
functy.0 = () -> (i64)

fn @boom(functy.0) {{
bb0:
    %0 = const bool false
    assert %0, div_by_zero
    %1 = const i64 0
    ret %1
}}

fn @f(functy.0) {{
bb0:
    %1 = invoke @func.0() to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad cleanup
{pad_tail}}}
"
    )
}

#[test]
fn folding_a_resume_operand_into_a_const_is_refused() {
    let reg = reg();
    let input = resume_body(
        "    %5 = const i32 4\n    %6 = const i32 5\n    %7 = add i32 %5, %6\n    resume %7\n",
    );
    assert!(run(&input, &input, &Deriv::header("f"), &reg).is_ok());
    // Validator: "resume of a value no landing pad produced: the operand is
    // a literal". The reader's rule (c) refuses it on the output body.
    let output = resume_body(
        "    %5 = const i32 4\n    %6 = const i32 5\n    %7 = const i32 9\n    resume %7\n",
    );
    let r = run(&input, &output, &fold(&reg, I32, 4, 5), &reg);
    assert!(
        matches!(
            r,
            Err(Rejection::MalformedBody {
                body: Body::Output,
                block: Some(2),
                ..
            })
        ),
        "{r:?}"
    );
    // Through a see-through copy the output validates and is accepted.
    let output = resume_body(
        "    %5 = const i32 4\n    %6 = const i32 5\n    %7 = const i32 9\n    %8 = copy i32 %7\n    resume %8\n",
    );
    assert!(run(&input, &output, &fold(&reg, I32, 4, 5), &reg).is_ok());
}

// ------------------------------------------------- exhaustive Switch selector

const SW_IN: &str = "\
enum @E repr(u8) { A, B, C } id=0

functy.0 = (enum.0) -> (u32)

fn @f(functy.0) {
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    %2 = zext u8 %1 to u32
    %3 = const u32 0
    %4 = add u32 %2, %3
    switch %4 [ 0: bb1 1: bb1 default: bb2 ] exhaustive
bb1:
    ret %2
bb2:
    unreachable
}
";

/// Validator: "switch claims exhaustive_enum_unreachable over the tag of
/// enum.0, but its case set does not cover the enum (no case for inhabited
/// variant(s) {C = 2}, ...)". In the input the `add` ends the trace.
const SW_OUT: &str = "\
enum @E repr(u8) { A, B, C } id=0

functy.0 = (enum.0) -> (u32)

fn @f(functy.0) {
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    %2 = zext u8 %1 to u32
    switch %2 [ 0: bb1 1: bb1 default: bb2 ] exhaustive
bb1:
    ret %2
bb2:
    unreachable
}
";

/// `(add R (const 0))` to `R`, R the zext (skeleton #1: its operand, the
/// tag, is not defined in the section 2.3 sense).
fn add_zero(reg: &Registry) -> Deriv {
    let mut d = Deriv::header("f").with_rule(reg, "add_zero");
    d.terms = vec![T::Result(0, 1, 0)];
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[])];
    d.claims = vec![0];
    d
}

#[test]
fn exposing_an_enum_tag_to_an_exhaustive_switch_is_refused() {
    let reg = reg();
    assert!(run(SW_IN, SW_IN, &Deriv::header("f"), &reg).is_ok());
    let r = run(SW_IN, SW_OUT, &add_zero(&reg), &reg);
    assert!(
        matches!(
            r,
            Err(Rejection::TagProvenanceChanged {
                block: 0,
                ordinal: 2,
                ..
            })
        ),
        "{r:?}"
    );
    assert_eq!(class(&r), "tag_provenance_changed");
}

#[test]
fn the_same_rewrite_under_a_non_exhaustive_switch_is_accepted() {
    let reg = reg();
    let (input, output) = (
        SW_IN.replace(" exhaustive", ""),
        SW_OUT.replace(" exhaustive", ""),
    );
    assert!(run(&input, &output, &add_zero(&reg), &reg).is_ok());
}

/// The trace follows copies, so removing one in front of a selector whose
/// input trace already reaches the tag (the full case set, which validates)
/// keeps the trace and is accepted.
#[test]
fn an_unchanged_tag_trace_is_accepted() {
    let input = "\
enum @E repr(u8) { A, B, C } id=0

functy.0 = (enum.0) -> (u32)

fn @f(functy.0) {
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    %2 = zext u8 %1 to u32
    %3 = copy u32 %2
    switch %3 [ 0: bb1 1: bb1 2: bb1 default: bb2 ] exhaustive
bb1:
    ret %2
bb2:
    unreachable
}
";
    let output = input
        .replace("    %3 = copy u32 %2\n", "")
        .replace("switch %3", "switch %2");
    let reg = reg();
    assert!(run(input, &output, &Deriv::header("f"), &reg).is_ok());
}

// ------------------------------------------------- handle-lane tag guards

/// A handle-bearing enum whose handle lane is read under a switch on its tag
/// read directly (validates). `HandleEnumGuards::new` counts the switch as a
/// guard only because `%1` is directly an `ExtractField { field: 0 }`.
const HG_IN: &str = "\
enum @H repr(u8) { None, Some(handle<\"Nat\", \"trust_bignum::Nat\">) } id=0

functy.0 = (enum.0) -> (u32)

fn @f(functy.0) {
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    switch %1 [ 1: bb1 default: bb2 ]
bb1:
    %2 = extractfield handle<\"Nat\", \"trust_bignum::Nat\"> %0, 1
    %3 = const u32 1
    ret %3
bb2:
    %4 = const u32 0
    ret %4
}
";

fn tag_provenance_changed(r: &Result<trust_cg_eqsat_check::Verdict, Rejection>) -> (u32, usize) {
    match r {
        Err(Rejection::TagProvenanceChanged { block, ordinal, .. }) => (*block, *ordinal),
        other => panic!("expected tag_provenance_changed, got {other:?}"),
    }
}

/// Validator on the output: "invalid handle use in f: a handle lane of an
/// enum is read only under a tag switch that selects a variant carrying it:
/// lane 1 of `enum.0` is read as `handle<...>` in bb1, which no dominating
/// switch case on that value's tag selects at that exact type". Every term
/// is unchanged (the copy is see-through), so only the definition rule
/// refuses it.
#[test]
fn a_copy_in_front_of_a_tag_guard_selector_is_refused() {
    let reg = reg();
    let output = HG_IN.replace("    switch %1 [", "    %9 = copy u8 %1\n    switch %9 [");
    let r = run(HG_IN, &output, &Deriv::header("f"), &reg);
    // The switch is skeleton #1 of bb0 (after the tag read).
    assert_eq!(tag_provenance_changed(&r), (0, 1), "{r:?}");
    assert_eq!(class(&r), "tag_provenance_changed");
}

/// The same with a chain of two copies (validator: the same refusal).
#[test]
fn a_copy_chain_in_front_of_a_tag_guard_selector_is_refused() {
    let reg = reg();
    let output = HG_IN.replace(
        "    switch %1 [",
        "    %8 = copy u8 %1\n    %9 = copy u8 %8\n    switch %9 [",
    );
    let r = run(HG_IN, &output, &Deriv::header("f"), &reg);
    assert_eq!(tag_provenance_changed(&r), (0, 1), "{r:?}");
}

/// The unchanged guard: the output selector is still the paired tag read.
#[test]
fn an_unchanged_tag_guard_selector_is_accepted() {
    let reg = reg();
    assert!(run(HG_IN, HG_IN, &Deriv::header("f"), &reg).is_ok());
}

/// The rule reads any `ExtractField` selector, not only a tag read: a copy in
/// front of a struct field read is refused too. The validator accepts both
/// bodies here (no handle, no guard); the refusal is the conservative
/// superset of `tag_reads`.
#[test]
fn a_copy_in_front_of_a_non_tag_field_selector_is_refused() {
    let input = "\
struct @S { u32, u8 } id=0

functy.0 = (struct.0) -> (u32)

fn @f(functy.0) {
bb0(%0: struct.0):
    %1 = extractfield u8 %0, 1
    switch %1 [ 1: bb1 default: bb2 ]
bb1:
    %3 = const u32 1
    ret %3
bb2:
    %4 = const u32 0
    ret %4
}
";
    let reg = reg();
    assert!(run(input, input, &Deriv::header("f"), &reg).is_ok());
    let output = input.replace("    switch %1 [", "    %9 = copy u8 %1\n    switch %9 [");
    let r = run(input, &output, &Deriv::header("f"), &reg);
    assert_eq!(tag_provenance_changed(&r), (0, 1), "{r:?}");
}

// ---------------------------------------------------- refinement predicates

/// The return value is consumed at a refined site, decided from the fact
/// forward propagation derives: `Interval{3, 3}` for the input's `Const`,
/// `top` for the output's `mul`. Validator on the output: "return value 0:
/// refinement not satisfied: value carries top ... but the site requires
/// pred.0 (in[0, 7])".
const REFINED_IN: &str = "\
type ty.0 = u32
pred pred.0 = in[0, 7]

functy.0 = (u32) -> (refine<ty.0, pred.0>)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 3
    ret %1
}
";

const REFINED_OUT: &str = "\
type ty.0 = u32
pred pred.0 = in[0, 7]

functy.0 = (u32) -> (refine<ty.0, pred.0>)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 3
    %2 = const u32 1
    %3 = mul u32 %1, %2
    ret %3
}
";

#[test]
fn a_module_with_refinement_predicates_is_refused() {
    let reg = reg();
    // `(const 3)` to `(mul (const 3) (const 1))`: Sym of mul_one.
    let mut d = Deriv::header("f").with_rule(&reg, "mul_one");
    d.terms = vec![T::Const(U32, 3)];
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[]), P::Sym(0)];
    d.claims = vec![1];
    let r = run(REFINED_IN, REFINED_OUT, &d, &reg);
    assert!(
        matches!(r, Err(Rejection::RefinementPredicates { predicates: 1 })),
        "{r:?}"
    );
    assert_eq!(class(&r), "refinement_predicates");
    // The same derivation without the predicate table (and the refined
    // return type) is a sound rewrite the checker accepts.
    let plain = |s: &str| {
        s.replace("type ty.0 = u32\npred pred.0 = in[0, 7]\n\n", "")
            .replace("refine<ty.0, pred.0>", "u32")
    };
    assert!(run(&plain(REFINED_IN), &plain(REFINED_OUT), &d, &reg).is_ok());
}
