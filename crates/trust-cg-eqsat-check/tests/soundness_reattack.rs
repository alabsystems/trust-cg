// trust-cg-eqsat-check/tests/soundness_reattack.rs - refusals of outputs that run or validate differently from their input
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Attacks on `check()` (docs/eqsat-tier-e.md sections 2.5, 4 and 8): each
//! builds an (input, output, derivation) whose output behaves differently
//! under trust-ir's reference interpreter, or is a body the pinned
//! `trust_ir_build::validate_module` refuses while the input passes it, and
//! asserts the checker refuses it. Covered: terminator-result availability
//! (invoke normal-edge rule), graph instructions after a terminator or before
//! a landing pad, redefined values, poison laundering through block
//! arguments, `select` arms and copies, non-canonical constants, landing-pad
//! selectors, claim bookkeeping, backwards `refines`, `Trans`/`Congr`
//! corners, pointer-width evaluation, operand order of skeleton asserts, and
//! the validity rules of section 2.5's last paragraph (value names,
//! instruction scopes, span files, cast width directions, the default block
//! of an exhaustive `Switch`, and the graph-operator typing the reader's
//! classification enforces), each with a positive control that a valid body
//! is still accepted.

mod common;

use common::*;
use trust_cg_eqsat_check::{Body, Rejection, Verdict, check};
use trust_ir::interpret::PanicStrategy;
use trust_ir::{
    Constant, Function, Inst, InterpretOptions, InterpretValue, Interpreter, Module, Ty,
};

const WASM: &str = "target \"wasm32-unknown-unknown\" 4 little\n";
const ARM64: &str = "target \"aarch64-apple-darwin\" 8 little\n";

const USIZE: u8 = 0x25;
const I32: u8 = 0x12;

fn parse_at(target: &str, body: &str) -> (Module, Function) {
    let text = format!("; TrustIr text format v1\nmodule \"m\"\n{target}file 0 \"m.rs\"\n\n{body}");
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("parse failed: {e}\n{text}"));
    let f = module.function_by_name("f").expect("function f").clone();
    (module, f)
}

fn run_at(
    target: &str,
    input: &str,
    output: &str,
    d: &Deriv,
    reg: &trust_cg_eqsat_check::Registry,
) -> Result<Verdict, Rejection> {
    let (module, i) = parse_at(target, input);
    let (_, o) = parse_at(target, output);
    check(&module, &i, &o, &d.encode(), reg)
}

/// The reference interpreter's outcome for `func` run in `module`.
fn outcome(
    module: &Module,
    func: &Function,
    args: &[InterpretValue],
    strategy: PanicStrategy,
) -> Result<String, String> {
    let options = InterpretOptions {
        panic_strategy: strategy,
        ..InterpretOptions::default()
    };
    match Interpreter::with_module(module)
        .with_options(options)
        .execute_function(func, args.iter().cloned())
    {
        Ok(out) => Ok(format!("{:?}", out.returns)),
        Err(e) => Err(format!("{:?}: {}", e.code, e.message)),
    }
}

/// Runs both bodies (the output inside the input's module) and returns the
/// two outcomes.
fn both(
    input: &str,
    output: &str,
    args: &[InterpretValue],
    strategy: PanicStrategy,
) -> (Result<String, String>, Result<String, String>) {
    let (module, i) = parse(input);
    let (_, o) = parse(output);
    (
        outcome(&module, &i, args, strategy),
        outcome(&module, &o, args, strategy),
    )
}

fn header() -> Deriv {
    Deriv::header("f")
}

fn refused_output_not_dominated(r: &Result<Verdict, Rejection>) {
    assert!(
        matches!(
            r,
            Err(Rejection::NotDominated {
                body: Body::Output,
                ..
            })
        ),
        "{r:?}"
    );
}

// ======================================================= terminator results

/// `@boom` panics; `@f`'s invoke unwinds into a catch-all pad that returns -1.
fn boom_module(f_body: &str) -> String {
    format!(
        "\
functy.0 = () -> (i64)
functy.1 = (i64) -> (i64)

fn @boom(functy.0) {{
bb0:
    %0 = const bool false
    assert %0, div_by_zero
    %1 = const i64 0
    ret %1
}}

fn @f(functy.1) {{
{f_body}}}
"
    )
}

/// The invoke's normal successor is its own block (S == the invoking block).
/// A copy of the result at the top of that block reads it before the first
/// call returns: the output fails with an undefined value where the input
/// catches the panic and returns -1.
#[test]
fn invoke_result_read_at_the_top_of_its_own_self_loop_block() {
    let input = boom_module(
        "bb0(%9: i64):
    br bb1(%9)
bb1(%1: i64):
    %0 = invoke @func.0() to bb1(%0) unwind bb2
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
",
    );
    let output = input.replace("bb1(%1: i64):\n", "bb1(%1: i64):\n    %7 = copy i64 %0\n");
    assert_ne!(input, output);
    let args = [InterpretValue::int(Ty::I64, 3).expect("i64")];
    let (i, o) = both(&input, &output, &args, PanicStrategy::Unwind);
    assert!(i.is_ok(), "{i:?}");
    assert!(o.is_err(), "{o:?}");

    let reg = registry();
    assert!(run(&input, &input, &header(), &reg).is_ok());
    refused_output_not_dominated(&run(&input, &output, &header(), &reg));
}

/// The invoke's normal successor is the entry block. A copy of the result in
/// the entry block reads it on the first entry, before any call.
#[test]
fn invoke_result_read_in_an_entry_block_normal_successor() {
    let input = boom_module(
        "bb0(%9: i64):
    %5 = const i64 0
    %6 = icmp eq i64 %9, %5
    condbr %6, bb1, bb3
bb1:
    %0 = invoke @func.0() to bb0(%0) unwind bb2
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
bb3:
    ret %9
",
    );
    let output = input.replace("bb0(%9: i64):\n", "bb0(%9: i64):\n    %7 = copy i64 %0\n");
    let args = [InterpretValue::int(Ty::I64, 3).expect("i64")];
    let (i, o) = both(&input, &output, &args, PanicStrategy::Unwind);
    assert!(i.is_ok(), "{i:?}");
    assert!(o.is_err(), "{o:?}");

    let reg = registry();
    assert!(run(&input, &input, &header(), &reg).is_ok());
    refused_output_not_dominated(&run(&input, &output, &header(), &reg));
}

/// The normal successor is also entered by two switch edges from a block it
/// does not dominate. The input reads the result only in its own normal-edge
/// arguments; the output adds a copy of it in the successor, which the
/// switch path reaches with the result never bound.
#[test]
fn invoke_result_read_in_a_successor_also_entered_by_switch_edges() {
    let input = "\
functy.0 = () -> (i64)
functy.1 = (i64) -> (i64)

fn @seven(functy.0) {
bb0:
    %0 = const i64 7
    ret %0
}

fn @f(functy.1) {
bb0(%9: i64):
    switch %9 [ 0: bb4 1: bb1(%9) default: bb1(%9) ]
bb4:
    %0 = invoke @func.0() to bb1(%0) unwind bb2
bb1(%1: i64):
    ret %1
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
}
";
    let output = input.replace(
        "bb1(%1: i64):\n    ret %1\n",
        "bb1(%1: i64):\n    %7 = copy i64 %0\n    ret %1\n",
    );
    assert_ne!(input, output);
    let args = [InterpretValue::int(Ty::I64, 5).expect("i64")];
    let (i, o) = both(input, &output, &args, PanicStrategy::Unwind);
    assert!(i.is_ok(), "{i:?}");
    assert!(o.is_err(), "{o:?}");

    let reg = registry();
    assert!(run(input, input, &header(), &reg).is_ok());
    refused_output_not_dominated(&run(input, &output, &header(), &reg));
}

/// Positive control: the normal successor's other edges are two switch
/// edges from itself (it dominates their source), so the result is
/// available there, and moving a copy of it into the successor is accepted.
#[test]
fn invoke_result_under_duplicate_self_edges_is_available() {
    let input = "\
functy.0 = () -> (i64)
functy.1 = (i64) -> (i64)

fn @seven(functy.0) {
bb0:
    %0 = const i64 7
    ret %0
}

fn @f(functy.1) {
bb0(%9: i64):
    %0 = invoke @func.0() to bb1() unwind bb3
bb1:
    switch %9 [ 0: bb1 1: bb1 default: bb2 ]
bb2:
    %7 = copy i64 %0
    ret %7
bb3:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
}
";
    let output = input
        .replace("bb1:\n    switch", "bb1:\n    %7 = copy i64 %0\n    switch")
        .replace("bb2:\n    %7 = copy i64 %0\n", "bb2:\n");
    assert_ne!(input, output);
    let args = [InterpretValue::int(Ty::I64, 5).expect("i64")];
    let (i, o) = both(input, &output, &args, PanicStrategy::Unwind);
    assert_eq!(i, o);
    assert!(i.is_ok(), "{i:?}");
    let reg = registry();
    let v = run(input, &output, &header(), &reg).expect("accepted");
    assert_eq!(v.changed_operands, 0);
}

/// Positive control: the result passed twice on its own normal edge.
#[test]
fn invoke_result_twice_in_its_own_normal_arguments_is_available() {
    let input = "\
functy.0 = () -> (i64)

fn @seven(functy.0) {
bb0:
    %0 = const i64 7
    ret %0
}

fn @f(functy.0) {
bb0:
    %0 = invoke @func.0() to bb1(%0, %0) unwind bb2
bb1(%1: i64, %5: i64):
    ret %5
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
}
";
    let reg = registry();
    let v = run(input, input, &header(), &reg).expect("accepted");
    assert_eq!(v.changed_operands, 0);
    // The two parameters are distinct leaves, whatever the edge passed.
    let output = input.replace(
        "bb1(%1: i64, %5: i64):\n    ret %5",
        "bb1(%1: i64, %5: i64):\n    ret %1",
    );
    assert_eq!(
        class(&run(input, &output, &header(), &reg)),
        "operand_unjustified"
    );
}

/// The output moves a see-through copy of the invoke result into the
/// landing-pad block (after the pad), where the result was never bound.
#[test]
fn invoke_result_copy_moved_into_the_pad_block() {
    let input = boom_module(
        "bb0(%9: i64):
    %0 = invoke @func.0() to bb1() unwind bb2
bb1:
    %7 = copy i64 %0
    ret %7
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
",
    );
    let output = input
        .replace("bb1:\n    %7 = copy i64 %0\n", "bb1:\n")
        .replace(
            "    %2, %3 = landingpad catch 0\n",
            "    %2, %3 = landingpad catch 0\n    %7 = copy i64 %0\n",
        );
    let reg = registry();
    assert!(run(&input, &input, &header(), &reg).is_ok());
    refused_output_not_dominated(&run(&input, &output, &header(), &reg));
}

/// A graph instruction over an invoke result is a frontier instruction (the
/// result may be poison): it is skeleton, so hoisting it is a count change.
#[test]
fn graph_form_over_an_invoke_result_is_skeleton() {
    let input = "\
functy.0 = () -> (i64)
functy.1 = (bool) -> (i64)

fn @seven(functy.0) {
bb0:
    %0 = const i64 7
    ret %0
}

fn @f(functy.1) {
bb0(%9: bool):
    %0 = invoke @func.0() to bb1() unwind bb3
bb1:
    condbr %9, bb2, bb4
bb2:
    %5 = const i64 1
    %6 = add i64 %0, %5
    ret %6
bb4:
    ret %0
bb3:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
}
";
    let output = input
        .replace(
            "bb1:\n    condbr",
            "bb1:\n    %5 = const i64 1\n    %6 = add i64 %0, %5\n    condbr",
        )
        .replace(
            "bb2:\n    %5 = const i64 1\n    %6 = add i64 %0, %5\n",
            "bb2:\n",
        );
    let reg = registry();
    assert!(run(input, input, &header(), &reg).is_ok());
    assert_eq!(
        class(&run(input, &output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}

// ========================================================= placement rules

/// A graph instruction after the block's terminator.
#[test]
fn graph_instruction_after_the_terminator() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 7
    ret %1
}
";
    let output = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 7
    ret %1
    %2 = const u32 8
}
";
    let reg = registry();
    let r = run(input, output, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(Rejection::MalformedBody {
                body: Body::Output,
                ..
            })
        ),
        "{r:?}"
    );
}

/// A see-through copy (not a graph instruction) placed before a landing
/// pad: the interpreter cannot unwind into the block.
#[test]
fn see_through_copy_before_a_landingpad() {
    let input = boom_module(
        "bb0(%9: i64):
    %5 = const i64 -1
    %0 = invoke @func.0() to bb1() unwind bb2
bb1:
    ret %0
bb2:
    %2, %3 = landingpad catch 0
    %4 = copy i64 %5
    ret %4
",
    );
    let output = input.replace(
        "    %2, %3 = landingpad catch 0\n    %4 = copy i64 %5\n",
        "    %4 = copy i64 %5\n    %2, %3 = landingpad catch 0\n",
    );
    let args = [InterpretValue::int(Ty::I64, 0).expect("i64")];
    let (i, o) = both(&input, &output, &args, PanicStrategy::Unwind);
    assert!(i.is_ok(), "{i:?}");
    assert!(o.is_err(), "{o:?}");
    let reg = registry();
    assert!(run(&input, &input, &header(), &reg).is_ok());
    let r = run(&input, &output, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(Rejection::MalformedBody {
                body: Body::Output,
                ..
            })
        ),
        "{r:?}"
    );
}

/// A graph value that reuses the id of a block parameter or a skeleton
/// result.
#[test]
fn graph_value_reusing_a_defined_id() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 7
    br bb1(%1)
bb1(%2: u32):
    ret %2
}
";
    let reg = registry();
    for output in [
        input.replace("    ret %2\n", "    %2 = const u32 7\n    ret %2\n"),
        input
            .replace("%1 = const u32 7", "%0 = const u32 7")
            .replace("bb1(%1)", "bb1(%0)"),
    ] {
        assert_eq!(
            class(&run(input, &output, &header(), &reg)),
            "duplicate_definition",
            "{output}"
        );
    }
}

// =================================================== definedness laundering

/// An undef passed through a block argument is a parameter leaf (may be
/// poison): the add over it is a frontier instruction, so hoisting it above
/// its guard is refused. The interpreter shows the hoist is unsound.
#[test]
fn block_argument_does_not_launder_poison() {
    let input = "\
functy.0 = (bool) -> (u32)

fn @f(functy.0) {
bb0(%0: bool):
    %1 = undef u32
    %2 = const u32 1
    br bb1(%1)
bb1(%3: u32):
    condbr %0, bb2, bb3
bb2:
    %4 = add u32 %3, %2
    ret %4
bb3:
    ret %2
}
";
    let output = input
        .replace(
            "bb1(%3: u32):\n    condbr",
            "bb1(%3: u32):\n    %4 = add u32 %3, %2\n    condbr",
        )
        .replace("bb2:\n    %4 = add u32 %3, %2\n", "bb2:\n");
    let args = [InterpretValue::bool(false)];
    let (i, o) = both(input, &output, &args, PanicStrategy::Abort);
    assert!(i.is_ok(), "{i:?}");
    assert!(o.is_err(), "{o:?}");
    let reg = registry();
    assert_eq!(
        class(&run(input, &output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}

/// A select with a maybe-poison arm is skeleton, and so is a graph form over
/// its result; a copy of an undef stays maybe-poison.
#[test]
fn select_arm_and_copy_do_not_launder_poison() {
    for (def, name) in [
        (
            "    %5 = const bool true\n    %6 = select u32 %5, %1, %2\n",
            "select",
        ),
        ("    %6 = copy u32 %1\n", "copy"),
    ] {
        let input = format!(
            "\
functy.0 = (bool) -> (u32)

fn @f(functy.0) {{
bb0(%0: bool):
    %1 = undef u32
    %2 = const u32 1
{def}    condbr %0, bb2, bb3
bb2:
    %4 = add u32 %6, %2
    ret %4
bb3:
    ret %2
}}
"
        );
        let output = input
            .replace(
                "    condbr %0, bb2, bb3\n",
                "    %4 = add u32 %6, %2\n    condbr %0, bb2, bb3\n",
            )
            .replace("bb2:\n    %4 = add u32 %6, %2\n", "bb2:\n");
        let args = [InterpretValue::bool(false)];
        let (i, o) = both(&input, &output, &args, PanicStrategy::Abort);
        assert!(i.is_ok(), "{name}: {i:?}");
        assert!(o.is_err(), "{name}: {o:?}");
        let reg = registry();
        assert_eq!(
            class(&run(&input, &output, &header(), &reg)),
            "skeleton_count_mismatch",
            "{name}"
        );
    }
}

/// Non-canonical constants (`U128` below u128, `Int` at Bool) are skeleton:
/// their results may not be read as graph constants, so replacing their use
/// with the canonical spelling is unjustified.
#[test]
fn non_canonical_constants_are_skeleton() {
    let base = "\
functy.0 = () -> (u8)

fn @f(functy.0) {
bb0:
    %1 = const u8 5
    ret %1
}
";
    let reg = registry();
    let (module, canonical) = parse(base);
    let mut spelled = canonical.clone();
    let Inst::Const { value, .. } = &mut spelled.blocks[0].body[0].inst else {
        panic!("const");
    };
    *value = Constant::U128(5);
    // The interpreter refuses the non-canonical spelling.
    assert!(outcome(&module, &spelled, &[], PanicStrategy::Abort).is_err());
    assert!(outcome(&module, &canonical, &[], PanicStrategy::Abort).is_ok());
    for (a, b) in [(&spelled, &canonical), (&canonical, &spelled)] {
        let r = check(&module, a, b, &header().encode(), &reg);
        assert_eq!(class(&r), "skeleton_count_mismatch", "{r:?}");
    }

    let base = "\
functy.0 = () -> (bool)

fn @f(functy.0) {
bb0:
    %1 = const bool true
    ret %1
}
";
    let (module, canonical) = parse(base);
    let mut spelled = canonical.clone();
    let Inst::Const { value, .. } = &mut spelled.blocks[0].body[0].inst else {
        panic!("const");
    };
    *value = Constant::Int(1);
    for (a, b) in [(&spelled, &canonical), (&canonical, &spelled)] {
        let r = check(&module, a, b, &header().encode(), &reg);
        assert_eq!(class(&r), "skeleton_count_mismatch", "{r:?}");
    }
}

/// The landing pad's selector may be poison: no rule binds it.
#[test]
fn landingpad_selector_is_not_a_defined_leaf() {
    let input = "\
functy.0 = () -> (i32)

fn @boom(functy.0) {
bb0:
    %0 = const bool false
    assert %0, div_by_zero
    %1 = const i32 0
    ret %1
}

fn @f(functy.0) {
bb0:
    %0 = invoke @func.0() to bb1() unwind bb2
bb1:
    ret %0
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i32 1
    %5 = mul i32 %3, %4
    ret %5
}
";
    let reg = registry();
    assert!(run(input, input, &header(), &reg).is_ok());
    // `mul S 1 = S` with S the selector: replay refuses the binding before
    // any operand is compared.
    let mut d = Deriv::header("f").with_rule(&reg, "mul_one");
    d.terms = vec![T::Result(2, 0, 1)];
    d.proofs = vec![rule(0, I32, &[("x", 0)], &[])];
    d.claims = vec![0];
    assert_eq!(class(&run(input, input, &d, &reg)), "maybe_poison_leaf");
}

// ================================================================= replay

/// Scenario A's output with `ret %2, %2` in both: one claim justifies two
/// operands with the same term pair (accepted, it is the same equation).
#[test]
fn one_claim_for_two_operands_is_accepted_and_a_repeated_conclusion_is_not() {
    let to_pair = |s: &str| {
        s.replace("(u32) -> (u32)", "(u32) -> (u32, u32)")
            .replace("    ret %4\n", "    ret %4, %4\n")
            .replace("    ret %2\n", "    ret %2, %2\n")
    };
    let (input, output) = (to_pair(A_IN), to_pair(A_OUT));
    let reg = registry();
    let v = run(&input, &output, &a_deriv(&reg), &reg).expect("accepted");
    assert_eq!((v.claims, v.changed_operands), (1, 2));

    // A second claim with the same conclusion (via Trans with Refl).
    let mut d = a_deriv(&reg);
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[]), P::Refl(0), P::Trans(0, 1)];
    d.claims = vec![0, 2];
    assert_eq!(class(&run(&input, &output, &d, &reg)), "claim_mismatch");
}

/// A `refines` rule used backwards: the input returns `0`, the output
/// returns `mul R 0` (equal values, but the registry states only the forward
/// direction).
#[test]
fn refines_rule_used_backwards() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    ret %1
}
";
    let output = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = mul u32 %2, %1
    ret %3
}
";
    let reg = registry();
    let mut d = Deriv::header("f").with_rule(&reg, "mul_zero");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[]), P::Sym(0)];
    d.claims = vec![1];
    assert_eq!(class(&run(input, output, &d, &reg)), "sym_of_refines");
    // Mixed: Trans(refines, equiv) is refines, and its Sym is refused too.
    let mut d = Deriv::header("f").with_rule(&reg, "mul_zero");
    d.terms = vec![T::Result(0, 0, 0), T::Const(U32, 0)];
    d.proofs = vec![
        rule(0, U32, &[("x", 0)], &[]),
        P::Refl(1),
        P::Trans(0, 1),
        P::Sym(2),
    ];
    d.claims = vec![3];
    assert_eq!(class(&run(input, output, &d, &reg)), "sym_of_refines");
}

/// Trans with different middle terms; Congr over a maybe-poison parameter.
#[test]
fn trans_and_congr_corner_cases() {
    let reg = registry();
    let mut d = Deriv::header("f")
        .with_rule(&reg, "add_zero")
        .with_rule(&reg, "mul_one");
    d.terms = vec![
        T::Result(0, 0, 0),
        T::Const(U32, 0),
        T::Op(OpD::Bin(ADD, U32), vec![0, 1]),
    ];
    // mul_one concludes (mul (add R 0) 1, add R 0); add_zero at R concludes
    // (add R 0, R) — swap the binding so the middle terms differ.
    d.proofs = vec![
        rule(1, U32, &[("x", 0)], &[]),
        rule(0, U32, &[("x", 2)], &[]),
        P::Trans(1, 0),
    ];
    d.claims = vec![2];
    assert_eq!(class(&run(B_IN, B_OUT, &d, &reg)), "trans_middle_mismatch");

    // Congr(add, Refl(Param), Refl(Const)) builds an add over a parameter.
    let mut d = Deriv::header("f");
    d.terms = vec![T::Param(0, 0), T::Const(U32, 0)];
    d.proofs = vec![
        P::Refl(0),
        P::Refl(1),
        P::Congr(OpD::Bin(ADD, U32), vec![0, 1]),
    ];
    d.claims = vec![2];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "maybe_poison_leaf");

    // Congr at an operator section 2.2 does not admit (add at Bool).
    let mut d = Deriv::header("f");
    d.terms = vec![T::Const(BOOL, 1)];
    d.proofs = vec![P::Refl(0), P::Congr(OpD::Bin(ADD, BOOL), vec![0, 0])];
    d.claims = vec![1];
    assert!(run(A_IN, A_OUT, &d, &reg).is_err());
}

const WIDTH_RULES: &str = "\
(rule fold_add_w
  (direction equiv)
  (domain usize u32)
  (lhs (add (const ?a) (const ?b)))
  (rhs (eval add ?a ?b))
  (where))

(rule rotl_full_w
  (direction equiv)
  (domain usize)
  (lhs (rotl ?x (const ?c)))
  (rhs ?x)
  (where (zero_mod_width ?c)))
";

/// `(eval add ...)` at usize folds at the module's pointer width: accepted at
/// 32 bits (the interpreter agrees), refused at 64 bits.
#[test]
fn eval_at_usize_follows_the_pointer_width() {
    let input = "\
functy.0 = () -> (usize)

fn @f(functy.0) {
bb0:
    %0 = const usize 4294967295
    %1 = const usize 1
    %2 = add usize %0, %1
    ret %2
}
";
    let output = "\
functy.0 = () -> (usize)

fn @f(functy.0) {
bb0:
    %3 = const usize 0
    ret %3
}
";
    let reg = trust_cg_eqsat_check::Registry::parse(WIDTH_RULES).expect("rules");
    let mut d = Deriv::header("f").with_rule(&reg, "fold_add_w");
    d.terms = vec![T::Const(USIZE, 0xffff_ffff), T::Const(USIZE, 1)];
    d.proofs = vec![rule(0, USIZE, &[("a", 0), ("b", 1)], &[])];
    d.claims = vec![0];

    let (module, i) = parse_at(WASM, input);
    let (_, o) = parse_at(WASM, output);
    assert_eq!(
        outcome(&module, &i, &[], PanicStrategy::Abort),
        outcome(&module, &o, &[], PanicStrategy::Abort)
    );
    assert!(run_at(WASM, input, output, &d, &reg).is_ok());

    let (module, i) = parse_at(ARM64, input);
    let (_, o) = parse_at(ARM64, output);
    assert_ne!(
        outcome(&module, &i, &[], PanicStrategy::Abort),
        outcome(&module, &o, &[], PanicStrategy::Abort)
    );
    assert_eq!(
        class(&run_at(ARM64, input, output, &d, &reg)),
        "conclusion_mismatch"
    );
    // The 64-bit residue as a 32-bit constant is ill typed.
    let mut wide = d.clone();
    wide.terms = vec![T::Const(USIZE, 0x1_0000_0000), T::Const(USIZE, 1)];
    assert_eq!(
        class(&run_at(WASM, input, output, &wide, &reg)),
        "ill_typed_term"
    );
}

/// `zero_mod_width` at usize reads the module's pointer width: rotating by
/// 32 is the identity at 32 bits only.
#[test]
fn zero_mod_width_at_usize_follows_the_pointer_width() {
    let input = "\
functy.0 = (usize) -> (usize)

fn @f(functy.0) {
bb0(%0: usize):
    %1 = const usize 0
    %2 = xor usize %0, %1
    %3 = const usize 32
    %4 = rotl usize %2, %3
    ret %4
}
";
    let output = "\
functy.0 = (usize) -> (usize)

fn @f(functy.0) {
bb0(%0: usize):
    %1 = const usize 0
    %2 = xor usize %0, %1
    ret %2
}
";
    let reg = trust_cg_eqsat_check::Registry::parse(WIDTH_RULES).expect("rules");
    let mut d = Deriv::header("f").with_rule(&reg, "rotl_full_w");
    d.terms = vec![T::Result(0, 0, 0), T::Const(USIZE, 32)];
    d.proofs = vec![rule(0, USIZE, &[("c", 1), ("x", 0)], &[0])];
    d.claims = vec![0];
    assert!(run_at(WASM, input, output, &d, &reg).is_ok());
    assert_eq!(
        class(&run_at(ARM64, input, output, &d, &reg)),
        "side_condition_failed"
    );
}

/// A rule instance at a type the module gives no width (usize with 16-bit
/// pointers) is refused; the add there is not a graph instruction at all.
#[test]
fn usize_without_an_established_width() {
    let t16 = "target \"msp430-none-elf\" 2 little\n";
    let input = "\
functy.0 = () -> (usize)

fn @f(functy.0) {
bb0:
    %0 = const usize 1
    %1 = const usize 1
    %2 = add usize %0, %1
    ret %2
}
";
    let output = "\
functy.0 = () -> (usize)

fn @f(functy.0) {
bb0:
    %3 = const usize 2
    ret %3
}
";
    let reg = trust_cg_eqsat_check::Registry::parse(WIDTH_RULES).expect("rules");
    let mut d = Deriv::header("f").with_rule(&reg, "fold_add_w");
    d.terms = vec![T::Const(USIZE, 1)];
    d.proofs = vec![rule(0, USIZE, &[("a", 0), ("b", 0)], &[])];
    d.claims = vec![0];
    assert!(run_at(t16, input, output, &d, &reg).is_err());
}

// ========================================================= instruction fields

/// The bounds-check operands of an assert are skeleton operands: swapping
/// them changes the panic message.
#[test]
fn assert_bounds_check_operands_swapped() {
    let input = "\
functy.0 = (usize, usize) -> ()

fn @f(functy.0) {
bb0(%0: usize, %1: usize):
    %2 = icmp ult usize %0, %1
    assert %2, bounds_check %0, %1
    ret
}
";
    let output = input.replace("bounds_check %0, %1", "bounds_check %1, %0");
    let args = [
        InterpretValue::int(Ty::Usize, 9).expect("usize"),
        InterpretValue::int(Ty::Usize, 4).expect("usize"),
    ];
    let (i, o) = both(input, &output, &args, PanicStrategy::Abort);
    assert_ne!(i, o);
    let reg = registry();
    assert_eq!(
        class(&run(input, &output, &header(), &reg)),
        "operand_unjustified"
    );
}

// =================================================================== validity
//
// Each refused output below runs exactly like its input under the
// interpreter, and the input passes `trust_ir_build::validate_module`, but
// the output does not; each positive control passes it (verdicts read with
// the pinned validator through `target.noindex/debug/examples/
// eqsat_corpus_probe`; this crate cannot depend on trust-ir-build).

/// The rejection is `malformed_body` in `body`.
fn refused_malformed(r: &Result<Verdict, Rejection>, body: Body) {
    assert!(
        matches!(r, Err(Rejection::MalformedBody { body: b, .. }) if *b == body),
        "{r:?}"
    );
}

/// The body accepted as its own rewrite (identity, empty derivation).
fn accepted_identity(body: &str) {
    let reg = registry();
    let r = run(body, body, &header(), &reg);
    assert!(r.is_ok(), "refused a valid body: {r:?}\n{body}");
}

/// Parses `body` under a module header with no source-file table.
fn parse_without_files(body: &str) -> (Module, Function) {
    let text = format!("; TrustIr text format v1\nmodule \"m\"\n\n{body}");
    let module = trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("parse failed: {e}\n{text}"));
    let f = module.function_by_name("f").expect("function f").clone();
    (module, f)
}

/// The output removes a copy and keeps its `value_names` entry:
/// `InvalidValueName` ("no block parameter or instruction result defines
/// it").
#[test]
fn validity_stale_value_name() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
    ; #names: %0=\"x\", %2=\"y\"
bb0(%0: u32):
    %1 = const u32 0
    %2 = copy u32 %0
    ret %2
}
";
    let output = input.replace("    %2 = copy u32 %0\n    ret %2\n", "    ret %0\n");
    let reg = registry();
    let r = run(input, &output, &header(), &reg);
    refused_malformed(&r, Body::Output);
}

/// One `ValueId` named twice: `InvalidValueName` ("the same SSA value
/// appears more than once").
#[test]
fn validity_value_named_twice() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
    ; #names: %0=\"x\"
bb0(%0: u32):
    ret %0
}
";
    let output = input.replace("%0=\"x\"\n", "%0=\"x\", %0=\"y\"\n");
    assert_ne!(input, output);
    let reg = registry();
    refused_malformed(&run(input, &output, &header(), &reg), Body::Output);
    refused_malformed(&run(&output, input, &header(), &reg), Body::Input);
}

/// Positive control: names of defined values, including one name string on
/// two values (the validator compares `ValueId`s only), are accepted.
#[test]
fn validity_valid_value_names_are_accepted() {
    accepted_identity(
        "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
    ; #names: %0=\"x\", %2=\"x\", %1=\"k\"
bb0(%0: u32):
    %1 = const u32 0
    %2 = copy u32 %0
    ret %2
}
",
    );
}

/// A graph instruction whose scope is outside the function's scope table:
/// `InvalidInstructionScope`.
#[test]
fn validity_graph_instruction_scope_out_of_range() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
    ; #scope: 0 root
bb0(%0: u32):
    %1 = const u32 7  ; #scope: 0
    ret %1  ; #scope: 0
}
";
    let reg = registry();
    for scope in ["1", "5"] {
        let output = input.replace(
            "%1 = const u32 7  ; #scope: 0",
            &format!("%1 = const u32 7  ; #scope: {scope}"),
        );
        let r = run(input, &output, &header(), &reg);
        refused_malformed(&r, Body::Output);
    }
}

/// A stamped scope in a function with no scope table (its length is 0):
/// `InvalidInstructionScope`.
#[test]
fn validity_graph_instruction_scope_without_a_table() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 7
    ret %0
}
";
    let output = input.replace("%1 = const u32 7\n", "%1 = const u32 7  ; #scope: 0\n");
    assert_ne!(input, output);
    let reg = registry();
    refused_malformed(&run(input, &output, &header(), &reg), Body::Output);
}

/// Positive control: scopes inside the table, and unstamped instructions.
#[test]
fn validity_valid_scopes_are_accepted() {
    accepted_identity(
        "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
    ; #scope: 0 root
    ; #scope: 1 parent=0
bb0(%0: u32):
    %1 = const u32 7  ; #scope: 1
    %2 = const u32 8
    ret %0  ; #scope: 0
}
",
    );
}

/// A graph instruction whose span names a file the module does not have:
/// `SpanFileIndexOutOfRange`.
#[test]
fn validity_graph_instruction_span_file_out_of_range() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 7  ; #loc: 0 1 1
    ret %1
}
";
    let reg = registry();
    for file in ["1", "9"] {
        let output = input.replace("#loc: 0 1 1", &format!("#loc: {file} 1 1"));
        let r = run(input, &output, &header(), &reg);
        refused_malformed(&r, Body::Output);
    }
}

/// A scope's opening span, or an inlining link's call-site span, naming a
/// file the module does not have: `SpanFileIndexOutOfRange`. The scope table
/// is equal in both bodies, so the input is refused.
#[test]
fn validity_scope_span_file_out_of_range() {
    let reg = registry();
    for table in [
        "    ; #scope: 0 root at 9 1 1\n",
        "    ; #scope: 0 root\n    ; #scope: 1 parent=0 inlined-at 9 1 1 callee \"g\"\n",
    ] {
        let body = format!(
            "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {{
{table}bb0(%0: u32):
    ret %0  ; #scope: 0
}}
"
        );
        refused_malformed(&run(&body, &body, &header(), &reg), Body::Input);
    }
}

/// Positive controls: spans inside the file table; and with no file table
/// at all, spans are file-less and any file index is accepted (the validator
/// checks nothing then).
#[test]
fn validity_valid_spans_are_accepted() {
    accepted_identity(
        "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
    ; #scope: 0 root at 0 1 1
bb0(%0: u32):
    %1 = const u32 7  ; #loc: 0 1 1  ; #scope: 0
    ret %0  ; #loc: 0 2 1
}
",
    );
    let body = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
    ; #scope: 0 root at 9 1 1
bb0(%0: u32):
    %1 = const u32 7  ; #loc: 9 1 1  ; #scope: 0
    ret %0
}
";
    let (module, f) = parse_without_files(body);
    assert!(module.files.is_empty());
    let r = check(&module, &f, &f, &header().encode(), &registry());
    assert!(r.is_ok(), "{r:?}");
}

/// A dead graph cast in a width direction the validator refuses (`trunc`
/// to a wider type, `zext` to a narrower one, and identity resizes: the
/// rule is strict): `CastWidthDirectionInvalid`.
#[test]
fn validity_dead_graph_cast_in_an_invalid_direction() {
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u8 7
    ret %0
}
";
    let reg = registry();
    for cast in [
        "    %2 = trunc u8 %1 to u32\n",
        "    %2 = zext u8 %1 to i8\n",
        "    %2 = trunc u8 %1 to u8\n",
        "    %2 = zext u8 %1 to u8\n",
        "    %2 = sext u8 %1 to i8\n",
        "    %2 = sext u8 %1 to u8\n",
    ] {
        let output = input.replace("    ret %0\n", &format!("{cast}    ret %0\n"));
        let r = run(input, &output, &header(), &reg);
        refused_malformed(&r, Body::Output);
    }
}

/// The rule covers every resize with target-independent widths, not only
/// graph casts: a `bool -> bool` extension (1 bit to 1 bit) is refused.
#[test]
fn validity_bool_identity_extension_is_refused() {
    let body = "\
functy.0 = (u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: bool):
    %2 = zext bool %1 to bool
    ret %0
}
";
    let reg = registry();
    refused_malformed(&run(body, body, &header(), &reg), Body::Input);
}

/// Positive control: resizes in their direction, the pointer-width integers
/// (no target-independent width, exempt in either direction), and `bool`
/// resizes (1 bit) are accepted.
#[test]
fn validity_valid_casts_are_accepted() {
    accepted_identity(
        "\
functy.0 = (u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: bool):
    %2 = trunc u32 %0 to u8
    %3 = zext u8 %2 to u64
    %4 = sext u8 %2 to i64
    %5 = zext u32 %0 to usize
    %6 = trunc usize %5 to u64
    %7 = zext usize %5 to u32
    %8 = zext bool %1 to u8
    %9 = trunc u8 %2 to bool
    ret %0
}
",
    );
}

/// Graph-operator typing: a dead instruction the validator refuses for its
/// type category (`not bool`, `neg bool`, `add bool`, `rotl bool`,
/// `bxor u32`) is not a graph instruction, so the output gains a skeleton
/// instruction and is refused.
#[test]
fn validity_dead_ill_typed_operator_is_skeleton_and_refused() {
    let input = "\
functy.0 = (u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: bool):
    ret %0
}
";
    let reg = registry();
    for inst in [
        "    %2 = not bool %1\n",
        "    %2 = neg bool %1\n",
        "    %2 = add bool %1, %1\n",
        "    %2 = rotl bool %1, %1\n",
        "    %2 = bxor u32 %0, %0\n",
    ] {
        let output = input.replace("    ret %0\n", &format!("{inst}    ret %0\n"));
        let r = run(input, &output, &header(), &reg);
        assert!(r.is_err(), "accepted {inst:?}: {r:?}");
    }
}

/// A flagged switch over the tag of a three-variant enum whose default block
/// bb2 is the dead arm; `{pre}` goes before the switch, `{dead}` before the
/// `unreachable`, and `{flag}` is ` exhaustive` or empty.
fn exhaustive_switch_body(pre: &str, dead: &str, flag: &str) -> String {
    format!(
        "\
enum @E repr(u8) {{ A, B, C }} id=0

functy.0 = (enum.0) -> (u32)

fn @f(functy.0) {{
bb0(%0: enum.0):
    %1 = extractfield u8 %0, 0
    %2 = zext u8 %1 to u32
{pre}    switch %2 [ 0: bb1 1: bb1 2: bb1 default: bb2 ]{flag}
bb1:
    %50 = const u32 1
    ret %50
bb2:
{dead}    unreachable
}}
"
    )
}

/// The instructions an output adds to (or moves into) the default block: a
/// dead graph constant, a see-through copy and a graph `add`.
const DEFAULT_ARM_ADDITIONS: [&str; 3] = [
    "    %7 = const u32 7\n",
    "    %7 = copy u32 %2\n",
    "    %7 = add u32 %2, %2\n",
];

/// Rule 1 (ii) of the validator's exhaustive-switch shape rule: the default
/// block of a `Switch` flagged `exhaustive_enum_unreachable` is exactly
/// `[unreachable]`. A graph instruction or copy added to it is never
/// executed (the arm is dead), so the output runs like the input, but the
/// validator refuses it: "switch claims exhaustive_enum_unreachable but its
/// default is not a dead arm (the default block bb2 is not exactly
/// [unreachable] (2 instruction(s)))".
#[test]
fn validity_graph_instruction_added_to_an_exhaustive_default_block() {
    let reg = registry();
    let input = exhaustive_switch_body("", "", " exhaustive");
    // Every addition is checked before the assertion, so a failure names
    // each one the checker did not refuse.
    let mut not_refused = Vec::new();
    for dead in DEFAULT_ARM_ADDITIONS {
        let output = exhaustive_switch_body("", dead, " exhaustive");
        let r = run(&input, &output, &header(), &reg);
        let refused = matches!(
            &r,
            Err(Rejection::MalformedBody {
                body: Body::Output,
                block: Some(0),
                detail,
                ..
            }) if detail.contains("default block bb2 is not exactly [unreachable]")
        );
        // The same body as an input is refused too.
        let as_input = run(&output, &output, &header(), &reg);
        let refused_as_input = matches!(
            &as_input,
            Err(Rejection::MalformedBody {
                body: Body::Input,
                ..
            })
        );
        if !refused || !refused_as_input {
            not_refused.push(format!("{dead:?}: {r:?} / as input: {as_input:?}"));
        }
    }
    assert!(not_refused.is_empty(), "{not_refused:#?}");
}

/// A dead graph constant moved from the switch's block into its default
/// block, with a header-only derivation (no term changes): the input
/// validates, the output is refused by the same rule.
#[test]
fn validity_dead_constant_moved_into_an_exhaustive_default_block() {
    let reg = registry();
    let constant = DEFAULT_ARM_ADDITIONS[0];
    let input = exhaustive_switch_body(constant, "", " exhaustive");
    let output = exhaustive_switch_body("", constant, " exhaustive");
    assert!(run(&input, &input, &header(), &reg).is_ok());
    let r = run(&input, &output, &header(), &reg);
    assert!(
        matches!(
            &r,
            Err(Rejection::MalformedBody {
                body: Body::Output,
                block: Some(0),
                ..
            })
        ),
        "{r:?}"
    );
}

/// Positive controls: the unchanged flagged input is accepted, and an
/// unflagged switch accepts the same additions and the same move (the
/// validator checks the default block only under the flag; each of these
/// outputs validates).
#[test]
fn validity_default_block_additions_under_an_unflagged_switch_are_accepted() {
    let reg = registry();
    accepted_identity(&exhaustive_switch_body("", "", " exhaustive"));
    let input = exhaustive_switch_body("", "", "");
    for dead in DEFAULT_ARM_ADDITIONS {
        let output = exhaustive_switch_body("", dead, "");
        let r = run(&input, &output, &header(), &reg);
        assert!(r.is_ok(), "{dead:?}: {r:?}");
    }
    let constant = DEFAULT_ARM_ADDITIONS[0];
    let r = run(
        &exhaustive_switch_body(constant, "", ""),
        &exhaustive_switch_body("", constant, ""),
        &header(),
        &reg,
    );
    assert!(r.is_ok(), "{r:?}");
}
