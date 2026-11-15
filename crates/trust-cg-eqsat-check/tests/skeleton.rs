// trust-cg-eqsat-check/tests/skeleton.rs - effectful skeleton, function fields, eligibility, availability and unwind shape
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Section 8 items 1-3: the skeleton may not be moved, reordered, deleted,
//! extended or changed beyond its value operands; function fields and blocks
//! must agree; ineligible functions are refused; every use must be
//! available (section 4, including the normal-edge rule for invoke results);
//! a landing pad stays first in its block and a `Resume` keeps an operand
//! trust-ir admits. Moving and merging graph instructions needs no proof.

mod common;

use common::*;
use trust_cg_eqsat_check::{Body, Rejection};
use trust_ir::interpret::PanicStrategy;
use trust_ir::{Function, InterpretOptions, InterpretValue, Interpreter, Module, Ty};

/// The reference interpreter's outcome: the returned values, or the error
/// code and message.
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

fn returns_i64(v: i128) -> Result<String, String> {
    Ok(format!(
        "{:?}",
        vec![InterpretValue::int(Ty::I64, v).expect("i64 value")]
    ))
}

fn header() -> Deriv {
    Deriv::header("f")
}

const STORE_IN: &str = "\
functy.0 = (ptr, ptr, u32) -> ()

fn @f(functy.0) {
bb0(%0: ptr, %1: ptr, %2: u32):
    store u32 %2, ptr %0  ; #loc: 0 3 5
    store u32 %2, ptr %1  ; #loc: 0 4 5
    br bb1
bb1:
    ret
}
";

#[test]
fn identical_output_with_header_only_derivation_is_accepted() {
    let reg = registry();
    for body in [A_IN, B_IN, C_IN, STORE_IN] {
        let v = run(body, body, &header(), &reg).expect("identity accepted");
        assert_eq!(v.claims, 0);
        assert_eq!(v.changed_operands, 0);
        assert!(v.skeleton_operands > 0);
    }
}

#[test]
fn moved_store() {
    let reg = registry();
    let output = "\
functy.0 = (ptr, ptr, u32) -> ()

fn @f(functy.0) {
bb0(%0: ptr, %1: ptr, %2: u32):
    store u32 %2, ptr %0  ; #loc: 0 3 5
    br bb1
bb1:
    store u32 %2, ptr %1  ; #loc: 0 4 5
    ret
}
";
    assert_eq!(
        class(&run(STORE_IN, output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}

#[test]
fn swapped_stores() {
    let reg = registry();
    let output = "\
functy.0 = (ptr, ptr, u32) -> ()

fn @f(functy.0) {
bb0(%0: ptr, %1: ptr, %2: u32):
    store u32 %2, ptr %1  ; #loc: 0 3 5
    store u32 %2, ptr %0  ; #loc: 0 4 5
    br bb1
bb1:
    ret
}
";
    assert_eq!(
        class(&run(STORE_IN, output, &header(), &reg)),
        "operand_unjustified"
    );
    // With the spans swapped too, the instructions themselves differ.
    let output = output
        .replace("%1  ; #loc: 0 3 5", "%1  ; #loc: 0 4 5")
        .replace("%0  ; #loc: 0 4 5", "%0  ; #loc: 0 3 5");
    assert_eq!(
        class(&run(STORE_IN, &output, &header(), &reg)),
        "skeleton_instruction_mismatch"
    );
}

#[test]
fn changed_span() {
    let reg = registry();
    let output = STORE_IN.replace("%0  ; #loc: 0 3 5", "%0  ; #loc: 0 3 6");
    assert_eq!(
        class(&run(STORE_IN, &output, &header(), &reg)),
        "skeleton_instruction_mismatch"
    );
}

#[test]
fn changed_attribute() {
    let reg = registry();
    let output = STORE_IN.replace("store u32 %2, ptr %0", "store u32 %2, ptr %0, align 4");
    assert_eq!(
        class(&run(STORE_IN, &output, &header(), &reg)),
        "skeleton_instruction_mismatch"
    );
}

#[test]
fn changed_branch_target() {
    let reg = registry();
    let input = "\
functy.0 = (bool) -> ()

fn @f(functy.0) {
bb0(%0: bool):
    condbr %0, bb1, bb2
bb1:
    ret
bb2:
    ret
}
";
    let output = input.replace("condbr %0, bb1, bb2", "condbr %0, bb2, bb1");
    assert_eq!(
        class(&run(input, &output, &header(), &reg)),
        "skeleton_instruction_mismatch"
    );
}

#[test]
fn extra_skeleton_instruction() {
    let reg = registry();
    let output = STORE_IN.replace(
        "    br bb1\n",
        "    store u32 %2, ptr %1  ; #loc: 0 4 5\n    br bb1\n",
    );
    assert_eq!(
        class(&run(STORE_IN, &output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}

const CALL_IN: &str = "\
functy.0 = (u32) -> (u32)

fn @g(functy.0) {
bb0(%0: u32):
    ret %0
}

fn @f(functy.0) {
bb0(%0: u32):
    %1 = call @func.0(%0)
    ret %0
}
";

#[test]
fn deleted_call() {
    let reg = registry();
    let output = CALL_IN.replace("    %1 = call @func.0(%0)\n", "");
    assert_eq!(
        class(&run(CALL_IN, &output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}

#[test]
fn call_result_is_a_maybe_poison_leaf() {
    // The call result is skeleton; it may be poison, so (add r 0) over it is
    // a frontier instruction and stays skeleton, and add_zero may not bind it.
    let reg = registry();
    let input = "\
functy.0 = (u32) -> (u32)

fn @g(functy.0) {
bb0(%0: u32):
    ret %0
}

fn @f(functy.0) {
bb0(%0: u32):
    %1 = call @func.0(%0)
    %2 = const u32 0
    %3 = add u32 %1, %2
    ret %3
}
";
    let output = "\
functy.0 = (u32) -> (u32)

fn @g(functy.0) {
bb0(%0: u32):
    ret %0
}

fn @f(functy.0) {
bb0(%0: u32):
    %1 = call @func.0(%0)
    %2 = const u32 0
    ret %1
}
";
    assert_eq!(
        class(&run(input, output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}

const DIV_IN: &str = "\
functy.0 = (u32, u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: u32):
    %2 = const u32 0
    %3 = icmp ne u32 %1, %2
    condbr %3, bb1, bb2
bb1:
    %4 = udiv u32 %0, %1
    ret %4
bb2:
    ret %2
}
";

#[test]
fn division_hoisted_above_its_guard() {
    let reg = registry();
    let output = "\
functy.0 = (u32, u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: u32):
    %2 = const u32 0
    %3 = icmp ne u32 %1, %2
    %4 = udiv u32 %0, %1
    condbr %3, bb1, bb2
bb1:
    ret %4
bb2:
    ret %2
}
";
    assert_eq!(
        class(&run(DIV_IN, output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}

#[test]
fn graph_instruction_hoisted_out_of_a_branch_is_accepted() {
    let reg = registry();
    let input = "\
functy.0 = (u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: bool):
    %2 = const u32 0
    %3 = xor u32 %0, %2
    condbr %1, bb1, bb2
bb1:
    %4 = mul u32 %3, %3
    ret %4
bb2:
    ret %3
}
";
    let output = "\
functy.0 = (u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: bool):
    %2 = const u32 0
    %3 = xor u32 %0, %2
    %4 = mul u32 %3, %3
    condbr %1, bb1, bb2
bb1:
    ret %4
bb2:
    ret %3
}
";
    let v = run(input, output, &header(), &reg).expect("accepted");
    assert_eq!(v.changed_operands, 0);
}

#[test]
fn merged_equal_graph_instructions_are_accepted() {
    let reg = registry();
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = mul u32 %2, %2
    %4 = mul u32 %2, %2
    %5 = copy u32 %4
    %6 = sub u32 %3, %5
    ret %6
}
";
    let output = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = mul u32 %2, %2
    %6 = sub u32 %3, %3
    ret %6
}
";
    assert!(run(input, output, &header(), &reg).is_ok());
}

#[test]
fn changed_function_attribute() {
    let reg = registry();
    let output = A_IN.replace(
        "fn @f(functy.0) {\n",
        "fn @f(functy.0) {\n    ; #attrs: inlinehint\n",
    );
    let r = run(A_IN, &output, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(trust_cg_eqsat_check::Rejection::FunctionFieldMismatch { field: "attrs" })
        ),
        "{r:?}"
    );
}

#[test]
fn changed_block_parameters() {
    let reg = registry();
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    br bb1(%0)
bb1(%1: u32):
    ret %1
}
";
    let output = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    br bb1(%0, %0)
bb1(%1: u32, %2: u32):
    ret %1
}
";
    assert_eq!(
        class(&run(input, output, &header(), &reg)),
        "block_shape_mismatch"
    );
}

#[test]
fn proof_annotated_function_is_ineligible() {
    let reg = registry();
    let input = A_IN.replace(
        "fn @f(functy.0) {\n",
        "fn @f(functy.0) {\n    ; #proof: terminates\n",
    );
    let r = run(&input, &input, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(Rejection::Ineligible {
                class: "function_proofs",
                ..
            })
        ),
        "{r:?}"
    );
    let input = A_IN.replace(
        "%2 = xor u32 %0, %1\n",
        "%2 = xor u32 %0, %1  ; #proof: pure\n",
    );
    assert_ne!(input, A_IN);
    let r = run(&input, &input, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(Rejection::Ineligible {
                class: "instruction_proofs",
                ..
            })
        ),
        "{r:?}"
    );
}

#[test]
fn unreachable_block_is_ineligible() {
    let reg = registry();
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    ret %0
bb1:
    ret %0
}
";
    let r = run(input, input, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(trust_cg_eqsat_check::Rejection::Ineligible {
                class: "unreachable_block",
                ..
            })
        ),
        "{r:?}"
    );
}

#[test]
fn use_not_dominated_by_its_definition() {
    let reg = registry();
    let input = "\
functy.0 = (u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: bool):
    %2 = const u32 0
    %3 = xor u32 %0, %2
    condbr %1, bb1, bb2
bb1:
    %4 = mul u32 %3, %3
    br bb3
bb2:
    br bb3
bb3:
    ret %3
}
";
    // The output sinks the graph mul into bb1 and uses it in bb3, which bb1
    // does not dominate.
    let output = input.replace("    ret %3\n", "    ret %4\n");
    let r = run(input, &output, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(trust_cg_eqsat_check::Rejection::NotDominated {
                body: trust_cg_eqsat_check::Body::Output,
                ..
            })
        ),
        "{r:?}"
    );
    // A use before its definition in the same block.
    let output = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %4 = mul u32 %2, %3
    %3 = const u32 1
    ret %4
}
";
    assert_eq!(class(&run(A_IN, output, &header(), &reg)), "not_dominated");
}

const INVOKE_IN: &str = "\
functy.0 = () -> (i64)

fn @g(functy.0) {
bb0:
    %0 = const i64 7
    ret %0
}

fn @f(functy.0) {
bb0:
    %0 = const functy.0 fndef<func.0>
    %1 = invoke_indirect %0(functy.0)() to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
}
";

#[test]
fn invoke_result_is_defined_only_on_its_normal_edge() {
    let reg = registry();
    assert!(run(INVOKE_IN, INVOKE_IN, &header(), &reg).is_ok());
    // The unwind block may not read the invoke's result.
    let output = INVOKE_IN.replace("    ret %4\n", "    ret %1\n");
    let r = run(INVOKE_IN, &output, &header(), &reg);
    assert_eq!(class(&r), "not_dominated", "{r:?}");
}

// ---------------------------------------------------------------- landing pads

/// `@f` catches `@boom`'s panic in bb2 and returns -1.
const PAD_IN: &str = "\
functy.0 = () -> (i64)

fn @boom(functy.0) {
bb0:
    %0 = const bool false
    assert %0, div_by_zero
    %1 = const i64 0
    ret %1
}

fn @f(functy.0) {
bb0:
    %1 = invoke @func.0() to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
}
";

/// The graph constant %4 heads the landing-pad block: every skeleton
/// instruction, operand term and dominance fact is that of `PAD_IN`.
const PAD_OUT: &str = "\
functy.0 = () -> (i64)

fn @boom(functy.0) {
bb0:
    %0 = const bool false
    assert %0, div_by_zero
    %1 = const i64 0
    ret %1
}

fn @f(functy.0) {
bb0:
    %1 = invoke @func.0() to bb1() unwind bb2
bb1:
    ret %1
bb2:
    %4 = const i64 -1
    %2, %3 = landingpad catch 0
    ret %4
}
";

#[test]
fn graph_instruction_before_a_landingpad_is_refused() {
    let reg = registry();
    let (module, input) = parse(PAD_IN);
    let (_, output) = parse(PAD_OUT);
    // The interpreter's evidence: the input catches the panic and returns
    // -1; the output cannot unwind into bb2.
    assert_eq!(
        outcome(&module, &input, &[], PanicStrategy::Unwind),
        returns_i64(-1)
    );
    let out = outcome(&module, &output, &[], PanicStrategy::Unwind);
    assert!(
        matches!(&out, Err(e) if e.starts_with("MalformedInstruction")),
        "{out:?}"
    );

    assert!(run(PAD_IN, PAD_IN, &header(), &reg).is_ok());
    let r = run(PAD_IN, PAD_OUT, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(Rejection::MalformedBody {
                body: Body::Output,
                block: Some(2),
                inst: Some(1),
                ..
            })
        ),
        "{r:?}"
    );
    // An input with the same shape is refused too.
    let r = run(PAD_OUT, PAD_OUT, &header(), &reg);
    assert!(
        matches!(
            r,
            Err(Rejection::MalformedBody {
                body: Body::Input,
                ..
            })
        ),
        "{r:?}"
    );
}

/// The landing-pad block re-raises through a copy of a value.
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
fn resume_of_a_literal_or_a_selector_is_refused() {
    let reg = registry();
    // Through a copy, each input is what trust-ir-build admits; removing the
    // copy keeps every term but makes the operand a literal or the pad's
    // selector, which rule (c) of `validate_unwind_structure` refuses.
    for (input_tail, output_tail) in [
        (
            "    %5 = const i32 0\n    %6 = copy i32 %5\n    resume %6\n",
            "    %5 = const i32 0\n    resume %5\n",
        ),
        ("    %6 = copy i32 %3\n    resume %6\n", "    resume %3\n"),
    ] {
        let (input, output) = (resume_body(input_tail), resume_body(output_tail));
        assert!(run(&input, &input, &header(), &reg).is_ok(), "{input_tail}");
        let r = run(&input, &output, &header(), &reg);
        assert!(
            matches!(
                r,
                Err(Rejection::MalformedBody {
                    body: Body::Output,
                    block: Some(2),
                    ..
                })
            ),
            "{output_tail}: {r:?}"
        );
    }
    // The exception object itself is admitted.
    let ok = resume_body("    resume %2\n");
    assert!(run(&ok, &ok, &header(), &reg).is_ok());
    // A resume in a function with no landingpad.
    let input = "\
functy.0 = (ptr) -> ()

fn @f(functy.0) {
bb0(%0: ptr):
    resume %0
}
";
    assert_eq!(class(&run(input, input, &header(), &reg)), "malformed_body");
}

// ------------------------------------------- availability of invoke results

/// Section 4: an invoke's result is available in its own normal-edge
/// arguments.
const INVOKE_OWN_ARG: &str = "\
functy.0 = () -> (i64)

fn @seven(functy.0) {
bb0:
    %0 = const i64 7
    ret %0
}

fn @f(functy.0) {
bb0:
    %0 = invoke @func.0() to bb1(%0) unwind bb2
bb1(%1: i64):
    ret %1
bb2:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
}
";

/// The normal successor bb1 is a loop header; its only other incoming edge
/// is its own back edge, so the normal edge dominates it.
const INVOKE_LOOP_HEADER: &str = "\
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
    condbr %9, bb1, bb2
bb2:
    ret %0
bb3:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
}
";

#[test]
fn invoke_result_in_its_own_normal_edge_arguments_is_available() {
    let reg = registry();
    let (module, f) = parse(INVOKE_OWN_ARG);
    assert_eq!(
        outcome(&module, &f, &[], PanicStrategy::Unwind),
        returns_i64(7)
    );
    let v = run(INVOKE_OWN_ARG, INVOKE_OWN_ARG, &header(), &reg).expect("identity accepted");
    assert_eq!(v.changed_operands, 0);
}

#[test]
fn invoke_result_under_a_loop_header_normal_successor_is_available() {
    let reg = registry();
    let (module, f) = parse(INVOKE_LOOP_HEADER);
    assert_eq!(
        outcome(
            &module,
            &f,
            &[InterpretValue::bool(false)],
            PanicStrategy::Unwind
        ),
        returns_i64(7)
    );
    let v =
        run(INVOKE_LOOP_HEADER, INVOKE_LOOP_HEADER, &header(), &reg).expect("identity accepted");
    assert_eq!(v.changed_operands, 0);
}

fn not_dominated(r: &Result<trust_cg_eqsat_check::Verdict, Rejection>) -> &str {
    match r {
        Err(Rejection::NotDominated {
            body: Body::Input,
            detail,
            ..
        }) => detail,
        other => panic!("expected an input NotDominated refusal, got {other:?}"),
    }
}

#[test]
fn invoke_result_outside_its_normal_edge_is_not_available() {
    let reg = registry();
    // `f_body` is the whole body of `@f(functy.1)`; `@func.0` returns 7.
    let identity = |f_body: &str| {
        let text = format!(
            "\
functy.0 = () -> (i64)
functy.1 = (bool) -> (i64)

fn @seven(functy.0) {{
bb0:
    %0 = const i64 7
    ret %0
}}

fn @f(functy.1) {{
{f_body}}}
"
        );
        run(&text, &text, &header(), &reg)
    };

    // Used in the unwind successor.
    let r = identity(
        "bb0(%9: bool):
    %0 = invoke @func.0() to bb1() unwind bb2
bb1:
    ret %0
bb2:
    %2, %3 = landingpad catch 0
    ret %0
",
    );
    assert!(
        not_dominated(&r).contains("its normal successor does not dominate"),
        "{r:?}"
    );

    // Used in a block the invoking block dominates but the normal successor
    // does not (the join of the normal and unwind paths).
    let r = identity(
        "bb0(%9: bool):
    %0 = invoke @func.0() to bb1() unwind bb2
bb1:
    br bb3
bb2:
    %2, %3 = landingpad cleanup
    br bb3
bb3:
    ret %0
",
    );
    assert!(
        not_dominated(&r).contains("its normal successor does not dominate"),
        "{r:?}"
    );

    // The normal successor has another incoming edge, from a block it does
    // not dominate.
    let r = identity(
        "bb0(%9: bool):
    condbr %9, bb4, bb5
bb4:
    %0 = invoke @func.0() to bb1() unwind bb3
bb5:
    br bb1
bb1:
    ret %0
bb3:
    %2, %3 = landingpad catch 0
    %4 = const i64 -1
    ret %4
",
    );
    assert!(
        not_dominated(&r).contains("normal edge does not dominate"),
        "{r:?}"
    );

    // Normal and unwind destination are the same block: the unwind edge is
    // a second incoming edge from a block the successor does not dominate.
    let r = identity(
        "bb0(%9: bool):
    %0 = invoke @func.0() to bb1() unwind bb1
bb1:
    %2, %3 = landingpad catch 0
    ret %0
",
    );
    assert!(
        not_dominated(&r).contains("normal edge does not dominate"),
        "{r:?}"
    );

    // Used as its own call argument (before the call).
    let text = "\
functy.0 = (i64) -> (i64)

fn @id(functy.0) {
bb0(%0: i64):
    ret %0
}

fn @f(functy.0) {
bb0(%9: i64):
    %0 = invoke @func.0(%0) to bb1(%0) unwind bb2
bb1(%1: i64):
    ret %1
bb2:
    %2, %3 = landingpad catch 0
    ret %9
}
";
    let r = run(text, text, &header(), &reg);
    assert!(
        not_dominated(&r).contains("outside its normal-edge arguments"),
        "{r:?}"
    );
}
