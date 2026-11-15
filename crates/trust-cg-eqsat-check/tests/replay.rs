// trust-cg-eqsat-check/tests/replay.rs - proof replay against the registry and the input body's leaves
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Correct proofs are accepted (a rule step, a transitive chain, a
//! congruence, a forward `refines` step, a side condition that holds, an
//! `eval` fold); each replay fault of docs/eqsat-tier-e.md sections 7.1 and 8
//! item 5 is rejected with its class.

mod common;

use common::*;
use trust_cg_eqsat_check::Rejection;

#[test]
fn mul_one_rule_step_is_accepted() {
    let reg = registry();
    let v = run(A_IN, A_OUT, &a_deriv(&reg), &reg).expect("accepted");
    assert_eq!(v.changed_operands, 1);
}

#[test]
fn wrong_digest() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.rules[0].1[0] ^= 1;
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "digest_mismatch");
}

#[test]
fn unknown_rule() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.rules[0].0 = "mul_two".to_owned();
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "unknown_rule");
}

#[test]
fn type_outside_domain() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.proofs = vec![rule(0, U64, &[("x", 0)], &[])];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "type_not_in_domain");
}

#[test]
fn missing_binding() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.terms = Vec::new();
    d.proofs = vec![rule(0, U32, &[], &[])];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "binding_mismatch");
}

#[test]
fn extra_binding() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.proofs = vec![rule(0, U32, &[("x", 0), ("y", 0)], &[])];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "binding_mismatch");
}

#[test]
fn wrong_sort() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.terms = vec![T::Const(BOOL, 1)];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "binding_mismatch");
}

#[test]
fn constant_variable_bound_to_a_leaf() {
    // rotl_full's ?c is a constant variable: binding it to a leaf is refused.
    let reg = registry();
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = rotl u32 %2, %2
    ret %3
}
";
    let output = A_OUT;
    let mut d = Deriv::header("f").with_rule(&reg, "rotl_full");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![rule(0, U32, &[("c", 0), ("x", 0)], &[0])];
    d.claims = vec![0];
    assert_eq!(class(&run(input, output, &d, &reg)), "binding_mismatch");
}

const ROTL_IN: &str = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = const u32 AMOUNT
    %4 = rotl u32 %2, %3
    ret %4
}
";

fn rotl_case(amount: u128, premises: &[u32]) -> Result<trust_cg_eqsat_check::Verdict, Rejection> {
    let reg = registry();
    let input = ROTL_IN.replace("AMOUNT", &amount.to_string());
    let mut d = Deriv::header("f").with_rule(&reg, "rotl_full");
    d.terms = vec![T::Const(U32, amount), T::Result(0, 0, 0)];
    d.proofs = vec![rule(0, U32, &[("c", 0), ("x", 1)], premises)];
    d.claims = vec![0];
    run(&input, A_OUT, &d, &reg)
}

#[test]
fn side_condition_holds() {
    assert!(rotl_case(64, &[0]).is_ok(), "{:?}", rotl_case(64, &[0]));
    assert!(rotl_case(0, &[0]).is_ok());
}

#[test]
fn side_condition_fails() {
    assert_eq!(class(&rotl_case(3, &[0])), "side_condition_failed");
}

#[test]
fn premises_must_be_exactly_the_conditions() {
    assert_eq!(class(&rotl_case(32, &[])), "premise_mismatch");
    assert_eq!(class(&rotl_case(32, &[0, 0])), "premise_mismatch");
    assert_eq!(class(&rotl_case(32, &[1])), "premise_mismatch");
}

#[test]
fn eval_fold_is_replayed() {
    let reg = registry();
    let input = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 4294967295
    %2 = const u32 2
    %3 = add u32 %1, %2
    ret %3
}
";
    let output = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 1
    ret %1
}
";
    let mut d = Deriv::header("f").with_rule(&reg, "fold_add");
    d.terms = vec![T::Const(U32, 0xffff_ffff), T::Const(U32, 2)];
    d.proofs = vec![rule(0, U32, &[("a", 0), ("b", 1)], &[])];
    d.claims = vec![0];
    assert!(run(input, output, &d, &reg).is_ok());
    // A wrong fold result in the output is not what the rule concludes.
    let wrong = output.replace("const u32 1", "const u32 2");
    assert_eq!(class(&run(input, &wrong, &d, &reg)), "conclusion_mismatch");
}

#[test]
fn conclusion_not_matching_the_registered_rule() {
    // The output returns (const 0), but mul_one concludes R.
    let reg = registry();
    let output = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    ret %1
}
";
    assert_eq!(
        class(&run(A_IN, output, &a_deriv(&reg), &reg)),
        "conclusion_mismatch"
    );
}

const ZERO_IN: &str = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = mul u32 %2, %1
    ret %3
}
";

const ZERO_OUT: &str = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    ret %1
}
";

#[test]
fn refines_forward_is_accepted() {
    let reg = registry();
    let mut d = Deriv::header("f").with_rule(&reg, "mul_zero");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[])];
    d.claims = vec![0];
    assert!(run(ZERO_IN, ZERO_OUT, &d, &reg).is_ok());
}

#[test]
fn refines_backward_is_rejected() {
    // Output (mul R 0) where the input had (const 0): the refines claim
    // concludes the other direction only.
    let reg = registry();
    let mut d = Deriv::header("f").with_rule(&reg, "mul_zero");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[])];
    d.claims = vec![0];
    assert_eq!(
        class(&run(ZERO_OUT, ZERO_IN, &d, &reg)),
        "operand_unjustified"
    );
}

#[test]
fn sym_of_refines() {
    let reg = registry();
    let mut d = Deriv::header("f").with_rule(&reg, "mul_zero");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[]), P::Sym(0)];
    d.claims = vec![1];
    assert_eq!(class(&run(ZERO_OUT, ZERO_IN, &d, &reg)), "sym_of_refines");
}

#[test]
fn sym_of_equiv_is_accepted() {
    // R to (mul R 1): the reverse of mul_one, by Sym.
    let reg = registry();
    let mut d = Deriv::header("f").with_rule(&reg, "mul_one");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![rule(0, U32, &[("x", 0)], &[]), P::Sym(0)];
    d.claims = vec![1];
    assert!(run(A_OUT, A_IN, &d, &reg).is_ok());
}

#[test]
fn trans_middle_mismatch() {
    let reg = registry();
    let mut d = b_deriv(&reg);
    d.proofs[2] = P::Trans(1, 0);
    assert_eq!(class(&run(B_IN, B_OUT, &d, &reg)), "trans_middle_mismatch");
}

const CONGR_IN: &str = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %3 = const u32 1
    %4 = mul u32 %2, %3
    %5 = add u32 %4, %2
    ret %5
}
";

const CONGR_OUT: &str = "\
functy.0 = (u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = xor u32 %0, %1
    %5 = add u32 %2, %2
    ret %5
}
";

#[test]
fn congruence_is_accepted() {
    let reg = registry();
    let mut d = Deriv::header("f").with_rule(&reg, "mul_one");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![
        rule(0, U32, &[("x", 0)], &[]),
        P::Refl(0),
        P::Congr(OpD::Bin(ADD, U32), vec![0, 1]),
    ];
    d.claims = vec![2];
    let v = run(CONGR_IN, CONGR_OUT, &d, &reg).expect("accepted");
    assert_eq!(v.proof_steps, 3);
}

#[test]
fn congruence_with_mismatched_children() {
    let reg = registry();
    let mut d = Deriv::header("f").with_rule(&reg, "mul_one");
    d.terms = vec![T::Result(0, 0, 0)];
    d.proofs = vec![
        rule(0, U32, &[("x", 0)], &[]),
        P::Refl(0),
        P::Congr(OpD::Bin(ADD, U64), vec![0, 1]),
    ];
    d.claims = vec![2];
    assert_eq!(class(&run(CONGR_IN, CONGR_OUT, &d, &reg)), "congr_mismatch");
}

#[test]
fn maybe_poison_leaf_bound_to_a_variable() {
    // Param(bb0, 0) is a function argument: it may be poison.
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.terms = vec![T::Param(0, 0)];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "maybe_poison_leaf");
}

#[test]
fn maybe_poison_leaf_under_an_operator() {
    let reg = registry();
    let mut d = Deriv::header("f");
    d.terms = vec![
        T::Param(0, 0),
        T::Const(U32, 1),
        T::Op(OpD::Bin(MUL, U32), vec![0, 1]),
    ];
    d.proofs = vec![P::Refl(2)];
    d.claims = vec![0];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "maybe_poison_leaf");
}

#[test]
fn maybe_poison_leaf_under_congruence() {
    let reg = registry();
    let mut d = Deriv::header("f");
    d.terms = vec![T::Param(0, 0), T::Const(U32, 1)];
    d.proofs = vec![
        P::Refl(0),
        P::Refl(1),
        P::Congr(OpD::Bin(MUL, U32), vec![0, 1]),
    ];
    d.claims = vec![2];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "maybe_poison_leaf");
}

#[test]
fn leaf_not_in_the_input() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.terms = vec![T::Result(0, 9, 0)];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "unknown_leaf");
    d.terms = vec![T::Param(7, 0)];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "unknown_leaf");
}

#[test]
fn ill_typed_terms() {
    let reg = registry();
    // add u32 over a u32 and a bool.
    let mut d = Deriv::header("f");
    d.terms = vec![
        T::Result(0, 0, 0),
        T::Const(BOOL, 1),
        T::Op(OpD::Bin(ADD, U32), vec![0, 1]),
    ];
    d.proofs = vec![P::Refl(2)];
    d.claims = vec![0];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "ill_typed_term");
    // A residue that does not fit its type.
    let mut d = Deriv::header("f");
    d.terms = vec![T::Const(U8, 300)];
    d.proofs = vec![P::Refl(0)];
    d.claims = vec![0];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "ill_typed_term");
    // add at bool is not admitted.
    let mut d = Deriv::header("f");
    d.terms = vec![T::Const(BOOL, 1), T::Op(OpD::Bin(ADD, BOOL), vec![0, 0])];
    d.proofs = vec![P::Refl(1)];
    d.claims = vec![0];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "ill_typed_term");
}

#[test]
fn claim_justifying_nothing() {
    let reg = registry();
    let mut d = a_deriv(&reg);
    d.proofs.push(P::Refl(0));
    d.claims = vec![0, 1];
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "claim_mismatch");
}

#[test]
fn missing_claim() {
    let reg = registry();
    let d = Deriv::header("f");
    assert_eq!(class(&run(A_IN, A_OUT, &d, &reg)), "operand_unjustified");
}

#[test]
fn registry_with_a_different_statement_under_the_same_name() {
    // The derivation carries the digest of the test registry's mul_one; a
    // registry whose mul_one states something else refuses it.
    let reg = registry();
    let other = trust_cg_eqsat_check::Registry::parse(
        "(rule mul_one (direction equiv) (domain u32) (lhs (mul ?x (const 1))) (rhs ?x) (where))",
    )
    .expect("parses");
    assert_eq!(
        class(&run(A_IN, A_OUT, &a_deriv(&reg), &other)),
        "digest_mismatch"
    );
}
