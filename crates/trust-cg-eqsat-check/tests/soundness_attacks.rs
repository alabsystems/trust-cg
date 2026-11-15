// trust-cg-eqsat-check/tests/soundness_attacks.rs - unjustified outputs the checker refuses
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Attacks on section 8 that keep the derivation empty and change the body
//! in a way the skeleton comparison, the classification of section 2 or the
//! operand terms must catch. Each is refused, with the reason named.

mod common;

use common::{Deriv, class, run};

fn header() -> Deriv {
    Deriv::header("f")
}

/// Swapping the block arguments of a switch case (same types, different
/// values): the operand terms of the terminator differ.
#[test]
fn switch_case_arguments_swapped() {
    let input = "\
functy.0 = (u32, u32) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: u32):
    switch %0 [ 1: bb1(%1) default: bb1(%0) ]
bb1(%2: u32):
    ret %2
}
";
    let output = input.replace("[ 1: bb1(%1)", "[ 1: bb1(%0)");
    assert_ne!(output, input);
    let reg = common::registry();
    assert_eq!(
        class(&run(input, &output, &header(), &reg)),
        "operand_unjustified"
    );
}

/// A frontier instruction (it inspects a maybe-poison parameter) is skeleton:
/// hoisting it out of its branch changes both blocks' skeletons.
#[test]
fn frontier_instruction_hoisted_out_of_a_branch() {
    let input = "\
functy.0 = (u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: bool):
    condbr %1, bb1, bb2
bb1:
    %2 = const u32 1
    %3 = add u32 %0, %2
    ret %3
bb2:
    %4 = const u32 0
    ret %4
}
";
    let output = "\
functy.0 = (u32, bool) -> (u32)

fn @f(functy.0) {
bb0(%0: u32, %1: bool):
    %2 = const u32 1
    %3 = add u32 %0, %2
    condbr %1, bb1, bb2
bb1:
    ret %3
bb2:
    %4 = const u32 0
    ret %4
}
";
    let reg = common::registry();
    assert_eq!(
        class(&run(input, output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}

/// An ordered comparison at Bool is not a graph operator (section 2.2): it
/// stays skeleton, so an output that replaces it by a constant is refused.
#[test]
fn bool_ordered_icmp_replaced_by_a_constant() {
    let input = "\
functy.0 = (u32) -> (bool)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = icmp eq u32 %0, %1
    %3 = icmp slt bool %2, %2
    ret %3
}
";
    let output = "\
functy.0 = (u32) -> (bool)

fn @f(functy.0) {
bb0(%0: u32):
    %1 = const u32 0
    %2 = icmp eq u32 %0, %1
    %3 = const bool false
    ret %3
}
";
    let reg = common::registry();
    assert_eq!(
        class(&run(input, output, &header(), &reg)),
        "skeleton_count_mismatch"
    );
}
