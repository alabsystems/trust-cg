// trust-cg-verify/trust_ir_mid_tv_tests.rs - tests of the mid-end checkers
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Each checker accepts the rewrite its pass is allowed to make and refuses a
//! named wrong one (the negative controls): a type-changing or misrouted copy
//! forward, an effectful or still-used or mislabelled removal, a branch folded
//! to the edge its constant does not select, a reachable block removed, a GEP
//! rewrite past its allocation, and a target that is not the claimed rewrite.
//! The differential leg catches a wrong function and excludes undefined
//! inputs.

use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"mid\"\n\
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

// ---------------------------------------------------------------------------
// Copy propagation
// ---------------------------------------------------------------------------

const COPIES: &str = "functy.0 = (i32, i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = copy i32 %0\n\
    \x20   %3 = copy i32 %2\n\
    \x20   %4 = copy u32 %1\n\
    \x20   %5 = add i32 %3, %1\n\
    \x20   ret %5\n\
    }\n";

const COPIES_FORWARDED: &str = "functy.0 = (i32, i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %4 = copy u32 %1\n\
    \x20   %5 = add i32 %0, %1\n\
    \x20   ret %5\n\
    }\n";

fn forwards(pairs: &[(u32, u32)]) -> PassWitness {
    PassWitness::CopyProp(CopyPropWitness {
        forwards: pairs
            .iter()
            .map(|&(copy, root)| CopyForward {
                copy: v(copy),
                root: v(root),
            })
            .collect(),
    })
}

#[test]
fn copy_forwarding_to_the_root_is_accepted() {
    let src = module(COPIES);
    let tgt = module(COPIES_FORWARDED);
    let verdict = check_pass(
        &src,
        32,
        func(&src, "f"),
        func(&tgt, "f"),
        &forwards(&[(2, 0), (3, 0)]),
    )
    .expect("a type-preserving copy chain forwards to its root");
    assert_eq!(verdict.exact, 2);
    assert_eq!(verdict.refinements, 0);
}

#[test]
fn negative_control_wrong_copy_root_is_refused() {
    let src = module(COPIES);
    let tgt = module(COPIES_FORWARDED);
    let err = check_pass(
        &src,
        32,
        func(&src, "f"),
        func(&tgt, "f"),
        &forwards(&[(2, 1), (3, 1)]),
    )
    .unwrap_err();
    assert!(matches!(err, MidTvError::WrongRoot { .. }), "{err}");
}

#[test]
fn negative_control_type_changing_copy_is_refused() {
    let src = module(COPIES);
    let mut tgt = func(&src, "f").clone();
    tgt.blocks[0].body.remove(2);
    let err = check_pass(&src, 32, func(&src, "f"), &tgt, &forwards(&[(4, 1)])).unwrap_err();
    assert!(matches!(err, MidTvError::TypeChange { .. }), "{err}");
}

#[test]
fn negative_control_target_beyond_the_witness_is_refused() {
    let src = module(COPIES);
    let tgt = module(COPIES_FORWARDED);
    // The target forwards %3 too, but the witness names only %2.
    let err = check_pass(
        &src,
        32,
        func(&src, "f"),
        func(&tgt, "f"),
        &forwards(&[(2, 0)]),
    )
    .unwrap_err();
    assert!(matches!(err, MidTvError::TargetDiffers { .. }), "{err}");
}

// ---------------------------------------------------------------------------
// Pure dead-code elimination
// ---------------------------------------------------------------------------

const DEAD: &str = "functy.0 = (i32, i32, ptr) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32, %2: ptr):\n\
    \x20   %3 = const i32 7\n\
    \x20   %4 = mul i32 %0, %1\n\
    \x20   store i32 %0, ptr %2\n\
    \x20   %5 = add i32 %0, %1\n\
    \x20   ret %5\n\
    }\n";

fn removal(block: u32, index: usize, result: Option<u32>, class: RemovalClass) -> DeadRemoval {
    DeadRemoval {
        block: b(block),
        index,
        results: result.map(v).into_iter().collect(),
        class,
    }
}

fn without(func: &Function, indices: &[usize]) -> Function {
    let mut out = func.clone();
    let mut index = 0usize;
    out.blocks[0].body.retain(|_| {
        let keep = !indices.contains(&index);
        index += 1;
        keep
    });
    out
}

#[test]
fn dead_pure_removals_are_accepted_and_labelled() {
    let src = module(DEAD);
    let f = func(&src, "f");
    let tgt = without(f, &[0, 1]);
    let witness = PassWitness::Dce(DceWitness {
        removals: vec![
            removal(0, 0, Some(3), RemovalClass::Exact),
            removal(0, 1, Some(4), RemovalClass::Refinement),
        ],
    });
    let verdict = check_pass(&src, 32, f, &tgt, &witness).expect("dead pure removals");
    assert_eq!(verdict.exact, 1);
    assert_eq!(
        verdict.refinements, 1,
        "a dead multiply may inspect poison: its removal is a refinement"
    );
}

#[test]
fn negative_control_dce_of_an_effectful_op_is_refused() {
    let src = module(DEAD);
    let f = func(&src, "f");
    let tgt = without(f, &[2]);
    let witness = PassWitness::Dce(DceWitness {
        removals: vec![removal(0, 2, None, RemovalClass::Exact)],
    });
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::Effectful { .. }), "{err}");
}

#[test]
fn negative_control_dce_of_a_used_value_is_refused() {
    let src = module(DEAD);
    let f = func(&src, "f");
    let tgt = without(f, &[3]);
    let witness = PassWitness::Dce(DceWitness {
        removals: vec![removal(0, 3, Some(5), RemovalClass::Refinement)],
    });
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::RemovedValueUsed { .. }), "{err}");
}

#[test]
fn negative_control_a_refinement_labelled_exact_is_refused() {
    let src = module(DEAD);
    let f = func(&src, "f");
    let tgt = without(f, &[1]);
    let witness = PassWitness::Dce(DceWitness {
        removals: vec![removal(0, 1, Some(4), RemovalClass::Exact)],
    });
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::WrongClass { .. }), "{err}");
}

/// A dead allocation counted by a positive constant goes (a refinement: an
/// allocation may exhaust the address space); one counted by a value whose
/// sign the source checks (a count below 1 is undefined behaviour) stays
/// unless that value is a positive constant.
#[test]
fn a_dead_constant_count_allocation_is_removed_and_a_variable_one_stays() {
    let text = "functy.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = const i32 2\n\
        \x20   %2 = alloca i64, %1\n\
        \x20   %3 = alloca i64, %0\n\
        \x20   %4 = const i32 0\n\
        \x20   %5 = alloca i64, %4\n\
        \x20   ret %0\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let witness = PassWitness::Dce(DceWitness {
        removals: vec![removal(0, 1, Some(2), RemovalClass::Refinement)],
    });
    check_pass(&src, 32, f, &without(f, &[1]), &witness).expect("a positive constant count");
    for (index, result) in [(2, 3), (4, 5)] {
        let witness = PassWitness::Dce(DceWitness {
            removals: vec![removal(0, index, Some(result), RemovalClass::Refinement)],
        });
        let err = check_pass(&src, 32, f, &without(f, &[index]), &witness).unwrap_err();
        assert!(
            matches!(err, MidTvError::Effectful { .. }),
            "%{result}: {err}"
        );
    }
}

// ---------------------------------------------------------------------------
// Constant-branch folding
// ---------------------------------------------------------------------------

const BRANCH: &str = "functy.0 = (i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = const bool false\n\
    \x20   condbr %1, bb1, bb2(%0)\n\
    bb1:\n\
    \x20   %2 = const i32 1\n\
    \x20   ret %2\n\
    bb2(%3: i32):\n\
    \x20   ret %3\n\
    }\n";

fn folded(src: &Function, target: u32, remove: &[u32]) -> Function {
    let mut out = src.clone();
    let last = out.blocks[0].body.last_mut().unwrap();
    let Inst::CondBr {
        then_target,
        then_args,
        else_target,
        else_args,
        ..
    } = last.inst.clone()
    else {
        panic!("condbr expected");
    };
    last.inst = if then_target == b(target) {
        Inst::Br {
            target: then_target,
            args: then_args,
        }
    } else {
        Inst::Br {
            target: else_target,
            args: else_args,
        }
    };
    out.blocks.retain(|blk| !remove.contains(&blk.id.index()));
    out
}

#[test]
fn constant_branch_fold_and_unreachable_removal_are_accepted() {
    let src = module(BRANCH);
    let f = func(&src, "f");
    let tgt = folded(f, 2, &[1]);
    let witness = PassWitness::BranchFold(BranchFoldWitness {
        folds: vec![BranchFold {
            block: b(0),
            target: b(2),
        }],
        removed_blocks: vec![b(1)],
    });
    check_pass(&src, 32, f, &tgt, &witness).expect("false selects the else edge");
}

#[test]
fn negative_control_mis_folded_branch_is_refused() {
    let src = module(BRANCH);
    let f = func(&src, "f");
    let tgt = folded(f, 1, &[2]);
    let witness = PassWitness::BranchFold(BranchFoldWitness {
        folds: vec![BranchFold {
            block: b(0),
            target: b(1),
        }],
        removed_blocks: vec![b(2)],
    });
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::WrongTarget { .. }), "{err}");
}

#[test]
fn negative_control_reachable_block_removal_is_refused() {
    let src = module(BRANCH);
    let f = func(&src, "f");
    let mut tgt = f.clone();
    tgt.blocks.retain(|blk| blk.id != b(2));
    let witness = PassWitness::BranchFold(BranchFoldWitness {
        folds: vec![],
        removed_blocks: vec![b(2)],
    });
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(
        matches!(err, MidTvError::ReachableBlockRemoved { .. }),
        "{err}"
    );
}

const SWITCH: &str = "functy.0 = (i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = const i32 3\n\
    \x20   switch %1 [ 1: bb1 3: bb2 default: bb3 ]\n\
    bb1:\n\
    \x20   ret %0\n\
    bb2:\n\
    \x20   %2 = const i32 9\n\
    \x20   ret %2\n\
    bb3:\n\
    \x20   ret %1\n\
    }\n";

#[test]
fn switch_on_a_constant_folds_to_its_case() {
    let src = module(SWITCH);
    let f = func(&src, "f");
    let mut tgt = f.clone();
    tgt.blocks[0].body.last_mut().unwrap().inst = Inst::Br {
        target: b(2),
        args: vec![],
    };
    tgt.blocks.retain(|blk| blk.id == b(0) || blk.id == b(2));
    let witness = PassWitness::BranchFold(BranchFoldWitness {
        folds: vec![BranchFold {
            block: b(0),
            target: b(2),
        }],
        removed_blocks: vec![b(1), b(3)],
    });
    check_pass(&src, 32, f, &tgt, &witness).expect("3 selects case 3");
    let wrong = PassWitness::BranchFold(BranchFoldWitness {
        folds: vec![BranchFold {
            block: b(0),
            target: b(3),
        }],
        removed_blocks: vec![b(1), b(3)],
    });
    assert!(check_pass(&src, 32, f, &tgt, &wrong).is_err());
}

// ---------------------------------------------------------------------------
// Pointer chain -> byte-offset GEP
// ---------------------------------------------------------------------------

fn chain(offset: i64) -> String {
    format!(
        "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: i32):\n\
         \x20   %1 = alloca [ty.0 x 2], align 4\n\
         \x20   %2 = ptrtoint ptr %1 to i32\n\
         \x20   %3 = const i32 {offset}\n\
         \x20   %4 = add i32 %2, %3\n\
         \x20   %5 = inttoptr i32 %4 to ptr\n\
         \x20   store i32 %0, ptr %5\n\
         \x20   %6 = load i32, ptr %5\n\
         \x20   ret %6\n\
         }}\n"
    )
}

fn gep_rewrite(offset: u64) -> PassWitness {
    PassWitness::PtrGep(PtrGepWitness {
        rewrites: vec![GepRewrite {
            block: b(0),
            index: 4,
            result: v(5),
            base: v(1),
            offset,
            offset_value: v(3),
            folded: None,
        }],
    })
}

fn gep_target(src: &Function, offset: u64) -> Function {
    let mut out = src.clone();
    out.blocks[0].body[4].inst = if offset == 0 {
        Inst::Copy {
            ty: Ty::Ptr,
            operand: v(1),
        }
    } else {
        Inst::GEP {
            pointee_ty: Ty::U8,
            base: v(1),
            indices: vec![v(3)],
            inbounds: true,
        }
    };
    out
}

#[test]
fn in_bounds_pointer_chain_becomes_a_byte_gep() {
    for offset in [0u64, 4, 7] {
        let src = module(&chain(offset as i64));
        let f = func(&src, "f");
        check_pass(&src, 32, f, &gep_target(f, offset), &gep_rewrite(offset))
            .unwrap_or_else(|e| panic!("offset {offset} inside 8 bytes: {e}"));
    }
}

#[test]
fn negative_control_out_of_bounds_gep_rewrite_is_refused() {
    // 8 is one past the end of the 8-byte slot: `inttoptr` may name a
    // neighbouring allocation there, a GEP never does.
    let src = module(&chain(8));
    let f = func(&src, "f");
    let err = check_pass(&src, 32, f, &gep_target(f, 8), &gep_rewrite(8)).unwrap_err();
    assert!(
        matches!(err, MidTvError::OffsetOutOfBounds { size: 8, .. }),
        "{err}"
    );
}

#[test]
fn negative_control_gep_rewrite_of_an_unknown_base_is_refused() {
    let text = "functy.0 = (ptr) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%1: ptr):\n\
        \x20   %0 = const i32 0\n\
        \x20   %2 = ptrtoint ptr %1 to i32\n\
        \x20   %3 = const i32 4\n\
        \x20   %4 = add i32 %2, %3\n\
        \x20   %5 = inttoptr i32 %4 to ptr\n\
        \x20   %6 = load i32, ptr %5\n\
        \x20   ret %6\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let err = check_pass(&src, 32, f, &gep_target(f, 4), &gep_rewrite(4)).unwrap_err();
    assert!(matches!(err, MidTvError::NotPointerChain { .. }), "{err}");
}

/// The bridge's other address shapes over a 16-byte slot: an integer round
/// trip of its address (`%3`), a constant offset from a pointer 4 bytes in
/// (`%8`), and an element addressed by a constant index times the element
/// size (`%13`).
const CHAINS: &str = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = alloca [ty.0 x 4], align 4\n\
    \x20   %2 = ptrtoint ptr %1 to i32\n\
    \x20   %3 = inttoptr i32 %2 to ptr\n\
    \x20   store i32 %0, ptr %3\n\
    \x20   %4 = const i32 4\n\
    \x20   %5 = gep inbounds u8, ptr %1, %4\n\
    \x20   %6 = ptrtoint ptr %5 to i32\n\
    \x20   %7 = add i32 %6, %4\n\
    \x20   %8 = inttoptr i32 %7 to ptr\n\
    \x20   store i32 %0, ptr %8\n\
    \x20   %9 = const u32 3\n\
    \x20   %10 = bitcast u32 %9 to i32\n\
    \x20   %11 = mul i32 %10, %4\n\
    \x20   %12 = add i32 %2, %11\n\
    \x20   %13 = inttoptr i32 %12 to ptr\n\
    \x20   store i32 %0, ptr %13\n\
    \x20   %14 = load i32, ptr %3\n\
    \x20   %15 = load i32, ptr %8\n\
    \x20   %16 = load i32, ptr %13\n\
    \x20   %17 = add i32 %14, %15\n\
    \x20   %18 = add i32 %17, %16\n\
    \x20   ret %18\n\
    }\n";

/// One rewrite of `CHAINS`: the `inttoptr` defining `result` at `index`.
fn chain_rewrite(
    index: usize,
    result: u32,
    base: u32,
    offset: u64,
    offset_value: u32,
    folded: Option<u32>,
) -> GepRewrite {
    GepRewrite {
        block: b(0),
        index,
        result: v(result),
        base: v(base),
        offset,
        offset_value: v(offset_value),
        folded: folded.map(v),
    }
}

fn chain_rewrites() -> Vec<GepRewrite> {
    vec![
        chain_rewrite(2, 3, 1, 0, 2, None),
        chain_rewrite(8, 8, 5, 4, 4, None),
        chain_rewrite(14, 13, 1, 12, 11, Some(100)),
    ]
}

/// The checker's own rebuild of `rewrites` on `CHAINS`, then the full check.
fn check_chains(src: &Module, rewrites: Vec<GepRewrite>) -> Result<Function, MidTvError> {
    let f = func(src, "f");
    let witness = PtrGepWitness { rewrites };
    let (target, _) = rebuild_ptr_gep(src, 32, f, &witness)?;
    check_pass(src, 32, f, &target, &PassWitness::PtrGep(witness))?;
    Ok(target)
}

#[test]
fn round_trips_derived_bases_and_constant_indices_become_byte_geps() {
    let src = module(CHAINS);
    let f = func(&src, "f");
    let target = check_chains(&src, chain_rewrites()).unwrap_or_else(|e| panic!("{e}"));
    let body = &target.blocks[0].body;
    assert_eq!(
        body[2].inst,
        Inst::Copy {
            ty: Ty::Ptr,
            operand: v(1)
        }
    );
    // The folded index is a fresh constant just before its `gep`.
    assert_eq!(body[14].results, vec![v(100)]);
    assert_eq!(
        body[14].inst,
        Inst::Const {
            ty: Ty::I32,
            value: Constant::Int(12)
        }
    );
    assert!(matches!(&body[15].inst, Inst::GEP { base, indices, .. }
        if *base == v(1) && indices == &vec![v(100)]));
    // The rewritten function agrees with the source in the interpreter.
    let inputs = seeded_inputs(&src, f, 32, 8, 3).unwrap();
    let mut tgt = src.clone();
    tgt.functions[0] = target.clone();
    let (source_runs, _) = run_samples(&src, f, &inputs, DifferentialBudget::default());
    let (target_runs, _) = run_samples(&tgt, &target, &inputs, DifferentialBudget::default());
    let report = compare_samples(&source_runs, &target_runs);
    assert!(
        report.mismatch.is_none() && report.compared > 0,
        "{report:?}"
    );
}

#[test]
fn negative_control_a_wrong_chain_rewrite_is_refused() {
    let src = module(CHAINS);
    let not_chain = |err: &MidTvError, needle: &str| matches!(err, MidTvError::NotPointerChain { why, .. } if why.contains(needle));
    // A round trip claimed at a nonzero offset.
    let mut rewrites = chain_rewrites();
    rewrites[0].offset = 4;
    let err = check_chains(&src, rewrites).unwrap_err();
    assert!(not_chain(&err, "round trip"), "{err}");
    // A folded offset other than the expression's value.
    let mut rewrites = chain_rewrites();
    rewrites[2].offset = 8;
    let err = check_chains(&src, rewrites).unwrap_err();
    assert!(not_chain(&err, "differs"), "{err}");
    // A folded value that is not fresh.
    let mut rewrites = chain_rewrites();
    rewrites[2].folded = Some(v(9));
    let err = check_chains(&src, rewrites).unwrap_err();
    assert!(not_chain(&err, "fresh"), "{err}");
    // A derived base whose offset leaves the slot: 4 + 12 = 16 bytes into 16.
    let past = module(&CHAINS.replace(
        "%7 = add i32 %6, %4",
        "%30 = const i32 12\n    %7 = add i32 %6, %30",
    ));
    let mut rewrites = chain_rewrites();
    rewrites[1] = chain_rewrite(9, 8, 5, 12, 30, None);
    rewrites[2].index = 15;
    let err = check_chains(&past, rewrites).unwrap_err();
    assert!(
        matches!(
            err,
            MidTvError::OffsetOutOfBounds {
                offset: 16,
                size: 16,
                ..
            }
        ),
        "{err}"
    );
    // An index whose value depends on the reading of its bits (u32::MAX is
    // -1 as an i32), and a product that overflows.
    for (what, from, to) in [
        (
            "a negative index",
            "%9 = const u32 3",
            "%9 = const u32 4294967295",
        ),
        (
            "an overflowing product",
            "%9 = const u32 3",
            "%9 = const u32 1073741824",
        ),
    ] {
        let text = CHAINS.replace(from, to);
        let err = check_chains(&module(&text), chain_rewrites()).unwrap_err();
        assert!(not_chain(&err, "constant expression"), "{what}: {err}");
    }
    // A base of another pointer type than `ptr`.
    let typed = module(&CHAINS.replace(
        "    %6 = ptrtoint ptr %5 to i32\n",
        "    %31 = ptrtoptr ptr %5 to &i32\n    %6 = ptrtoint ptr %31 to i32\n",
    ));
    let mut rewrites = chain_rewrites();
    rewrites[1] = chain_rewrite(9, 8, 31, 4, 4, None);
    rewrites[2].index = 15;
    let err = check_chains(&typed, rewrites).unwrap_err();
    assert!(not_chain(&err, "not a ptr"), "{err}");
}

// ---------------------------------------------------------------------------
// Interpreter differential
// ---------------------------------------------------------------------------

const ARITH: &str = "functy.0 = (u32, u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32, %1: u32):\n\
    \x20   %2 = udiv u32 %0, %1\n\
    \x20   %3 = add u32 %2, %1\n\
    \x20   ret %3\n\
    }\n\n\
    fn @g(functy.0) {\n\
    bb0(%0: u32, %1: u32):\n\
    \x20   %2 = udiv u32 %0, %1\n\
    \x20   %3 = sub u32 %2, %1\n\
    \x20   ret %3\n\
    }\n";

#[test]
fn differential_agrees_on_itself_and_excludes_undefined_inputs() {
    let m = module(ARITH);
    let f = func(&m, "f");
    let inputs = seeded_inputs(&m, f, 32, 32, 7).expect("u32 parameters");
    let (a, _) = run_samples(&m, f, &inputs, DifferentialBudget::default());
    let (b, _) = run_samples(&m, f, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &b);
    assert!(report.mismatch.is_none());
    assert!(report.compared > 0, "some inputs are compared");
    assert!(
        report.ub_excluded > 0,
        "a zero divisor is drawn and excluded as undefined"
    );
    assert_eq!(
        report.compared + report.ub_excluded + report.not_executed,
        32
    );
}

#[test]
fn negative_control_differential_catches_a_wrong_function() {
    let m = module(ARITH);
    let inputs = seeded_inputs(&m, func(&m, "f"), 32, 32, 7).expect("u32 parameters");
    let (a, _) = run_samples(&m, func(&m, "f"), &inputs, DifferentialBudget::default());
    let (b, _) = run_samples(&m, func(&m, "g"), &inputs, DifferentialBudget::default());
    assert!(compare_samples(&a, &b).mismatch.is_some());
}

#[test]
fn pointer_parameters_are_not_synthesized() {
    let src = module(DEAD);
    assert!(seeded_inputs(&src, func(&src, "f"), 32, 4, 1).is_none());
}

#[test]
fn negative_control_dce_of_a_write_through_insertfield_is_refused() {
    // The rustc bridge writes `insertfield` over a POINTER to the aggregate;
    // the wasm lane stores the field through it, so the unused result does not
    // make it dead.
    let text = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 1], align 4\n\
        \x20   %2 = insertfield [ty.0 x 1] %1, 0, %0\n\
        \x20   %3 = load i32, ptr %1\n\
        \x20   ret %3\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let tgt = without(f, &[1]);
    let witness = PassWitness::Dce(DceWitness {
        removals: vec![removal(0, 1, Some(2), RemovalClass::Refinement)],
    });
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::Effectful { .. }), "{err}");
}

#[test]
fn negative_control_dce_of_an_address_bits_division_is_refused() {
    // Past the division execution knows the divisor is not zero, here a bit
    // of an address: the wasm lane reads that as exposing the allocation, so
    // removing the dead division is refused.
    let text = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 1], align 4\n\
        \x20   %2 = ptrtoint ptr %1 to i32\n\
        \x20   %3 = const i32 1\n\
        \x20   %4 = udiv i32 %3, %2\n\
        \x20   ret %0\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let tgt = without(f, &[3]);
    let witness = PassWitness::Dce(DceWitness {
        removals: vec![removal(0, 3, Some(4), RemovalClass::Refinement)],
    });
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::Effectful { .. }), "{err}");
}

// ---------------------------------------------------------------------------
// Single-dominating-store forwarding
// ---------------------------------------------------------------------------

/// Two `i32` fields of an unobservable slot, stored in the entry and read in
/// one arm each; `bb3` reads the first field again after the join.
const SLOTS: &str = "type ty.0 = i32\n\nfuncty.0 = (i32, i32) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = alloca [ty.0 x 2], align 4\n\
    \x20   %3 = const i32 4\n\
    \x20   %4 = gep inbounds u8, ptr %2, %3\n\
    \x20   store i32 %0, ptr %2\n\
    \x20   store i32 %1, ptr %4\n\
    \x20   %5 = icmp slt i32 %0, %1\n\
    \x20   condbr %5, bb1, bb2\n\
    bb1:\n\
    \x20   %6 = load i32, ptr %2\n\
    \x20   br bb3(%6)\n\
    bb2:\n\
    \x20   %7 = load i32, ptr %4\n\
    \x20   br bb3(%7)\n\
    bb3(%8: i32):\n\
    \x20   %9 = load i32, ptr %2\n\
    \x20   %10 = add i32 %8, %9\n\
    \x20   ret %10\n\
    }\n";

/// Where `value` is defined in `func`: (block id, node index).
fn at(func: &Function, value: u32) -> (BlockId, usize) {
    for block in &func.blocks {
        for (i, node) in block.body.iter().enumerate() {
            if node.results.contains(&v(value)) {
                return (block.id, i);
            }
        }
    }
    panic!("%{value} is not defined");
}

/// The node index of the `nth` store of `block` of `func`.
fn store_index(func: &Function, block: u32, nth: usize) -> usize {
    let block = func.blocks.iter().find(|bl| bl.id == b(block)).unwrap();
    block
        .body
        .iter()
        .enumerate()
        .filter(|(_, n)| matches!(n.inst, Inst::Store { .. }))
        .nth(nth)
        .expect("store")
        .0
}

/// The forward of load `%load` to the `nth` store of `block`, and the target
/// with that load replaced by `copy` of the stored value.
fn forward(src: &Function, load: u32, block: u32, nth: usize) -> (LoadForward, Function) {
    let (lb, li) = at(src, load);
    let si = store_index(src, block, nth);
    let store = &src.blocks.iter().find(|bl| bl.id == b(block)).unwrap().body[si].inst;
    let Inst::Store { value, .. } = store else {
        unreachable!()
    };
    let mut tgt = src.clone();
    let node = tgt
        .blocks
        .iter_mut()
        .find(|bl| bl.id == lb)
        .map(|bl| &mut bl.body[li])
        .unwrap();
    let Inst::Load { ty, .. } = &node.inst else {
        panic!("%{load} is not a load");
    };
    node.inst = Inst::Copy {
        ty: ty.clone(),
        operand: *value,
    };
    (
        LoadForward {
            block: lb,
            index: li,
            result: v(load),
            store_block: b(block),
            store_index: si,
            value: *value,
        },
        tgt,
    )
}

fn check_forward(
    text: &str,
    load: u32,
    block: u32,
    nth: usize,
) -> Result<WitnessVerdict, MidTvError> {
    let src = module(text);
    let f = func(&src, "f");
    let (fwd, tgt) = forward(f, load, block, nth);
    let witness = PassWitness::StoreFwd(StoreFwdWitness {
        forwards: vec![fwd],
    });
    check_pass(&src, 32, f, &tgt, &witness)
}

#[test]
fn a_load_with_a_dominating_store_is_forwarded() {
    for (load, nth) in [(6, 0), (7, 1), (9, 0)] {
        let verdict = check_forward(SLOTS, load, 0, nth).unwrap_or_else(|e| panic!("%{load}: {e}"));
        assert_eq!(verdict.exact, 1);
    }
}

/// A chain of `n` diamonds over one slot of `k` `i32` fields, each stored in
/// the entry; diamond `i`'s arm reads field `i % k`. `clobber` names a
/// diamond whose arm overwrites the field after reading it.
fn diamond_chain(n: usize, k: usize, clobber: Option<usize>) -> String {
    let mut s = String::from(
        "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\nfn @f(functy.0) {\nbb0(%0: i32):\n",
    );
    s += &format!("    %1 = alloca [ty.0 x {k}], align 4\n");
    let mut next = 2usize;
    let mut fields = Vec::new();
    for j in 0..k {
        s += &format!("    %{next} = const i32 {}\n", 4 * j);
        s += &format!("    %{} = gep inbounds u8, ptr %1, %{next}\n", next + 1);
        s += &format!("    store i32 %0, ptr %{}\n", next + 1);
        fields.push(next + 1);
        next += 2;
    }
    s += &format!("    %{next} = const i32 0\n    br bb1(%{next})\n");
    next += 1;
    for i in 0..n {
        let (head, arm, join) = (1 + 2 * i, 2 + 2 * i, 3 + 2 * i);
        let (acc, c, cond, l, sum) = (next, next + 1, next + 2, next + 3, next + 4);
        next += 5;
        let field = fields[i % k];
        s += &format!(
            "bb{head}(%{acc}: i32):\n    %{c} = const i32 {i}\n    %{cond} = icmp slt i32 %0, %{c}\n    condbr %{cond}, bb{arm}, bb{join}(%{acc})\n"
        );
        let clobbered = if clobber == Some(i) {
            format!("    store i32 %{acc}, ptr %{field}\n")
        } else {
            String::new()
        };
        s += &format!(
            "bb{arm}:\n    %{l} = load i32, ptr %{field}\n{clobbered}    %{sum} = add i32 %{acc}, %{l}\n    br bb{join}(%{sum})\n"
        );
    }
    s += &format!("bb{}(%{next}: i32):\n    ret %{next}\n}}\n", 1 + 2 * n);
    s
}

/// Every load of `src` forwarded to the entry store through its pointer.
fn forward_all_to_entry(src: &Function) -> (StoreFwdWitness, Function) {
    let entry = &src.blocks[0];
    let mut tgt = src.clone();
    let mut forwards = Vec::new();
    for (bi, block) in src.blocks.iter().enumerate() {
        for (ni, node) in block.body.iter().enumerate() {
            let Inst::Load { ty, ptr, .. } = &node.inst else {
                continue;
            };
            let (si, value) = entry
                .body
                .iter()
                .enumerate()
                .find_map(|(si, n)| match &n.inst {
                    Inst::Store { ptr: p, value, .. } if p == ptr => Some((si, *value)),
                    _ => None,
                })
                .expect("an entry store");
            tgt.blocks[bi].body[ni].inst = Inst::Copy {
                ty: ty.clone(),
                operand: value,
            };
            forwards.push(LoadForward {
                block: block.id,
                index: ni,
                result: node.results[0],
                store_block: entry.id,
                store_index: si,
                value,
            });
        }
    }
    (StoreFwdWitness { forwards }, tgt)
}

#[test]
fn the_forwarding_check_scans_each_block_once_per_store() {
    // 2,000 diamonds, 4,002 blocks, 2,000 forwards over 4 stores. Each
    // forward walks back to the entry; without sharing the walks the check
    // enters about 2 million blocks, with it at most once per block and key.
    let (n, k) = (2000, 4);
    let src = module(&diamond_chain(n, k, None));
    let f = func(&src, "f");
    let (witness, tgt) = forward_all_to_entry(f);
    assert_eq!(witness.forwards.len(), n);
    let mut proofs = ReachProofs::default();
    let (expected, verdict) =
        rebuild_store_fwd_with(&src, f, &witness, &mut proofs).expect("every load forwards");
    assert_eq!(expected, tgt);
    assert_eq!(verdict.exact, n);
    assert_eq!(proofs.states.len(), k);
    assert!(
        proofs.block_scans <= k * f.blocks.len() && proofs.block_visits <= k * f.blocks.len(),
        "{} block scans and {} visits for {} blocks and {k} keys",
        proofs.block_scans,
        proofs.block_visits,
        f.blocks.len()
    );
    // The shared walks still refuse: diamond 10 overwrites field 2 after
    // its own (forwardable) read, so the read of field 2 in diamond 14 has
    // another reaching store, while the forwards of diamonds 2, 6 and 10
    // have already proved the blocks before diamond 10's arm.
    let src = module(&diamond_chain(n, k, Some(10)));
    let f = func(&src, "f");
    let (witness, tgt) = forward_all_to_entry(f);
    let err = check_pass(&src, 32, f, &tgt, &PassWitness::StoreFwd(witness)).unwrap_err();
    assert!(
        matches!(err, MidTvError::NoUniqueReachingStore { why, .. } if why.contains("intervenes")),
        "{err}"
    );
}

#[test]
fn negative_control_a_may_alias_store_on_a_path_is_refused() {
    // bb1 overwrites the first field: the joined read in bb3 has two
    // reaching stores.
    let text = SLOTS.replace(
        "bb1:\n    %6 = load",
        "bb1:\n    store i32 %1, ptr %2\n    %6 = load",
    );
    let err = check_forward(&text, 9, 0, 0).unwrap_err();
    assert!(
        matches!(err, MidTvError::NoUniqueReachingStore { why, .. } if why.contains("intervenes")),
        "{err}"
    );
}

#[test]
fn negative_control_a_partial_overlap_is_refused() {
    let text = SLOTS.replace(
        "    store i32 %1, ptr %4\n",
        "    store i32 %1, ptr %4\n    %20 = const i32 2\n    %21 = gep inbounds u8, ptr %2, %20\n    %22 = const u8 7\n    store u8 %22, ptr %21\n",
    );
    let err = check_forward(&text, 6, 0, 0).unwrap_err();
    assert!(
        matches!(err, MidTvError::NoUniqueReachingStore { why, .. } if why.contains("intervenes")),
        "{err}"
    );
}

#[test]
fn negative_control_a_mixed_width_read_is_refused() {
    let text = SLOTS
        .replace("%9 = load i32, ptr %2", "%9 = load u32, ptr %2")
        .replace(
            "%10 = add i32 %8, %9",
            "%11 = bitcast u32 %9 to i32\n    %10 = add i32 %8, %11",
        );
    let err = check_forward(&text, 9, 0, 0).unwrap_err();
    assert!(matches!(err, MidTvError::NotForwardable { .. }), "{err}");
}

#[test]
fn negative_control_an_undefined_read_is_refused() {
    // The first field is stored on one arm only.
    let text = SLOTS.replace("    store i32 %0, ptr %2\n", "").replace(
        "bb1:\n    %6 = load",
        "bb1:\n    store i32 %0, ptr %2\n    %6 = load",
    );
    let err = check_forward(&text, 9, 1, 0).unwrap_err();
    assert!(
        matches!(err, MidTvError::NoUniqueReachingStore { why, .. } if why.contains("undefined read")),
        "{err}"
    );
}

#[test]
fn negative_control_an_escaping_or_observed_slot_is_refused() {
    let escaped = format!(
        "{}\nfn @g(functy.1) {{\n}}\n",
        SLOTS
            .replace(
                "functy.0 = (i32, i32) -> (i32)\n\n",
                "functy.0 = (i32, i32) -> (i32)\n\nfuncty.1 = (ptr) -> ()\n\n",
            )
            .replace(
                "    %5 = icmp slt",
                "    call @func.1(%2)\n    %5 = icmp slt"
            )
    );
    let observed = SLOTS.replace(
        "    ret %10\n",
        "    %30 = ptrtoint ptr %2 to i32\n    %31 = add i32 %10, %30\n    ret %31\n",
    );
    for text in [escaped, observed] {
        let err = check_forward(&text, 9, 0, 0).unwrap_err();
        assert!(matches!(err, MidTvError::SlotObservable { .. }), "{err}");
    }
}

#[test]
fn negative_control_a_reloaded_pointer_is_not_forwarded() {
    let text = "functy.0 = (ptr) -> (ptr)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: ptr):\n\
        \x20   %1 = alloca ptr\n\
        \x20   store ptr %0, ptr %1\n\
        \x20   %2 = load ptr, ptr %1\n\
        \x20   ret %2\n\
        }\n";
    let err = check_forward(text, 2, 0, 0).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotForwardable { why, .. } if why.contains("reload")),
        "{err}"
    );
}

#[test]
fn negative_control_a_forward_to_the_wrong_value_is_refused() {
    let src = module(SLOTS);
    let f = func(&src, "f");
    let (mut fwd, tgt) = forward(f, 6, 0, 0);
    fwd.value = v(1);
    let witness = PassWitness::StoreFwd(StoreFwdWitness {
        forwards: vec![fwd],
    });
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::NotForwardable { .. }), "{err}");
}

// ---------------------------------------------------------------------------
// Dead slots
// ---------------------------------------------------------------------------

#[test]
fn the_stores_of_an_unread_slot_are_removed_and_a_read_slot_is_refused() {
    let text = "type ty.0 = i32\n\nfuncty.0 = (i32) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 2], align 4\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   ret %0\n\
        }\n";
    let src = module(text);
    let f = func(&src, "f");
    let tgt = without(f, &[1]);
    let witness = PassWitness::DeadSlot(DeadSlotWitness {
        slots: vec![DeadSlot {
            alloca: v(1),
            stores: vec![(b(0), 1)],
        }],
    });
    let verdict = check_pass(&src, 32, f, &tgt, &witness).expect("a dead slot");
    assert_eq!(verdict.refinements, 1);
    // Claiming no store leaves the target with one it says is gone.
    let short = PassWitness::DeadSlot(DeadSlotWitness {
        slots: vec![DeadSlot {
            alloca: v(1),
            stores: Vec::new(),
        }],
    });
    assert!(check_pass(&src, 32, f, &tgt, &short).is_err());
    // A read slot is not dead.
    let read = module(&text.replace("    ret %0\n", "    %2 = load i32, ptr %1\n    ret %2\n"));
    let f = func(&read, "f");
    let tgt = without(f, &[1]);
    let err = check_pass(&read, 32, f, &tgt, &witness).unwrap_err();
    assert!(
        matches!(err, MidTvError::SlotObservable { why, .. } if why.contains("read")),
        "{err}"
    );
}

// ---------------------------------------------------------------------------
// Constant-table promotion
// ---------------------------------------------------------------------------

/// A local `[3, 1, 4, 1]` of `u32` in the mid-end's cleaned-up form (byte
/// `gep` stores), read at `t[i & 7]` behind the check `i & 7 < 4` through the
/// rustc bridge's `inttoptr(ptrtoint(t) + idx * 4)`.
const TABLE: &str = "type ty.0 = u32\ntype ty.1 = u8\n\nfuncty.0 = (u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%1: u32):\n\
    \x20   %6 = alloca [ty.0 x 4], align 4\n\
    \x20   %7 = const u32 3\n\
    \x20   store u32 %7, ptr %6\n\
    \x20   %8 = const u32 1\n\
    \x20   %9 = const i32 4\n\
    \x20   %14 = gep inbounds u8, ptr %6, %9\n\
    \x20   store u32 %8, ptr %14\n\
    \x20   %15 = const u32 4\n\
    \x20   %16 = const i32 8\n\
    \x20   %21 = gep inbounds u8, ptr %6, %16\n\
    \x20   store u32 %15, ptr %21\n\
    \x20   %23 = const i32 12\n\
    \x20   %28 = gep inbounds u8, ptr %6, %23\n\
    \x20   store u32 %8, ptr %28\n\
    \x20   %58 = const u32 7\n\
    \x20   %57 = and u32 %1, %58\n\
    \x20   %61 = const u32 4\n\
    \x20   %60 = icmp ult u32 %57, %61\n\
    \x20   condbr %60, bb1, bb3\n\
    bb3:\n\
    \x20   unreachable\n\
    bb1:\n\
    \x20   %67 = ptrtoint ptr %6 to i32\n\
    \x20   %68 = bitcast u32 %57 to i32\n\
    \x20   %69 = const i32 4\n\
    \x20   %70 = mul i32 %68, %69\n\
    \x20   %71 = add i32 %67, %70\n\
    \x20   %72 = inttoptr i32 %71 to ptr\n\
    \x20   %65 = load u32, ptr %72\n\
    \x20   ret %65\n\
    }\n";

const TABLE_IMAGE: [u8; 16] = [3, 0, 0, 0, 1, 0, 0, 0, 4, 0, 0, 0, 1, 0, 0, 0];

/// The promotion of `%6` to the module's next global, its witness and the
/// target, for the stores of `src` the test names.
fn promotion(src: &Module, image: &[u8]) -> (PassWitness, Function) {
    let f = func(src, "f");
    let global = GlobalId::new(u32::try_from(src.globals.len()).unwrap());
    let (ab, ai) = at(f, 6);
    let mut stores = Vec::new();
    for block in &f.blocks {
        for (i, node) in block.body.iter().enumerate() {
            if matches!(node.inst, Inst::Store { .. }) {
                stores.push((block.id, i));
            }
        }
    }
    let mut tgt = f.clone();
    for block in &mut tgt.blocks {
        let id = block.id;
        let mut i = 0usize;
        block.body.retain(|_| {
            let keep = !stores.contains(&(id, i));
            i += 1;
            keep
        });
        if id == ab {
            block.body[ai].inst = Inst::GlobalAddr { global };
        }
    }
    let witness = PassWitness::Ctp(CtpWitness {
        promotions: vec![CtpPromotion {
            block: ab,
            index: ai,
            alloca: v(6),
            global,
            stores,
        }],
        new_types: Vec::new(),
        new_globals: vec![Global {
            name: "f.irmid.ctp.6".to_string(),
            ty: Ty::Array(trust_ir::TyId::new(1), 16),
            mutable: false,
            initializer: Some(Constant::Bytes {
                data: image.to_vec(),
                utf8: false,
            }),
            linkage: trust_ir::Linkage::Internal,
            tls: None,
            align: Some(4),
            section: None,
            visibility: trust_ir::Visibility::Default,
            retained: false,
        }],
    });
    (witness, tgt)
}

fn check_promotion(text: &str) -> Result<WitnessVerdict, MidTvError> {
    let src = module(text);
    let (witness, tgt) = promotion(&src, &TABLE_IMAGE);
    check_pass(&src, 32, func(&src, "f"), &tgt, &witness)
}

#[test]
fn a_constant_table_is_promoted_as_a_refinement() {
    let verdict = check_promotion(TABLE).expect("a constant table");
    assert_eq!(verdict.refinements, 1);
    assert_eq!(verdict.exact, 0);
}

#[test]
fn negative_controls_a_table_that_is_not_constant_data_is_refused() {
    // The address is compared: its bits are observed.
    let observed = TABLE.replace(
        "    ret %65\n",
        "    %80 = icmp ult i32 %67, %69\n    %81 = select u32 %80, %65, %57\n    ret %81\n",
    );
    // It escapes through a call.
    let escaped = format!(
        "{}\nfn @g(functy.1) {{\n}}\n",
        TABLE
            .replace(
                "functy.0 = (u32) -> (u32)\n\n",
                "functy.0 = (u32) -> (u32)\n\nfuncty.1 = (ptr) -> ()\n\n",
            )
            .replace(
                "    %58 = const u32 7\n",
                "    call @func.1(%6)\n    %58 = const u32 7\n"
            )
    );
    // A write after initialization, of a value no constant gives.
    let written = TABLE.replace(
        "    %65 = load u32",
        "    store u32 %1, ptr %6\n    %65 = load u32",
    );
    // An index no check bounds: the read may land in a neighbour.
    let unbounded = TABLE.replace("condbr %60, bb1, bb3", "br bb1");
    for (what, text) in [
        ("observed", observed),
        ("escaped", escaped),
        ("written", written),
        ("unbounded", unbounded),
    ] {
        let err = check_promotion(&text).unwrap_err();
        assert!(
            matches!(err, MidTvError::NotPromotable { .. }),
            "{what}: {err}"
        );
    }
}

#[test]
fn negative_controls_a_global_that_is_not_the_image_is_refused() {
    let src = module(TABLE);
    let f = func(&src, "f");
    let mut wrong = TABLE_IMAGE;
    wrong[4] = 9;
    let (witness, tgt) = promotion(&src, &wrong);
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::BadGlobal { .. }), "{err}");
    let (mut witness, tgt) = promotion(&src, &TABLE_IMAGE);
    if let PassWitness::Ctp(w) = &mut witness {
        w.new_globals[0].mutable = true;
    }
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::BadGlobal { .. }), "{err}");
    // A store the witness does not name stays in the source's position.
    let (mut witness, tgt) = promotion(&src, &TABLE_IMAGE);
    if let PassWitness::Ctp(w) = &mut witness {
        w.promotions[0].stores.pop();
    }
    let err = check_pass(&src, 32, f, &tgt, &witness).unwrap_err();
    assert!(matches!(err, MidTvError::NotPromotable { .. }), "{err}");
}

#[test]
fn negative_control_a_value_of_another_type_is_not_forwarded() {
    // The callee returns a `u32` the store writes as an `i32`: `copy i32` of
    // it would change its type.
    let text = format!(
        "{}\nfn @g(functy.1) {{\n}}\n",
        SLOTS
            .replace(
                "functy.0 = (i32, i32) -> (i32)\n\n",
                "functy.0 = (i32, i32) -> (i32)\n\nfuncty.1 = () -> (u32)\n\n",
            )
            .replace(
                "    store i32 %0, ptr %2\n",
                "    %40 = call @func.1()\n    store i32 %40, ptr %2\n",
            )
    );
    let err = check_forward(&text, 6, 0, 0).unwrap_err();
    assert!(
        matches!(err, MidTvError::NotForwardable { why, .. } if why.contains("type")),
        "{err}"
    );
}

// ---------------------------------------------------------------------------
// The harness: memory inputs, drivers, the view and the fuel ladder
// ---------------------------------------------------------------------------

/// Run the harness differential of `name` in `m` against `target`: the
/// source's runs and, per input, the comparison with the target's run.
fn harness_differential(m: &Module, name: &str, target: &Function) -> Vec<InputVerdict> {
    let budget = DifferentialBudget::default();
    let mut view = interpretable_module(m);
    let index = view
        .functions
        .iter()
        .position(|f| f.name == name)
        .expect("function");
    let harness = Harness::build(
        &view,
        &view.functions[index],
        32,
        8,
        7,
        budget,
        HarnessLimits::default(),
    )
    .expect("synthesizable");
    let mut left = u64::MAX;
    let inputs: Vec<usize> = (0..harness.inputs()).collect();
    let source: Vec<InputRun> = run_inputs(&mut view, &harness, &inputs, &[], budget, &mut left)
        .into_iter()
        .map(|(_, run)| run)
        .collect();
    let mut viewed = interpretable(&view, target).unwrap_or_else(|| target.clone());
    std::mem::swap(&mut view.functions[index], &mut viewed);
    let target_runs = run_target(&mut view, &harness, &source, budget, &mut left);
    source
        .iter()
        .zip(&target_runs)
        .map(|(s, t)| match t {
            Some(t) => compare_input(&s.outcome, &t.outcome),
            None => compare_input(&s.outcome, &InputOutcome::OverBudget),
        })
        .collect()
}

fn compared(verdicts: &[InputVerdict]) -> usize {
    verdicts
        .iter()
        .filter(|v| matches!(v, InputVerdict::Compared { .. }))
        .count()
}

fn mismatched(verdicts: &[InputVerdict]) -> bool {
    verdicts
        .iter()
        .any(|v| matches!(v, InputVerdict::Mismatch(_)))
}

/// `f(p) = *p + p[1]`, with `g(p)` storing 2 into `*p`.
const POINTER_PARAM: &str = "type ty.0 = i32\n\n\
    functy.0 = (ptr) -> (i32)\n\n\
    functy.1 = (ptr) -> ()\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: ptr):\n\
    \x20   %1 = load i32, ptr %0\n\
    \x20   %2 = const usize 1\n\
    \x20   %3 = gep i32, ptr %0, %2\n\
    \x20   %4 = load i32, ptr %3\n\
    \x20   %5 = add i32 %1, %4\n\
    \x20   ret %5\n\
    }\n\n\
    fn @g(functy.1) {\n\
    bb0(%0: ptr):\n\
    \x20   %1 = const i32 2\n\
    \x20   store i32 %1, ptr %0\n\
    \x20   ret\n\
    }\n";

#[test]
fn a_pointer_parameter_gets_an_object_from_its_accesses() {
    let m = module(POINTER_PARAM);
    let f = func(&m, "f");
    assert!(
        seeded_inputs(&m, f, 32, 8, 7).is_none(),
        "the scalar-only differential has no input for a pointer parameter"
    );
    let harness = Harness::build(
        &m,
        f,
        32,
        8,
        7,
        DifferentialBudget::default(),
        HarnessLimits::default(),
    )
    .expect("a pointer parameter is synthesized");
    assert!(harness.driven());
    assert_eq!(harness.objects(), 1);
    let verdicts = harness_differential(&m, "f", f);
    assert_eq!(compared(&verdicts), 8, "{verdicts:?}");
    assert!(
        verdicts.iter().all(|v| matches!(
            v,
            InputVerdict::Compared {
                observed: Observed::Memory
            }
        )),
        "the object's bytes are compared too: {verdicts:?}"
    );
}

/// `h(p)`: `*p = 1; g(p); return *p`, where `g` writes 2 through `p`.
const FORWARD_ACROSS_CALL: &str = "type ty.0 = i32\n\n\
    functy.0 = (ptr) -> (i32)\n\n\
    functy.1 = (ptr) -> ()\n\n\
    fn @h(functy.0) {\n\
    bb0(%0: ptr):\n\
    \x20   %1 = const i32 1\n\
    \x20   store i32 %1, ptr %0\n\
    \x20   call @func.1(%0)\n\
    \x20   %2 = load i32, ptr %0\n\
    \x20   ret %2\n\
    }\n\n\
    fn @g(functy.1) {\n\
    bb0(%0: ptr):\n\
    \x20   %1 = const i32 2\n\
    \x20   store i32 %1, ptr %0\n\
    \x20   ret\n\
    }\n";

/// Negative control: forwarding the store to `*p` across a call that writes
/// through `p` is wrong. The scalar-only differential has no input for `h`
/// (a pointer parameter); the harness runs `g`'s body through the call and
/// catches it, and agrees with the right function.
#[test]
fn negative_control_a_wrong_forwarding_through_a_pointer_parameter_is_caught() {
    let m = module(FORWARD_ACROSS_CALL);
    let h = func(&m, "h");
    assert!(seeded_inputs(&m, h, 32, 8, 7).is_none());
    let mut wrong = h.clone();
    // `%2 = load i32, ptr %0` becomes `%2 = copy i32 %1`.
    wrong.blocks[0].body[3].inst = Inst::Copy {
        ty: Ty::I32,
        operand: v(1),
    };
    let verdicts = harness_differential(&m, "h", &wrong);
    assert!(mismatched(&verdicts), "{verdicts:?}");
    let right = harness_differential(&m, "h", h);
    assert!(!mismatched(&right) && compared(&right) > 0, "{right:?}");
}

/// `k(p, x)`: `*q = x` into a fresh slot `q`, then `copy(q, p)` copies `*q`
/// to `*p`; nothing returns.
const CALL_READS_SLOT: &str = "type ty.0 = i32\n\n\
    functy.0 = (ptr, i32) -> ()\n\n\
    functy.1 = (ptr, ptr) -> ()\n\n\
    fn @k(functy.0) {\n\
    bb0(%0: ptr, %1: i32):\n\
    \x20   %2 = alloca [ty.0 x 1], align 4\n\
    \x20   store i32 %1, ptr %2\n\
    \x20   call @func.1(%2, %0)\n\
    \x20   ret\n\
    }\n\n\
    fn @copy(functy.1) {\n\
    bb0(%0: ptr, %1: ptr):\n\
    \x20   %2 = load i32, ptr %0\n\
    \x20   store i32 %2, ptr %1\n\
    \x20   ret\n\
    }\n";

/// Negative control: removing the store a callee reads is wrong, and only
/// the memory the call leaves behind shows it (`k` returns nothing). The
/// scalar-only differential has no input for `k`; the harness observes `p`'s
/// object after the call, where the target left poison.
#[test]
fn negative_control_a_wrong_dce_of_a_call_reachable_store_is_caught() {
    let m = module(CALL_READS_SLOT);
    let k = func(&m, "k");
    assert!(seeded_inputs(&m, k, 32, 8, 7).is_none());
    let wrong = without(k, &[1]);
    let verdicts = harness_differential(&m, "k", &wrong);
    assert!(mismatched(&verdicts), "{verdicts:?}");
    let right = harness_differential(&m, "k", k);
    assert!(
        right.iter().any(|v| matches!(
            v,
            InputVerdict::Compared {
                observed: Observed::Memory
            }
        )),
        "{right:?}"
    );
}

/// Negative control: a store to the parameter's object that a rewrite drops
/// is seen in the object's bytes after the call.
#[test]
fn negative_control_a_dropped_store_through_a_parameter_is_caught() {
    let m = module(POINTER_PARAM);
    let g = func(&m, "g");
    let wrong = without(g, &[1]);
    assert!(mismatched(&harness_differential(&m, "g", &wrong)));
}

/// A pointer loaded from the parameter's object gets its own object (a
/// slot), so a function reading through two levels runs.
#[test]
fn a_loaded_pointer_gets_a_child_object() {
    let text = "type ty.0 = i32\n\n\
        functy.0 = (ptr) -> (i32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: ptr):\n\
        \x20   %1 = const usize 1\n\
        \x20   %2 = gep ptr, ptr %0, %1\n\
        \x20   %3 = load ptr, ptr %2\n\
        \x20   %4 = load i32, ptr %3\n\
        \x20   ret %4\n\
        }\n";
    let m = module(text);
    let f = func(&m, "f");
    let harness = Harness::build(
        &m,
        f,
        32,
        8,
        7,
        DifferentialBudget::default(),
        HarnessLimits::default(),
    )
    .unwrap();
    assert_eq!(
        harness.objects(),
        2,
        "the parameter's object and its slot's"
    );
    assert_eq!(compared(&harness_differential(&m, "f", f)), 8);
}

#[test]
fn a_function_pointer_parameter_is_not_synthesized_by_name() {
    let text = "functy.0 = (i32) -> (i32)\n\n\
        functy.1 = (functy.0) -> (i32)\n\n\
        fn @f(functy.1) {\n\
        bb0(%0: functy.0):\n\
        \x20   %1 = const i32 0\n\
        \x20   ret %1\n\
        }\n";
    let m = module(text);
    let why = Harness::build(
        &m,
        func(&m, "f"),
        32,
        8,
        7,
        DifferentialBudget::default(),
        HarnessLimits::default(),
    )
    .unwrap_err();
    assert_eq!(why.reason, "function_pointer");
}

/// A loop of about 45,000 steps: past the scalar-only differential's fixed
/// 20,000-step run, inside the harness's ladder sized from the function and
/// its loop.
const LONG_LOOP: &str = "functy.0 = (u32) -> (u32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: u32):\n\
    \x20   %1 = const u32 0\n\
    \x20   br bb1(%1)\n\
    bb1(%2: u32):\n\
    \x20   %3 = const u32 1\n\
    \x20   %4 = add u32 %2, %3\n\
    \x20   %5 = xor u32 %4, %0\n\
    \x20   %6 = and u32 %5, %4\n\
    \x20   %7 = or u32 %6, %3\n\
    \x20   %8 = mul u32 %7, %3\n\
    \x20   %9 = const u32 5000\n\
    \x20   %10 = icmp ult u32 %4, %9\n\
    \x20   condbr %10, bb1(%4), bb2\n\
    bb2:\n\
    \x20   ret %8\n\
    }\n";

#[test]
fn loops_run_on_a_fuel_ladder_sized_from_the_function() {
    let m = module(LONG_LOOP);
    let f = func(&m, "f");
    let inputs = seeded_inputs(&m, f, 32, 4, 7).unwrap();
    let (fixed, _) = run_samples(&m, f, &inputs, DifferentialBudget::default());
    assert!(
        fixed
            .iter()
            .all(|o| *o == SampleOutcome::NotExecuted("out_of_fuel")),
        "{fixed:?}"
    );
    let harness = Harness::build(
        &m,
        f,
        32,
        4,
        7,
        DifferentialBudget::default(),
        HarnessLimits::default(),
    )
    .unwrap();
    assert!(harness.fuel_cap() > 45_000, "{}", harness.fuel_cap());
    let mut view = m.clone();
    let mut left = u64::MAX;
    let runs = run_inputs(
        &mut view,
        &harness,
        &[0, 1, 2, 3],
        &[],
        DifferentialBudget::default(),
        &mut left,
    );
    for (_, run) in &runs {
        assert!(
            matches!(run.outcome, InputOutcome::Returned { .. }),
            "{:?}",
            run.outcome
        );
        // The run took about 45,000 steps; the rungs below the one it
        // finished on (4,096 and 32,768) are charged too.
        assert!(
            run.charged >= 45_000 && run.charged <= 45_000 + 4_096 + 32_768 + 100,
            "{}",
            run.charged
        );
        assert_eq!(
            run.rung,
            harness.fuel_cap().min(32_768 * FUEL_LADDER_FACTOR)
        );
    }
}

#[test]
fn a_run_past_its_cap_is_not_executed_by_name() {
    let text = LONG_LOOP.replace("5000", "4000000000");
    let m = module(&text);
    let f = func(&m, "f");
    let budget = DifferentialBudget::default();
    let harness = Harness::build(&m, f, 32, 1, 7, budget, HarnessLimits::default()).unwrap();
    let mut view = m.clone();
    let mut left = u64::MAX;
    let runs = run_inputs(&mut view, &harness, &[0], &[], budget, &mut left);
    assert_eq!(runs[0].1.outcome, InputOutcome::NotExecuted("out_of_fuel"));
    assert!(runs[0].1.charged >= harness.fuel_cap());
}

#[test]
fn a_call_to_a_declaration_is_named() {
    let text = "functy.0 = (u32) -> (u32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: u32):\n\
        \x20   %1 = call @func.1(%0)\n\
        \x20   ret %1\n\
        }\n\n\
        fn @ext(functy.0) {\n\
        }\n";
    let m = module(text);
    let f = func(&m, "f");
    let budget = DifferentialBudget::default();
    let harness = Harness::build(&m, f, 32, 2, 7, budget, HarnessLimits::default()).unwrap();
    let mut view = m.clone();
    let mut left = u64::MAX;
    let runs = run_inputs(&mut view, &harness, &[0, 1], &[], budget, &mut left);
    for (_, run) in runs {
        assert_eq!(
            run.outcome,
            InputOutcome::NotExecuted("call_to_declaration")
        );
    }
}

#[test]
fn the_budget_stops_runs_by_name() {
    let m = module(POINTER_PARAM);
    let f = func(&m, "f");
    let budget = DifferentialBudget::default();
    let harness = Harness::build(&m, f, 32, 2, 7, budget, HarnessLimits::default()).unwrap();
    let mut view = m.clone();
    let mut left = 0;
    let runs = run_inputs(&mut view, &harness, &[0, 1], &[], budget, &mut left);
    assert!(
        runs.iter()
            .all(|(_, r)| r.outcome == InputOutcome::OverBudget)
    );
}

/// The bridge's lane idioms the interpreter refuses as type errors run in
/// the view: a copy that reinterprets an integer's sign, a shift by an
/// amount of another type, a `bool` constant spelled as an integer, a
/// pointer comparison, and the write-through `insertfield` over a pointer.
#[test]
fn the_view_runs_the_lanes_idioms() {
    let text = "type ty.0 = i32\n\n\
        functy.0 = (i32, u32) -> (u32)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: u32):\n\
        \x20   %2 = copy u32 %0\n\
        \x20   %3 = const i32 3\n\
        \x20   %4 = shl u32 %2, %3\n\
        \x20   %5 = const bool 1\n\
        \x20   %6 = alloca [ty.0 x 2], align 4\n\
        \x20   %7 = insertfield [ty.0 x 2] %6, 1, %0\n\
        \x20   %8 = icmp eq ptr %6, %7\n\
        \x20   %9 = and bool %5, %8\n\
        \x20   condbr %9, bb1, bb2\n\
        bb1:\n\
        \x20   ret %4\n\
        bb2:\n\
        \x20   ret %1\n\
        }\n";
    let m = module(text);
    let f = func(&m, "f");
    let inputs = seeded_inputs(&m, f, 32, 4, 7).unwrap();
    let (raw, _) = run_samples(&m, f, &inputs, DifferentialBudget::default());
    assert!(
        raw.iter()
            .all(|o| *o == SampleOutcome::NotExecuted("type_error")),
        "the interpreter refuses the raw idioms: {raw:?}"
    );
    let viewed = interpretable(&m, f).expect("the view rewrites them");
    let mut view = m.clone();
    view.functions[0] = viewed;
    let (outcomes, _) = run_samples(
        &view,
        &view.functions[0],
        &inputs,
        DifferentialBudget::default(),
    );
    for (outcome, input) in outcomes.iter().zip(&inputs) {
        let x = input[0].as_int().unwrap().as_signed() as u32;
        let SampleOutcome::Returned(values) = outcome else {
            panic!("{outcome:?}");
        };
        assert_eq!(
            values[0].as_int().unwrap().as_unsigned(),
            u128::from(x << 3)
        );
    }
}

/// The bridge's global-address stub constant is the global's address in the
/// view, and a global initialized with another global's address
/// (`symaddr` at `ptr`) is materialized.
#[test]
fn the_view_resolves_global_addresses() {
    let text = "type ty.0 = u8\n\ntype ty.1 = i32\n\n\
        struct @pair { part0: ptr @0, part1: [ty.0 x 4] @4 } size=8 align=4 id=0\n\n\
        functy.0 = () -> (i32)\n\n\
        global internal align(4) @data [ty.0 x 4] = bytes<07000000>\n\n\
        global internal align(4) @table struct.0 = { symaddr<data>, bytes<01020304> }\n\n\
        fn @f(functy.0) {\n\
        bb0:\n\
        \x20   %0 = const ptr 18076885958606716928\n\
        \x20   %1 = load ptr, ptr %0\n\
        \x20   %2 = load i32, ptr %1\n\
        \x20   ret %2\n\
        }\n";
    let m = module(text);
    assert_eq!(
        global_addr_stub(18076885958606716928),
        Some((1, 0)),
        "0xFADE << 48 | 1 << 32"
    );
    let f = func(&m, "f");
    let (raw, _) = run_samples(&m, f, &[Vec::new()], DifferentialBudget::default());
    assert!(matches!(raw[0], SampleOutcome::NotExecuted(_)), "{raw:?}");
    let view = interpretable_module(&m);
    let (outcomes, _) = run_samples(
        &view,
        &view.functions[0],
        &[Vec::new()],
        DifferentialBudget::default(),
    );
    let SampleOutcome::Returned(values) = &outcomes[0] else {
        panic!("{outcomes:?}");
    };
    assert_eq!(values[0].as_int().unwrap().as_signed(), 7);
}

/// `f`: the `i32` 16 bytes past `@ext`'s address, computed as an integer
/// (`ptrtoint`, `add`, `inttoptr`, as the bridge indexes a static), with
/// `@data` (holding 7) allocated right after `@ext`. `ext` is the text of
/// `@ext`'s declaration.
fn past_a_global(ext: &str) -> String {
    format!(
        "type ty.0 = u8\n\ntype ty.1 = i32\n\n\
         functy.0 = () -> (i32)\n\n\
         {ext}\n\n\
         global internal align(4) @data [ty.0 x 4] = bytes<07000000>\n\n\
         fn @f(functy.0) {{\n\
         bb0:\n\
         \x20   %0 = const ptr 18076885954311749632\n\
         \x20   %1 = const ptr 18076885958606716928\n\
         \x20   %2 = ptrtoint ptr %0 to i32\n\
         \x20   %3 = const i32 16\n\
         \x20   %4 = add i32 %2, %3\n\
         \x20   %5 = inttoptr i32 %4 to ptr\n\
         \x20   %6 = load i32, ptr %5\n\
         \x20   ret %6\n\
         }}\n"
    )
}

/// Regression (round-13 merge review): a global without an initializer (the
/// bridge's declaration of a static another unit defines, at the
/// placeholder type `ptr`) gets [`harness::EXTERN_GLOBAL_RESERVE`] bytes in
/// the view, which the interpreter zero-fills, so an access past its
/// declared size reads the reserve's 0, never `@data`'s bytes. Control: a
/// global that is defined at 4 bytes is not retyped, and the same access
/// reads `@data`'s 7.
#[test]
fn the_view_reserves_a_declared_global_so_no_access_reads_its_neighbour() {
    let run = |text: &str| {
        let view = interpretable_module(&module(text));
        let (outcomes, _) = run_samples(
            &view,
            func(&view, "f"),
            &[Vec::new()],
            DifferentialBudget::default(),
        );
        (view, outcomes)
    };
    let (view, outcomes) = run(&past_a_global(
        "global internal align(4) @ext [ty.0 x 4] = bytes<00000000>",
    ));
    assert!(
        matches!(view.globals[0].ty, Ty::Array(_, 4)),
        "{:?}",
        view.globals[0]
    );
    let SampleOutcome::Returned(values) = &outcomes[0] else {
        panic!("{outcomes:?}");
    };
    assert_eq!(
        values[0].as_int().unwrap().as_signed(),
        7,
        "the control reads @data"
    );
    let (view, outcomes) = run(&past_a_global("global mut @ext ptr"));
    assert_eq!(
        view.globals[0].ty,
        Ty::Array(
            trust_ir::value::TyId::new(0),
            harness::EXTERN_GLOBAL_RESERVE
        ),
    );
    assert!(view.globals[0].initializer.is_none());
    let SampleOutcome::Returned(values) = &outcomes[0] else {
        panic!("{outcomes:?}");
    };
    assert_eq!(
        values[0].as_int().unwrap().as_signed(),
        0,
        "the reserve, not @data"
    );
    // A type table without a one-byte integer (the reserve is the first
    // small type, repeated): `i16` here, so half as many elements.
    let text = past_a_global("global mut @ext ptr")
        .replace("type ty.0 = u8", "type ty.0 = i16")
        .replace("[ty.0 x 4] = bytes<07000000>", "i32 = 7");
    let (view, outcomes) = run(&text);
    assert_eq!(
        view.globals[0].ty,
        Ty::Array(
            trust_ir::value::TyId::new(0),
            harness::EXTERN_GLOBAL_RESERVE / 2
        ),
    );
    let SampleOutcome::Returned(values) = &outcomes[0] else {
        panic!("{outcomes:?}");
    };
    assert_eq!(values[0].as_int().unwrap().as_signed(), 0);
}

/// `f(p, q)`: `*p = 1; *q = 2; return *p`.
const TWO_POINTERS: &str = "type ty.0 = i32\n\n\
    functy.0 = (ptr, ptr) -> (i32)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: ptr, %1: ptr):\n\
    \x20   %2 = const i32 1\n\
    \x20   store i32 %2, ptr %0\n\
    \x20   %3 = const i32 2\n\
    \x20   store i32 %3, ptr %1\n\
    \x20   %4 = load i32, ptr %0\n\
    \x20   ret %4\n\
    }\n";

/// Negative control: forwarding `*p = 1` to the load of `*p` past a store
/// through `q` is wrong exactly when `q` aliases `p`. Inputs that give each
/// parameter its own object agree with it; the aliasing inputs (both at one
/// address, and `q` two bytes into `p`'s word) catch it.
#[test]
fn negative_control_a_wrong_forwarding_between_aliased_parameters_is_caught() {
    let m = module(TWO_POINTERS);
    let f = func(&m, "f");
    let harness = Harness::build(
        &m,
        f,
        32,
        8,
        7,
        DifferentialBudget::default(),
        HarnessLimits::default(),
    )
    .unwrap();
    assert_eq!(harness.inputs(), 10);
    assert_eq!(harness.aliased_inputs(), 2);
    assert!(harness.is_aliased(8) && harness.is_aliased(9) && !harness.is_aliased(7));
    let mut wrong = f.clone();
    // `%4 = load i32, ptr %0` becomes `%4 = copy i32 %2`.
    wrong.blocks[0].body[4].inst = Inst::Copy {
        ty: Ty::I32,
        operand: v(2),
    };
    let verdicts = harness_differential(&m, "f", &wrong);
    assert!(
        verdicts[..8]
            .iter()
            .all(|v| matches!(v, InputVerdict::Compared { .. })),
        "disjoint objects cannot tell: {verdicts:?}"
    );
    assert!(
        verdicts[8..]
            .iter()
            .all(|v| matches!(v, InputVerdict::Mismatch(_))),
        "{verdicts:?}"
    );
    let right = harness_differential(&m, "f", f);
    assert!(
        right.iter().all(|v| matches!(
            v,
            InputVerdict::Compared {
                observed: Observed::Memory
            }
        )),
        "{right:?}"
    );
}

/// A by-value aggregate parameter is not a memory parameter an aliasing
/// input binds, and one memory parameter has no aliasing input.
#[test]
fn only_two_or_more_memory_parameters_get_aliasing_inputs() {
    let m = module(POINTER_PARAM);
    let budget = DifferentialBudget::default();
    let limits = HarnessLimits::default();
    let f = Harness::build(&m, func(&m, "f"), 32, 8, 7, budget, limits).unwrap();
    assert_eq!((f.inputs(), f.aliased_inputs()), (8, 0));
}

/// `f(p)`: stores a padded struct `{ u8 @0, u32 @4 }` at `p` (its padding
/// bytes are left uninitialised), then `7` at `p + 8`.
const PADDED_STORE: &str = "type ty.0 = u8\n\ntype ty.1 = i32\n\n\
    struct @pad { a: u8 @0, b: u32 @4 } size=8 align=4 id=0\n\n\
    functy.0 = (ptr) -> ()\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: ptr):\n\
    \x20   %1 = const struct.0 { 1, 2 }\n\
    \x20   store struct.0 %1, ptr %0\n\
    \x20   %2 = const usize 8\n\
    \x20   %3 = gep u8, ptr %0, %2\n\
    \x20   %4 = const i32 7\n\
    \x20   store i32 %4, ptr %3\n\
    \x20   ret\n\
    }\n";

/// Negative control: a function that leaves bytes of its parameter's object
/// uninitialised (struct padding) still has the rest of the object read back,
/// so dropping the store of `7` is caught; the right function compares
/// memory on every input.
#[test]
fn negative_control_a_dropped_store_beside_padding_is_caught() {
    let m = module(PADDED_STORE);
    let f = func(&m, "f");
    let wrong = without(f, &[5]);
    let verdicts = harness_differential(&m, "f", &wrong);
    // An input whose fill already holds 7 there cannot tell.
    let caught = verdicts
        .iter()
        .filter(|v| matches!(v, InputVerdict::Mismatch(_)))
        .count();
    assert!(caught >= 6, "{verdicts:?}");
    let right = harness_differential(&m, "f", f);
    assert!(
        right.iter().all(|v| matches!(
            v,
            InputVerdict::Compared {
                observed: Observed::Memory
            }
        )),
        "{right:?}"
    );
}

/// The narrowed read skips exactly the padding: the source's reading reads
/// the `u8` and the bytes from offset 4 on.
#[test]
fn a_read_back_narrows_to_the_initialised_bytes() {
    let m = module(PADDED_STORE);
    let f = func(&m, "f");
    let budget = DifferentialBudget::default();
    let harness = Harness::build(&m, f, 32, 2, 7, budget, HarnessLimits::default()).unwrap();
    let mut view = m.clone();
    let mut left = u64::MAX;
    let runs = run_inputs(&mut view, &harness, &[0, 1], &[], budget, &mut left);
    for (_, run) in &runs {
        let InputOutcome::Returned { results, memory } = &run.outcome else {
            panic!("{:?}", run.outcome);
        };
        assert!(results.is_empty());
        assert_eq!(memory.len(), 2, "{memory:?}");
        assert!(run.reading.narrowed());
        assert_eq!(run.reading.bytes(), 12 - 3);
    }
}

/// A read plan punched at a byte stops reading the rest of its word, and
/// what a failure proves is everything read before it.
#[test]
fn a_read_plan_is_narrowed_and_proven_by_reading_order() {
    let mut plan = ReadPlan(vec![vec![(0, 12)], vec![(0, 8)]]);
    assert!(plan.punch(1));
    assert_eq!(plan.0, vec![vec![(0, 1), (4, 8)], vec![(0, 8)]]);
    assert!(plan.punch(5));
    assert_eq!(plan.0, vec![vec![(0, 1), (4, 1), (8, 4)], vec![(0, 8)]]);
    // Byte 2 is read only by the second object.
    assert!(plan.punch(2));
    assert_eq!(plan.0[1], vec![(0, 2), (4, 4)]);
    assert!(!plan.punch(40));
    let proven = plan.proven_before(9).unwrap();
    assert_eq!(proven.0, vec![vec![(0, 1), (4, 1), (8, 1)], vec![]]);
    assert_eq!(
        harness::uninit_offset("Load: reading uninitialized byte at offset 17"),
        Some(17)
    );
}

/// The wrong-global probe: `f() = &a`, the wrong target returns `&b`.
const TWO_GLOBALS: &str = "type ty.0 = u8\n\n\
    functy.0 = () -> (ptr)\n\n\
    global internal align(4) @a [ty.0 x 4] = bytes<01000000>\n\n\
    global internal align(4) @b [ty.0 x 4] = bytes<02000000>\n\n\
    fn @f(functy.0) {\n\
    bb0:\n\
    \x20   %0 = global_addr @global.0\n\
    \x20   ret %0\n\
    }\n";

/// Negative control: a pointer to the wrong global is not renamed equal to
/// the right one. The function's globals are allocated before the call (a
/// driver takes their addresses first), so they keep their identity; only
/// allocations made during the call are renamed.
#[test]
fn negative_control_a_pointer_to_the_wrong_global_is_caught() {
    let m = module(TWO_GLOBALS);
    let f = func(&m, "f");
    let harness = Harness::build(
        &m,
        f,
        32,
        8,
        7,
        DifferentialBudget::default(),
        HarnessLimits::default(),
    )
    .unwrap();
    assert!(!harness.driven());
    assert_eq!(harness.globals(), 1);
    let mut wrong = f.clone();
    wrong.blocks[0].body[0].inst = Inst::GlobalAddr {
        global: GlobalId::new(1),
    };
    let verdicts = harness_differential(&m, "f", &wrong);
    assert!(
        verdicts
            .iter()
            .all(|v| matches!(v, InputVerdict::Mismatch(_))),
        "{verdicts:?}"
    );
    let right = harness_differential(&m, "f", f);
    assert!(
        right.iter().all(|v| matches!(
            v,
            InputVerdict::Compared {
                observed: Observed::Results
            }
        )),
        "{right:?}"
    );
}

/// The globals of the module functions a function reaches are allocated
/// before the call too, after its own.
#[test]
fn the_globals_a_callee_names_keep_their_identity() {
    let text = TWO_GLOBALS.replace(
        "fn @f(functy.0) {\n\
         bb0:\n\
         \x20   %0 = global_addr @global.0\n\
         \x20   ret %0\n\
         }\n",
        "fn @f(functy.0) {\n\
         bb0:\n\
         \x20   %0 = call @func.1()\n\
         \x20   ret %0\n\
         }\n\n\
         fn @g(functy.0) {\n\
         bb0:\n\
         \x20   %0 = global_addr @global.0\n\
         \x20   ret %0\n\
         }\n",
    );
    let m = module(&text);
    let f = func(&m, "f");
    let budget = DifferentialBudget::default();
    let harness = Harness::build(&m, f, 32, 2, 7, budget, HarnessLimits::default()).unwrap();
    assert_eq!(harness.globals(), 1);
    let mut wrong = func(&m, "g").clone();
    wrong.blocks[0].body[0].inst = Inst::GlobalAddr {
        global: GlobalId::new(1),
    };
    // The callee's wrong body is seen through `f`.
    let mut wrong_module = m.clone();
    let g = wrong_module
        .functions
        .iter()
        .position(|f| f.name == "g")
        .unwrap();
    wrong_module.functions[g] = wrong;
    let mut view = m.clone();
    let mut left = u64::MAX;
    let source = run_inputs(&mut view, &harness, &[0, 1], &[], budget, &mut left);
    let source: Vec<InputRun> = source.into_iter().map(|(_, r)| r).collect();
    let target = run_target(&mut wrong_module, &harness, &source, budget, &mut left);
    for (s, t) in source.iter().zip(&target) {
        let t = t.as_ref().unwrap();
        assert!(
            matches!(
                compare_input(&s.outcome, &t.outcome),
                InputVerdict::Mismatch(_)
            ),
            "{s:?} {t:?}"
        );
    }
}

/// A scalar function's inputs compare its results, not memory; a function
/// that returns nothing and is given no memory observes only that it
/// returned.
#[test]
fn what_an_input_observes_is_named() {
    let text = "functy.0 = (i32) -> (i32)\n\n\
        functy.1 = (i32) -> ()\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   ret %0\n\
        }\n\n\
        fn @g(functy.1) {\n\
        bb0(%0: i32):\n\
        \x20   ret\n\
        }\n";
    let m = module(text);
    let verdicts = harness_differential(&m, "f", func(&m, "f"));
    assert!(
        verdicts.iter().all(|v| matches!(
            v,
            InputVerdict::Compared {
                observed: Observed::Results
            }
        )),
        "{verdicts:?}"
    );
    let verdicts = harness_differential(&m, "g", func(&m, "g"));
    assert!(
        verdicts.iter().all(|v| matches!(
            v,
            InputVerdict::Compared {
                observed: Observed::Termination
            }
        )),
        "{verdicts:?}"
    );
}

/// A slot written at `i32` and read at `refine<ty.0, pred.0>`. The checkers
/// model no refinement: a value crosses one only where its type is
/// unchanged, so a forward or a copy root across it is refused.
const REFINED: &str = "type ty.0 = i32\n\npred pred.0 = top\n\n\
    functy.0 = (i32) -> (refine<ty.0, pred.0>)\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = alloca i32\n\
    \x20   store i32 %0, ptr %1\n\
    \x20   %2 = load refine<ty.0, pred.0>, ptr %1\n\
    \x20   ret %2\n\
    }\n";

#[test]
fn negative_control_a_forward_or_copy_across_a_refinement_is_refused() {
    let err = check_forward(REFINED, 2, 0, 0).unwrap_err();
    assert!(matches!(err, MidTvError::NotForwardable { .. }), "{err}");
    // The reverse: stored refined, read at the base type.
    let reverse = REFINED
        .replace(
            "(i32) -> (refine<ty.0, pred.0>)",
            "(refine<ty.0, pred.0>) -> (i32)",
        )
        .replace("bb0(%0: i32)", "bb0(%0: refine<ty.0, pred.0>)")
        .replace("store i32 %0", "store refine<ty.0, pred.0> %0")
        .replace("load refine<ty.0, pred.0>, ptr %1", "load i32, ptr %1");
    let err = check_forward(&reverse, 2, 0, 0).unwrap_err();
    assert!(matches!(err, MidTvError::NotForwardable { .. }), "{err}");
    // Control: the same slot read at the stored type forwards.
    let same = REFINED
        .replace("(i32) -> (refine<ty.0, pred.0>)", "(i32) -> (i32)")
        .replace("load refine<ty.0, pred.0>, ptr %1", "load i32, ptr %1");
    check_forward(&same, 2, 0, 0).unwrap_or_else(|e| panic!("{e}"));
    // A copy that adds the refinement is not forwarded to its bare root.
    let copied = "type ty.0 = i32\n\npred pred.0 = top\n\n\
        functy.0 = (i32) -> (refine<ty.0, pred.0>)\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = copy refine<ty.0, pred.0> %0\n\
        \x20   ret %1\n\
        }\n";
    let src = module(copied);
    let mut tgt = func(&src, "f").clone();
    tgt.blocks[0].body.remove(0);
    let Inst::Return { values } = &mut tgt.blocks[0].body[0].inst else {
        unreachable!()
    };
    values[0] = v(0);
    let err = check_pass(&src, 32, func(&src, "f"), &tgt, &forwards(&[(1, 0)])).unwrap_err();
    assert!(matches!(err, MidTvError::TypeChange { .. }), "{err}");
}
