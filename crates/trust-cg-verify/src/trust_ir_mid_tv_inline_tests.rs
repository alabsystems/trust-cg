// trust-cg-verify/trust_ir_mid_tv_inline_tests.rs - the inliner's checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker accepts an in-place splice of a one-block callee, a split
//! splice of a callee returning from two blocks (joined at the
//! continuation) and from one, an out-pointer callee writing the caller's
//! slot, a pointer argument of another pointer type bound through
//! `ptrtoptr`, and two sites in one block (each also agreeing with the source in
//! the reference interpreter and adding no trust-ir validation finding), and
//! refuses a named wrong one for each failure class (the negative controls):
//! a wrong argument binding (in the witness, and in the target alone), a
//! dropped effect, a duplicated non-idempotent call, an interposable or
//! link-once callee, a recursive callee, a callee a proof obligation names, a
//! renaming into a used value, an allocating callee in a loop, with a slot
//! in a loop of its own or in a recursive caller, slots past the byte bound, and a target with a dangling
//! edge. An array the rustc bridge passes and returns by address (a
//! closure's environment, its `Option` result in its own return slot) is
//! bound through loads of the pointee's bytes and spliced into a loop of
//! the caller, agreeing with the source in the differential's view; refused:
//! a missing or used returned-load name, the array bound to the pointer
//! itself or passed as an integer, a pointer returned for a non-array
//! return, a slot whose address escapes or that is not returned (in a
//! loop), and a binding load of another slot (which the view's run also
//! tells apart). `InlineSite::returned` is a provisional surface pending the
//! owner's sign-off (`docs/wasm32_perf_roadmap.md`, "Pending owner
//! sign-off").

use super::*;
use crate::trust_ir_mid_tv::{
    DifferentialBudget, PassWitness, check_pass, compare_samples, run_samples, seeded_inputs,
};
use trust_ir::proof::{ObligationKind, ProofObligation, ProofStatus};

const HEADER: &str = "; TrustIr text format v1\nmodule \"inline\"\n\
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

/// The site inlining the call at node `index` of block `block` of `caller`,
/// renaming into values from `vbase` and (split splice) blocks from `bbase`.
fn site(
    m: &Module,
    caller: &Function,
    block: u32,
    index: usize,
    split: bool,
    vbase: u32,
    bbase: u32,
) -> InlineSite {
    let node = &caller
        .blocks
        .iter()
        .find(|bl| bl.id == b(block))
        .expect("block")
        .body[index];
    let Inst::Call { callee, args } = &node.inst else {
        panic!("not a call");
    };
    let g = m.function_by_id(*callee).expect("callee");
    let entry = g.blocks.iter().find(|bl| bl.id == g.entry).unwrap();
    let params = entry
        .params
        .iter()
        .map(|(p, _)| *p)
        .zip(args.iter().copied())
        .collect();
    let mut next = vbase;
    let mut values = Vec::new();
    for bl in &g.blocks {
        let mut own: Vec<ValueId> = Vec::new();
        if bl.id != g.entry {
            own.extend(bl.params.iter().map(|(p, _)| *p));
        }
        own.extend(bl.body.iter().flat_map(|n| n.results.iter().copied()));
        for value in own {
            values.push((value, v(next)));
            next += 1;
        }
    }
    let (blocks, continuation) = if split {
        let blocks: Vec<(BlockId, BlockId)> = g
            .blocks
            .iter()
            .enumerate()
            .map(|(i, bl)| (bl.id, b(bbase + i as u32)))
            .collect();
        let cont = b(bbase + blocks.len() as u32);
        (blocks, Some(cont))
    } else {
        (Vec::new(), None)
    };
    InlineSite {
        block: b(block),
        index,
        callee: *callee,
        params,
        values,
        blocks,
        continuation,
        returned: Vec::new(),
    }
}

/// The checker's own rebuild of `sites` on `name`, then the full check of it.
fn check(m: &Module, name: &str, sites: Vec<InlineSite>) -> Result<Function, MidTvError> {
    let f = func(m, name);
    let witness = InlineWitness { sites };
    let (target, _) = apply_sites(m, f, &witness)?;
    let verdict = check_pass(m, 32, f, &target, &PassWitness::Inline(witness.clone()))?;
    assert_eq!(verdict.refinements, witness.rewrite_count());
    assert_eq!(verdict.exact, 0);
    Ok(target)
}

/// The target of the correct witness, for the negative controls to corrupt.
fn rebuilt(m: &Module, name: &str, sites: &[InlineSite]) -> Function {
    apply_sites(
        m,
        func(m, name),
        &InlineWitness {
            sites: sites.to_vec(),
        },
    )
    .expect("the correct witness rebuilds")
    .0
}

fn refused(m: &Module, name: &str, target: &Function, sites: Vec<InlineSite>) -> MidTvError {
    check_pass(
        m,
        32,
        func(m, name),
        target,
        &PassWitness::Inline(InlineWitness { sites }),
    )
    .expect_err("the checker must refuse")
}

/// No call of `callee` remains in `target`, trust-ir's validator finds
/// nothing new in it, and the source and the target agree on every seeded
/// input the interpreter finishes (at least one).
fn assert_inlined_and_equivalent(m: &Module, name: &str, target: &Function, callee: u32) {
    for node in target.blocks.iter().flat_map(|bl| &bl.body) {
        assert!(
            !matches!(node.inst, Inst::Call { callee: c, .. } if c == FuncId::new(callee)),
            "a call of the callee remains"
        );
    }
    let f = func(m, name);
    let mut tgt = m.clone();
    let position = tgt.functions.iter().position(|g| g.name == name).unwrap();
    tgt.functions[position] = target.clone();
    let findings = |m: &Module| -> Vec<String> {
        trust_ir_build::validate_module(m)
            .iter()
            .map(|e| format!("{e:?}"))
            .collect()
    };
    let before = findings(m);
    let new: Vec<String> = findings(&tgt)
        .into_iter()
        .filter(|e| !before.contains(e))
        .collect();
    assert!(new.is_empty(), "new validation findings: {new:?}");
    let inputs = seeded_inputs(m, f, 32, 16, 7).expect("synthesizable parameters");
    let budget = DifferentialBudget::default();
    let (source_runs, _) = run_samples(m, f, &inputs, budget);
    let (target_runs, _) = run_samples(&tgt, target, &inputs, budget);
    let report = compare_samples(&source_runs, &target_runs);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "{report:?}");
}

// ---------------------------------------------------------------------------
// Accepted splices
// ---------------------------------------------------------------------------

/// `f(a, b) = sq(b, a) - a` with `sq(x, y) = x * y + x`: the arguments are
/// passed swapped, so a wrong binding changes the result.
const SQ: &str = "functy.0 = (i32, i32) -> (i32)\n\n\
    fn @sq(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = mul i32 %0, %1\n\
    \x20   %3 = add i32 %2, %0\n\
    \x20   ret %3\n\
    }\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = call @func.0(%1, %0)\n\
    \x20   %3 = sub i32 %2, %0\n\
    \x20   ret %3\n\
    }\n";

#[test]
fn an_in_place_splice_of_a_one_block_callee_is_accepted() {
    let m = module(SQ);
    let f = func(&m, "f");
    let target = check(&m, "f", vec![site(&m, f, 0, 0, false, 10, 0)]).unwrap();
    assert_eq!(target.blocks.len(), 1, "an in-place splice keeps the CFG");
    assert_inlined_and_equivalent(&m, "f", &target, 0);
    // The same callee spliced by a split is accepted too.
    let target = check(&m, "f", vec![site(&m, f, 0, 0, true, 10, 1)]).unwrap();
    assert_eq!(target.blocks.len(), 3);
    assert_inlined_and_equivalent(&m, "f", &target, 0);
}

/// `pick` returns from two blocks: the results join at the continuation.
const PICK: &str = "functy.0 = (i32, i32) -> (i32)\n\n\
    fn @pick(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = icmp slt i32 %0, %1\n\
    \x20   condbr %2, bb1, bb2\n\
    bb1:\n\
    \x20   %3 = add i32 %0, %1\n\
    \x20   ret %3\n\
    bb2:\n\
    \x20   ret %1\n\
    }\n\n\
    fn @f(functy.0) {\n\
    bb0(%0: i32, %1: i32):\n\
    \x20   %2 = call @func.0(%0, %1)\n\
    \x20   %3 = mul i32 %2, %0\n\
    \x20   ret %3\n\
    }\n";

#[test]
fn a_callee_returning_from_two_blocks_joins_at_the_continuation() {
    let m = module(PICK);
    let f = func(&m, "f");
    let target = check(&m, "f", vec![site(&m, f, 0, 0, true, 10, 1)]).unwrap();
    let cont = target.blocks.last().unwrap();
    assert_eq!(cont.params, vec![(v(2), Ty::I32)], "the result is joined");
    assert_inlined_and_equivalent(&m, "f", &target, 0);
    // A multi-block callee cannot be spliced in place.
    let err = check(&m, "f", vec![site(&m, f, 0, 0, false, 10, 1)]).unwrap_err();
    assert!(matches!(err, MidTvError::NotInlinable { .. }), "{err}");
}

/// `bump` takes `&mut i32`; the caller passes its slot's `ptr`, as the rustc
/// bridge passes an `alloca` to a closure's environment reference.
const POINTER_KINDS: &str = "type ty.0 = i32\n\n\
    functy.0 = (&mut i32, i32) -> ()\n\
    functy.1 = (i32) -> (i32)\n\n\
    fn @bump(functy.0) {\n\
    bb0(%0: &mut i32, %1: i32):\n\
    \x20   %2 = load i32, ptr %0\n\
    \x20   %3 = add i32 %2, %1\n\
    \x20   store i32 %3, ptr %0\n\
    \x20   ret\n\
    }\n\n\
    fn @f(functy.1) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = alloca [ty.0 x 1], align 4\n\
    \x20   store i32 %0, ptr %1\n\
    \x20   call @func.0(%1, %0)\n\
    \x20   %2 = load i32, ptr %1\n\
    \x20   ret %2\n\
    }\n";

#[test]
fn a_pointer_of_another_pointer_type_is_bound_through_ptrtoptr() {
    let m = module(POINTER_KINDS);
    let f = func(&m, "f");
    let mut s = site(&m, f, 0, 2, false, 20, 0);
    // Bound directly, the `ptr` argument is not of the `&mut i32` type.
    let err = check(&m, "f", vec![s.clone()]).unwrap_err();
    assert!(matches!(err, MidTvError::WrongBinding { .. }), "{err}");
    s.params[0].1 = v(30);
    let target = check(&m, "f", vec![s.clone()]).unwrap();
    assert!(target.blocks[0].body.iter().any(|n| matches!(
        n.inst,
        Inst::Cast {
            op: CastOp::PtrToPtr,
            operand,
            ..
        } if operand == v(1)
    ) && n.results == vec![v(30)]));
    // The validator's call-argument finding goes with the call.
    let mut tgt = m.clone();
    tgt.functions[1] = target;
    let kinds = |m: &Module| {
        trust_ir_build::validate_module(m)
            .iter()
            .filter(|e| format!("{e:?}").starts_with("CallArgTypeMismatch"))
            .count()
    };
    assert_eq!((kinds(&m), kinds(&tgt)), (1, 0));
    // The cast's value must be fresh.
    s.params[0].1 = v(2);
    let err = check(&m, "f", vec![s]).unwrap_err();
    assert!(matches!(err, MidTvError::NotFresh { .. }), "{err}");
}

/// `init` writes its out-pointer; the caller's slot is read back after it.
const SRET: &str = "type ty.0 = i32\n\n\
    functy.0 = (ptr, i32) -> ()\n\
    functy.1 = (i32) -> (i32)\n\n\
    fn @init(functy.0) {\n\
    bb0(%0: ptr, %1: i32):\n\
    \x20   %2 = const i32 4\n\
    \x20   %3 = gep inbounds u8, ptr %0, %2\n\
    \x20   store i32 %1, ptr %0\n\
    \x20   %4 = add i32 %1, %1\n\
    \x20   store i32 %4, ptr %3\n\
    \x20   ret\n\
    }\n\n\
    fn @f(functy.1) {\n\
    bb0(%0: i32):\n\
    \x20   %1 = alloca [ty.0 x 2], align 4\n\
    \x20   call @func.0(%1, %0)\n\
    \x20   %2 = const i32 4\n\
    \x20   %3 = gep inbounds u8, ptr %1, %2\n\
    \x20   %4 = load i32, ptr %3\n\
    \x20   %5 = load i32, ptr %1\n\
    \x20   %6 = sub i32 %4, %5\n\
    \x20   ret %6\n\
    }\n";

#[test]
fn an_out_pointer_callee_writes_the_callers_slot() {
    let m = module(SRET);
    let f = func(&m, "f");
    let target = check(&m, "f", vec![site(&m, f, 0, 1, false, 20, 0)]).unwrap();
    // The stores now go through the caller's own slot.
    let stores = target
        .blocks
        .iter()
        .flat_map(|bl| &bl.body)
        .filter(|n| matches!(n.inst, Inst::Store { ptr, .. } if ptr == v(1)))
        .count();
    assert_eq!(stores, 1);
    assert_inlined_and_equivalent(&m, "f", &target, 0);
}

#[test]
fn two_sites_in_one_block_apply_in_order() {
    let text = "functy.0 = (i32, i32) -> (i32)\n\n\
        fn @pick(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = icmp slt i32 %0, %1\n\
        \x20   condbr %2, bb1, bb2\n\
        bb1:\n\
        \x20   ret %0\n\
        bb2:\n\
        \x20   ret %1\n\
        }\n\n\
        fn @sq(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = mul i32 %0, %1\n\
        \x20   ret %2\n\
        }\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = call @func.0(%0, %1)\n\
        \x20   %3 = call @func.1(%2, %1)\n\
        \x20   ret %3\n\
        }\n";
    let m = module(text);
    let f = func(&m, "f");
    let first = site(&m, f, 0, 0, true, 10, 1);
    let after_first = rebuilt(&m, "f", std::slice::from_ref(&first));
    // The second call now opens the continuation block.
    let cont = first.continuation.unwrap();
    let second = site(&m, &after_first, cont.index(), 0, false, 20, 0);
    let target = check(&m, "f", vec![first, second]).unwrap();
    assert_inlined_and_equivalent(&m, "f", &target, 0);
    assert_inlined_and_equivalent(&m, "f", &target, 1);
}

// ---------------------------------------------------------------------------
// Negative controls
// ---------------------------------------------------------------------------

#[test]
fn a_wrong_argument_binding_is_refused() {
    let m = module(SQ);
    let f = func(&m, "f");
    let good = site(&m, f, 0, 0, false, 10, 0);
    // In the witness: the parameters bound to the arguments the other way.
    let mut swapped = good.clone();
    swapped.params = vec![(v(0), v(0)), (v(1), v(1))];
    let target = rebuilt(&m, "f", std::slice::from_ref(&good));
    let err = refused(&m, "f", &target, vec![swapped]);
    assert!(matches!(err, MidTvError::WrongBinding { .. }), "{err}");
    // In the target alone: the cloned `add` reads the other argument.
    let mut wrong = target.clone();
    for node in &mut wrong.blocks[0].body {
        if let Inst::BinOp { rhs, .. } = &mut node.inst
            && *rhs == v(1)
        {
            *rhs = v(0);
        }
    }
    let err = refused(&m, "f", &wrong, vec![good]);
    assert!(matches!(err, MidTvError::TargetDiffers { .. }), "{err}");
}

/// `put` stores through its pointer and calls `tick` (a declaration whose
/// every call is an effect) before returning.
const EFFECTS: &str = "functy.0 = (ptr, i32) -> ()\n\
    functy.1 = () -> ()\n\
    functy.2 = (ptr, i32) -> ()\n\n\
    fn @tick(functy.1) {\n\
    }\n\n\
    fn @put(functy.0) {\n\
    bb0(%0: ptr, %1: i32):\n\
    \x20   store i32 %1, ptr %0\n\
    \x20   call @func.0()\n\
    \x20   ret\n\
    }\n\n\
    fn @f(functy.2) {\n\
    bb0(%0: ptr, %1: i32):\n\
    \x20   call @func.1(%0, %1)\n\
    \x20   ret\n\
    }\n";

#[test]
fn a_dropped_effect_is_refused() {
    let m = module(EFFECTS);
    let f = func(&m, "f");
    let good = site(&m, f, 0, 0, false, 10, 0);
    let target = check(&m, "f", vec![good.clone()]).unwrap();
    let mut dropped = target.clone();
    dropped.blocks[0]
        .body
        .retain(|n| !matches!(n.inst, Inst::Store { .. }));
    let err = refused(&m, "f", &dropped, vec![good]);
    assert!(
        matches!(&err, MidTvError::NotConserved { detail } if detail.contains("Store")),
        "{err}"
    );
}

#[test]
fn a_duplicated_non_idempotent_call_is_refused() {
    let m = module(EFFECTS);
    let f = func(&m, "f");
    let good = site(&m, f, 0, 0, false, 10, 0);
    let target = rebuilt(&m, "f", std::slice::from_ref(&good));
    let mut twice = target.clone();
    let at = twice.blocks[0]
        .body
        .iter()
        .position(|n| matches!(n.inst, Inst::Call { .. }))
        .expect("the cloned call of tick");
    let call = twice.blocks[0].body[at].clone();
    twice.blocks[0].body.insert(at, call);
    let err = refused(&m, "f", &twice, vec![good]);
    assert!(
        matches!(&err, MidTvError::NotConserved { detail } if detail.contains("Call")),
        "{err}"
    );
}

#[test]
fn an_interposable_or_link_once_callee_is_refused() {
    for linkage in [
        "weak",
        "linkonce",
        "linkonce_odr",
        "weak_odr",
        "external_weak",
    ] {
        let text = SQ.replace("fn @sq(", &format!("{linkage} fn @sq("));
        let m = module(&text);
        let f = func(&m, "f");
        let good = site(&m, f, 0, 0, false, 10, 0);
        let target = rebuilt(&module(SQ), "f", std::slice::from_ref(&good));
        let err = refused(&m, "f", &target, vec![good]);
        assert!(
            matches!(&err, MidTvError::NotInlinable { why, .. } if why.contains("replace")),
            "{linkage}: {err}"
        );
    }
}

#[test]
fn a_recursive_callee_is_refused() {
    let text = "functy.0 = (i32, i32) -> (i32)\n\n\
        fn @r(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = icmp slt i32 %0, %1\n\
        \x20   condbr %2, bb1, bb2\n\
        bb1:\n\
        \x20   %3 = call @func.0(%1, %0)\n\
        \x20   ret %3\n\
        bb2:\n\
        \x20   ret %0\n\
        }\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32, %1: i32):\n\
        \x20   %2 = call @func.0(%0, %1)\n\
        \x20   ret %2\n\
        }\n";
    let m = module(text);
    let f = func(&m, "f");
    let s = site(&m, f, 0, 0, true, 10, 1);
    let err = refused(&m, "f", f, vec![s]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { why, .. } if why.contains("recursive")),
        "{err}"
    );
}

#[test]
fn a_callee_a_proof_obligation_names_is_refused() {
    let mut m = module(SQ);
    m.proof_obligations.push(ProofObligation::new(
        trust_ir::value::ProofId::new(0),
        ObligationKind::MemorySafety,
        ProofStatus::Pending,
        "names the callee",
    ));
    m.proof_obligations[0].function = Some(FuncId::new(0));
    let f = func(&m, "f");
    let good = site(&m, f, 0, 0, false, 10, 0);
    let target = rebuilt(&module(SQ), "f", std::slice::from_ref(&good));
    let err = refused(&m, "f", &target, vec![good]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { why, .. } if why.contains("obligation")),
        "{err}"
    );
}

#[test]
fn a_renaming_into_a_used_value_is_refused() {
    let m = module(SQ);
    let f = func(&m, "f");
    // Values from %3 on collide with the caller's %3.
    let s = site(&m, f, 0, 0, false, 3, 0);
    let err = refused(&m, "f", f, vec![s]);
    assert!(matches!(err, MidTvError::NotFresh { .. }), "{err}");
}

#[test]
fn an_allocating_callee_is_not_spliced_into_a_loop() {
    let text = "type ty.0 = i32\n\n\
        functy.0 = (i32) -> (i32)\n\n\
        fn @tmp(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   %1 = alloca [ty.0 x 1], align 4\n\
        \x20   store i32 %0, ptr %1\n\
        \x20   %2 = load i32, ptr %1\n\
        \x20   ret %2\n\
        }\n\n\
        fn @f(functy.0) {\n\
        bb0(%0: i32):\n\
        \x20   br bb1(%0)\n\
        bb1(%1: i32):\n\
        \x20   %2 = call @func.0(%1)\n\
        \x20   %3 = const i32 1\n\
        \x20   %4 = sub i32 %2, %3\n\
        \x20   %5 = const i32 0\n\
        \x20   %6 = icmp sgt i32 %4, %5\n\
        \x20   condbr %6, bb1(%4), bb2\n\
        bb2:\n\
        \x20   ret %4\n\
        }\n";
    let m = module(text);
    let f = func(&m, "f");
    let s = site(&m, f, 1, 0, false, 10, 0);
    let err = refused(&m, "f", f, vec![s]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { why, .. } if why.contains("cycle")),
        "{err}"
    );
}

/// A callee `@lp` counting `%0` down in a loop through a slot, made in the
/// loop (`in_loop`) or once in its entry, called once from `@f`.
fn looping_slot_module(in_loop: bool) -> Module {
    let (entry_slot, loop_slot) = if in_loop {
        ("", "\x20   %2 = alloca [ty.0 x 4], align 4\n")
    } else {
        ("\x20   %2 = alloca [ty.0 x 4], align 4\n", "")
    };
    module(&format!(
        "type ty.0 = i32\n\n\
         functy.0 = (i32) -> (i32)\n\n\
         fn @lp(functy.0) {{\n\
         bb0(%0: i32):\n\
         {entry_slot}\
         \x20   br bb1(%0)\n\
         bb1(%1: i32):\n\
         {loop_slot}\
         \x20   store i32 %1, ptr %2\n\
         \x20   %3 = load i32, ptr %2\n\
         \x20   %4 = const i32 1\n\
         \x20   %5 = sub i32 %3, %4\n\
         \x20   %6 = const i32 0\n\
         \x20   %7 = icmp sgt i32 %5, %6\n\
         \x20   condbr %7, bb1(%5), bb2\n\
         bb2:\n\
         \x20   ret %5\n\
         }}\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: i32):\n\
         \x20   %1 = call @func.0(%0)\n\
         \x20   ret %1\n\
         }}\n"
    ))
}

#[test]
fn an_allocating_callee_is_not_spliced_when_its_slot_is_in_its_own_loop() {
    // The call's block is on no cycle of `f`, but the splice would put the
    // callee's loop, and the slot made in it, on a cycle of `f`: carved per
    // iteration and held until `f` returns.
    let m = looping_slot_module(true);
    let f = func(&m, "f");
    let s = site(&m, f, 0, 0, true, 10, 1);
    let err = refused(&m, "f", f, vec![s]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { why, .. }
            if why.contains("allocates on a cycle of its own")),
        "{err}"
    );
    // The same loop over a slot made once, in the callee's entry, is accepted.
    let m = looping_slot_module(false);
    let f = func(&m, "f");
    let s = site(&m, f, 0, 0, true, 10, 1);
    let target = check(&m, "f", vec![s]).expect("a slot made outside the loop is spliced");
    assert_inlined_and_equivalent(&m, "f", &target, 0);
}

/// A callee with a slot of `words` 32-bit words.
fn slot_callee(words: usize) -> String {
    format!(
        "type ty.0 = i32\n\n\
         functy.0 = (i32) -> (i32)\n\n\
         fn @tmp(functy.0) {{\n\
         bb0(%0: i32):\n\
         \x20   %1 = alloca [ty.0 x {words}], align 4\n\
         \x20   store i32 %0, ptr %1\n\
         \x20   %2 = load i32, ptr %1\n\
         \x20   ret %2\n\
         }}\n\n"
    )
}

#[test]
fn an_allocating_callee_is_not_spliced_into_a_recursive_caller() {
    // `f` reaches itself; the call of `tmp` is on its base path only, yet a
    // spliced slot would be held by every level of the recursion.
    let recursive = format!(
        "{}fn @f(functy.0) {{\n\
         bb0(%0: i32):\n\
         \x20   %1 = const i32 0\n\
         \x20   %2 = icmp sgt i32 %0, %1\n\
         \x20   condbr %2, bb1, bb2\n\
         bb1:\n\
         \x20   %3 = const i32 1\n\
         \x20   %4 = sub i32 %0, %3\n\
         \x20   %5 = call @func.1(%4)\n\
         \x20   ret %5\n\
         bb2:\n\
         \x20   %6 = call @func.0(%0)\n\
         \x20   ret %6\n\
         }}\n",
        slot_callee(1)
    );
    let m = module(&recursive);
    let f = func(&m, "f");
    let s = site(&m, f, 2, 0, false, 10, 0);
    let err = refused(&m, "f", f, vec![s]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { why, .. } if why.contains("reaches itself")),
        "{err}"
    );
    // The same callee into a caller that does not recur is accepted.
    let plain = format!(
        "{}fn @f(functy.0) {{\n\
         bb0(%0: i32):\n\
         \x20   %1 = call @func.0(%0)\n\
         \x20   ret %1\n\
         }}\n",
        slot_callee(1)
    );
    let m = module(&plain);
    let f = func(&m, "f");
    let s = site(&m, f, 0, 0, false, 10, 0);
    let target = check(&m, "f", vec![s]).expect("a non-recursive caller takes the slot");
    assert_inlined_and_equivalent(&m, "f", &target, 0);
}

#[test]
fn slots_past_the_byte_bound_are_refused() {
    let two_sites = |words: usize| {
        module(&format!(
            "{}fn @f(functy.0) {{\n\
             bb0(%0: i32):\n\
             \x20   %1 = call @func.0(%0)\n\
             \x20   %2 = call @func.0(%1)\n\
             \x20   ret %2\n\
             }}\n",
            slot_callee(words)
        ))
    };
    let words = usize::try_from(MAX_SPLICED_SLOT_BYTES / 4).unwrap();
    // Exactly the bound in one site: accepted.
    let m = two_sites(words);
    let f = func(&m, "f");
    let first = site(&m, f, 0, 0, false, 10, 0);
    check(&m, "f", vec![first.clone()]).expect("a slot of exactly the bound is accepted");
    // One word more: refused.
    let m = two_sites(words + 1);
    let f = func(&m, "f");
    let over = site(&m, f, 0, 0, false, 10, 0);
    let err = refused(&m, "f", f, vec![over]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { why, .. } if why.contains("over")),
        "{err}"
    );
    // Two sites of half the bound and one word: the first fits, the second
    // passes the bound across the witness.
    let m = two_sites(words / 2 + 1);
    let f = func(&m, "f");
    let first = site(&m, f, 0, 0, false, 10, 0);
    let after_first = rebuilt(&m, "f", std::slice::from_ref(&first));
    let second = site(&m, &after_first, 0, 4, false, 20, 0);
    check(&m, "f", vec![first.clone()]).expect("one site fits");
    let err = refused(&m, "f", f, vec![first, second]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { site: 1, why } if why.contains("over")),
        "{err}"
    );
}

#[test]
fn a_target_with_a_dangling_edge_is_refused() {
    let m = module(PICK);
    let f = func(&m, "f");
    let good = site(&m, f, 0, 0, true, 10, 1);
    let mut target = rebuilt(&m, "f", std::slice::from_ref(&good));
    if let Some(Inst::Br { target: t, .. }) = target.blocks[0].body.last_mut().map(|n| &mut n.inst)
    {
        *t = b(99);
    }
    let err = refused(&m, "f", &target, vec![good]);
    assert!(matches!(err, MidTvError::MalformedCfg { .. }), "{err}");
}

// ---------------------------------------------------------------------------
// Arrays passed and returned by address (round 17 stage B)
// ---------------------------------------------------------------------------

/// A closure's environment `[u32 x 1]` passed by the address of a caller's
/// slot, and its `Option<u8>`-like `[u8 x 1]` result returned by the
/// address of its own slot (`ret %2`), called in a loop of the caller as
/// the rustc bridge spells `Iterator::find`'s predicate. `{callee}` is the
/// closure's body after its slot.
fn by_address(callee: &str, env_arg: &str) -> Module {
    module(&format!(
        "type ty.0 = u32\ntype ty.1 = u8\n\n\
         functy.0 = ([ty.0 x 1], u32) -> ([ty.1 x 1])\n\
         functy.1 = (u32, u32) -> (u32)\n\n\
         fn @clo(functy.0) {{\n\
         bb0(%0: [ty.0 x 1], %1: u32):\n\
         \x20   %2 = alloca [ty.1 x 1], align 1\n\
         {callee}\
         }}\n\n\
         fn @f(functy.1) {{\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = alloca [ty.0 x 1], align 4\n\
         \x20   store u32 %0, ptr %2\n\
         \x20   %20 = alloca [ty.0 x 1], align 4\n\
         \x20   store u32 %1, ptr %20\n\
         \x20   %3 = const u32 0\n\
         \x20   br bb1(%3, %3)\n\
         bb1(%4: u32, %5: u32):\n\
         \x20   %6 = call @func.0({env_arg}, %4)\n\
         \x20   %7 = extractfield [ty.1 x 1] %6, 0\n\
         \x20   %8 = zext u8 %7 to u32\n\
         \x20   %9 = add u32 %5, %8\n\
         \x20   %10 = const u32 1\n\
         \x20   %11 = add u32 %4, %10\n\
         \x20   %12 = const u32 4\n\
         \x20   %13 = icmp ult u32 %11, %12\n\
         \x20   condbr %13, bb1(%11, %9), bb2\n\
         bb2:\n\
         \x20   ret %9\n\
         }}\n"
    ))
}

/// The closure's body: the environment's lane plus the argument, stored
/// into its result slot, returned by address.
const CLOSURE: &str = "\x20   %3 = extractfield [ty.0 x 1] %0, 0\n\
    \x20   %4 = add u32 %3, %1\n\
    \x20   %5 = trunc u32 %4 to u8\n\
    \x20   store u8 %5, ptr %2\n\
    \x20   ret %2\n";

/// The in-place site of the call in `bb1` with the environment bound to
/// the fresh load `%30` and the result loaded into `%31`.
fn by_address_site(m: &Module) -> InlineSite {
    let f = func(m, "f");
    let mut s = site(m, f, 1, 0, false, 40, 0);
    s.params[0].1 = v(30);
    s.returned = vec![v(31)];
    s
}

/// The source and `target` run in the differential's view (the bridge's
/// by-address aggregates read as the pointee's bytes), on every seeded
/// input: they agree, and at least one input is compared.
fn assert_agrees_in_the_view(m: &Module, target: &Function) {
    let f = func(m, "f");
    let mut tgt = m.clone();
    let at = tgt.functions.iter().position(|g| g.name == "f").unwrap();
    tgt.functions[at] = target.clone();
    let inputs = seeded_inputs(m, f, 32, 16, 7).expect("scalar parameters");
    let budget = DifferentialBudget::default();
    let run = |module: &Module, func: &Function| {
        let view = crate::trust_ir_mid_tv::interpretable_module(module);
        let viewed =
            crate::trust_ir_mid_tv::interpretable(&view, func).unwrap_or_else(|| func.clone());
        run_samples(&view, &viewed, &inputs, budget).0
    };
    let report = compare_samples(&run(m, f), &run(&tgt, target));
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "{report:?}");
}

#[test]
fn an_array_passed_and_returned_by_address_is_bound_through_loads_in_a_loop() {
    let m = by_address(CLOSURE, "%2");
    let s = by_address_site(&m);
    // The callee's only slot is its return slot: spliced into the loop.
    let target = check(&m, "f", vec![s]).expect("accepted");
    let body = &target.blocks[1].body;
    assert!(body.iter().any(|n| n.results == [v(30)]
        && matches!(&n.inst, Inst::Load { ty: Ty::Array(..), ptr, align: Some(1), .. } if *ptr == v(2))));
    let ret_load = body
        .iter()
        .position(|n| n.results == [v(31)])
        .expect("the returned slot is loaded");
    assert!(matches!(
        &body[ret_load].inst,
        Inst::Load {
            ty: Ty::Array(..),
            ..
        }
    ));
    assert_eq!(
        body[ret_load + 1].inst,
        Inst::Copy {
            ty: m.func_type(func(&m, "clo").ty).unwrap().returns[0].clone(),
            operand: v(31)
        }
    );
    assert_eq!(body[ret_load + 1].results, vec![v(6)]);
    assert!(
        !body.iter().any(|n| matches!(n.inst, Inst::Call { .. })),
        "the call is gone"
    );
    assert_agrees_in_the_view(&m, &target);
}

#[test]
fn by_address_bindings_off_the_form_are_refused() {
    let m = by_address(CLOSURE, "%2");
    let f = func(&m, "f");
    // No load named for the returned slot.
    let mut s = by_address_site(&m);
    s.returned.clear();
    let err = refused(&m, "f", f, vec![s]);
    assert!(matches!(err, MidTvError::WrongBinding { .. }), "{err}");
    // A returned load that is not fresh.
    let mut s = by_address_site(&m);
    s.returned = vec![v(9)];
    let err = refused(&m, "f", f, vec![s]);
    assert!(matches!(err, MidTvError::NotFresh { .. }), "{err}");
    // The environment bound directly to the pointer (no load).
    let mut s = by_address_site(&m);
    s.params[0].1 = v(2);
    let err = refused(&m, "f", f, vec![s]);
    assert!(matches!(err, MidTvError::WrongBinding { .. }), "{err}");
    // An integer where the array is passed: no load binds it.
    let m2 = by_address(CLOSURE, "%0");
    let f2 = func(&m2, "f");
    let err = refused(&m2, "f", f2, vec![by_address_site(&m2)]);
    assert!(matches!(err, MidTvError::WrongBinding { .. }), "{err}");
    // A pointer returned where the declared return is not an array.
    let m3 = module(
        "functy.0 = (u32) -> (u32)\nfuncty.1 = (u32) -> (u32)\n\n\
         fn @g(functy.0) {\n\
         bb0(%0: u32):\n\
         \x20   %1 = alloca u32\n\
         \x20   store u32 %0, ptr %1\n\
         \x20   ret %1\n\
         }\n\n\
         fn @f(functy.1) {\n\
         bb0(%0: u32):\n\
         \x20   %1 = call @func.0(%0)\n\
         \x20   ret %1\n\
         }\n",
    );
    let f3 = func(&m3, "f");
    let mut s = site(&m3, f3, 0, 0, false, 10, 0);
    s.returned = vec![v(20)];
    let err = refused(&m3, "f", f3, vec![s]);
    assert!(matches!(err, MidTvError::NotInlinable { .. }), "{err}");
}

#[test]
fn a_slot_that_is_not_only_a_return_slot_stays_out_of_loops() {
    // The slot's address is also stored (it escapes): not a return slot.
    let escapes = "\x20   %3 = extractfield [ty.0 x 1] %0, 0\n\
        \x20   %4 = add u32 %3, %1\n\
        \x20   %5 = trunc u32 %4 to u8\n\
        \x20   store u8 %5, ptr %2\n\
        \x20   %6 = alloca ptr\n\
        \x20   store ptr %2, ptr %6\n\
        \x20   ret %2\n";
    let m = by_address(escapes, "%2");
    let f = func(&m, "f");
    let err = refused(&m, "f", f, vec![by_address_site(&m)]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { why, .. } if why.contains("return slot")),
        "{err}"
    );
    // A slot the callee does not return (read back as a value).
    let unreturned = "functy.0 = (u32) -> (u32)\n\
        functy.1 = (u32) -> (u32)\n\n\
        fn @g(functy.0) {\n\
        bb0(%0: u32):\n\
        \x20   %1 = alloca u32\n\
        \x20   store u32 %0, ptr %1\n\
        \x20   %2 = load u32, ptr %1\n\
        \x20   ret %2\n\
        }\n\n\
        fn @f(functy.1) {\n\
        bb0(%0: u32):\n\
        \x20   br bb1(%0)\n\
        bb1(%1: u32):\n\
        \x20   %2 = call @func.0(%1)\n\
        \x20   %3 = const u32 1\n\
        \x20   %4 = icmp ugt u32 %2, %3\n\
        \x20   %5 = sub u32 %2, %3\n\
        \x20   condbr %4, bb1(%5), bb2\n\
        bb2:\n\
        \x20   ret %2\n\
        }\n";
    let m = module(unreturned);
    let f = func(&m, "f");
    let err = refused(&m, "f", f, vec![site(&m, f, 1, 0, false, 10, 0)]);
    assert!(
        matches!(&err, MidTvError::NotInlinable { why, .. } if why.contains("return slot")),
        "{err}"
    );
}

#[test]
fn a_binding_load_of_another_slot_is_refused_and_disagrees() {
    let m = by_address(CLOSURE, "%2");
    let s = by_address_site(&m);
    let mut target = rebuilt(&m, "f", std::slice::from_ref(&s));
    // The environment loaded from the caller's other slot (`%20`).
    for node in target.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if node.results == [v(30)]
            && let Inst::Load { ptr, .. } = &mut node.inst
        {
            *ptr = v(20);
        }
    }
    let err = refused(&m, "f", &target, vec![s]);
    assert!(matches!(err, MidTvError::TargetDiffers { .. }), "{err}");
    let f = func(&m, "f");
    let mut tgt = m.clone();
    let at = tgt.functions.iter().position(|g| g.name == "f").unwrap();
    tgt.functions[at] = target.clone();
    let inputs = seeded_inputs(&m, f, 32, 16, 7).expect("scalar parameters");
    let budget = DifferentialBudget::default();
    let run = |module: &Module, func: &Function| {
        let view = crate::trust_ir_mid_tv::interpretable_module(module);
        let viewed =
            crate::trust_ir_mid_tv::interpretable(&view, func).unwrap_or_else(|| func.clone());
        run_samples(&view, &viewed, &inputs, budget).0
    };
    assert!(
        compare_samples(&run(&m, f), &run(&tgt, &target))
            .mismatch
            .is_some()
    );
}

#[test]
fn a_typed_return_slot_is_inlined_in_a_loop_only_for_fixed_scalar_readers() {
    let text = r#"
type ty.0 = u32
type ty.1 = u8
functy.0 = ([ty.0 x 1], u32) -> ([ty.1 x 1])
functy.1 = (u32, u32) -> (u32)
fn @clo(functy.0) {
bb0(%0: [ty.0 x 1], %1: u32):
    %2 = alloca [ty.1 x 1], align 1
    %3 = const usize 0
    %4 = extractelement u32 %0, %3
    %5 = add u32 %4, %1
    %6 = trunc u32 %5 to u8
    store u8 %6, ptr %2
    %7 = load [ty.1 x 1], ptr %2
    ret %7
}
fn @f(functy.1) {
bb0(%0: u32, %1: u32):
    %2 = alloca [ty.0 x 1], align 4
    store u32 %0, ptr %2
    %3 = const u32 0
    br bb1(%3, %3)
bb1(%4: u32, %5: u32):
    %20 = load [ty.0 x 1], ptr %2
    %6 = call @func.0(%20, %4)
    %21 = const usize 0
    %7 = extractelement u8 %6, %21
    %8 = zext u8 %7 to u32
    %9 = add u32 %5, %8
    %10 = const u32 1
    %11 = add u32 %4, %10
    %12 = const u32 4
    %13 = icmp ult u32 %11, %12
    condbr %13, bb1(%11, %9), bb2
bb2:
    ret %9
}
"#;
    let m = module(text);
    assert!(trust_ir_build::validate_module(&m).is_empty());
    let claim = |m: &Module| site(m, func(m, "f"), 1, 1, false, 40, 0);
    let target = check(&m, "f", vec![claim(&m)]).expect("typed return snapshot");
    let mut out = m.clone();
    out.functions[1] = target.clone();
    assert!(trust_ir_build::validate_module(&out).is_empty());
    assert_agrees_in_the_view(&m, &target);
    // A nested aggregate is valid IR, but it is outside this fixed-scalar
    // return-slot rule. Its element could carry an aggregate past reuse.
    let nested = text
        .replace("type ty.1 = u8", "type ty.1 = u8\ntype ty.2 = [ty.1 x 1]")
        .replace("-> ([ty.1 x 1])", "-> ([ty.2 x 1])")
        .replace("%2 = alloca [ty.1 x 1]", "%2 = alloca [ty.2 x 1]")
        .replace("%7 = load [ty.1 x 1]", "%7 = load [ty.2 x 1]")
        .replace(
            "%7 = extractelement u8 %6",
            "%7 = extractelement [ty.1 x 1] %6",
        )
        .replace(
            "%8 = zext u8 %7",
            "%22 = extractelement u8 %7, %21\n    %8 = zext u8 %22",
        );
    let nested = module(&nested);
    assert!(trust_ir_build::validate_module(&nested).is_empty());
    assert!(check(&nested, "f", vec![claim(&nested)]).is_err());
    for bad in [
        text.replace("%7 = load [ty.1 x 1]", "%7 = volatile load [ty.1 x 1]"),
        text.replace(
            "    ret %7",
            "    %30 = alloca ptr\n    store ptr %2, ptr %30\n    ret %7",
        ),
        text.replace(
            "    %21 = const usize 0",
            "    store [ty.1 x 1] %6, ptr %2\n    %21 = const usize 0",
        ),
        text.replace(
            "    %21 = const usize 0",
            "    %22 = const usize 0\n    %21 = copy usize %22",
        ),
    ] {
        let bad = module(&bad);
        assert!(check(&bad, "f", vec![claim(&bad)]).is_err());
    }
}
