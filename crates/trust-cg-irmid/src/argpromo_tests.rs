// trust-cg-irmid/argpromo_tests.rs - argument promotion and its refusals
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Argument promotion (`passes/argpromo.rs`): the pass alone, its witness
//! against the independent checker, the pipeline (the caller's and the
//! clone's slots dissolve), the reference interpreter on the input and the
//! output, and each refusal by name (an array passed by address with a lane
//! the caller may not have written, a call carrying proof material, and a
//! parameter the clone would keep with an entry type other than its
//! declared one, included).
//!
//! The witness types (`ArgPromoWitness` and its elements) and
//! `PassWitness::function_additions` are new provisional surfaces pending
//! the owner's sign-off: this test follows them if they change.

use std::collections::BTreeSet;

use trust_cg_verify::trust_ir_mid_tv::{
    ARGPROMO_CLONE_MARK, ArgPromoField, ArgPromoWitness, PassWitness, check_pass,
};
use trust_ir::{
    Function, Inst, InterpretOptions, InterpretValue, InterpretValueKind, Interpreter, Module, Ty,
};

use crate::passes::{self, MidPass, PassContext};
use crate::{MidConfig, optimize_module};

const HEADER: &str = "; TrustIr text format v1\nmodule \"argpromo\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n\
                      type ty.0 = i32\n\n\
                      functy.0 = (ptr, ptr) -> ()\n\
                      functy.1 = (i32, i32) -> (i32)\n\n";

const CALLEE: &str = "pair.tcg.crate.00000000000000aa";

/// `pair` reads two `i32` fields through its second parameter and writes
/// their sum and product through its first; `f` passes two slots. `callee`
/// is `pair`'s body after its entry label, `caller` `f`'s.
fn program(name: &str, callee: &str, caller: &str) -> Module {
    let text = format!(
        "{HEADER}fn @{name}(functy.0) {{\n    ; #visibility: hidden\nbb0(%0: ptr, %1: ptr):\n\
         {callee}}}\n\nfn @f(functy.1) {{\nbb0(%0: i32, %1: i32):\n{caller}}}\n"
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("the test module does not parse: {e}\n{text}"))
}

const PAIR: &str = "    %2 = load i32, ptr %1\n    %3 = const i32 4\n    \
                    %4 = gep inbounds u8, ptr %1, %3\n    %5 = load i32, ptr %4\n    \
                    %6 = add i32 %2, %5\n    %7 = mul i32 %2, %5\n    \
                    store i32 %6, ptr %0\n    %8 = gep inbounds u8, ptr %0, %3\n    \
                    store i32 %7, ptr %8\n    ret\n";

const F: &str = "    %2 = alloca [ty.0 x 2], align 4\n    %3 = alloca [ty.0 x 2], align 4\n    \
                 store i32 %0, ptr %2\n    %4 = const i32 4\n    \
                 %5 = gep inbounds u8, ptr %2, %4\n    store i32 %1, ptr %5\n    \
                 call @func.0(%3, %2)\n    %6 = load i32, ptr %3\n    \
                 %7 = gep inbounds u8, ptr %3, %4\n    %8 = load i32, ptr %7\n    \
                 %9 = sub i32 %6, %8\n    ret %9\n";

fn func<'m>(module: &'m Module, name: &str) -> &'m Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .unwrap_or_else(|| panic!("no function {name}"))
}

fn promote(m: &Module) -> Option<(Function, ArgPromoWitness)> {
    let cx = PassContext {
        module: m,
        pointer_bits: 32,
    };
    let (out, witness) = passes::ArgPromo::new(BTreeSet::new()).run(&cx, func(m, "f"))?;
    let PassWitness::ArgPromo(w) = witness else {
        panic!("an argument-promotion witness");
    };
    Some((out, w))
}

fn allocas(f: &Function) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| matches!(n.inst, Inst::Alloca { .. }))
        .count()
}

fn interpret(m: &Module, a: i64, b: i64) -> Option<i64> {
    let f = m.function_by_name("f").expect("f");
    let args = [a, b].map(|v| InterpretValue::int(Ty::I32, i128::from(v)).expect("i32"));
    let out = Interpreter::with_module(m)
        .with_options(InterpretOptions {
            fuel: 100_000,
            max_call_depth: 16,
            panic_strategy: trust_ir::interpret::PanicStrategy::Abort,
        })
        .execute_func(f.id, args)
        .ok()?;
    match &out.returns[0].kind {
        InterpretValueKind::Int(i) => Some(i.as_signed() as i64),
        other => panic!("f returned {other:?}"),
    }
}

fn field(offset: u64) -> ArgPromoField {
    ArgPromoField {
        offset,
        ty: Ty::I32,
    }
}

/// `MidConfig::wasm32` with `pair` left called by the inliner.
fn config() -> MidConfig {
    MidConfig {
        never_inline: BTreeSet::from([CALLEE.to_string()]),
        ..MidConfig::wasm32()
    }
}

#[test]
fn both_slots_are_passed_by_value_and_checked() {
    let m = program(CALLEE, PAIR, F);
    let (out, w) = promote(&m).expect("the call is promoted");
    assert_eq!(w.sites.len(), 1);
    let site = &w.sites[0];
    assert_eq!(site.params.len(), 2);
    assert_eq!(
        (&site.params[0].reads, &site.params[0].writes),
        (&vec![], &vec![field(0), field(4)]),
        "the out-pointer is copied out"
    );
    assert_eq!(
        (&site.params[1].reads, &site.params[1].writes),
        (&vec![field(0), field(4)], &vec![]),
        "the read-only pointer is copied in"
    );
    assert_eq!(w.new_functions.len(), 1);
    assert_eq!(w.new_func_types.len(), 1);
    let clone = &w.new_functions[0];
    assert!(clone.name.contains(ARGPROMO_CLONE_MARK), "{}", clone.name);
    assert!(clone.name.ends_with(".tcg.crate.00000000000000aa"));
    assert_eq!(
        w.new_func_types[0].params,
        vec![Ty::I32, Ty::I32],
        "the read fields"
    );
    assert_eq!(
        w.new_func_types[0].returns,
        vec![Ty::I32, Ty::I32],
        "the written fields"
    );
    check_pass(
        &m,
        32,
        func(&m, "f"),
        &out,
        &PassWitness::ArgPromo(w.clone()),
    )
    .expect("the checker accepts the promotion");

    // The pipeline: both slots of `f` and the clone's copy dissolve.
    let (opt, report) = optimize_module(&m, &config());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(opt.functions.len(), 3, "one clone is appended");
    let f = func(&opt, "f");
    assert_eq!(allocas(f), 0, "{f:#?}");
    let clone = opt
        .functions
        .iter()
        .find(|f| f.name.contains(ARGPROMO_CLONE_MARK))
        .expect("the clone");
    assert_eq!(allocas(clone), 0, "{clone:#?}");
    assert_eq!(allocas(func(&opt, CALLEE)), 0);
    let changed = report
        .passes
        .iter()
        .find(|p| p.name == "argpromo")
        .map_or(0, |p| p.functions_changed);
    assert_eq!(changed, 1);
    for (a, b) in [(3, 4), (-7, 9), (i32::MAX as i64, 2), (0, 0)] {
        let want = interpret(&m, a, b).expect("the input runs");
        assert_eq!(interpret(&opt, a, b), Some(want), "f({a}, {b})");
    }
}

#[test]
fn a_switched_off_pass_is_named_withheld() {
    let m = program(CALLEE, PAIR, F);
    let (opt, report) = optimize_module(
        &m,
        &MidConfig {
            arg_promotion: false,
            ..config()
        },
    );
    assert_eq!(opt.functions.len(), 2);
    assert!(report.passes_withheld.contains_key("argpromo"));
}

/// The caller stores only the first read field: the second may be poison at
/// the call, so the read-only parameter stays a pointer (the out-pointer is
/// still promoted).
#[test]
fn refusal_a_copied_in_field_the_caller_may_not_have_written() {
    let caller = F.replace("    store i32 %1, ptr %5\n", "");
    let m = program(CALLEE, PAIR, &caller);
    let (_, w) = promote(&m).expect("the out-pointer is promoted");
    let indices: Vec<usize> = w.sites[0].params.iter().map(|p| p.index).collect();
    assert_eq!(indices, vec![0]);
}

/// A copied-in value that may be poison: a load's result stored into the
/// slot.
#[test]
fn refusal_a_copied_in_field_written_with_a_maybe_poison_value() {
    let caller = F.replace(
        "    store i32 %1, ptr %5\n",
        "    %20 = load i32, ptr %3\n    store i32 %20, ptr %5\n",
    );
    let m = program(CALLEE, PAIR, &caller);
    let (_, w) = promote(&m).expect("the out-pointer is promoted");
    assert_eq!(w.sites[0].params.len(), 1);
    assert_eq!(w.sites[0].params[0].index, 0);
}

/// The callee writes its second output field on one path only: the field
/// returned may be poison at the other `ret`, so the out-pointer stays.
#[test]
fn refusal_a_copied_out_field_the_callee_may_not_write() {
    let callee = "    %2 = load i32, ptr %1\n    %3 = const i32 4\n    \
                  %4 = gep inbounds u8, ptr %1, %3\n    %5 = load i32, ptr %4\n    \
                  %6 = add i32 %2, %5\n    store i32 %6, ptr %0\n    \
                  %9 = icmp slt i32 %2, %5\n    condbr %9, bb1, bb2\n\
                  bb1:\n    %8 = gep inbounds u8, ptr %0, %3\n    store i32 %5, ptr %8\n    ret\n\
                  bb2:\n    ret\n";
    let m = program(CALLEE, callee, F);
    let (_, w) = promote(&m).expect("the read-only pointer is promoted");
    let indices: Vec<usize> = w.sites[0].params.iter().map(|p| p.index).collect();
    assert_eq!(indices, vec![1]);
}

/// Every refusal that leaves the call alone.
#[test]
fn refusals_that_leave_the_call() {
    // The callee is not a crate-private name: its clone's name would not be
    // unique to this object.
    let m = program("pair", PAIR, F);
    assert!(
        promote(&m).is_none(),
        "a name without the crate-private mark"
    );
    // The callee hands its read-only parameter on: only the out-pointer is
    // promoted.
    let escaping = PAIR.replace("    ret\n", "    call @func.0(%1, %1)\n    ret\n");
    let m = program(CALLEE, &escaping, F);
    let (_, w) = promote(&m).expect("the out-pointer alone");
    assert!(
        w.sites[0].params.iter().all(|p| p.index != 1),
        "the callee passes the address on"
    );
    // The callee observes the address.
    let observed = PAIR.replace(
        "    ret\n",
        "    %30 = ptrtoint ptr %1 to i32\n    store i32 %30, ptr %0\n    ret\n",
    );
    let m = program(CALLEE, &observed, F);
    let (_, w) = promote(&m).expect("the out-pointer alone");
    assert!(w.sites[0].params.iter().all(|p| p.index != 1));
    // The caller's slot escapes elsewhere: an integer view of its address.
    let leaked = F.replace(
        "    %9 = sub i32 %6, %8\n",
        "    %20 = ptrtoint ptr %2 to i32\n    %21 = ptrtoint ptr %3 to i32\n    \
         %22 = add i32 %20, %21\n    %9 = sub i32 %6, %22\n",
    );
    let m = program(CALLEE, PAIR, &leaked);
    assert!(promote(&m).is_none(), "the slots' addresses are observed");
    // Both arguments are the same slot: the callee could read what it wrote.
    let aliased = F.replace("call @func.0(%3, %2)", "call @func.0(%2, %2)");
    let m = program(CALLEE, PAIR, &aliased);
    assert!(promote(&m).is_none(), "two arguments derived from one slot");
    // A volatile access in the callee.
    let volatile = PAIR.replace("%2 = load i32, ptr %1", "%2 = volatile load i32, ptr %1");
    let m = program(CALLEE, &volatile, F);
    let (_, w) = promote(&m).expect("the out-pointer alone");
    assert!(w.sites[0].params.iter().all(|p| p.index != 1));
}

/// A callee called from two sites with the same plan gets one clone, which
/// the second site reuses.
#[test]
fn one_clone_serves_every_site_with_its_plan() {
    let caller = "    %2 = alloca [ty.0 x 2], align 4\n    %3 = alloca [ty.0 x 2], align 4\n    \
                  store i32 %0, ptr %2\n    %4 = const i32 4\n    \
                  %5 = gep inbounds u8, ptr %2, %4\n    store i32 %1, ptr %5\n    \
                  call @func.0(%3, %2)\n    %6 = load i32, ptr %3\n    \
                  %20 = add i32 %6, %0\n    store i32 %20, ptr %2\n    call @func.0(%3, %2)\n    \
                  %7 = gep inbounds u8, ptr %3, %4\n    %8 = load i32, ptr %7\n    ret %8\n";
    let m = program(CALLEE, PAIR, caller);
    let (out, w) = promote(&m).expect("both calls are promoted");
    assert_eq!(
        w.sites.len(),
        2,
        "the second call reads the first's results"
    );
    assert_eq!(w.new_functions.len(), 1);
    assert_eq!(w.sites[0].clone, w.sites[1].clone);
    check_pass(&m, 32, func(&m, "f"), &out, &PassWitness::ArgPromo(w))
        .expect("the checker accepts both sites");
    let (opt, report) = optimize_module(&m, &config());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(allocas(func(&opt, "f")), 0);
    for (a, b) in [(3, 4), (-7, 9), (100, -3)] {
        assert_eq!(interpret(&opt, a, b), interpret(&m, a, b), "f({a}, {b})");
    }
}

/// Policy: a clone returns several values only when each is a scalar, so
/// an out-pointer is left beside a callee's aggregate result; and a callee
/// argument promotion was told to leave alone keeps its pointers.
#[test]
fn policy_an_aggregate_result_and_an_excluded_callee() {
    // The callee returns an aggregate: the read-only pointer is promoted,
    // the out-pointer is not.
    let callee = PAIR.replace(
        "    ret\n",
        "    %20 = alloca [ty.0 x 2], align 4\n    store i32 %6, ptr %20\n    \
         %21 = load [ty.0 x 2], ptr %20\n    ret %21\n",
    );
    let text = HEADER.replace(
        "functy.0 = (ptr, ptr) -> ()",
        "functy.0 = (ptr, ptr) -> ([ty.0 x 2])",
    ) + &format!(
        "fn @{CALLEE}(functy.0) {{\n    ; #visibility: hidden\nbb0(%0: ptr, %1: ptr):\n\
         {callee}}}\n\nfn @f(functy.1) {{\nbb0(%0: i32, %1: i32):\n{}}}\n",
        F.replace("call @func.0(%3, %2)", "%30 = call @func.0(%3, %2)")
    );
    let m = trust_ir::parser::parse_module(&text).expect("parse");
    let (_, w) = promote(&m).expect("the read-only pointer is promoted");
    let indices: Vec<usize> = w.sites[0].params.iter().map(|p| p.index).collect();
    assert_eq!(indices, vec![1]);
    // An excluded callee is not cloned.
    let m = program(CALLEE, PAIR, F);
    let cx = PassContext {
        module: &m,
        pointer_bits: 32,
    };
    let excluded = passes::ArgPromo::new(BTreeSet::from([CALLEE.to_string()]));
    assert!(excluded.run(&cx, func(&m, "f")).is_none());
}

/// The pass names why each slot argument stays a pointer (the hook the
/// corpus probes read).
#[test]
fn refusals_are_named() {
    let reasons = |m: &Module| {
        let cx = PassContext {
            module: m,
            pointer_bits: 32,
        };
        passes::argpromo_refusals(&cx, func(m, "f"))
            .into_iter()
            .map(|(_, j, why)| (j, why))
            .collect::<Vec<_>>()
    };
    let m = program(CALLEE, PAIR, F);
    assert_eq!(reasons(&m), vec![(0, "promotable"), (1, "promotable")]);
    let m = program(CALLEE, PAIR, &F.replace("    store i32 %1, ptr %5\n", ""));
    assert_eq!(
        reasons(&m),
        vec![(0, "promotable"), (1, "copy_in_unproved")]
    );
    let escaping = PAIR.replace("    ret\n", "    call @func.0(%1, %1)\n    ret\n");
    let m = program(CALLEE, &escaping, F);
    assert!(reasons(&m).contains(&(1, "callee_param_use")));
    let m = program("pair", PAIR, F);
    assert_eq!(
        reasons(&m),
        vec![(0, "callee_not_admitted"), (1, "callee_not_admitted")]
    );
}

/// An array passed by address is proved like any slot: every lane read is
/// copied in only when the caller wrote it with a never-poison value on
/// every path (an array of `MaybeUninit` lanes reaches trust-ir as an array
/// of its payload type, and the wasm32 lane reads the lanes lazily).
#[test]
fn an_array_by_address_needs_every_lane_proved() {
    let program = |second: &str| {
        let text = format!(
            "; TrustIr text format v1\nmodule \"argpromo\"\n\
             target \"wasm32-unknown-unknown\" 4 little\n\n\
             type ty.0 = i32\n\n\
             functy.0 = ([ty.0 x 2]) -> (i32)\n\
             functy.1 = (i32, i32) -> (i32)\n\n\
             fn @{CALLEE}(functy.0) {{\n    ; #visibility: hidden\nbb0(%0: [ty.0 x 2]):\n    \
             %1 = extractfield [ty.0 x 2] %0, 0\n    %2 = extractfield [ty.0 x 2] %0, 1\n    \
             %3 = add i32 %1, %2\n    ret %3\n}}\n\n\
             fn @f(functy.1) {{\nbb0(%0: i32, %1: i32):\n    \
             %2 = alloca [ty.0 x 2], align 4\n    store i32 %0, ptr %2\n    \
             %4 = const i32 4\n    %5 = gep inbounds u8, ptr %2, %4\n{second}    \
             %6 = call @func.0(%2)\n    ret %6\n}}\n"
        );
        trust_ir::parser::parse_module(&text)
            .unwrap_or_else(|e| panic!("the test module does not parse: {e}\n{text}"))
    };
    let m = program("    store i32 %1, ptr %5\n");
    let (out, w) = promote(&m).expect("both lanes are written");
    assert_eq!(w.sites[0].params[0].reads, vec![field(0), field(4)]);
    check_pass(&m, 32, func(&m, "f"), &out, &PassWitness::ArgPromo(w))
        .expect("the checker accepts the promotion");
    for second in ["", "    %7 = load i32, ptr %2\n    store i32 %7, ptr %5\n"] {
        let m = program(second);
        assert!(promote(&m).is_none(), "lane 1 may be poison: {second:?}");
        let cx = PassContext {
            module: &m,
            pointer_bits: 32,
        };
        let reasons: Vec<_> = passes::argpromo_refusals(&cx, func(&m, "f"))
            .into_iter()
            .map(|(_, j, why)| (j, why))
            .collect();
        assert_eq!(reasons, vec![(0, "copy_in_unproved")]);
    }
}

/// A call carrying a proof annotation keeps its callee: the annotation
/// describes that call, not the clone's.
#[test]
fn a_call_with_proof_material_is_left_alone() {
    let mut m = program(CALLEE, PAIR, F);
    let f = m.functions.iter_mut().find(|f| f.name == "f").expect("f");
    let at = f.blocks[0]
        .body
        .iter()
        .position(|n| matches!(n.inst, Inst::Call { .. }))
        .expect("the call");
    f.blocks[0].body[at]
        .proofs
        .push(trust_ir::ProofAnnotation::NotNull);
    assert!(promote(&m).is_none());
    let cx = PassContext {
        module: &m,
        pointer_bits: 32,
    };
    let reasons: Vec<_> = passes::argpromo_refusals(&cx, func(&m, "f"))
        .into_iter()
        .map(|(_, j, why)| (j, why))
        .collect();
    assert_eq!(
        reasons,
        vec![(0, "call_proof_material"), (1, "call_proof_material")]
    );
}

/// `m` with the callee's entry parameter `index` typed `&mut i32` (a thin
/// pointer of another type than the declared `ptr`, which trust-ir's module
/// validation reports as `EntryParamsMismatch`).
fn retype_entry(m: &mut Module, name: &str, index: usize) {
    let f = m
        .functions
        .iter_mut()
        .find(|f| f.name == name)
        .expect("the callee");
    let entry = f.entry;
    let block = f
        .blocks
        .iter_mut()
        .find(|b| b.id == entry)
        .expect("the entry");
    block.params[index].1 = Ty::RefMut(Box::new(Ty::I32));
}

/// A parameter the clone keeps must be of exactly its declared type at the
/// entry: the clone declares the signature's type and keeps the entry's, so
/// it would copy the callee's module-level `EntryParamsMismatch`. A retyped
/// parameter that is promoted is replaced by values and does not count.
#[test]
fn a_kept_parameter_retyped_at_the_entry_is_not_cloned() {
    // Both parameters promoted: the clone keeps no retyped one.
    let mut m = program(CALLEE, PAIR, F);
    retype_entry(&mut m, CALLEE, 1);
    let (out, w) = promote(&m).expect("both parameters are promoted");
    let indices: Vec<usize> = w.sites[0].params.iter().map(|p| p.index).collect();
    assert_eq!(indices, vec![0, 1]);
    check_pass(&m, 32, func(&m, "f"), &out, &PassWitness::ArgPromo(w))
        .expect("the checker accepts a promoted retyped parameter");

    // The callee hands its second parameter on, so only the out-pointer is
    // promoted and the clone keeps the second.
    let escaping = PAIR.replace("    ret\n", "    call @func.0(%1, %1)\n    ret\n");
    let m = program(CALLEE, &escaping, F);
    let (out, mut w) = promote(&m).expect("control: the out-pointer alone");
    let indices: Vec<usize> = w.sites[0].params.iter().map(|p| p.index).collect();
    assert_eq!(indices, vec![0]);

    let mut retyped = m.clone();
    retype_entry(&mut retyped, CALLEE, 1);
    assert!(promote(&retyped).is_none(), "the kept parameter is retyped");
    let cx = PassContext {
        module: &retyped,
        pointer_bits: 32,
    };
    let reasons: Vec<_> = passes::argpromo_refusals(&cx, func(&retyped, "f"))
        .into_iter()
        .map(|(_, j, why)| (j, why))
        .collect();
    assert_eq!(
        reasons,
        vec![(0, "kept_param_retyped"), (1, "callee_param_use")]
    );

    // The checker refuses the control's plan on the retyped callee, the
    // clone retyped alike, by this premise.
    let clone = &mut w.new_functions[0];
    let entry = clone.entry;
    let block = clone
        .blocks
        .iter_mut()
        .find(|b| b.id == entry)
        .expect("the clone's entry");
    let kept = block
        .params
        .iter_mut()
        .find(|(v, _)| *v == trust_ir::ValueId::new(1))
        .expect("the kept parameter");
    kept.1 = Ty::RefMut(Box::new(Ty::I32));
    let refused = check_pass(
        &retyped,
        32,
        func(&retyped, "f"),
        &out,
        &PassWitness::ArgPromo(w),
    )
    .expect_err("a kept retyped parameter is refused");
    assert!(
        format!("{refused:?}").contains("a parameter the clone keeps has an entry type"),
        "{refused:?}"
    );
}

/// A valid array argument captures the old bytes even when its source slot
/// is overwritten before the call. Promotion must extract that SSA value,
/// prove initialization at its load, and retain the old result.
#[test]
fn typed_array_promotion_preserves_the_loaded_snapshot() {
    let text = format!(
        r#"; TrustIr text format v1
module "typed_argpromo"
target "wasm32-unknown-unknown" 4 little

type ty.0 = i32
functy.0 = ([ty.0 x 2]) -> (i32)
functy.1 = (i32, i32) -> (i32)
fn @{CALLEE}(functy.0) {{
    ; #visibility: hidden
bb0(%0: [ty.0 x 2]):
    %1 = const usize 0
    %2 = const usize 1
    %3 = extractelement i32 %0, %1
    %4 = extractelement i32 %0, %2
    %5 = sub i32 %3, %4
    ret %5
}}
fn @f(functy.1) {{
bb0(%0: i32, %1: i32):
    %2 = alloca [ty.0 x 2], align 4
    store i32 %0, ptr %2
    %3 = const usize 4
    %4 = gep u8, ptr %2, %3
    store i32 %1, ptr %4
    %5 = load [ty.0 x 2], ptr %2
    store i32 %1, ptr %2
    store i32 %0, ptr %4
    %6 = call @func.0(%5)
    ret %6
}}
"#
    );
    let parse = |s: &str| trust_ir::parser::parse_module(s).expect("typed fixture");
    let m = parse(&text);
    assert!(trust_ir_build::validate_module(&m).is_empty());
    let (out, w) = promote(&m).expect("typed array promoted");
    assert_eq!(w.sites.len(), 1);
    assert_eq!(w.sites[0].params[0].reads, vec![field(0), field(4)]);
    check_pass(
        &m,
        32,
        func(&m, "f"),
        &out,
        &PassWitness::ArgPromo(w.clone()),
    )
    .expect("independently rechecked");
    let mut opt = m.clone();
    opt.functions[1] = out.clone();
    opt.functions.extend(w.new_functions.iter().cloned());
    opt.func_types.extend(w.new_func_types.iter().cloned());
    assert!(trust_ir_build::validate_module(&opt).is_empty());
    for (a, b) in [(3, 4), (-7, 9), (i32::MAX as i64, 2), (0, 0)] {
        assert_eq!(
            interpret(&m, a, b),
            Some((a as i32).wrapping_sub(b as i32) as i64)
        );
        assert_eq!(interpret(&opt, a, b), interpret(&m, a, b));
    }
    // The whole-aggregate load stays. Forging the extracted lane cannot
    // pass the exact reconstruction even when that lane is in bounds.
    let mut wrong = out.clone();
    let index = wrong.blocks[0]
        .body
        .iter()
        .find_map(|n| match n.inst {
            Inst::ExtractElement { array, index, .. } if array == trust_ir::ValueId::new(5) => {
                Some(index)
            }
            _ => None,
        })
        .expect("snapshot extraction");
    let n = wrong.blocks[0]
        .body
        .iter_mut()
        .find(|n| n.results == [index])
        .unwrap();
    n.inst = Inst::Const {
        ty: Ty::Usize,
        value: trust_ir::Constant::Int(1),
    };
    assert!(
        check_pass(
            &m,
            32,
            func(&m, "f"),
            &wrong,
            &PassWitness::ArgPromo(w.clone())
        )
        .is_err()
    );
    // A write after the load cannot retrospectively initialize its bytes.
    let uninitialized = parse(&text.replacen("    store i32 %1, ptr %4\n", "", 1));
    assert!(promote(&uninitialized).is_none());
    assert!(
        check_pass(
            &uninitialized,
            32,
            func(&uninitialized, "f"),
            &out,
            &PassWitness::ArgPromo(w)
        )
        .is_err()
    );
    for bad in [
        text.replace("%2 = const usize 1", "%2 = const usize 2"),
        text.replace("%2 = const usize 1", "%2 = const isize -1"),
        text.replace("%2 = const usize 1", "%2 = copy usize %1"),
        text.replace("%4 = extractelement i32", "%4 = extractelement u32"),
        text.replace("%5 = load [ty.0 x 2]", "%5 = volatile load [ty.0 x 2]"),
    ] {
        assert!(promote(&parse(&bad)).is_none());
    }
}
#[test]
fn typed_tuple_promotion_uses_field_layout_and_old_values() {
    let m = trust_ir::parser::parse_module(&format!(
        r#"; TrustIr text format v1
module "typed_tuple"
target "wasm32-unknown-unknown" 4 little
type ty.0 = (i32, i64)
tuple_layout ty.0 size=16 align=8 offsets=[0, 8]
functy.0 = ((i32, i64)) -> (i32)
functy.1 = (i32, i32) -> (i32)
fn @{CALLEE}(functy.0) {{
    ; #visibility: hidden
bb0(%0: (i32, i64)):
    %1 = extractfield i32 %0, 0
    %2 = extractfield i64 %0, 1
    %3 = trunc i64 %2 to i32
    %4 = sub i32 %1, %3
    ret %4
}}
fn @f(functy.1) {{
bb0(%0: i32, %1: i32):
    %2 = alloca (i32, i64), align 8
    store i32 %0, ptr %2
    %3 = const usize 8
    %4 = gep u8, ptr %2, %3
    %5 = sext i32 %1 to i64
    store i64 %5, ptr %4
    %6 = load (i32, i64), ptr %2
    store i32 %1, ptr %2
    %7 = sext i32 %0 to i64
    store i64 %7, ptr %4
    %8 = call @func.0(%6)
    ret %8
}}
"#
    ))
    .expect("typed tuple fixture");
    assert!(trust_ir_build::validate_module(&m).is_empty());
    // Layout is explicit: the padding is not guessed or required initialized.
    let mut no_layout = m.clone();
    no_layout.tuple_layouts.clear();
    assert!(promote(&no_layout).is_none());
    let (out, w) = promote(&m).expect("typed tuple promoted");
    assert_eq!(
        w.sites[0].params[0].reads,
        vec![
            field(0),
            ArgPromoField {
                offset: 8,
                ty: Ty::I64
            }
        ]
    );
    check_pass(
        &m,
        32,
        func(&m, "f"),
        &out,
        &PassWitness::ArgPromo(w.clone()),
    )
    .expect("independent tuple reconstruction");
    let mut target = m.clone();
    target.functions[1] = out;
    target.functions.extend(w.new_functions);
    target.func_types.extend(w.new_func_types);
    assert!(trust_ir_build::validate_module(&target).is_empty());
    for (a, b) in [(1, 2), (-9, 17), (i32::MAX as i64, i32::MIN as i64)] {
        assert_eq!(interpret(&target, a, b), interpret(&m, a, b));
        assert_eq!(
            interpret(&target, a, b),
            Some((a as i32).wrapping_sub(b as i32) as i64)
        );
    }
}
