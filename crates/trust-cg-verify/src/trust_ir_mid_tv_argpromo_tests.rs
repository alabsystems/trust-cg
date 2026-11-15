// trust-cg-verify/trust_ir_mid_tv_argpromo_tests.rs - argument promotion's checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The checker accepts a read-only pointer and an out-pointer of one call, two
//! sites sharing one clone (the second copying in what the first copied
//! out), an array passed by address from a slot, the bridge's
//! read-through `extractfield` of a tuple pointer and writes through an
//! integer address chain (each also agreeing with the source in the
//! reference interpreter), and refuses a named wrong one for each failure
//! class (the negative controls): fields other than the callee's, a
//! parameter passed on or observed in the callee, a non-constant integer
//! offset, an access its alignment does not divide, a copied-in byte the
//! caller may not have written or wrote with a value that may be poison, a
//! copied-out byte the callee may not write, a slot that escapes elsewhere,
//! another argument derived from the slot, a field outside the slot, an
//! argument not derived from a slot, a struct or an array passed by address
//! whose lanes are not proved, an array passed by address that another
//! argument aliases or that is not a slot, a call carrying a proof
//! annotation or proof context, a callee that is not a strong hidden crate-private
//! symbol, a clone whose body or name is not the derivation, two plans under
//! one clone, a signature the table already holds, a new function no site
//! calls, and a target other than the rewrite.

use super::*;
use crate::trust_ir_mid_tv::{PassWitness, check_pass};
use trust_ir::{InterpretOptions, InterpretValue, InterpretValueKind, Interpreter};

const HEADER: &str = "; TrustIr text format v1\nmodule \"argpromo\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n\
                      type ty.0 = i32\ntype ty.1 = i64\n\n\
                      functy.0 = (ptr, ptr) -> ()\n\
                      functy.1 = (i32, i32) -> (i32)\n\
                      functy.2 = ([ty.1 x 2]) -> (i64)\n\
                      functy.3 = (&(i32, f32, i64)) -> (i64)\n\
                      functy.4 = (ptr, i32) -> ()\n\n";

const CALLEE: &str = "pair.tcg.crate.00000000000000aa";

/// `pair` reads two `i32`s through `%1` and writes their sum and product
/// through `%0`.
const PAIR: &str = "    %2 = load i32, ptr %1\n    %3 = const i32 4\n    \
                    %4 = gep inbounds u8, ptr %1, %3\n    %5 = load i32, ptr %4\n    \
                    %6 = add i32 %2, %5\n    %7 = mul i32 %2, %5\n    \
                    store i32 %6, ptr %0\n    %8 = gep inbounds u8, ptr %0, %3\n    \
                    store i32 %7, ptr %8\n    ret\n";

/// `f` passes two slots to `pair`.
const F: &str = "    %2 = alloca [ty.0 x 2], align 4\n    %3 = alloca [ty.0 x 2], align 4\n    \
                 store i32 %0, ptr %2\n    %4 = const i32 4\n    \
                 %5 = gep inbounds u8, ptr %2, %4\n    store i32 %1, ptr %5\n    \
                 call @func.0(%3, %2)\n    %6 = load i32, ptr %3\n    \
                 %7 = gep inbounds u8, ptr %3, %4\n    %8 = load i32, ptr %7\n    \
                 %9 = sub i32 %6, %8\n    ret %9\n";

fn program(callee_name: &str, hidden: bool, callee: &str, caller: &str) -> Module {
    let vis = if hidden {
        "    ; #visibility: hidden\n"
    } else {
        ""
    };
    let text = format!(
        "{HEADER}fn @{callee_name}(functy.0) {{\n{vis}bb0(%0: ptr, %1: ptr):\n{callee}}}\n\n\
         fn @f(functy.1) {{\nbb0(%0: i32, %1: i32):\n{caller}}}\n"
    );
    trust_ir::parser::parse_module(&text)
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{text}"))
}

fn func<'m>(module: &'m Module, name: &str) -> &'m Function {
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .expect("function")
}

/// The call sites of `caller` as `(block, index, callee, promoted parameter
/// indices)`, rewritten in order.
type Spec = (u32, usize, u32, Vec<usize>);

/// The witness the pass would claim for `specs` (shapes from this module's
/// own derivation, clones appended in site order, reused by plan), and the
/// caller it claims, from this module's rebuild.
fn claimed(m: &Module, caller: &str, specs: &[Spec]) -> (Function, ArgPromoWitness) {
    let layout = FsymLayout::new(m);
    let mut witness = ArgPromoWitness::default();
    let mut next_id = m.functions.iter().map(|f| f.id.index()).max().unwrap() + 1;
    for &(block, index, callee, ref indices) in specs {
        let f = m.function_by_id(FuncId::new(callee)).expect("callee");
        let sig = m.func_type(f.ty).expect("signature");
        let shapes: Vec<Shape> = indices
            .iter()
            .map(|&j| param_shape(&layout, m, f, j).expect("the parameter's shape"))
            .collect();
        let params: Vec<ArgPromoParam> = indices
            .iter()
            .zip(&shapes)
            .map(|(&index, s)| ArgPromoParam {
                index,
                reads: s.reads.clone(),
                writes: s.writes.clone(),
            })
            .collect();
        let name = argpromo_clone_name(&f.name, &params).expect("a crate-private name");
        let clone = match witness.new_functions.iter().find(|g| g.name == name) {
            Some(g) => g.id,
            None => {
                let csig = clone_sig(sig, &params);
                let ty = match m.func_types.iter().position(|t| *t == csig) {
                    Some(i) => i,
                    None => {
                        witness.new_func_types.push(csig);
                        m.func_types.len() + witness.new_func_types.len() - 1
                    }
                };
                let id = FuncId::new(next_id);
                next_id += 1;
                let (g, _) = derive_clone(
                    &layout,
                    m,
                    f,
                    sig,
                    &params,
                    &shapes,
                    id,
                    name,
                    trust_ir::FuncTyId::new(ty as u32),
                );
                witness.new_functions.push(g);
                id
            }
        };
        witness.sites.push(ArgPromoSite {
            block: BlockId::new(block),
            index,
            callee: FuncId::new(callee),
            clone,
            params,
        });
    }
    let (target, _) =
        rebuild_argpromo(m, func(m, caller), &witness).expect("the claimed witness rebuilds");
    (target, witness)
}

/// The position of the first call of function `callee` in `f`'s entry block.
fn call_of(f: &Function, callee: u32) -> usize {
    f.blocks[0]
        .body
        .iter()
        .position(|n| matches!(n.inst, Inst::Call { callee: c, .. } if c == FuncId::new(callee)))
        .expect("the call")
}

fn check(
    m: &Module,
    caller: &str,
    target: &Function,
    witness: &ArgPromoWitness,
) -> Result<WitnessVerdict, MidTvError> {
    check_pass(
        m,
        32,
        func(m, caller),
        target,
        &PassWitness::ArgPromo(witness.clone()),
    )
}

/// The refusal's text, for a witness the checker must refuse.
fn refused(m: &Module, caller: &str, target: &Function, witness: &ArgPromoWitness) -> String {
    match check(m, caller, target, witness) {
        Ok(_) => panic!("the checker accepted a wrong witness: {witness:#?}"),
        Err(e) => e.to_string(),
    }
}

fn run(m: &Module, name: &str, a: i32, b: i32) -> Option<i128> {
    let f = m.function_by_name(name).expect("function");
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
        InterpretValueKind::Int(i) => Some(i.as_signed()),
        other => panic!("{name} returned {other:?}"),
    }
}

/// The module after the rewrite: the caller replaced, the clones appended.
fn after(m: &Module, caller: &str, target: &Function, witness: &ArgPromoWitness) -> Module {
    let mut out = m.clone();
    let i = out.functions.iter().position(|f| f.name == caller).unwrap();
    out.functions[i] = target.clone();
    out.func_types
        .extend(witness.new_func_types.iter().cloned());
    out.functions.extend(witness.new_functions.iter().cloned());
    out
}

fn assert_agrees(m: &Module, out: &Module) {
    for (a, b) in [(3, 4), (-7, 9), (i32::MAX, 2), (0, 0), (100, -100)] {
        let want = run(m, "f", a, b).expect("the source runs");
        assert_eq!(run(out, "f", a, b), Some(want), "f({a}, {b})");
    }
}

#[test]
fn a_read_only_pointer_and_an_out_pointer_are_accepted() {
    let m = program(CALLEE, true, PAIR, F);
    let (target, w) = claimed(&m, "f", &[(0, 6, 0, vec![0, 1])]);
    let verdict = check(&m, "f", &target, &w).expect("accepted");
    assert_eq!(verdict.refinements, 1);
    assert_eq!(
        w.sites[0].params[1].reads,
        vec![
            ArgPromoField {
                offset: 0,
                ty: Ty::I32
            },
            ArgPromoField {
                offset: 4,
                ty: Ty::I32
            }
        ]
    );
    assert_agrees(&m, &after(&m, "f", &target, &w));
}

#[test]
fn two_sites_share_one_clone() {
    let caller = "    %2 = alloca [ty.0 x 2], align 4\n    %3 = alloca [ty.0 x 2], align 4\n    \
                  store i32 %0, ptr %2\n    %4 = const i32 4\n    \
                  %5 = gep inbounds u8, ptr %2, %4\n    store i32 %1, ptr %5\n    \
                  call @func.0(%3, %2)\n    %6 = load i32, ptr %3\n    \
                  %10 = add i32 %6, %0\n    store i32 %10, ptr %2\n    \
                  call @func.0(%3, %2)\n    \
                  %7 = gep inbounds u8, ptr %3, %4\n    %8 = load i32, ptr %7\n    ret %8\n";
    let m = program(CALLEE, true, PAIR, caller);
    // Each site is named in the function the earlier ones left.
    let (first, _) = claimed(&m, "f", &[(0, 6, 0, vec![0, 1])]);
    let second = call_of(&first, 0);
    let (target, w) = claimed(
        &m,
        "f",
        &[(0, 6, 0, vec![0, 1]), (0, second, 0, vec![0, 1])],
    );
    check(&m, "f", &target, &w).expect("accepted");
    assert_eq!(w.new_functions.len(), 1);
    assert_eq!(w.sites[0].clone, w.sites[1].clone);
    assert_agrees(&m, &after(&m, "f", &target, &w));
}

#[test]
fn an_array_by_address_a_tuple_read_through_and_an_integer_chain_are_accepted() {
    let text = format!(
        "{HEADER}fn @agg.tcg.crate.00000000000000ab(functy.2) {{\n    ; #visibility: hidden\n\
         bb0(%0: [ty.1 x 2]):\n    %1 = extractfield [ty.1 x 2] %0, 0\n    \
         %2 = extractfield [ty.1 x 2] %0, 1\n    %3 = mul i64 %1, %2\n    ret %3\n}}\n\n\
         fn @sum3.tcg.crate.00000000000000ac(functy.3) {{\n    ; #visibility: hidden\n\
         bb0(%0: &(i32, f32, i64)):\n    %1 = extractfield (i32, f32, i64) %0, 0\n    \
         %2 = extractfield (i32, f32, i64) %0, 2\n    %3 = sext i32 %1 to i64\n    \
         %4 = add i64 %3, %2\n    ret %4\n}}\n\n\
         fn @chain.tcg.crate.00000000000000ad(functy.4) {{\n    ; #visibility: hidden\n\
         bb0(%0: ptr, %1: i32):\n    %2 = ptrtoint ptr %0 to i32\n    %3 = const i32 4\n    \
         %4 = add i32 %2, %3\n    %5 = inttoptr i32 %4 to ptr\n    store i32 %1, ptr %5\n    \
         store i32 %1, ptr %0\n    ret\n}}\n\n\
         fn @f(functy.1) {{\nbb0(%0: i32, %1: i32):\n    \
         %2 = alloca [ty.1 x 2], align 8\n    %3 = sext i32 %0 to i64\n    \
         store i64 %3, ptr %2\n    %4 = const i32 8\n    %5 = gep inbounds u8, ptr %2, %4\n    \
         %6 = add i64 %3, %3\n    store i64 %6, ptr %5\n    \
         %7 = call @func.0(%2)\n    \
         %8 = alloca [ty.1 x 2], align 8\n    store i32 %1, ptr %8\n    \
         %9 = const i32 8\n    %10 = gep inbounds u8, ptr %8, %9\n    \
         %11 = sext i32 %1 to i64\n    store i64 %11, ptr %10\n    \
         %12 = ptrtoptr ptr %8 to &(i32, f32, i64)\n    %13 = call @func.1(%12)\n    \
         %14 = alloca [ty.0 x 2], align 4\n    call @func.2(%14, %0)\n    \
         %15 = load i32, ptr %14\n    %16 = const i32 4\n    \
         %17 = gep inbounds u8, ptr %14, %16\n    %18 = load i32, ptr %17\n    \
         %19 = add i64 %7, %13\n    %20 = trunc i64 %19 to i32\n    %21 = add i32 %20, %15\n    \
         %22 = add i32 %21, %18\n    ret %22\n}}\n"
    );
    let m = trust_ir::parser::parse_module(&text).expect("parse");
    // Both lanes of the array are stored from never-poison values.
    let (first, _) = claimed(&m, "f", &[(0, 7, 0, vec![0])]);
    let (second, _) = claimed(
        &m,
        "f",
        &[(0, 7, 0, vec![0]), (0, call_of(&first, 1), 1, vec![0])],
    );
    let specs = [
        (0, 7, 0, vec![0]),
        (0, call_of(&first, 1), 1, vec![0]),
        (0, call_of(&second, 2), 2, vec![0]),
    ];
    let (target, w) = claimed(&m, "f", &specs);
    check(&m, "f", &target, &w).expect("accepted");
    assert_eq!(w.new_functions.len(), 3);
    assert!(w.sites[2].params[0].reads.is_empty());
    assert_eq!(w.sites[2].params[0].writes.len(), 2);
    let out = after(&m, "f", &target, &w);
    let view_in = crate::trust_ir_mid_tv::interpretable_module(&m);
    let view_out = crate::trust_ir_mid_tv::interpretable_module(&out);
    for (a, b) in [(3, 4), (-7, 9), (0, 0)] {
        let want = run(&view_in, "f", a, b).expect("the source runs");
        assert_eq!(run(&view_out, "f", a, b), Some(want), "f({a}, {b})");
    }
}

#[test]
fn negative_controls_in_the_callee() {
    let base = program(CALLEE, true, PAIR, F);
    let (target, good) = claimed(&base, "f", &[(0, 6, 0, vec![0, 1])]);
    // Fields other than the callee's.
    let mut w = good.clone();
    w.sites[0].params[1].reads.pop();
    assert!(refused(&base, "f", &target, &w).contains("not the callee's"));
    // A parameter passed on, observed, offset by a non-constant, or accessed
    // at an offset its alignment does not divide.
    for (callee, why) in [
        (
            PAIR.replace("    ret\n", "    call @func.0(%1, %1)\n    ret\n"),
            "escapes",
        ),
        (
            PAIR.replace(
                "    ret\n",
                "    %20 = ptrtoint ptr %1 to i32\n    store i32 %20, ptr %0\n    ret\n",
            ),
            "observed",
        ),
        (
            PAIR.replace(
                "    ret\n",
                "    %20 = ptrtoint ptr %1 to i32\n    %21 = add i32 %20, %2\n    \
                 %22 = inttoptr i32 %21 to ptr\n    store i32 %2, ptr %22\n    ret\n",
            ),
            "non-constant",
        ),
        (
            PAIR.replace("%3 = const i32 4", "%3 = const i32 2"),
            "alignment",
        ),
    ] {
        let m = program(CALLEE, true, &callee, F);
        let msg = refused(&m, "f", &target, &good);
        assert!(msg.contains(why), "{why}: {msg}");
    }
    // A copied-out byte the callee writes on one path only.
    let one_path = "    %2 = load i32, ptr %1\n    %3 = const i32 4\n    \
                    %4 = gep inbounds u8, ptr %1, %3\n    %5 = load i32, ptr %4\n    \
                    store i32 %5, ptr %0\n    %6 = icmp slt i32 %2, %5\n    \
                    condbr %6, bb1, bb2\n\
                    bb1:\n    %8 = gep inbounds u8, ptr %0, %3\n    store i32 %2, ptr %8\n    ret\n\
                    bb2:\n    ret\n";
    let m = program(CALLEE, true, one_path, F);
    let (t, w) = claimed_unchecked(&m, &[(0, 6, 0, vec![0, 1])]);
    assert!(refused(&m, "f", &t, &w).contains("may be poison at a ret"));
    // Not a strong hidden crate-private symbol.
    let m = program(CALLEE, false, PAIR, F);
    assert!(refused(&m, "f", &target, &good).contains("strong hidden"));
    let m = program("pair", true, PAIR, F);
    assert!(refused(&m, "f", &target, &good).contains("crate-private"));
}

/// The witness and target `claimed` would build, without its own check (for
/// a premise this checker must refuse).
fn claimed_unchecked(m: &Module, specs: &[Spec]) -> (Function, ArgPromoWitness) {
    let good = program(CALLEE, true, PAIR, F);
    let (target, mut w) = claimed(&good, "f", specs);
    // Re-derive the clone from `m`'s callee, so only the premise differs.
    let layout = FsymLayout::new(m);
    let f = m.function_by_id(FuncId::new(0)).unwrap();
    let sig = m.func_type(f.ty).unwrap();
    let shapes: Vec<Shape> = w.sites[0]
        .params
        .iter()
        .map(|p| param_shape(&layout, m, f, p.index).unwrap())
        .collect();
    let g = &w.new_functions[0];
    let (clone, _) = derive_clone(
        &layout,
        m,
        f,
        sig,
        &w.sites[0].params,
        &shapes,
        g.id,
        g.name.clone(),
        g.ty,
    );
    w.new_functions[0] = clone;
    (target, w)
}

#[test]
fn negative_controls_in_the_caller() {
    let base = program(CALLEE, true, PAIR, F);
    let (target, good) = claimed(&base, "f", &[(0, 6, 0, vec![0, 1])]);
    for (caller, why) in [
        // The caller writes one copied-in field only.
        (
            F.replace("    store i32 %1, ptr %5\n", ""),
            "may be poison at the call",
        ),
        // ... or writes it with a load's value.
        (
            F.replace(
                "    store i32 %1, ptr %5\n",
                "    %20 = load i32, ptr %3\n    store i32 %20, ptr %5\n",
            ),
            "may be poison at the call",
        ),
        // The slot's address also reaches a block argument.
        (
            F.replace(
                "    %9 = sub i32 %6, %8\n    ret %9\n",
                "    %9 = sub i32 %6, %8\n    br bb1(%2)\nbb1(%30: ptr):\n    ret %9\n",
            ),
            "escapes",
        ),
        // Another argument is derived from the same slot.
        (
            F.replace("call @func.0(%3, %2)", "call @func.0(%2, %2)"),
            "derived from the slot",
        ),
        // The slot is smaller than the fields read.
        (
            F.replace(
                "%2 = alloca [ty.0 x 2], align 4",
                "%2 = alloca [ty.0 x 1], align 4",
            )
            .replace("    store i32 %1, ptr %5\n", ""),
            "outside",
        ),
    ] {
        let m = program(CALLEE, true, PAIR, &caller);
        let mut w = good.clone();
        w.sites[0].index = call_of(func(&m, "f"), 0);
        let msg = refused(&m, "f", &target, &w);
        assert!(msg.contains(why), "{why}: {msg}");
    }
    // The argument is not derived from a slot.
    let caller = "    %2 = alloca [ty.0 x 2], align 4\n    store i32 %0, ptr %2\n    \
                  %4 = const i32 4\n    %5 = gep inbounds u8, ptr %2, %4\n    \
                  store i32 %1, ptr %5\n    %3 = global_addr @global.0\n    \
                  call @func.0(%3, %2)\n    ret %0\n";
    let text = format!(
        "{HEADER}global internal align(4) @g [ty.0 x 2] = bytes<0000000000000000>\n\n\
         fn @{CALLEE}(functy.0) {{\n    ; #visibility: hidden\nbb0(%0: ptr, %1: ptr):\n{PAIR}}}\n\n\
         fn @f(functy.1) {{\nbb0(%0: i32, %1: i32):\n{caller}}}\n"
    );
    let m = trust_ir::parser::parse_module(&text).expect("parse");
    let (t, w) = claimed(&m, "f", &[(0, 6, 0, vec![1])]);
    check(&m, "f", &t, &w).expect("the read-only slot alone");
    let mut both = w.clone();
    both.sites[0].params.insert(
        0,
        ArgPromoParam {
            index: 0,
            reads: Vec::new(),
            writes: good.sites[0].params[0].writes.clone(),
        },
    );
    assert!(refused(&m, "f", &t, &both).contains("not derived from a slot"));
}

#[test]
fn negative_controls_in_the_witness_and_the_target() {
    let m = program(CALLEE, true, PAIR, F);
    let (target, good) = claimed(&m, "f", &[(0, 6, 0, vec![0, 1])]);
    // The clone's body is not the derivation.
    let mut w = good.clone();
    let body = &mut w.new_functions[0].blocks[0].body;
    let at = body
        .iter()
        .position(|n| matches!(n.inst, Inst::BinOp { .. }))
        .unwrap();
    if let Inst::BinOp { op, .. } = &mut body[at].inst {
        *op = trust_ir::BinOp::Sub;
    }
    assert!(refused(&m, "f", &target, &w).contains("not the callee's body"));
    // The clone's name is not the plan's.
    let mut w = good.clone();
    w.new_functions[0].name = format!("{CALLEE}x");
    assert!(refused(&m, "f", &target, &w).contains("not the callee's body"));
    // A new signature the table already holds.
    let mut w = good.clone();
    w.new_func_types.push(m.func_types[0].clone());
    assert!(refused(&m, "f", &target, &w).contains("already holds"));
    // A new function no site calls.
    let mut w = good.clone();
    let mut extra = w.new_functions[0].clone();
    extra.id = FuncId::new(extra.id.index() + 1);
    extra.name.push('y');
    w.new_functions.push(extra);
    assert!(refused(&m, "f", &target, &w).contains("no site calls"));
    // Two plans under one clone.
    let caller = F.replace(
        "    %9 = sub i32 %6, %8\n",
        "    call @func.0(%3, %2)\n    %9 = sub i32 %6, %8\n",
    );
    let m2 = program(CALLEE, true, PAIR, &caller);
    let (first, _) = claimed(&m2, "f", &[(0, 6, 0, vec![0, 1])]);
    let second = call_of(&first, 0);
    let (t2, mut w2) = claimed(
        &m2,
        "f",
        &[(0, 6, 0, vec![0, 1]), (0, second, 0, vec![0, 1])],
    );
    w2.sites[1].params.remove(1);
    let msg = refused(&m2, "f", &t2, &w2);
    assert!(
        msg.contains("two plans") || msg.contains("not the callee's"),
        "{msg}"
    );
    // A target whose copied-in load reads the wrong offset.
    let mut t = target.clone();
    for n in &mut t.blocks[0].body {
        if let Inst::Const {
            value: Constant::Int(k),
            ..
        } = &mut n.inst
            && *k == 4
        {
            *k = 0;
            break;
        }
    }
    assert!(refused(&m, "f", &t, &good).contains("target differs"));
}

/// A tuple passed by address: the call's view of its bytes need not cover
/// an unwritten lane, so each lane copied in is proved like a pointer's
/// field (accepted with both lanes stored from parameters, refused with one
/// unwritten or written from a load).
#[test]
fn a_tuple_by_address_needs_its_lanes_proved() {
    let program = |store_second: &str| {
        let text = format!(
            "{HEADER}functy.5 = ((i32, i64)) -> (i64)\n\n\
             fn @tup.tcg.crate.00000000000000ae(functy.5) {{\n    ; #visibility: hidden\n\
             bb0(%0: (i32, i64)):\n    %1 = extractfield (i32, i64) %0, 0\n    \
             %2 = extractfield (i32, i64) %0, 1\n    %3 = sext i32 %1 to i64\n    \
             %4 = add i64 %3, %2\n    ret %4\n}}\n\n\
             fn @f(functy.1) {{\nbb0(%0: i32, %1: i32):\n    \
             %2 = alloca [ty.1 x 2], align 8\n    store i32 %0, ptr %2\n    \
             %3 = const i32 8\n    %4 = gep inbounds u8, ptr %2, %3\n{store_second}    \
             %6 = call @func.0(%2)\n    %7 = trunc i64 %6 to i32\n    ret %7\n}}\n"
        );
        trust_ir::parser::parse_module(&text).expect("parse")
    };
    let good = program("    %5 = sext i32 %1 to i64\n    store i64 %5, ptr %4\n");
    let at = call_of(func(&good, "f"), 0);
    let (target, w) = claimed(&good, "f", &[(0, at, 0, vec![0])]);
    check(&good, "f", &target, &w).expect("accepted");
    let view_in = crate::trust_ir_mid_tv::interpretable_module(&good);
    let view_out = crate::trust_ir_mid_tv::interpretable_module(&after(&good, "f", &target, &w));
    for (a, b) in [(3, 4), (-7, 9)] {
        assert_eq!(run(&view_out, "f", a, b), run(&view_in, "f", a, b));
    }
    for second in [
        "    %5 = const i64 0\n",
        "    %8 = load i64, ptr %2\n    store i64 %8, ptr %4\n    %5 = const i64 0\n",
    ] {
        let m = program(second);
        let mut w2 = w.clone();
        w2.sites[0].index = call_of(func(&m, "f"), 0);
        let msg = refused(&m, "f", &target, &w2);
        assert!(msg.contains("may be poison at the call"), "{msg}");
    }
}

/// An array passed by address is a slot like any other: the wasm32 lane
/// reads its lanes where the callee extracts them, so an aliasing argument
/// the callee writes through first, an array that is not a frame slot, and
/// a lane the caller may not have written (a `[MaybeUninit<T>; N]` reaches
/// trust-ir as `[T x N]`) are each refused.
#[test]
fn an_array_by_address_needs_its_slot_and_lanes_proved() {
    let program = |caller_body: &str| {
        let text = format!(
            "{HEADER}functy.5 = ([ty.1 x 2], ptr) -> (i64)\n\n\
             global internal align(8) @g [ty.1 x 2] = bytes<00000000000000000000000000000000>\n\n\
             fn @agg.tcg.crate.00000000000000af(functy.5) {{\n    ; #visibility: hidden\n\
             bb0(%0: [ty.1 x 2], %1: ptr):\n    %2 = const i64 99\n    \
             store i64 %2, ptr %1\n    %3 = extractfield [ty.1 x 2] %0, 0\n    \
             %4 = extractfield [ty.1 x 2] %0, 1\n    %5 = add i64 %3, %4\n    ret %5\n}}\n\n\
             fn @f(functy.1) {{\nbb0(%0: i32, %1: i32):\n    \
             %2 = alloca [ty.1 x 2], align 8\n    %3 = sext i32 %0 to i64\n    \
             store i64 %3, ptr %2\n    %4 = const i32 8\n    \
             %5 = gep inbounds u8, ptr %2, %4\n{caller_body}    \
             %7 = trunc i64 %6 to i32\n    ret %7\n}}\n"
        );
        trust_ir::parser::parse_module(&text).expect("parse")
    };
    let second = "    %10 = sext i32 %1 to i64\n    store i64 %10, ptr %5\n";
    let other = "    %8 = alloca [ty.1 x 1], align 8\n";
    let good = program(&format!("{second}{other}    %6 = call @func.0(%2, %8)\n"));
    let at = call_of(func(&good, "f"), 0);
    let (target, w) = claimed(&good, "f", &[(0, at, 0, vec![0])]);
    check(&good, "f", &target, &w).expect("accepted");
    let view_in = crate::trust_ir_mid_tv::interpretable_module(&good);
    let view_out = crate::trust_ir_mid_tv::interpretable_module(&after(&good, "f", &target, &w));
    for (a, b) in [(3, 4), (-7, 9)] {
        assert_eq!(run(&view_out, "f", a, b), run(&view_in, "f", a, b));
    }
    for (body, why) in [
        // The second argument is the array's own slot: the callee writes 99
        // over lane 0 before it reads it.
        (
            format!("{second}{other}    %6 = call @func.0(%2, %2)\n"),
            "derived from the slot",
        ),
        // The array is a global, not a frame slot.
        (
            format!(
                "{second}{other}    %9 = global_addr @global.0\n    %6 = call @func.0(%9, %8)\n"
            ),
            "not derived from a slot",
        ),
        // Lane 1 is never written.
        (
            format!("{other}    %6 = call @func.0(%2, %8)\n"),
            "may be poison at the call",
        ),
        // Lane 1 is written with a load's value.
        (
            format!(
                "    %10 = load i64, ptr %2\n    store i64 %10, ptr %5\n{other}    \
                 %6 = call @func.0(%2, %8)\n"
            ),
            "may be poison at the call",
        ),
    ] {
        let m = program(&body);
        let mut w2 = w.clone();
        w2.sites[0].index = call_of(func(&m, "f"), 0);
        let msg = refused(&m, "f", &target, &w2);
        assert!(msg.contains(why), "{why}: {msg}");
    }
}

/// A proof annotation or proof context names the call it is attached to,
/// not the clone's call: the site is refused.
#[test]
fn a_call_with_proof_material_is_refused() {
    let m = program(CALLEE, true, PAIR, F);
    let (target, w) = claimed(&m, "f", &[(0, 6, 0, vec![0, 1])]);
    let mut annotated = m.clone();
    let f = annotated
        .functions
        .iter_mut()
        .find(|f| f.name == "f")
        .unwrap();
    f.blocks[0].body[6]
        .proofs
        .push(trust_ir::ProofAnnotation::NotNull);
    let msg = refused(&annotated, "f", &target, &w);
    assert!(msg.contains("proof annotation or proof context"), "{msg}");
}
