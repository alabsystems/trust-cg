// trust-cg-irmid/loop_tests.rs - the loop passes
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Closed-form induction and loop-invariant code motion: each rewrite is
//! made where its shape holds, kept by the checker and the interpreter
//! differential, and not made where it does not (a second effect, a step
//! other than one, a non-affine accumulator, a wrapping exit under an
//! extension; a load beside an aliasing store, a trapping instruction that
//! is not guaranteed to execute, an instruction that costs nothing on
//! wasm); a pass that lies is rolled back and counted. The witness types
//! (`LoopCfWitness`, `LicmWitness`) are provisional surfaces pending the
//! owner's sign-off.

use trust_cg_verify::trust_ir_mid_tv::PassWitness;
use trust_ir::{BlockId, Constant, Function, Inst, Module, ValueId};

use crate::manager;
use crate::passes::{self, MidPass, PassContext};
use crate::{IrmidReport, MidConfig, PassStats, optimize_module};

const HEADER: &str = "; TrustIr text format v1\nmodule \"irmid\"\n\
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

fn stats(report: &IrmidReport, name: &str) -> PassStats {
    report
        .passes
        .iter()
        .find(|p| p.name == name)
        .cloned()
        .unwrap_or_default()
}

/// Whether some block of `f` branches to a block at or before itself in
/// layout (every loop the bridge emits has such a back edge).
fn loops_back(f: &Function) -> bool {
    let at = |id: BlockId| f.blocks.iter().position(|b| b.id == id);
    f.blocks.iter().enumerate().any(|(i, b)| {
        b.body.last().is_some_and(|t| {
            t.inst
                .successor_edges()
                .iter()
                .any(|e| at(e.target).is_some_and(|j| j <= i))
        })
    })
}

fn run_pass(pass: &dyn MidPass, m: &Module, name: &str) -> Option<(Function, PassWitness)> {
    let cx = PassContext {
        module: m,
        pointer_bits: 32,
    };
    pass.run(&cx, func(m, name))
}

/// `e_range_sum` as the bridge spells it after scalar replacement: the sum
/// of `zext i` for `i` in `0..(a % 1000)`, through `add.overflow` with a
/// dead flag, with the bound an invariant parameter.
const SUM: &str = "functy.0 = (u32) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%1: u32):\n\
\x20   %14 = const u32 1000\n\
\x20   %13 = urem u32 %1, %14\n\
\x20   %16 = const u64 0\n\
\x20   %17 = const u32 0\n\
\x20   br bb1(%16, %13, %17)\n\
bb1(%18: u64, %19: u32, %20: u32):\n\
\x20   %22 = icmp ult u32 %20, %19\n\
\x20   condbr %22, bb2, bb3\n\
bb3:\n\
\x20   ret %18\n\
bb2:\n\
\x20   %25 = const u32 1\n\
\x20   %24 = add u32 %20, %25\n\
\x20   %46 = zext u32 %20 to u64\n\
\x20   %47, %48 = add.overflow u64 %18, %46\n\
\x20   br bb4\n\
bb4:\n\
\x20   %49 = copy u64 %47\n\
\x20   br bb1(%49, %19, %24)\n\
}\n";

#[test]
fn a_counted_sum_is_closed_and_kept_by_the_checker_and_the_differential() {
    let m = module(SUM);
    assert!(loops_back(func(&m, "f")));
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(!loops_back(func(&out, "f")), "{}", func(&out, "f"));
    assert_eq!(stats(&report, "loop_cf").functions_changed, 1);
    let tv = report
        .tv
        .by_pass
        .get("loop_cf")
        .expect("loop_cf candidates");
    assert_eq!(tv.compared, 1, "{tv:?}");
}

/// [`SUM`] with `edit` applied to its text.
fn sum_with(edit: &[(&str, &str)]) -> Module {
    let mut text = SUM.to_string();
    for (from, to) in edit {
        assert!(text.contains(from), "{from}");
        text = text.replace(from, to);
    }
    module(&text)
}

#[test]
fn reductions_outside_the_shape_are_left() {
    let cases = [
        // A second effect: a store in the body.
        sum_with(&[(
            "\x20   %49 = copy u64 %47\n",
            "\x20   %49 = copy u64 %47\n\x20   %60 = alloca u64\n\x20   store u64 %49, ptr %60\n",
        )]),
        // A step of two.
        sum_with(&[("%25 = const u32 1", "%25 = const u32 2")]),
        // A geometric accumulator.
        sum_with(&[(
            "%47, %48 = add.overflow u64 %18, %46",
            "%60 = const u64 3\n\x20   %61 = mul u64 %18, %60\n\x20   %47, %48 = add.overflow u64 %61, %46",
        )]),
        // A wrapping exit under a zero extension.
        sum_with(&[("icmp ult u32 %20, %19", "icmp ne u32 %20, %19")]),
        // The overflow flag read.
        sum_with(&[("\x20   br bb4\n", "\x20   assert %48\n\x20   br bb4\n")]),
        // A possibly poison initial value.
        sum_with(&[("%16 = const u64 0", "%16 = undef u64")]),
    ];
    for m in &cases {
        assert!(
            run_pass(&passes::LoopClosedForm, m, "f").is_none(),
            "{}",
            func(m, "f")
        );
    }
}

/// Two nested counted loops: the inner one's sum closes, which leaves the
/// outer one a counted reduction of a non-affine term (left).
const NESTED: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 15\n\
\x20   %2 = and u32 %0, %1\n\
\x20   %3 = const u32 0\n\
\x20   br bb1(%3, %3)\n\
bb1(%10: u32, %11: u32):\n\
\x20   %12 = icmp ult u32 %10, %2\n\
\x20   condbr %12, bb2, bb5\n\
bb2:\n\
\x20   %13 = const u32 0\n\
\x20   br bb3(%11, %13)\n\
bb3(%20: u32, %21: u32):\n\
\x20   %22 = icmp ult u32 %21, %10\n\
\x20   condbr %22, bb4, bb6\n\
bb4:\n\
\x20   %23 = add u32 %20, %21\n\
\x20   %24 = const u32 1\n\
\x20   %25 = add u32 %21, %24\n\
\x20   br bb3(%23, %25)\n\
bb6:\n\
\x20   %26 = const u32 1\n\
\x20   %27 = add u32 %10, %26\n\
\x20   br bb1(%27, %20)\n\
bb5:\n\
\x20   ret %11\n\
}\n";

#[test]
fn an_inner_sum_closes_inside_its_outer_loop() {
    let m = module(NESTED);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert_eq!(stats(&report, "loop_cf").functions_changed, 1);
    // The outer loop stays.
    assert!(loops_back(f), "{f}");
    assert!(!f.blocks.iter().any(|b| b.id == BlockId::new(4)), "{f}");
}

/// A loop with an invariant parameter `j`, a product of it, a division by an
/// invariant divisor in the header, a load in the header and (optionally)
/// a store.
fn invariant_loop(store: bool, div_in_body: bool) -> Module {
    let store = if store {
        "\x20   store u32 %18, ptr %0\n"
    } else {
        ""
    };
    let (head_div, body_div) = if div_in_body {
        ("", "\x20   %17 = udiv u32 %5, %2\n")
    } else {
        ("\x20   %17 = udiv u32 %5, %2\n", "")
    };
    module(&format!(
        "functy.0 = (ptr, u32, u32) -> (u32)\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: ptr, %1: u32, %2: u32):\n\
         \x20   %3 = const u32 0\n\
         \x20   %4 = const u32 3\n\
         \x20   %5 = and u32 %1, %4\n\
         \x20   br bb1(%3, %3, %5)\n\
         bb1(%10: u32, %11: u32, %12: u32):\n\
         \x20   %13 = load u32, ptr %0\n\
         {head_div}\
         \x20   %14 = icmp ult u32 %10, %13\n\
         \x20   condbr %14, bb2, bb3\n\
         bb2:\n\
         \x20   %15 = const u32 4\n\
         \x20   %16 = mul u32 %12, %15\n\
         {body_div}\
         \x20   %18 = add u32 %11, %16\n\
         \x20   %30 = add u32 %18, %17\n\
         {store}\
         \x20   %19 = const u32 1\n\
         \x20   %20 = add u32 %10, %19\n\
         \x20   br bb1(%20, %30, %12)\n\
         bb3:\n\
         \x20   ret %11\n\
         }}\n"
    ))
}

fn hoisted(w: &PassWitness) -> (Vec<ValueId>, Vec<ValueId>) {
    let PassWitness::Licm(w) = w else {
        panic!("licm witness")
    };
    let l = &w.loops[0];
    (l.invariant_params.clone(), l.hoisted.clone())
}

#[test]
fn invariant_code_is_hoisted_by_tier() {
    let v = ValueId::new;
    // Store-free loop: the parameter goes; the header's load and division
    // are guaranteed to execute; the product and its constant speculate.
    let m = invariant_loop(false, false);
    let (_, w) = run_pass(&passes::Licm, &m, "f").expect("hoists");
    assert_eq!(hoisted(&w), (vec![v(12)], vec![v(13), v(17), v(15), v(16)]));
    // An aliasing store: the load stays, so does the compare reading it.
    let m = invariant_loop(true, false);
    let (_, w) = run_pass(&passes::Licm, &m, "f").expect("hoists");
    assert_eq!(hoisted(&w), (vec![v(12)], vec![v(17), v(15), v(16)]));
    // A division by a divisor that may be zero, in the body: it stays.
    let m = invariant_loop(false, true);
    let (_, w) = run_pass(&passes::Licm, &m, "f").expect("hoists");
    assert_eq!(hoisted(&w), (vec![v(12)], vec![v(13), v(15), v(16)]));
}

#[test]
fn hoisting_is_kept_by_the_checker_and_the_differential() {
    for (store, div) in [(false, false), (true, false), (false, true)] {
        let m = invariant_loop(store, div);
        let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&passes::Licm]);
        assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
        assert_ne!(func(&out, "f"), func(&m, "f"));
        assert_eq!(stats(&report, "licm").functions_changed, 1);
    }
}

#[test]
fn free_instructions_alone_are_not_hoisted() {
    // Only a constant and a pointer cast are invariant: nothing moves.
    let m = module(
        "functy.0 = (ptr, u32) -> (u32)\n\n\
         fn @f(functy.0) {\n\
         bb0(%0: ptr, %1: u32):\n\
         \x20   %2 = const u32 0\n\
         \x20   br bb1(%2, %2)\n\
         bb1(%10: u32, %11: u32):\n\
         \x20   %12 = icmp ult u32 %10, %1\n\
         \x20   condbr %12, bb2, bb3\n\
         bb2:\n\
         \x20   %13 = ptrtoint ptr %0 to u32\n\
         \x20   %14 = const u32 1\n\
         \x20   %15 = add u32 %10, %14\n\
         \x20   %16 = add u32 %11, %15\n\
         \x20   br bb1(%15, %16)\n\
         bb3:\n\
         \x20   ret %11\n\
         }\n",
    );
    assert!(run_pass(&passes::Licm, &m, "f").is_none());
}

#[test]
fn a_division_by_all_ones_or_a_wrapping_zero_is_not_speculated() {
    // A guarded division in the body speculates only when its divisor,
    // at the operation's width, is nonzero and (signed) not -1.
    let guarded = |ty: &str, op: &str, k: &str| {
        module(&format!(
            "functy.0 = ({ty}, u32) -> ({ty})\n\n\
             fn @f(functy.0) {{\n\
             bb0(%0: {ty}, %1: u32):\n\
             \x20   %2 = const u32 0\n\
             \x20   %3 = const {ty} {k}\n\
             \x20   %4 = const {ty} 0\n\
             \x20   br bb1(%2, %4)\n\
             bb1(%10: u32, %11: {ty}):\n\
             \x20   %12 = icmp ult u32 %10, %1\n\
             \x20   condbr %12, bb2, bb3\n\
             bb2:\n\
             \x20   %13 = icmp ne {ty} %0, %4\n\
             \x20   condbr %13, bb4, bb5(%11)\n\
             bb4:\n\
             \x20   %15 = {op} {ty} %0, %3\n\
             \x20   %16 = add {ty} %11, %15\n\
             \x20   br bb5(%16)\n\
             bb5(%17: {ty}):\n\
             \x20   %18 = const u32 1\n\
             \x20   %19 = add u32 %10, %18\n\
             \x20   br bb1(%19, %17)\n\
             bb3:\n\
             \x20   ret %11\n\
             }}\n"
        ))
    };
    for (ty, op, k) in [
        ("u32", "sdiv", "4294967295"),
        ("u32", "srem", "4294967295"),
        ("usize", "udiv", "4294967296"),
        ("usize", "sdiv", "4294967296"),
    ] {
        // The guard's invariant compare may move; the division may not.
        let m = guarded(ty, op, k);
        let moved = run_pass(&passes::Licm, &m, "f").map(|(_, w)| hoisted(&w).1);
        assert!(
            !moved.is_some_and(|h| h.contains(&ValueId::new(15))),
            "{op} {ty} by {k} was hoisted"
        );
    }
    // Controls: the same shapes by a safe divisor hoist and are kept.
    for (ty, op, k) in [
        ("u32", "sdiv", "4294967294"),
        ("usize", "udiv", "4294967297"),
    ] {
        let m = guarded(ty, op, k);
        let (_, w) = run_pass(&passes::Licm, &m, "f").expect("hoists");
        assert!(
            hoisted(&w).1.contains(&ValueId::new(15)),
            "{op} {ty} by {k}"
        );
        let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&passes::Licm]);
        assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
        assert_ne!(func(&out, "f"), func(&m, "f"));
    }
}

/// Closed-form induction whose target adds one to the sum.
struct LyingClosedForm;

impl MidPass for LyingClosedForm {
    fn name(&self) -> &'static str {
        "loop_cf"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let (mut out, w) = passes::LoopClosedForm.run(cx, func)?;
        let node = out.blocks[0].body.iter_mut().find(|n| {
            matches!(
                n.inst,
                Inst::Const {
                    value: Constant::Int(0),
                    ..
                }
            )
        })?;
        node.inst = Inst::Const {
            ty: trust_ir::Ty::U64,
            value: Constant::Int(1),
        };
        Some((out, w))
    }
}

#[test]
fn a_lying_closed_form_is_rolled_back() {
    let m = module(SUM);
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&LyingClosedForm]);
    assert_eq!(out, m, "the snapshot stays");
    assert_eq!(report.rollback_count(), 1);
    assert!(
        report.rollbacks[0].reason.starts_with("witness:"),
        "{:?}",
        report.rollbacks
    );
}

/// The bridge's global-address stub of `@G` (global 0) at `offset`.
const STUB_G: u64 = 0xFADE << 48;

/// A loop indexing the static `@G` with an invariant index `k = b & 7`: the
/// address `G + 4k` is spelled from the bridge's global-address stub
/// constant `stub` (in the body, as the bridge emits it), then loaded.
fn static_indexed_loop(stub: u64) -> Module {
    module(&format!(
        "type ty.0 = u8\n\n\
         functy.0 = (u32, u32) -> (u32)\n\n\
         global internal align(4) @G [ty.0 x 32] = bytes<0100000002000000030000000400000005000000060000000700000008000000>\n\n\
         fn @f(functy.0) {{\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = const u32 0\n\
         \x20   %3 = const u32 7\n\
         \x20   %4 = and u32 %1, %3\n\
         \x20   %5 = const u32 40\n\
         \x20   %6 = urem u32 %0, %5\n\
         \x20   br bb1(%2, %2)\n\
         bb1(%10: u32, %11: u32):\n\
         \x20   %12 = icmp ult u32 %10, %6\n\
         \x20   condbr %12, bb2, bb3\n\
         bb2:\n\
         \x20   %13 = const ptr {stub}\n\
         \x20   %14 = ptrtoint ptr %13 to u32\n\
         \x20   %15 = const u32 4\n\
         \x20   %16 = mul u32 %4, %15\n\
         \x20   %17 = add u32 %14, %16\n\
         \x20   %18 = inttoptr u32 %17 to ptr\n\
         \x20   %19 = load u32, ptr %18\n\
         \x20   %20 = add u32 %11, %19\n\
         \x20   %21 = const u32 1\n\
         \x20   %22 = add u32 %10, %21\n\
         \x20   br bb1(%22, %20)\n\
         bb3:\n\
         \x20   ret %11\n\
         }}\n"
    ))
}

/// Regression (round-13 merge review): the pass and the checker agree on
/// which constants speculate. The stub of a module global at offset zero
/// does (the differential reads it as the global's address), so the address
/// of a static indexed by an invariant index moves and is kept: before, the
/// pass moved any integer constant whatever its type, the checker refused
/// the pointer-typed stub, and every hoist of the function was rolled back.
/// A stub with an offset (a `gep` in the differential's reading) or naming
/// no global of the module stays in the loop, with no rollback, and a
/// witness that moves one anyway is refused by the checker.
#[test]
fn a_static_indexed_by_an_invariant_index_is_hoisted_and_kept() {
    let v = ValueId::new;
    let m = static_indexed_loop(STUB_G);
    let (target, w) = run_pass(&passes::Licm, &m, "f").expect("hoists");
    let moved = hoisted(&w).1;
    assert!(
        moved.contains(&v(13)) && moved.contains(&v(17)),
        "{moved:?}"
    );
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&passes::Licm]);
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_ne!(func(&out, "f"), func(&m, "f"));
    assert_eq!(stats(&report, "licm").functions_changed, 1);
    // The same witness over a stub at offset 4: the checker refuses it.
    let offset = static_indexed_loop(STUB_G + 4);
    let mut lying = target.clone();
    for node in lying.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::Const {
            value: Constant::Int(k),
            ..
        } = &mut node.inst
            && *k == i128::from(STUB_G)
        {
            *k += 4;
        }
    }
    let refused =
        trust_cg_verify::trust_ir_mid_tv::check_pass(&offset, 32, func(&offset, "f"), &lying, &w);
    assert!(
        matches!(
            refused,
            Err(trust_cg_verify::trust_ir_mid_tv::MidTvError::NotLoopRewrite { .. })
        ),
        "{refused:?}"
    );
    // The pass leaves such stubs (and their uses) in the loop.
    for stub in [STUB_G + 4, STUB_G + (5 << 32)] {
        let m = static_indexed_loop(stub);
        let moved = run_pass(&passes::Licm, &m, "f").map(|(_, w)| hoisted(&w).1);
        assert!(
            !moved
                .as_ref()
                .is_some_and(|h| h.contains(&v(13)) || h.contains(&v(17))),
            "{stub:#x}: {moved:?}"
        );
        let (_, report) = manager::run(&m, &MidConfig::wasm32(), &[&passes::Licm]);
        assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    }
}

/// The pass leaves a constant the checker's typing refuses (a `bool`
/// spelled as an integer) in the loop rather than have the witness refused.
#[test]
fn a_constant_the_checker_does_not_type_is_not_hoisted() {
    let m = module(
        "functy.0 = (u32, u32) -> (u32)\n\n\
         fn @f(functy.0) {\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = const u32 0\n\
         \x20   %3 = const u32 3\n\
         \x20   %4 = and u32 %1, %3\n\
         \x20   br bb1(%2, %2)\n\
         bb1(%10: u32, %11: u32):\n\
         \x20   %12 = icmp ult u32 %10, %0\n\
         \x20   condbr %12, bb2, bb3\n\
         bb2:\n\
         \x20   %13 = const bool 1\n\
         \x20   %14 = const u32 5\n\
         \x20   %15 = mul u32 %4, %14\n\
         \x20   %16 = select u32 %13, %15, %4\n\
         \x20   %17 = add u32 %11, %16\n\
         \x20   %18 = const u32 1\n\
         \x20   %19 = add u32 %10, %18\n\
         \x20   br bb1(%19, %17)\n\
         bb3:\n\
         \x20   ret %11\n\
         }\n",
    );
    let v = ValueId::new;
    let (_, w) = run_pass(&passes::Licm, &m, "f").expect("hoists the product");
    let moved = hoisted(&w).1;
    assert!(moved.contains(&v(15)), "{moved:?}");
    assert!(
        !moved.contains(&v(13)) && !moved.contains(&v(16)),
        "{moved:?}"
    );
    let (_, report) = manager::run(&m, &MidConfig::wasm32(), &[&passes::Licm]);
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
}
