// trust-cg-irmid/unroll_tests.rs - full unrolling, strength reduction and their cleanup
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The passes of round 14: full unrolling, constant folding, algebraic
//! simplification, address folding, dead block parameters, block merging,
//! strength reduction and the load tier (b) of invariant code motion. Each
//! rewrite is made where its shape holds and kept by its checker and the
//! interpreter differential; over the pipeline a constant-trip loop over a
//! local array leaves neither the loop nor the array. Each pass leaves the
//! shapes outside its rule alone (a trip count over the policy's bound, a
//! body the validator flags, a side exit whose target reads the header
//! after a join; a scale of one; a store through an unknown pointer), and
//! a pass that lies is rolled back and counted. The unroller's cost model
//! makes no copy that keeps a call or a 128-bit operation, and still
//! unrolls a loop over a 128-bit table in a slot. The witness types are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use trust_cg_verify::trust_ir_mid_tv::PassWitness;
use trust_ir::{BlockId, Function, Inst, Module};

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

/// Whether some block of `f` branches to a block at or before itself.
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

fn edited(text: &str, edit: &[(&str, &str)]) -> Module {
    let mut text = text.to_string();
    for (from, to) in edit {
        assert!(text.contains(from), "{from}");
        text = text.replace(from, to);
    }
    module(&text)
}

/// `horner`'s shape: a constant table in a slot walked backwards by a
/// pointer from one past its end (`p != begin`, `p -= 8` through the
/// bridge's integer round trips).
const HORNER: &str = "functy.0 = (f64) -> (f64)\n\n\
type ty.0 = f64\n\n\
fn @f(functy.0) {\n\
bb0(%0: f64):\n\
\x20   %1 = alloca [ty.0 x 3], align 8\n\
\x20   %2 = const f64 1.0\n\
\x20   store f64 %2, ptr %1\n\
\x20   %3 = const f64 -0.5\n\
\x20   %4 = const i32 8\n\
\x20   %5 = gep inbounds u8, ptr %1, %4\n\
\x20   store f64 %3, ptr %5\n\
\x20   %6 = const f64 0.25\n\
\x20   %7 = const i32 16\n\
\x20   %8 = gep inbounds u8, ptr %1, %7\n\
\x20   store f64 %6, ptr %8\n\
\x20   %9 = ptrtoint ptr %1 to i32\n\
\x20   %10 = const u32 3\n\
\x20   %11 = bitcast u32 %10 to i32\n\
\x20   %12 = mul i32 %11, %4\n\
\x20   %13 = add i32 %9, %12\n\
\x20   %14 = const f64 0.0\n\
\x20   br bb1(%14, %13)\n\
bb1(%20: f64, %21: i32):\n\
\x20   %22 = inttoptr i32 %21 to ptr\n\
\x20   %23 = ptrtoptr ptr %22 to *const f64\n\
\x20   %24 = inttoptr i32 %9 to ptr\n\
\x20   %25 = ptrtoptr ptr %24 to *const f64\n\
\x20   %26 = icmp eq *const f64 %25, %23\n\
\x20   condbr %26, bb2, bb3\n\
bb3:\n\
\x20   %27 = inttoptr i32 %21 to ptr\n\
\x20   %28 = ptrtoint ptr %27 to i32\n\
\x20   %29 = const i32 -8\n\
\x20   %30 = add i32 %28, %29\n\
\x20   %31 = inttoptr i32 %30 to ptr\n\
\x20   %32 = load f64, ptr %31\n\
\x20   %33 = fmul f64 %20, %0\n\
\x20   %34 = fadd f64 %33, %32\n\
\x20   br bb1(%34, %30)\n\
bb2:\n\
\x20   ret %20\n\
}\n";

#[test]
fn a_constant_table_walked_by_a_pointer_loses_its_loop_and_its_slot() {
    let m = module(HORNER);
    assert!(loops_back(func(&m, "f")));
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert!(!loops_back(f), "{f}");
    assert_eq!(report.allocas_after, 0, "{f}");
    assert!(
        !f.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Load { .. } | Inst::Store { .. })),
        "{f}"
    );
    for pass in ["unroll", "addr_fold", "dead_param", "merge"] {
        assert!(stats(&report, pass).functions_changed >= 1, "{pass}");
    }
    let tv = report.tv.by_pass.get("unroll").expect("unroll candidates");
    assert_eq!(tv.compared, 1, "{tv:?}");
}

/// `for i in 0..8 { h = h * 3 + ((a >> i) & 1) }`.
const BITS: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 0\n\
\x20   br bb1(%1, %1)\n\
bb1(%10: u32, %11: u32):\n\
\x20   %12 = const u32 8\n\
\x20   %13 = icmp ult u32 %10, %12\n\
\x20   condbr %13, bb2, bb3\n\
bb2:\n\
\x20   %14 = const u32 31\n\
\x20   %15 = and u32 %10, %14\n\
\x20   %16 = lshr u32 %0, %15\n\
\x20   %17 = const u32 1\n\
\x20   %18 = and u32 %16, %17\n\
\x20   %19 = const u32 3\n\
\x20   %20 = mul u32 %11, %19\n\
\x20   %21 = add u32 %20, %18\n\
\x20   %22 = add u32 %10, %17\n\
\x20   br bb1(%22, %21)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

#[test]
fn a_counted_loop_is_unrolled_and_its_induction_folded() {
    let m = module(BITS);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert!(!loops_back(f), "{f}");
    // The shift amounts are constants now: no `and` of the variable left,
    // and the first shift (by 0) is gone.
    let shifts = f
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| {
            matches!(
                n.inst,
                Inst::BinOp {
                    op: trust_ir::BinOp::LShr,
                    ..
                }
            )
        })
        .count();
    assert_eq!(shifts, 7, "{f}");
    assert!(stats(&report, "const_fold").functions_changed >= 1);
    assert!(stats(&report, "simplify").functions_changed >= 1);
}

/// A counted loop that converts a float to an integer each trip: `{CAST}` is
/// `fptosi.sat` (Rust's `as`, what the rustc bridge emits) or the raw
/// `fptosi`.
const FLOAT_TO_INT: &str = "functy.0 = (f64) -> (i32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: f64):\n\
\x20   %1 = const u32 0\n\
\x20   %2 = const i32 0\n\
\x20   br bb1(%1, %2)\n\
bb1(%10: u32, %11: i32):\n\
\x20   %12 = const u32 4\n\
\x20   %13 = icmp ult u32 %10, %12\n\
\x20   condbr %13, bb2, bb3\n\
bb2:\n\
\x20   %14 = uitofp u32 %10 to f64\n\
\x20   %15 = fmul f64 %0, %14\n\
\x20   %16 = {CAST} f64 %15 to i32\n\
\x20   %17 = add i32 %11, %16\n\
\x20   %18 = const u32 1\n\
\x20   %19 = add u32 %10, %18\n\
\x20   br bb1(%19, %17)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

/// The saturating float -> integer conversion is a body instruction the
/// unroller copies, as the raw one is: the validator reads both with the
/// same shape rule, and the bridge lowers every `as` to the saturating form.
#[test]
fn a_loop_converting_a_float_to_an_integer_is_unrolled() {
    for cast in ["fptosi.sat", "fptosi"] {
        let m = module(&FLOAT_TO_INT.replace("{CAST}", cast));
        let (out, report) = optimize_module(&m, &MidConfig::wasm32());
        assert_eq!(report.rollback_count(), 0, "{cast}: {:?}", report.rollbacks);
        let f = func(&out, "f");
        assert!(!loops_back(f), "{cast}: the loop was kept:\n{f}");
    }
}

#[test]
fn unrolling_leaves_loops_outside_its_shape() {
    // A trip count over the policy's bound.
    let m = edited(BITS, &[("%12 = const u32 8", "%12 = const u32 20")]);
    assert!(run_pass(&passes::Unroll, &m, "f").is_none());
    // A bound that varies.
    let m = edited(
        BITS,
        &[("%13 = icmp ult u32 %10, %12", "%13 = icmp ult u32 %10, %0")],
    );
    assert!(run_pass(&passes::Unroll, &m, "f").is_none());
    // A body instruction the validator flags (an operand of another type).
    let m = edited(
        BITS,
        &[(
            "%21 = add u32 %20, %18",
            "%40 = bitcast u32 %18 to i32\n\x20   %21 = add u32 %20, %40",
        )],
    );
    assert!(run_pass(&passes::Unroll, &m, "f").is_none());
    // A side exit to a block that joins the header's exit and reads the
    // header's value.
    let m = edited(
        BITS,
        &[
            (
                "\x20   %22 = add u32 %10, %17\n\x20   br bb1(%22, %21)\n",
                "\x20   %22 = add u32 %10, %17\n\x20   %40 = icmp eq u32 %21, %0\n\x20   condbr %40, bb4, bb5\nbb5:\n\x20   br bb1(%22, %21)\nbb4:\n\x20   br bb6\n",
            ),
            (
                "bb3:\n\x20   ret %11\n",
                "bb3:\n\x20   br bb6\nbb6:\n\x20   ret %11\n",
            ),
        ],
    );
    assert!(run_pass(&passes::Unroll, &m, "f").is_none());
}

struct LyingUnroll;

impl MidPass for LyingUnroll {
    fn name(&self) -> &'static str {
        "unroll"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let (out, mut w) = passes::Unroll.run(cx, func)?;
        // One iteration fewer than the copies.
        if let PassWitness::Unroll(uw) = &mut w {
            uw.loops[0].trips -= 1;
        }
        Some((out, w))
    }
}

#[test]
fn a_lying_unroll_is_rolled_back() {
    let m = module(BITS);
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&LyingUnroll]);
    assert_eq!(out, m, "the snapshot stays");
    assert_eq!(report.rollback_count(), 1);
    assert!(
        report.rollbacks[0].reason.starts_with("witness:"),
        "{:?}",
        report.rollbacks
    );
}

/// Row-major `a[i * 4 + j]` summed over `j` in a loop the unrollers leave
/// (a variable bound, `3 - (n & 3)`, whose interval neither full nor
/// interval-bounded unrolling derives): the element address is linear in
/// `j`.
const ROW: &str = "functy.0 = (ptr, u32, u32) -> (u64)\n\n\
fn @f(functy.0) {\n\
bb0(%0: ptr, %1: u32, %2: u32):\n\
\x20   %3 = const u32 3\n\
\x20   %7 = and u32 %2, %3\n\
\x20   %4 = sub u32 %3, %7\n\
\x20   %5 = const u32 0\n\
\x20   %6 = const u64 0\n\
\x20   br bb1(%5, %6)\n\
bb1(%10: u32, %11: u64):\n\
\x20   %12 = icmp ult u32 %10, %4\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = const u32 4\n\
\x20   %14 = mul u32 %1, %13\n\
\x20   %15 = add u32 %14, %10\n\
\x20   %16 = ptrtoint ptr %0 to i32\n\
\x20   %17 = bitcast u32 %15 to i32\n\
\x20   %18 = const i32 8\n\
\x20   %19 = mul i32 %17, %18\n\
\x20   %20 = add i32 %16, %19\n\
\x20   %21 = inttoptr i32 %20 to ptr\n\
\x20   %22 = load u64, ptr %21\n\
\x20   %23 = add u64 %11, %22\n\
\x20   %24 = const u32 1\n\
\x20   %25 = add u32 %10, %24\n\
\x20   br bb1(%25, %23)\n\
bb3:\n\
\x20   ret %11\n\
}\n";

#[test]
fn a_row_major_address_becomes_a_pointer_induction_variable() {
    let m = module(ROW);
    let (out, witness) = run_pass(&passes::IvStrength, &m, "f").expect("a strand");
    let PassWitness::IvSr(w) = &witness else {
        panic!("strength-reduction witness");
    };
    let strand = &w.loops[0].strands[0];
    assert_eq!(strand.scale, 8);
    // Two roots: the base pointer, and `i * 4` (the outer index) times 8.
    assert_eq!(strand.roots.len(), 2, "{strand:?}");
    assert_eq!(strand.uses.len(), 1);
    // The replaced address is the new parameter, read in place.
    let replaced = out
        .blocks
        .iter()
        .flat_map(|b| &b.body)
        .find(|n| n.results.first() == Some(&strand.uses[0].value))
        .expect("the replaced value");
    assert!(
        matches!(&replaced.inst, Inst::Copy { operand, .. } if *operand == strand.param),
        "{out}"
    );
    let (opt, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "iv_sr").functions_changed, 1);
    let tv = report.tv.by_pass.get("iv_sr").expect("candidates");
    assert_eq!(tv.compared, 1, "{tv:?}");
    let f = func(&opt, "f");
    let muls = f
        .blocks
        .iter()
        .filter(|b| b.id != f.entry)
        .flat_map(|b| &b.body)
        .filter(|n| {
            matches!(
                n.inst,
                Inst::BinOp {
                    op: trust_ir::BinOp::Mul,
                    ..
                }
            )
        })
        .count();
    assert_eq!(muls, 0, "every multiply left the loop: {f}");
}

#[test]
fn strength_reduction_leaves_a_unit_scale_and_a_variable_step() {
    // `a + j * 1`: nothing to reduce.
    let m = edited(ROW, &[("%18 = const i32 8", "%18 = const i32 1")]);
    assert!(run_pass(&passes::IvStrength, &m, "f").is_none());
    // A step that is not a constant.
    let m = edited(ROW, &[("%25 = add u32 %10, %24", "%25 = add u32 %10, %1")]);
    assert!(run_pass(&passes::IvStrength, &m, "f").is_none());
}

/// A load of one slot in a loop that stores to another.
const TWO_SLOTS: &str = "functy.0 = (u32, ptr) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32, %9: ptr):\n\
\x20   %1 = alloca u32, align 4\n\
\x20   %2 = alloca u32, align 4\n\
\x20   store u32 %0, ptr %1\n\
\x20   store u32 %0, ptr %2\n\
\x20   %3 = const u32 0\n\
\x20   br bb1(%3)\n\
bb1(%10: u32):\n\
\x20   %11 = load u32, ptr %1\n\
\x20   %12 = icmp ult u32 %10, %0\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = add u32 %10, %11\n\
\x20   store u32 %13, ptr %2\n\
\x20   %14 = const u32 1\n\
\x20   %15 = add u32 %10, %14\n\
\x20   br bb1(%15)\n\
bb3:\n\
\x20   %16 = load u32, ptr %2\n\
\x20   ret %16\n\
}\n";

#[test]
fn a_load_beside_a_store_to_another_slot_is_hoisted() {
    let m = module(TWO_SLOTS);
    let (out, witness) = run_pass(&passes::Licm, &m, "f").expect("a hoist");
    let PassWitness::Licm(w) = &witness else {
        panic!("licm witness");
    };
    assert!(
        w.loops[0].hoisted.contains(&trust_ir::ValueId::new(11)),
        "{w:?}"
    );
    assert!(
        out.blocks[0]
            .body
            .iter()
            .any(|n| matches!(n.inst, Inst::Load { .. })),
        "{out}"
    );
    // Through an unknown pointer the store may alias: the load stays.
    let m = edited(
        TWO_SLOTS,
        &[("store u32 %13, ptr %2", "store u32 %13, ptr %9")],
    );
    let moved = run_pass(&passes::Licm, &m, "f").is_some_and(|(_, w)| match w {
        PassWitness::Licm(w) => w.loops[0].hoisted.contains(&trust_ir::ValueId::new(11)),
        _ => false,
    });
    assert!(!moved);
}

/// A load of global `@a` through one `global_addr` in a loop that stores
/// through `%2`, a second `global_addr` of a global (`@global.0`, the same
/// one, in the source text).
const TWO_GLOBAL_ADDRS: &str = "functy.0 = (u32) -> (u32)\n\n\
type ty.0 = u8\n\n\
global internal align(4) @a [ty.0 x 8] = bytes<0700000000000000>\n\n\
global internal align(4) @b [ty.0 x 8] = bytes<0000000000000000>\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = global_addr @global.0\n\
\x20   %2 = global_addr @global.0\n\
\x20   %5 = const u32 7\n\
\x20   %7 = and u32 %0, %5\n\
\x20   %6 = sub u32 %5, %7\n\
\x20   %3 = const u32 0\n\
\x20   br bb1(%3, %3)\n\
bb1(%10: u32, %30: u32):\n\
\x20   %11 = load u32, ptr %1\n\
\x20   %12 = icmp ult u32 %10, %6\n\
\x20   condbr %12, bb2, bb3\n\
bb2:\n\
\x20   %13 = add u32 %30, %11\n\
\x20   %14 = const u32 1\n\
\x20   %15 = add u32 %10, %14\n\
\x20   store u32 %15, ptr %2\n\
\x20   br bb1(%15, %13)\n\
bb3:\n\
\x20   ret %30\n\
}\n";

#[test]
fn a_load_beside_a_store_through_another_global_addr_of_its_global_stays() {
    let hoists = |m: &Module| {
        run_pass(&passes::Licm, m, "f").is_some_and(|(_, w)| match w {
            PassWitness::Licm(w) => w
                .loops
                .iter()
                .any(|l| l.hoisted.contains(&trust_ir::ValueId::new(11))),
            _ => false,
        })
    };
    // The same bytes, and overlapping bytes, of the same global: the load
    // stays.
    assert!(!hoists(&module(TWO_GLOBAL_ADDRS)));
    let m = edited(
        TWO_GLOBAL_ADDRS,
        &[(
            "store u32 %15, ptr %2",
            "%20 = const i32 2\n\x20   %21 = gep inbounds u8, ptr %2, %20\n\x20   store u32 %15, ptr %21",
        )],
    );
    assert!(!hoists(&m));
    // The whole mid-end keeps the loop's reads of the stored global.
    let (out, report) = optimize_module(&module(TWO_GLOBAL_ADDRS), &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert!(loops_back(f), "{f}");
    // Other bytes of the same global, or another global: the load moves.
    let m = edited(
        TWO_GLOBAL_ADDRS,
        &[(
            "store u32 %15, ptr %2",
            "%20 = const i32 4\n\x20   %21 = gep inbounds u8, ptr %2, %20\n\x20   store u32 %15, ptr %21",
        )],
    );
    assert!(hoists(&m));
    let m = edited(
        TWO_GLOBAL_ADDRS,
        &[("%2 = global_addr @global.0", "%2 = global_addr @global.1")],
    );
    assert!(hoists(&m));
}

/// `cmp_accum`'s unrolled shape: `rotate_left(k * c) & 0xf` per copy.
const MASKED_ROTATES: &str = "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 5\n\
\x20   %2 = rotl u32 %0, %1\n\
\x20   %3 = const u32 15\n\
\x20   %4 = and u32 %2, %3\n\
\x20   %5 = const u32 3\n\
\x20   %6 = rotl u32 %0, %5\n\
\x20   %7 = and u32 %6, %3\n\
\x20   %8 = add u32 %4, %7\n\
\x20   ret %8\n\
}\n";

#[test]
fn a_rotate_masked_to_its_top_bits_becomes_a_shift() {
    let m = module(MASKED_ROTATES);
    let (out, w) = run_pass(&passes::SimplifyPass, &m, "f").expect("a rewrite");
    let PassWitness::Simplify(w) = &w else {
        panic!("simplify witness");
    };
    // `rotl 5` under `15` reads `x >> 27`; `rotl 3` under `15` keeps bit 3
    // of `x << 3` and stays.
    assert_eq!(w.rewrites.len(), 1, "{w:?}");
    assert_eq!(w.rewrites[0].value, trust_ir::ValueId::new(2));
    let rotates = |f: &Function| {
        f.blocks
            .iter()
            .flat_map(|b| &b.body)
            .filter(|n| {
                matches!(
                    n.inst,
                    Inst::BinOp {
                        op: trust_ir::BinOp::RotL,
                        ..
                    }
                )
            })
            .count()
    };
    assert_eq!(rotates(&out), 1, "{out}");
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(rotates(func(&out, "f")), 1);
}

#[test]
fn constants_fold_simplifications_apply_and_dead_parameters_go() {
    let m = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const u32 6\n\
\x20   %2 = const u32 7\n\
\x20   %3 = mul u32 %1, %2\n\
\x20   %4 = const u32 0\n\
\x20   %5 = or u32 %0, %4\n\
\x20   %6 = add u32 %5, %3\n\
\x20   br bb1(%6, %3)\n\
bb1(%7: u32, %8: u32):\n\
\x20   ret %7\n\
}\n",
    );
    let (_, w) = run_pass(&passes::ConstFoldPass, &m, "f").expect("a fold");
    assert_eq!(w.rewrite_count(), 1);
    let (_, w) = run_pass(&passes::SimplifyPass, &m, "f").expect("an identity");
    assert_eq!(w.rewrite_count(), 1);
    let (_, w) = run_pass(&passes::DeadParamPass, &m, "f").expect("a dead parameter");
    assert_eq!(w.rewrite_count(), 1);
    let (_, w) = run_pass(&passes::MergeBlocks, &m, "f").expect("a merge");
    assert_eq!(w.rewrite_count(), 1);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert_eq!(f.blocks.len(), 1, "{f}");
}

/// A hidden callee reading a field through a pointer (the bridge's
/// `extractfield` over a pointer), called on the caller's slot.
const FIELD_CALLEE: &str = "functy.0 = (&(u32, u32)) -> (u32)\n\n\
functy.1 = (u32, u32) -> (u32)\n\n\
type ty.0 = u32\n\n\
fn @get.tcg.crate.0000000000000001(functy.0) {\n\
\x20   ; #visibility: hidden\n\
bb0(%0: &(u32, u32)):\n\
\x20   %1 = extractfield (u32, u32) %0, 1\n\
\x20   %2 = extractfield (u32, u32) %0, 0\n\
\x20   %3 = sub u32 %1, %2\n\
\x20   ret %3\n\
}\n\n\
fn @f(functy.1) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 2], align 4\n\
\x20   store u32 %0, ptr %2\n\
\x20   %3 = const i32 4\n\
\x20   %4 = gep inbounds u8, ptr %2, %3\n\
\x20   store u32 %1, ptr %4\n\
\x20   %5 = ptrtoptr ptr %2 to &(u32, u32)\n\
\x20   %6 = call @func.0(%5)\n\
\x20   ret %6\n\
}\n";

#[test]
fn a_callee_reading_fields_through_a_pointer_is_inlined_and_its_slot_dissolves() {
    let m = module(FIELD_CALLEE);
    let (callee, w) = run_pass(
        &passes::FieldAccessPass,
        &m,
        "get.tcg.crate.0000000000000001",
    )
    .expect("two reads");
    assert_eq!(w.rewrite_count(), 2);
    assert!(
        !callee
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::ExtractField { .. } | Inst::InsertField { .. }))
    );
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    let f = func(&out, "f");
    assert!(
        !f.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Call { .. } | Inst::Alloca { .. })),
        "{f}"
    );
    assert_eq!(stats(&report, "inline").functions_changed, 1);
}

#[test]
fn a_bool_constant_spelled_as_an_integer_is_respelled() {
    let m = module(
        "functy.0 = (u32) -> (u32)\n\n\
fn @f(functy.0) {\n\
bb0(%0: u32):\n\
\x20   %1 = const bool 1\n\
\x20   %2 = const u32 7\n\
\x20   %3 = select u32 %1, %0, %2\n\
\x20   ret %3\n\
}\n",
    );
    let (out, w) = run_pass(&passes::ConstFoldPass, &m, "f").expect("a respelling");
    assert_eq!(w.rewrite_count(), 1);
    assert!(matches!(
        out.blocks[0].body[0].inst,
        Inst::Const {
            value: trust_ir::Constant::Bool(true),
            ..
        }
    ));
}

/// The cost model (round 15): a copy that keeps a call or a 128-bit
/// operation is not made; a 128-bit slot access at a constant offset is not
/// such an operation (scalar replacement removes it once the offset is a
/// constant), nor is a 128-bit extension or truncation.
#[test]
fn copies_that_keep_a_call_or_a_wide_operation_are_not_made() {
    let pass = passes::Unroll;
    let with = |edit: &[(&str, &str)]| {
        let mut text = BITS.to_string();
        for (from, to) in edit {
            assert!(text.contains(from), "{from}");
            text = text.replace(from, to);
        }
        text
    };
    // The counted loop unrolls as it is.
    assert!(run_pass(&pass, &module(BITS), "f").is_some());
    // A call in the body: each copy would keep it.
    let call = with(&[
        (
            "fn @f(functy.0) {",
            "fn @g(functy.0) {\nbb0(%0: u32):\n    ret %0\n}\n\nfn @f(functy.0) {",
        ),
        (
            "%21 = add u32 %20, %18",
            "%30 = call @func.0(%18)\n\x20   %21 = add u32 %20, %30",
        ),
    ]);
    assert!(run_pass(&pass, &module(&call), "f").is_none());
    // A 128-bit multiply of the argument: each copy would keep it.
    let wide = with(&[(
        "%21 = add u32 %20, %18",
        "%31 = zext u32 %0 to u128\n\x20   %32 = mul u128 %31, %31\n\x20   \
         %33 = trunc u128 %32 to u32\n\x20   %34 = add u32 %20, %18\n\x20   \
         %21 = xor u32 %34, %33",
    )]);
    assert!(run_pass(&pass, &module(&wide), "f").is_none());
    // A 128-bit table in a slot read at the induction variable: each copy
    // reads it at a constant offset, so the loop unrolls.
    let table = with(&[
        (
            "functy.0 = (u32) -> (u32)\n\n",
            "functy.0 = (u32) -> (u32)\n\ntype ty.0 = u128\n\n",
        ),
        (
            "bb0(%0: u32):\n",
            "bb0(%0: u32):\n\x20   %40 = alloca [ty.0 x 8], align 16\n",
        ),
        (
            "%21 = add u32 %20, %18",
            "%41 = const u32 16\n\x20   %42 = mul u32 %10, %41\n\x20   \
             %43 = ptrtoint ptr %40 to u32\n\x20   %44 = add u32 %43, %42\n\x20   \
             %45 = inttoptr u32 %44 to ptr\n\x20   %46 = load u128, ptr %45\n\x20   \
             %47 = trunc u128 %46 to u32\n\x20   %48 = add u32 %20, %18\n\x20   \
             %21 = xor u32 %48, %47",
        ),
    ]);
    assert!(run_pass(&pass, &module(&table), "f").is_some());
}
