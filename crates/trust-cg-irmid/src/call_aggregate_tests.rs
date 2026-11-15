// trust-cg-irmid/call_aggregate_tests.rs - the round-17 stage-B rewrites over the pipeline
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Over the wasm32 pipeline, each kept by its checker and compared by the
//! interpreter differential (and run again here in the differential's
//! view): a closure whose environment the rustc bridge passes as a `[u32 x
//! 1]` array by the address of the caller's slot and whose `Option<u8>`
//! result it returns by the address of its own slot is spliced into the
//! caller's loop, its environment and result read as scalars (no call, no
//! slot left); a slice-iterator step comparing `*mut u32`s and reading a
//! `*const` lane as `*mut` is spliced once its comparison and copy are
//! respelled; a callee whose `memcopy` count is a `u32` and whose niche is
//! `const i8 254` is spliced once both are respelled; the default profile
//! withholds the comparison-call rewrite (OD-164) and keeps a `memcmp`
//! call, and the pass run on its own turns a `memcmp` of three bytes read
//! by a zero test into loads and compares (kept by its checker; the
//! differential's view gives the declaration no body). Controls: a `memcmp` whose
//! result's sign is read stays a call, a closure reading
//! its environment by lane and also passing it on whole stays a call, a
//! comparison expansion spelled with signed bytes is rolled back, and a
//! packed callee that frees, drops, retains or releases memory through
//! another pointer between its lane copies and its loads gets no clone, nor
//! does one that writes the caller's array there through an `i64` or `u64`
//! pointer carrier, or builds an `insertfield` there over an `i32`, `usize`
//! or `fatptr<str>` operand (a type the allowlist does not name). Run on
//! its own, by-address cloning proposes none of these clones its checker
//! would roll back: an `insertfield` over a `select`, `undef` or
//! `insertfield` array value, a `select` or `nullptr` argument, an array it
//! does not promote read ahead of the promoted one's copies, interleaved
//! copies whose plan empties only in a third round, and a kept thin-pointer
//! parameter entered as another pointer type than declared. The pass
//! names `lane_load`, `respell`, `mem_cmp` and `byaddr` and the witness types are
//! provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use trust_cg_verify::trust_ir_mid_tv::{
    DifferentialBudget, PassWitness, compare_samples, interpretable, interpretable_module,
    run_samples, seeded_inputs,
};
use trust_ir::{CastOp, Function, Inst, Module};

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

fn count(f: &Function, pred: impl Fn(&Inst) -> bool) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| pred(&n.inst))
        .count()
}

fn calls(f: &Function) -> usize {
    count(f, |i| matches!(i, Inst::Call { .. }))
}

/// `f` of `out` against `f` of `m`, both run in the differential's view on
/// seeded inputs: they agree, and some inputs are compared.
fn agrees_in_the_view(m: &Module, out: &Module) {
    let inputs = seeded_inputs(m, func(m, "f"), 32, 32, 3).expect("scalar parameters");
    let run = |module: &Module| {
        let view = interpretable_module(module);
        let f = func(module, "f");
        let viewed = interpretable(&view, f).unwrap_or_else(|| f.clone());
        run_samples(&view, &viewed, &inputs, DifferentialBudget::default()).0
    };
    let report = compare_samples(&run(m), &run(out));
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "{report:?}");
}

/// The closure `clo(env, x) = Some((env[0] + x) as u8)` as the bridge
/// spells it (`{body}` after its result slot), and `f(a, b)` summing
/// `clo(&[a], i)` over `i < 4 + (b & 3)`.
fn closure(body: &str) -> Module {
    module(&format!(
        "type ty.0 = u32\ntype ty.1 = u8\n\n\
         functy.0 = ([ty.0 x 1], u32) -> ([ty.1 x 1])\n\
         functy.1 = (u32, u32) -> (u32)\n\
         functy.2 = ([ty.0 x 1]) -> (u32)\n\n\
         fn @clo(functy.0) {{\n\
         bb0(%0: [ty.0 x 1], %1: u32):\n\
         \x20   %2 = alloca [ty.1 x 1], align 1\n\
         {body}\
         }}\n\n\
         fn @sink(functy.2) {{\n\
         bb0(%0: [ty.0 x 1]):\n\
         \x20   %1 = extractfield [ty.0 x 1] %0, 0\n\
         \x20   ret %1\n\
         }}\n\n\
         fn @f(functy.1) {{\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = alloca [ty.0 x 1], align 4\n\
         \x20   store u32 %0, ptr %2\n\
         \x20   %3 = const u32 0\n\
         \x20   %14 = const u32 3\n\
         \x20   %15 = and u32 %1, %14\n\
         \x20   %16 = const u32 4\n\
         \x20   %17 = add u32 %15, %16\n\
         \x20   br bb1(%3, %3)\n\
         bb1(%4: u32, %5: u32):\n\
         \x20   %6 = call @func.0(%2, %4)\n\
         \x20   %7 = extractfield [ty.1 x 1] %6, 0\n\
         \x20   %8 = zext u8 %7 to u32\n\
         \x20   %9 = add u32 %5, %8\n\
         \x20   %10 = const u32 1\n\
         \x20   %11 = add u32 %4, %10\n\
         \x20   %13 = icmp ult u32 %11, %17\n\
         \x20   condbr %13, bb1(%11, %9), bb2\n\
         bb2:\n\
         \x20   ret %9\n\
         }}\n"
    ))
}

const CLOSURE: &str = "\x20   %3 = extractfield [ty.0 x 1] %0, 0\n\
    \x20   %4 = add u32 %3, %1\n\
    \x20   %5 = trunc u32 %4 to u8\n\
    \x20   store u8 %5, ptr %2\n\
    \x20   ret %2\n";

#[test]
fn a_closure_with_its_environment_and_result_by_address_is_spliced_into_a_loop() {
    let m = closure(CLOSURE);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(stats(&report, "inline").functions_changed >= 1);
    assert!(stats(&report, "lane_load").functions_changed >= 1);
    let f = func(&out, "f");
    assert_eq!(calls(f), 0, "{f}");
    assert_eq!(count(f, |i| matches!(i, Inst::Alloca { .. })), 0, "{f}");
    assert_eq!(
        count(f, |i| matches!(i, Inst::ExtractField { .. })),
        0,
        "no array-value lane read is left: {f}"
    );
    assert!(
        report
            .tv
            .by_pass
            .get("lane_load")
            .is_some_and(|c| c.compared > 0)
    );
    agrees_in_the_view(&m, &out);
}

#[test]
fn a_closure_passing_its_environment_on_stays_a_call() {
    // The environment is read by lane and also reaches another call whole:
    // not every use of it is a lane read, so lane-load scalarization could
    // not take the spliced lane read apart (trust-ir's validator reports
    // it), and the policy leaves the closure called.
    let passes_on = "\x20   %6 = extractfield [ty.0 x 1] %0, 0\n\
        \x20   %3 = call @func.1(%0)\n\
        \x20   %7 = add u32 %3, %6\n\
        \x20   %4 = add u32 %7, %1\n\
        \x20   %5 = trunc u32 %4 to u8\n\
        \x20   store u8 %5, ptr %2\n\
        \x20   ret %2\n";
    let m = closure(passes_on);
    let mut config = MidConfig::wasm32();
    config.never_inline.insert("sink".to_string());
    let (out, report) = optimize_module(&m, &config);
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(
        func(&out, "f")
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(
                n.inst,
                Inst::Call { callee, .. } if callee == func(&m, "clo").id
            )),
        "the closure stays a call"
    );
}

/// A slice iterator's step as the bridge spells it: the position read
/// through `&mut (*const u32, *const u32)` and copied as `*mut u32`, the end
/// cast, and the two compared at `*mut u32`; `f` sums the elements of a
/// four-word slot while the step says so.
const ITER: &str = "type ty.0 = u32\n\n\
functy.0 = (&mut (*const u32, *const u32)) -> (u32)\n\
functy.1 = (u32, u32) -> (u32)\n\n\
fn @step(functy.0) {\n\
bb0(%0: &mut (*const u32, *const u32)):\n\
\x20   %1 = extractfield (*const u32, *const u32) %0, 0\n\
\x20   %2 = extractfield (*const u32, *const u32) %0, 1\n\
\x20   %3 = copy *mut u32 %1\n\
\x20   %4 = ptrtoptr *const u32 %2 to *mut u32\n\
\x20   %5 = icmp eq *mut u32 %3, %4\n\
\x20   condbr %5, bb1, bb2\n\
bb1:\n\
\x20   %6 = const u32 0\n\
\x20   ret %6\n\
bb2:\n\
\x20   %7 = load u32, ptr %3\n\
\x20   %8 = const usize 4\n\
\x20   %9 = gep u8, ptr %3, %8\n\
\x20   %10 = ptrtoptr ptr %9 to *const u32\n\
\x20   %11 = insertfield (*const u32, *const u32) %0, 0, %10\n\
\x20   ret %7\n\
}\n\n\
fn @f(functy.1) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 4], align 4\n\
\x20   store u32 %0, ptr %2\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   store u32 %1, ptr %4\n\
\x20   %5 = const usize 8\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   %7 = xor u32 %0, %1\n\
\x20   store u32 %7, ptr %6\n\
\x20   %8 = const usize 12\n\
\x20   %9 = gep u8, ptr %2, %8\n\
\x20   store u32 %0, ptr %9\n\
\x20   %10 = alloca (*const u32, *const u32), align 4\n\
\x20   %11 = ptrtoptr ptr %2 to *const u32\n\
\x20   %12 = const u32 3\n\
\x20   %13 = and u32 %1, %12\n\
\x20   %14 = const u32 4\n\
\x20   %15 = mul u32 %13, %14\n\
\x20   %16 = bitcast u32 %15 to usize\n\
\x20   %17 = gep u8, ptr %2, %16\n\
\x20   %18 = ptrtoptr ptr %17 to *const u32\n\
\x20   store *const u32 %11, ptr %10\n\
\x20   %19 = const usize 4\n\
\x20   %20 = gep u8, ptr %10, %19\n\
\x20   store *const u32 %18, ptr %20\n\
\x20   %21 = const u32 0\n\
\x20   br bb1(%21)\n\
bb1(%22: u32):\n\
\x20   %23 = ptrtoptr ptr %10 to &mut (*const u32, *const u32)\n\
\x20   %24 = call @func.0(%23)\n\
\x20   %25 = add u32 %22, %24\n\
\x20   %26 = const u32 0\n\
\x20   %27 = icmp ne u32 %24, %26\n\
\x20   condbr %27, bb1(%25), bb2\n\
bb2:\n\
\x20   ret %25\n\
}\n";

#[test]
fn a_slice_step_is_spliced_once_its_compare_and_copy_are_respelled() {
    let m = module(ITER);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    for pass in ["respell", "field_access", "retype_copy", "inline"] {
        assert!(stats(&report, pass).functions_changed >= 1, "{pass}");
    }
    let step = func(&out, "step");
    assert_eq!(
        count(step, |i| matches!(
            i,
            Inst::ICmp {
                ty: trust_ir::Ty::PtrMut(_),
                ..
            }
        )),
        0,
        "{step}"
    );
    assert_eq!(calls(func(&out, "f")), 0, "{}", func(&out, "f"));
    agrees_in_the_view(&m, &out);
}

/// `fill(p, a)` copies 8 constant bytes into `p` by a `memcopy` of a `u32`
/// count and stores `a`'s niche test (`const i8 254`) after them; `f`
/// calls it on a slot.
const COUNT_AND_NICHE: &str = "type ty.0 = u8\n\n\
functy.0 = (ptr, u32) -> ()\n\
functy.1 = (u32, u32) -> (u32)\n\n\
global internal align(1) @K [ty.0 x 8] = bytes<0102030405060708>\n\n\
fn @fill(functy.0) {\n\
bb0(%0: ptr, %1: u32):\n\
\x20   %2 = global_addr @global.0\n\
\x20   %3 = const u32 8\n\
\x20   memcopy ptr %0, ptr %2, %3\n\
\x20   %4 = const i8 254\n\
\x20   %5 = trunc u32 %1 to i8\n\
\x20   %6 = icmp eq i8 %5, %4\n\
\x20   %7 = zext bool %6 to u8\n\
\x20   %8 = const usize 8\n\
\x20   %9 = gep u8, ptr %0, %8\n\
\x20   store u8 %7, ptr %9\n\
\x20   ret\n\
}\n\n\
fn @f(functy.1) {\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca [ty.0 x 12], align 4\n\
\x20   call @func.0(%2, %0)\n\
\x20   %3 = const usize 5\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   %5 = load u32, ptr %4\n\
\x20   %6 = add u32 %5, %1\n\
\x20   ret %6\n\
}\n";

#[test]
fn a_u32_count_and_an_out_of_range_niche_are_respelled_and_spliced() {
    let m = module(COUNT_AND_NICHE);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(stats(&report, "respell").functions_changed >= 1);
    assert!(stats(&report, "const_fold").functions_changed >= 1);
    let fill = func(&out, "fill");
    assert!(
        fill.blocks.iter().flat_map(|b| &b.body).all(|n| !matches!(
            &n.inst,
            Inst::Const {
                ty: trust_ir::Ty::I8,
                value: trust_ir::Constant::Int(254)
            }
        )),
        "{fill}"
    );
    assert_eq!(calls(func(&out, "f")), 0, "{}", func(&out, "f"));
    agrees_in_the_view(&m, &out);
}

/// `memcmp(A, B, 3)` of two slots holding `a` and `a ^ (b & 1) << 17`,
/// read by `{read}`.
fn memcmp_program(read: &str) -> Module {
    module(&format!(
        "type ty.0 = u32\n\n\
         functy.0 = (ptr, ptr, i32) -> (i32)\n\
         functy.1 = (u32, u32) -> (u32)\n\n\
         fn @memcmp(functy.0) {{\n}}\n\n\
         fn @f(functy.1) {{\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = alloca [ty.0 x 1], align 4\n\
         \x20   %3 = alloca [ty.0 x 1], align 4\n\
         \x20   store u32 %0, ptr %2\n\
         \x20   %4 = const u32 1\n\
         \x20   %5 = and u32 %1, %4\n\
         \x20   %6 = const u32 17\n\
         \x20   %7 = shl u32 %5, %6\n\
         \x20   %8 = xor u32 %0, %7\n\
         \x20   store u32 %8, ptr %3\n\
         \x20   %9 = const i32 3\n\
         \x20   %10 = call @func.0(%2, %3, %9)\n\
         \x20   %11 = const i32 0\n\
         \x20   {read}\n\
         \x20   %13 = zext bool %12 to u32\n\
         \x20   ret %13\n\
         }}\n"
    ))
}

#[test]
fn the_default_profile_withholds_the_comparison_call_rewrite() {
    // A declaration's name and prototype do not authenticate the C
    // library's comparison (OD-164): the call keeps its effects.
    let m = memcmp_program("%12 = icmp eq i32 %10, %11");
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert!(
        report.passes_withheld["mem_cmp"].contains("OD-164"),
        "{:?}",
        report.passes_withheld
    );
    assert_eq!(stats(&report, "mem_cmp").functions_changed, 0);
    assert_eq!(calls(func(&out, "f")), 1, "{}", func(&out, "f"));
}

#[test]
fn a_short_memcmp_read_by_a_zero_test_becomes_loads() {
    // The withheld pass run on its own, kept by its checker under the C
    // library premise. The differential's view gives the declaration no
    // body (OD-164's merge boundary), so no candidate is compared; the
    // checker's own tests run it in a view that does.
    let m = memcmp_program("%12 = icmp eq i32 %10, %11");
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&passes::MemCmpPass]);
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "mem_cmp").functions_changed, 1);
    assert_eq!(calls(func(&out, "f")), 0, "{}", func(&out, "f"));
    assert!(
        report
            .tv
            .by_pass
            .get("mem_cmp")
            .is_none_or(|c| c.compared == 0),
        "{:?}",
        report.tv.by_pass
    );
    // The sign read: the call stays.
    let m = memcmp_program("%12 = icmp slt i32 %10, %11");
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&passes::MemCmpPass]);
    assert_eq!(stats(&report, "mem_cmp").functions_changed, 0);
    assert_eq!(calls(func(&out, "f")), 1);
}

/// The comparison-call rewrite with every byte compared as a signed char.
struct SignedMemCmp;

impl MidPass for SignedMemCmp {
    fn name(&self) -> &'static str {
        "mem_cmp"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let (mut out, w) = passes::MemCmpPass.run(cx, func)?;
        for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let Inst::Cast {
                op,
                src_ty: trust_ir::Ty::U8,
                ..
            } = &mut node.inst
            {
                *op = CastOp::SExt;
            }
        }
        Some((out, w))
    }
}

#[test]
fn a_comparison_spelled_with_signed_bytes_is_rolled_back() {
    let m = module(
        "type ty.0 = u32\n\n\
         functy.0 = (ptr, ptr, i32) -> (i32)\n\
         functy.1 = (u32, u32) -> (u32)\n\n\
         fn @memcmp(functy.0) {\n}\n\n\
         fn @f(functy.1) {\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = alloca [ty.0 x 1], align 4\n\
         \x20   %3 = alloca [ty.0 x 1], align 4\n\
         \x20   store u32 %0, ptr %2\n\
         \x20   store u32 %1, ptr %3\n\
         \x20   %9 = const i32 1\n\
         \x20   %10 = call @func.0(%2, %3, %9)\n\
         \x20   %11 = bitcast i32 %10 to u32\n\
         \x20   ret %11\n\
         }\n",
    );
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&SignedMemCmp]);
    assert_eq!(func(&out, "f"), func(&m, "f"), "the snapshot stays");
    assert_eq!(report.rollback_count(), 1);
    assert!(
        report.rollbacks[0].reason.starts_with("witness:"),
        "{:?}",
        report.rollbacks
    );
}

/// `sumpk(p: [u8 x 7])` as the rustc bridge spells a packed by-value
/// parameter (its lanes copied into a slot, three fields loaded from it),
/// `#[inline(never)]`; `f` stores the bytes of `a` and `b` and calls it.
fn packed() -> Module {
    packed_with("", "", "", "")
}

/// [`packed`] with `{param}`/`{entry}` appended to the callee's signature
/// and entry parameters, `{effect}` before its field loads and `{arg}`
/// appended to the call's arguments.
fn packed_with(param: &str, entry: &str, effect: &str, arg: &str) -> Module {
    module(&packed_text(param, entry, effect, arg))
}

/// The text of [`packed_with`].
fn packed_text(param: &str, entry: &str, effect: &str, arg: &str) -> String {
    let mut copy = String::new();
    for j in 0..7 {
        copy.push_str(&format!(
            "\x20   %{x} = extractfield [ty.0 x 7] %0, {j}\n\
             \x20   %{y} = insertfield [ty.0 x 7] %10, {j}, %{x}\n",
            x = 20 + 2 * j,
            y = 21 + 2 * j,
        ));
    }
    format!(
        "type ty.0 = u8\n\n\
         functy.0 = ([ty.0 x 7]{param}) -> (u32)\n\
         functy.1 = (u32, u32) -> (u32)\n\n\
         fn @sumpk.tcg.crate.0123456789abcdef(functy.0) {{\n\
         \x20   ; #visibility: hidden\n\
         bb0(%0: [ty.0 x 7]{entry}):\n\
         \x20   %10 = alloca [ty.0 x 7], align 1\n\
         {copy}\
         {effect}\
         \x20   %40 = const i32 1\n\
         \x20   %41 = gep inbounds u8, ptr %10, %40\n\
         \x20   %42 = load u32, ptr %41\n\
         \x20   %43 = const i32 5\n\
         \x20   %44 = gep inbounds u8, ptr %10, %43\n\
         \x20   %45 = load u16, ptr %44\n\
         \x20   %46 = load u8, ptr %10\n\
         \x20   %47 = zext u16 %45 to u32\n\
         \x20   %48 = zext u8 %46 to u32\n\
         \x20   %49 = add u32 %42, %47\n\
         \x20   %50 = add u32 %49, %48\n\
         \x20   ret %50\n\
         }}\n\n\
         fn @f(functy.1) {{\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = alloca [ty.0 x 7], align 1\n\
         \x20   store u32 %0, ptr %2\n\
         \x20   %3 = const usize 3\n\
         \x20   %4 = gep u8, ptr %2, %3\n\
         \x20   store u32 %1, ptr %4\n\
         \x20   %6 = call @func.0(%2{arg})\n\
         \x20   %7 = xor u32 %6, %0\n\
         \x20   ret %7\n\
         }}\n"
    )
}

#[test]
fn a_packed_parameter_is_read_through_its_address_by_a_clone() {
    let m = packed();
    let mut config = MidConfig::wasm32();
    config
        .never_inline
        .insert("sumpk.tcg.crate.0123456789abcdef".to_string());
    let (out, report) = optimize_module(&m, &config);
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "byaddr").functions_changed, 1);
    assert!(
        report
            .tv
            .by_pass
            .get("byaddr")
            .is_some_and(|c| c.compared > 0)
    );
    let clone = out
        .functions
        .iter()
        .find(|f| f.name.contains(".tcg.ap"))
        .expect("the clone is appended");
    assert_eq!(
        count(clone, |i| matches!(i, Inst::Alloca { .. })),
        0,
        "{clone}"
    );
    assert_eq!(
        count(clone, |i| matches!(i, Inst::Load { .. })),
        3,
        "{clone}"
    );
    assert!(
        func(&out, "f")
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Call { callee, .. } if callee == clone.id))
    );
    agrees_in_the_view(&m, &out);
    // With argument promotion withheld, no clone is made.
    let config = MidConfig {
        arg_promotion: false,
        ..config
    };
    let (out, report) = optimize_module(&m, &config);
    assert!(report.passes_withheld.contains_key("byaddr"));
    assert!(!out.functions.iter().any(|f| f.name.contains(".tcg.ap")));
}

/// [`packed`] with a second `ptr` parameter, given the argument's own
/// storage, and `{effect}` between the lane copies and the slot's loads.
fn packed_effect(effect: &str) -> Module {
    packed_with(", ptr", ", %1: ptr", effect, ", %2")
}

#[test]
fn a_packed_callee_with_an_effect_the_allowlist_does_not_name_gets_no_clone() {
    let mut config = MidConfig::wasm32();
    config
        .never_inline
        .insert("sumpk.tcg.crate.0123456789abcdef".to_string());
    let (_, report) = optimize_module(&packed_effect(""), &config);
    assert_eq!(stats(&report, "byaddr").functions_changed, 1, "control");
    for effect in [
        "    dealloc %1\n",
        "    drop [ty.0 x 7], %1\n",
        "    retain %1\n",
        "    release %1\n",
    ] {
        let m = packed_effect(effect);
        let (out, report) = optimize_module(&m, &config);
        let s = stats(&report, "byaddr");
        assert_eq!((s.functions_changed, s.rollbacks), (0, 0), "{effect}");
        assert!(
            !out.functions.iter().any(|f| f.name.contains(".tcg.ap")),
            "{effect}"
        );
    }
}

const CARRIER_CALLEE: &str = "wr.tcg.crate.0123456789abcdef";

/// `wr(p: [u8 x 15], q: i64)`: the bridge's copy of `p` into a slot, then
/// (with `write`) byte 0 of the caller's array set to 99 through `q`, an
/// `i64` pointer carrier, then the slot's first four bytes loaded as an
/// `i32`; `g(a, b)` fills the 15 bytes and passes their address as both.
fn i64_carrier(write: bool) -> Module {
    let mut copy = String::new();
    for j in 0..15 {
        copy.push_str(&format!(
            "\x20   %{x} = extractfield [ty.0 x 15] %0, {j}\n\
             \x20   %{y} = insertfield [ty.0 x 15] %10, {j}, %{x}\n",
            x = 20 + 2 * j,
            y = 21 + 2 * j,
        ));
    }
    let write = if write {
        "\x20   %60 = const u8 99\n\x20   %61 = insertfield [ty.0 x 15] %1, 0, %60\n"
    } else {
        ""
    };
    module(&format!(
        "type ty.0 = u8\n\n\
         functy.0 = ([ty.0 x 15], i64) -> (i32)\n\
         functy.1 = (i32, i32) -> (i32)\n\n\
         fn @{CARRIER_CALLEE}(functy.0) {{\n\
         \x20   ; #visibility: hidden\n\
         bb0(%0: [ty.0 x 15], %1: i64):\n\
         \x20   %10 = alloca [ty.0 x 15], align 1\n\
         {copy}\
         {write}\
         \x20   %62 = load i32, ptr %10\n\
         \x20   ret %62\n\
         }}\n\n\
         fn @g(functy.1) {{\n\
         bb0(%0: i32, %1: i32):\n\
         \x20   %2 = alloca [ty.0 x 15], align 1\n\
         \x20   store i32 %0, ptr %2\n\
         \x20   %3 = const usize 4\n\
         \x20   %4 = gep u8, ptr %2, %3\n\
         \x20   store i32 %1, ptr %4\n\
         \x20   %8 = const usize 8\n\
         \x20   %9 = gep u8, ptr %2, %8\n\
         \x20   store i32 %1, ptr %9\n\
         \x20   %11 = const usize 11\n\
         \x20   %12 = gep u8, ptr %2, %11\n\
         \x20   store i32 %0, ptr %12\n\
         \x20   %5 = ptrtoint ptr %2 to i64\n\
         \x20   %6 = call @func.0(%2, %5)\n\
         \x20   ret %6\n\
         }}\n"
    ))
}

/// `wr(p: [u16 x 8], q: u64)`: the bridge's copy of `p` into a slot, then
/// (with `write`) lane 3 of the caller's array set through `q`, a `u64`
/// pointer carrier, then the slot's bytes 6..10 loaded as a `u32` (wider
/// than a lane); `g(a, b)` fills the 16 bytes and passes their address as
/// both (`ptrtoint` to `u32`, then `zext`).
fn u64_carrier(write: bool) -> Module {
    let mut copy = String::new();
    for j in 0..8 {
        copy.push_str(&format!(
            "\x20   %{x} = extractfield [ty.0 x 8] %0, {j}\n\
             \x20   %{y} = insertfield [ty.0 x 8] %10, {j}, %{x}\n",
            x = 20 + 2 * j,
            y = 21 + 2 * j,
        ));
    }
    let write = if write {
        "\x20   %50 = const u16 48879\n\x20   %51 = insertfield [ty.0 x 8] %1, 3, %50\n"
    } else {
        ""
    };
    module(&format!(
        "type ty.0 = u16\n\n\
         functy.0 = ([ty.0 x 8], u64) -> (u32)\n\
         functy.1 = (i32, i32) -> (i32)\n\n\
         fn @{CARRIER_CALLEE}(functy.0) {{\n\
         \x20   ; #visibility: hidden\n\
         bb0(%0: [ty.0 x 8], %1: u64):\n\
         \x20   %10 = alloca [ty.0 x 8], align 2\n\
         {copy}\
         {write}\
         \x20   %52 = const usize 6\n\
         \x20   %53 = gep u8, ptr %10, %52\n\
         \x20   %54 = load u32, ptr %53\n\
         \x20   ret %54\n\
         }}\n\n\
         fn @g(functy.1) {{\n\
         bb0(%0: i32, %1: i32):\n\
         \x20   %2 = alloca [ty.0 x 8], align 2\n\
         \x20   store i32 %0, ptr %2\n\
         \x20   %3 = const usize 4\n\
         \x20   %4 = gep u8, ptr %2, %3\n\
         \x20   store i32 %1, ptr %4\n\
         \x20   %5 = const usize 8\n\
         \x20   %6 = gep u8, ptr %2, %5\n\
         \x20   %7 = xor i32 %0, %1\n\
         \x20   store i32 %7, ptr %6\n\
         \x20   %8 = const usize 12\n\
         \x20   %9 = gep u8, ptr %2, %8\n\
         \x20   store i32 %0, ptr %9\n\
         \x20   %10 = ptrtoint ptr %2 to u32\n\
         \x20   %11 = zext u32 %10 to u64\n\
         \x20   %12 = call @func.0(%2, %11)\n\
         \x20   %13 = bitcast u32 %12 to i32\n\
         \x20   ret %13\n\
         }}\n"
    ))
}

/// The wasm32 lane (like `escape::is_pointer_carrier`) reads an `i64`/`u64`
/// aggregate operand of `insertfield` as the address of the aggregate's
/// bytes and writes the field through it. A callee that writes the caller's
/// array through such a carrier between its lane copies and the slot's
/// loads gets no clone: the clone would read the byte after the write (the
/// source and the lane's O0 read the copy the call saw). Controls: without
/// the write, each callee is cloned.
#[test]
fn a_callee_writing_through_an_integer_pointer_carrier_gets_no_clone() {
    let mut config = MidConfig::wasm32();
    config.never_inline.insert(CARRIER_CALLEE.to_string());
    // Per carrier: byaddr's (changed, rolled back) without the write, then
    // with it, and whether a clone was appended.
    let mut rows = Vec::new();
    for (name, build) in [
        ("i64", i64_carrier as fn(bool) -> Module),
        ("u64", u64_carrier),
    ] {
        let (_, report) = optimize_module(&build(false), &config);
        let control = stats(&report, "byaddr");
        let (out, report) = optimize_module(&build(true), &config);
        let s = stats(&report, "byaddr");
        rows.push((
            name,
            (control.functions_changed, control.rollbacks),
            (s.functions_changed, s.rollbacks),
            out.functions.iter().any(|f| f.name.contains(".tcg.ap")),
        ));
    }
    assert_eq!(
        rows,
        [
            ("i64", (1, 0), (0, 0), false),
            ("u64", (1, 0), (0, 0), false)
        ]
    );
}

/// [`packed`] with `%58 = {operand}` and an `insertfield [ty.0 x 7]` over
/// `%58` between the lane copies and the slot's loads.
fn packed_insert_over(operand: &str) -> Module {
    packed_with(
        "",
        "",
        &format!(
            "\x20   %58 = {operand}\n\
             \x20   %59 = const u8 1\n\
             \x20   %61 = insertfield [ty.0 x 7] %58, 0, %59\n"
        ),
        "",
    )
}

/// The allowlist of OD-166 ruling 2 names the aggregate VALUE types an
/// `insertfield` may build over (struct, tuple, array, record, enum); every
/// other operand type keeps the slot, not only the pointer carriers. Rows:
/// an `i32`, a `usize` and a `fatptr<str>` operand, none of them a pointer
/// carrier (`escape::is_pointer_carrier`), so a deny list of the carriers
/// would clone each callee. Control: the same `insertfield` over the
/// slot's bytes loaded as the array is cloned.
#[test]
fn a_callee_inserting_over_a_type_the_allowlist_does_not_name_gets_no_clone() {
    let mut config = MidConfig::wasm32();
    config
        .never_inline
        .insert("sumpk.tcg.crate.0123456789abcdef".to_string());
    // Per operand: byaddr's (changed, rolled back), and whether a clone was
    // appended.
    let mut rows = Vec::new();
    for (name, operand) in [
        ("array", "load [ty.0 x 7], ptr %10"),
        ("i32", "const i32 0"),
        ("usize", "const usize 0"),
        ("fatptr", "load fatptr<str>, ptr %10"),
    ] {
        let (out, report) = optimize_module(&packed_insert_over(operand), &config);
        let s = stats(&report, "byaddr");
        rows.push((
            name,
            (s.functions_changed, s.rollbacks),
            out.functions.iter().any(|f| f.name.contains(".tcg.ap")),
        ));
    }
    assert_eq!(
        rows,
        [
            ("array", (1, 0), true),
            ("i32", (0, 0), false),
            ("usize", (0, 0), false),
            ("fatptr", (0, 0), false)
        ]
    );
}

/// `sumpk(x: [u32 x 2], y: [u8 x 7])`: `y` as [`packed`]'s parameter (its
/// lanes copied into a slot `%10`, three fields loaded from it) and `x`
/// copied into a slot `%11` of its own and read by one `u32` load (two
/// lanes, which argument promotion passes as values, so by-address cloning
/// does not promote `x`); with `x_first`, `x`'s copies come before `y`'s.
/// `f` passes both by address.
fn two_arrays(x_first: bool) -> Module {
    let mut y = String::new();
    for j in 0..7 {
        y.push_str(&format!(
            "\x20   %{a} = extractfield [ty.0 x 7] %0, {j}\n\
             \x20   %{b} = insertfield [ty.0 x 7] %10, {j}, %{a}\n",
            a = 20 + 2 * j,
            b = 21 + 2 * j,
        ));
    }
    let x = "\x20   %90 = extractfield [ty.1 x 2] %1, 0\n\
             \x20   %91 = insertfield [ty.1 x 2] %11, 0, %90\n\
             \x20   %92 = extractfield [ty.1 x 2] %1, 1\n\
             \x20   %93 = insertfield [ty.1 x 2] %11, 1, %92\n"
        .to_string();
    let (first, second) = if x_first { (x, y) } else { (y, x) };
    module(&format!(
        "type ty.0 = u8\n\
         type ty.1 = u32\n\n\
         functy.0 = ([ty.1 x 2], [ty.0 x 7]) -> (u32)\n\
         functy.1 = (u32, u32) -> (u32)\n\n\
         fn @sumpk.tcg.crate.0123456789abcdef(functy.0) {{\n\
         \x20   ; #visibility: hidden\n\
         bb0(%1: [ty.1 x 2], %0: [ty.0 x 7]):\n\
         \x20   %10 = alloca [ty.0 x 7], align 1\n\
         \x20   %11 = alloca [ty.1 x 2], align 4\n\
         {first}\
         {second}\
         \x20   %40 = const i32 1\n\
         \x20   %41 = gep inbounds u8, ptr %10, %40\n\
         \x20   %42 = load u32, ptr %41\n\
         \x20   %43 = const i32 5\n\
         \x20   %44 = gep inbounds u8, ptr %10, %43\n\
         \x20   %45 = load u16, ptr %44\n\
         \x20   %46 = load u8, ptr %10\n\
         \x20   %47 = zext u16 %45 to u32\n\
         \x20   %48 = zext u8 %46 to u32\n\
         \x20   %49 = add u32 %42, %47\n\
         \x20   %50 = add u32 %49, %48\n\
         \x20   %94 = load u32, ptr %11\n\
         \x20   %51 = add u32 %50, %94\n\
         \x20   ret %51\n\
         }}\n\n\
         fn @f(functy.1) {{\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = alloca [ty.0 x 7], align 1\n\
         \x20   store u32 %0, ptr %2\n\
         \x20   %3 = const usize 3\n\
         \x20   %4 = gep u8, ptr %2, %3\n\
         \x20   store u32 %1, ptr %4\n\
         \x20   %5 = alloca [ty.1 x 2], align 4\n\
         \x20   store u32 %1, ptr %5\n\
         \x20   %8 = const usize 4\n\
         \x20   %9 = gep u8, ptr %5, %8\n\
         \x20   store u32 %0, ptr %9\n\
         \x20   %6 = call @func.0(%5, %2)\n\
         \x20   %7 = xor u32 %6, %0\n\
         \x20   ret %7\n\
         }}\n"
    ))
}

/// `sumpk(y: [u8 x 7], z: [u8 x 7], x: [u32 x 2])`: each copied into a slot
/// of its own, `y` and `z` read wider than a lane (so by-address cloning
/// would promote them) and `x` by one `u32` load (two lanes, which it does
/// not promote), the copies interleaved as `y[0..3]`, `z[0..3]`, `y[3..7]`,
/// `x`, `z[3..7]`. Under the prologue of `{y, z}` (it ends at `x`'s first
/// lane read) `z` is read after it, under that of `{y}` (it ends at `z`'s
/// first read) so is `y`: the plan reaches the empty set only in a third
/// round. `f` passes all three by address.
fn three_rounds() -> Module {
    let lane = |p: u32, s: u32, t: &str, n: u32, j: u32, base: u32| {
        format!(
            "\x20   %{e} = extractfield [{t} x {n}] %{p}, {j}\n\
             \x20   %{x} = insertfield [{t} x {n}] %{s}, {j}, %{e}\n",
            e = base + 2 * j,
            x = base + 2 * j + 1
        )
    };
    let mut body = String::new();
    for j in 0..3 {
        body.push_str(&lane(100, 200, "ty.0", 7, j, 1000));
    }
    for j in 0..3 {
        body.push_str(&lane(101, 201, "ty.0", 7, j, 1100));
    }
    for j in 3..7 {
        body.push_str(&lane(100, 200, "ty.0", 7, j, 1000));
    }
    for j in 0..2 {
        body.push_str(&lane(102, 202, "ty.1", 2, j, 1200));
    }
    for j in 3..7 {
        body.push_str(&lane(101, 201, "ty.0", 7, j, 1100));
    }
    module(&format!(
        "type ty.0 = u8\n\
         type ty.1 = u32\n\n\
         functy.0 = ([ty.0 x 7], [ty.0 x 7], [ty.1 x 2]) -> (u32)\n\
         functy.1 = (u32, u32) -> (u32)\n\n\
         fn @sumpk.tcg.crate.0123456789abcdef(functy.0) {{\n\
         \x20   ; #visibility: hidden\n\
         bb0(%100: [ty.0 x 7], %101: [ty.0 x 7], %102: [ty.1 x 2]):\n\
         \x20   %200 = alloca [ty.0 x 7], align 1\n\
         \x20   %201 = alloca [ty.0 x 7], align 1\n\
         \x20   %202 = alloca [ty.1 x 2], align 4\n\
         {body}\
         \x20   %40 = const i32 1\n\
         \x20   %41 = gep inbounds u8, ptr %200, %40\n\
         \x20   %42 = load u32, ptr %41\n\
         \x20   %43 = gep inbounds u8, ptr %201, %40\n\
         \x20   %44 = load u32, ptr %43\n\
         \x20   %45 = load u32, ptr %202\n\
         \x20   %46 = add u32 %42, %44\n\
         \x20   %47 = add u32 %46, %45\n\
         \x20   ret %47\n\
         }}\n\n\
         fn @f(functy.1) {{\n\
         bb0(%0: u32, %1: u32):\n\
         \x20   %2 = alloca [ty.0 x 7], align 1\n\
         \x20   store u32 %0, ptr %2\n\
         \x20   %5 = alloca [ty.0 x 7], align 1\n\
         \x20   store u32 %1, ptr %5\n\
         \x20   %9 = alloca [ty.1 x 2], align 4\n\
         \x20   store u32 %1, ptr %9\n\
         \x20   %6 = call @func.0(%2, %5, %9)\n\
         \x20   %7 = xor u32 %6, %0\n\
         \x20   ret %7\n\
         }}\n"
    ))
}

/// By-address cloning run on its own reads a callee by its checker's
/// prologue and typing and requires the parameters a clone keeps to have
/// their declared types, so it proposes none of these clones the checker
/// would refuse and the manager roll back. Rows, byaddr's (changed, rolled
/// back): an `insertfield` over an array value defined by an `undef`, a
/// `select` or another `insertfield` (forms the checker types nothing), a
/// caller argument defined by a `select` of pointers or by `nullptr` (the
/// same), a callee that reads an array parameter it does not promote ahead
/// of the promoted array's lane copies (the checker's prologue ends at that
/// read), the interleaved copies whose plan shrinks to nothing only in a
/// third round ([`three_rounds`]), and a kept thin-pointer parameter whose
/// entry type is another pointer type than its declared one (`*mut u8` for
/// `ptr`, and `ptr` for `*const u8`): none gets a clone. Controls, cloned and
/// kept: the same `insertfield` over the slot's bytes loaded as the array,
/// the two-array callee with the unpromoted array's copies after the
/// promoted array's, and a kept `ptr` parameter entered as `ptr`.
#[test]
fn byaddr_proposes_no_clone_its_checker_rolls_back() {
    let insert_over = |def: &str| {
        packed_with(
            "",
            "",
            &format!(
                "\x20   %58 = load [ty.0 x 7], ptr %10\n\
                 \x20   %57 = const bool true\n\
                 {def}\
                 \x20   %59 = const u8 1\n\
                 \x20   %61 = insertfield [ty.0 x 7] %60, 0, %59\n"
            ),
            "",
        )
    };
    let argument = |def: &str| {
        module(&packed_text("", "", "", "").replace(
            "\x20   %6 = call @func.0(%2)\n",
            &format!("{def}\x20   %6 = call @func.0(%8)\n"),
        ))
    };
    let pass = passes::ByAddr::new(Default::default());
    let (mut rows, mut reasons) = (Vec::new(), Vec::new());
    for (name, m) in [
        ("load", insert_over("\x20   %60 = copy [ty.0 x 7] %58\n")),
        ("undef", insert_over("\x20   %60 = undef [ty.0 x 7]\n")),
        (
            "select",
            insert_over("\x20   %60 = select [ty.0 x 7] %57, %58, %58\n"),
        ),
        (
            "chained",
            insert_over(
                "\x20   %56 = const u8 2\n\
                 \x20   %60 = insertfield [ty.0 x 7] %58, 1, %56\n",
            ),
        ),
        (
            "select argument",
            argument(
                "\x20   %5 = icmp ult u32 %0, %1\n\
                 \x20   %8 = select ptr %5, %2, %2\n",
            ),
        ),
        ("null argument", argument("\x20   %8 = null ptr\n")),
        ("unpromoted after", two_arrays(false)),
        ("unpromoted first", two_arrays(true)),
        ("three rounds", three_rounds()),
        (
            "kept thin match",
            packed_with(", ptr", ", %1: ptr", "", ", %2"),
        ),
        (
            "kept thin mismatch",
            packed_with(", ptr", ", %1: *mut u8", "", ", %2"),
        ),
        (
            "kept thin mismatch reversed",
            packed_with(", *const u8", ", %1: ptr", "", ", %2"),
        ),
    ] {
        let (_, report) = manager::run(&m, &MidConfig::wasm32(), &[&pass]);
        let s = stats(&report, "byaddr");
        rows.push((name, (s.functions_changed, s.rollbacks)));
        reasons.extend(report.rollbacks.iter().map(|r| (name, r.reason.clone())));
    }
    assert_eq!(
        rows,
        [
            ("load", (1, 0)),
            ("undef", (0, 0)),
            ("select", (0, 0)),
            ("chained", (0, 0)),
            ("select argument", (0, 0)),
            ("null argument", (0, 0)),
            ("unpromoted after", (1, 0)),
            ("unpromoted first", (0, 0)),
            ("three rounds", (0, 0)),
            ("kept thin match", (1, 0)),
            ("kept thin mismatch", (0, 0)),
            ("kept thin mismatch reversed", (0, 0))
        ],
        "{reasons:#?}"
    );
}
