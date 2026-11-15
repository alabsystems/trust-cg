// trust-cg-irmid/mem_call_tests.rs - the memory-call rewrite
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The memory-call rewrite turns `ptr::swap`'s `memmove` of a constant
//! count (and a constant `memset`) into the trust-ir instruction, kept by
//! its checker and by the interpreter differential, whose inputs include the
//! two pointers bound into one object (overlapping ranges); over the
//! pipeline no call is left. The default profile leaves a copy of a
//! run-time count (`copy_from_slice`'s `memcpy` of a slice's length) a
//! call (OD-165's merge boundary); the pass's run-time-count widening, run
//! on its own, makes it the instruction. It leaves alone a `memset` of a
//! run-time count, a `memmove` the module defines, a
//! callee of another prototype (a signed count, an 8-bit fill) and a call
//! whose returned pointer is used, and a pass that spells `memmove` as
//! `memcpy` is rolled back. The witness types and the
//! pass name `mem_call` are provisional surfaces pending the owner's
//! sign-off (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use trust_cg_verify::trust_ir_mid_tv::PassWitness;
use trust_ir::{Function, Inst, Module};

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

fn calls(f: &Function) -> usize {
    f.blocks
        .iter()
        .flat_map(|b| &b.body)
        .filter(|n| matches!(n.inst, Inst::Call { .. }))
        .count()
}

fn edited(text: &str, edit: &[(&str, &str)]) -> Module {
    let mut text = text.to_string();
    for (from, to) in edit {
        assert!(text.contains(from), "{from}");
        text = text.replace(from, to);
    }
    module(&text)
}

/// `ptr::swap::<u32>(p, q)` as the bridge lowers it on wasm32 (typed
/// pointers passed for the prototype's `*mut u8`, the count a constant
/// product, as `count * size_of::<T>()` arrives), and a
/// `write_bytes` of eight bytes at `p` in `fill`.
const SWAP: &str = "functy.0 = (*mut u8, *const u8, u32) -> (*mut u8)\n\
functy.1 = (ptr, ptr) -> ()\n\
functy.2 = (ptr, i32, u32) -> (ptr)\n\
functy.3 = (ptr, u32) -> ()\n\n\
fn @memmove(functy.0) {\n}\n\n\
fn @memset(functy.2) {\n}\n\n\
fn @f(functy.1) {\n\
bb0(%0: ptr, %1: ptr):\n\
\x20   %2 = load u32, ptr %0\n\
\x20   %3 = ptrtoptr ptr %0 to *mut u32\n\
\x20   %4 = ptrtoptr ptr %1 to *const u32\n\
\x20   %5 = const u32 1\n\
\x20   %6 = const u32 4\n\
\x20   %7 = mul u32 %5, %6\n\
\x20   %8 = call @func.0(%3, %4, %7)\n\
\x20   store u32 %2, ptr %1\n\
\x20   ret\n\
}\n\n\
fn @fill(functy.3) {\n\
bb0(%0: ptr, %1: u32):\n\
\x20   %2 = const u32 255\n\
\x20   %3 = and u32 %1, %2\n\
\x20   %4 = bitcast u32 %3 to i32\n\
\x20   %5 = const u32 8\n\
\x20   %6 = call @func.1(%0, %4, %5)\n\
\x20   ret\n\
}\n";

#[test]
fn a_swap_through_memmove_loses_its_call() {
    let m = module(SWAP);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "mem_call").functions_changed, 2);
    for name in ["f", "fill"] {
        let f = func(&out, name);
        assert_eq!(calls(f), 0, "{f}");
    }
    let f = func(&out, "f");
    assert!(
        f.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::MemCopy { overlap: true, .. })),
        "{f}"
    );
    assert!(
        func(&out, "fill")
            .blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::MemSet { .. }))
    );
    // Both rewrites ran in the differential, the library bodies in the view.
    let tv = report.tv.by_pass.get("mem_call").expect("candidates");
    assert_eq!(tv.compared, 2, "{tv:?}");
}

#[test]
fn calls_off_the_form_stay_calls() {
    let cx = |m: &Module| {
        let cx = PassContext {
            module: m,
            pointer_bits: 32,
        };
        passes::MemCallPass::WITH_RUN_TIME_COUNTS
            .run(&cx, func(m, "f"))
            .is_none()
    };
    let constant_only = |m: &Module| {
        let cx = PassContext {
            module: m,
            pointer_bits: 32,
        };
        passes::MemCallPass::CONSTANT_COUNTS
            .run(&cx, func(m, "f"))
            .is_none()
    };
    // Before constant folding the count is a run-time value of a copy: the
    // widening rewrites the call too (the count's `bitcast` folds later);
    // the default profile's instance leaves it.
    assert!(!cx(&module(SWAP)));
    assert!(constant_only(&module(SWAP)));
    let folded = [("%7 = mul u32 %5, %6", "%7 = const u32 4")];
    assert!(!cx(&edited(SWAP, &folded)));
    assert!(!constant_only(&edited(SWAP, &folded)));
    // A run-time count of a copy is rewritten by the widening alone; of a
    // memset it is not.
    let run_time = [("%7 = mul u32 %5, %6", "%7 = ptrtoint ptr %0 to u32")];
    assert!(!cx(&edited(SWAP, &run_time)));
    assert!(constant_only(&edited(SWAP, &run_time)));
    // A memmove the module defines.
    assert!(cx(&edited(
        SWAP,
        &[
            folded[0],
            (
                "fn @memmove(functy.0) {\n}",
                "fn @memmove(functy.0) {\nbb0(%0: *mut u8, %1: *const u8, %2: u32):\n    ret %0\n}",
            ),
        ]
    )));
    // Not the C prototype (a signed count).
    assert!(cx(&edited(
        SWAP,
        &[
            ("%7 = mul u32 %5, %6", "%7 = const i32 4"),
            (
                "functy.0 = (*mut u8, *const u8, u32)",
                "functy.0 = (*mut u8, *const u8, i32)"
            ),
        ]
    )));
    // The returned pointer is used.
    assert!(cx(&edited(
        SWAP,
        &[folded[0], ("store u32 %2, ptr %1", "store u32 %2, ptr %8"),]
    )));
    // A `memset` whose fill is a byte already (`trunc` to `u8` would not
    // narrow, which trust-ir's validator rejects) is not the C prototype.
    let fill = |m: &Module| {
        let cx = PassContext {
            module: m,
            pointer_bits: 32,
        };
        passes::MemCallPass::WITH_RUN_TIME_COUNTS
            .run(&cx, func(m, "fill"))
            .is_none()
    };
    assert!(!fill(&module(SWAP)));
    assert!(fill(&edited(
        SWAP,
        &[("%5 = const u32 8", "%5 = copy u32 %1")]
    )));
    for byte in ["u8", "i8"] {
        assert!(fill(&edited(
            SWAP,
            &[
                (
                    "functy.2 = (ptr, i32, u32)",
                    &format!("functy.2 = (ptr, {byte}, u32)")
                ),
                (
                    "%4 = bitcast u32 %3 to i32",
                    &format!("%4 = trunc u32 %3 to {byte}")
                ),
            ]
        )));
    }
}

struct LyingMemCall;

impl MidPass for LyingMemCall {
    fn name(&self) -> &'static str {
        "mem_call"
    }

    fn run(&self, cx: &PassContext<'_>, func: &Function) -> Option<(Function, PassWitness)> {
        let (mut out, w) = passes::MemCallPass::CONSTANT_COUNTS.run(cx, func)?;
        // memmove spelled as memcpy: overlapping ranges become undefined.
        for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
            if let Inst::MemCopy { overlap, .. } = &mut node.inst {
                *overlap = false;
            }
        }
        Some((out, w))
    }
}

#[test]
fn a_memmove_spelled_as_memcpy_is_rolled_back() {
    let m = edited(SWAP, &[("%7 = mul u32 %5, %6", "%7 = const u32 4")]);
    let (out, report) = manager::run(&m, &MidConfig::wasm32(), &[&LyingMemCall]);
    assert_eq!(func(&out, "f"), func(&m, "f"), "the snapshot stays");
    assert_eq!(report.rollback_count(), 1);
    assert!(
        report.rollbacks[0].reason.starts_with("witness:"),
        "{:?}",
        report.rollbacks
    );
}

/// `copy_from_slice` of `n % 8` bytes between two buffers as the bridge
/// spells it: a `memcpy` whose count is the slice's length.
const COPY_FROM_SLICE: &str = "functy.0 = (*mut u8, *const u8, u32) -> (*mut u8)\n\
functy.1 = (ptr, ptr, u32) -> ()\n\n\
fn @memcpy(functy.0) {\n}\n\n\
fn @f(functy.1) {\n\
bb0(%0: ptr, %1: ptr, %2: u32):\n\
\x20   %3 = const u32 7\n\
\x20   %4 = and u32 %2, %3\n\
\x20   %5 = ptrtoptr ptr %0 to *mut u8\n\
\x20   %6 = ptrtoptr ptr %1 to *const u8\n\
\x20   %7 = call @func.0(%5, %6, %4)\n\
\x20   ret\n\
}\n";

#[test]
fn the_default_profile_keeps_a_copy_of_a_run_time_count_a_call() {
    // OD-165's merge boundary: the widening is withheld by default.
    let m = module(COPY_FROM_SLICE);
    let (out, report) = optimize_module(&m, &MidConfig::wasm32());
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "mem_call").functions_changed, 0);
    assert_eq!(calls(func(&out, "f")), 1, "{}", func(&out, "f"));
}

#[test]
fn a_copy_of_a_run_time_count_loses_its_call() {
    let m = module(COPY_FROM_SLICE);
    let (out, report) = manager::run(
        &m,
        &MidConfig::wasm32(),
        &[&passes::MemCallPass::WITH_RUN_TIME_COUNTS],
    );
    assert_eq!(report.rollback_count(), 0, "{:?}", report.rollbacks);
    assert_eq!(stats(&report, "mem_call").functions_changed, 1);
    let f = func(&out, "f");
    assert_eq!(calls(f), 0, "{f}");
    assert!(
        f.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::MemCopy { overlap: false, .. })),
        "{f}"
    );
    let tv = report.tv.by_pass.get("mem_call").expect("candidates");
    assert_eq!(tv.compared, 1, "{tv:?}");
}
