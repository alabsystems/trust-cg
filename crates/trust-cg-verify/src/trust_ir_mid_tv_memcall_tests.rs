// trust-cg-verify/trust_ir_mid_tv_memcall_tests.rs - tests of the memory-call checker
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A call of the `memmove`, `memcpy` and `memset` declarations with a
//! constant count becomes `memcopy overlap`, `memcopy` and `memset`, a
//! `memmove` or `memcpy` with a run-time count becomes the copy of that
//! count as `usize`, and the target agrees with the source run in the
//! differential's view (which gives those declarations the C library's
//! bodies) on an overlapping `memmove` in both directions, an unaligned
//! copy, a fill and copies of a run-time count (zero included). Refused: a
//! callee the module defines under the name, a callee of another name, a
//! prototype that is not C's (a 16-bit count, an 8-bit fill, which the view
//! leaves without a body too), a `memset` of a run-time count, a run-time
//! count of another type than the parameter's, a used result, a fill byte
//! claimed for a copy or missing for `memset`, a name that is not fresh,
//! the target of a `memmove` spelled without `overlap` (the checker rebuilds
//! `memcopy overlap`, so the target differs) and a target whose run-time
//! count is narrowed. A target copying the other way disagrees with the
//! source in the differential.
//!
//! The witness types (`MemCallWitness`, `MemCall` and the `PassWitness`
//! variant) are provisional surfaces pending the owner's sign-off
//! (`docs/wasm32_perf_roadmap.md`, "Pending owner sign-off").

use super::super::{
    DifferentialBudget, MidTvError, PassWitness, check_pass, compare_samples, interpretable_module,
    run_samples, seeded_inputs,
};
use super::*;

const HEADER: &str = "; TrustIr text format v1\nmodule \"memcall\"\n\
                      target \"wasm32-unknown-unknown\" 4 little\n\n";

fn module(body: &str) -> Module {
    trust_ir::parser::parse_module(&format!("{HEADER}{body}"))
        .unwrap_or_else(|e| panic!("test module failed to parse: {e}\n{body}"))
}

fn f(m: &Module) -> &Function {
    m.functions.iter().find(|f| f.name == "f").expect("f")
}

fn v(n: u32) -> ValueId {
    ValueId::new(n)
}

fn witness(rewrites: &[(u32, u32, Option<u32>)]) -> MemCallWitness {
    MemCallWitness {
        rewrites: rewrites
            .iter()
            .map(|&(value, count, byte)| MemCall {
                value: v(value),
                count: v(count),
                byte: byte.map(v),
            })
            .collect(),
    }
}

/// The declarations: `memmove` (`func.0`), `memcpy` (`func.1`) and
/// `memset` (`func.2`) at the prototypes the bridge declares on wasm32.
const DECLS: &str = "functy.0 = (*mut u8, *const u8, u32) -> (*mut u8)\n\
functy.1 = (ptr, i32, u32) -> (ptr)\n\
functy.2 = (u32, u32) -> (u64)\n\n\
fn @memmove(functy.0) {\n}\n\n\
fn @memcpy(functy.0) {\n}\n\n\
fn @memset(functy.1) {\n}\n\n";

/// Twelve bytes holding `a`, `b` and `a ^ b`; `callee` moves `count` bytes
/// from byte `from` to byte `to` (`fill` a `memset` of `count` bytes at
/// `to` with the low byte of `b` instead); the result reads bytes 0..8.
fn program(callee: u32, to: u32, from: u32, count: u32) -> String {
    let (second, second_v, dst) = if callee == 2 {
        (
            "%9 = bitcast u32 %1 to i32".to_string(),
            "%9",
            "%21 = copy ptr %8",
        )
    } else {
        (
            format!(
                "%9 = const usize {from}\n\x20   %10 = gep u8, ptr %2, %9\n\x20   \
                 %20 = ptrtoptr ptr %10 to *const u8"
            ),
            "%20",
            "%21 = ptrtoptr ptr %8 to *mut u8",
        )
    };
    format!(
        "{DECLS}fn @f(functy.2) {{\n\
bb0(%0: u32, %1: u32):\n\
\x20   %2 = alloca (u32, u32, u32), align 4\n\
\x20   store u32 %0, ptr %2\n\
\x20   %3 = const usize 4\n\
\x20   %4 = gep u8, ptr %2, %3\n\
\x20   store u32 %1, ptr %4\n\
\x20   %5 = const usize 8\n\
\x20   %6 = gep u8, ptr %2, %5\n\
\x20   %11 = xor u32 %0, %1\n\
\x20   store u32 %11, ptr %6\n\
\x20   %7 = const usize {to}\n\
\x20   %8 = gep u8, ptr %2, %7\n\
\x20   {second}\n\
\x20   {dst}\n\
\x20   %12 = const u32 {count}\n\
\x20   %13 = call @func.{callee}(%21, {second_v}, %12)\n\
\x20   %14 = load u64, ptr %2\n\
\x20   ret %14\n\
}}\n"
    )
}

/// The rewrite on `m` checked and run against the source in the view.
fn accepted_and_agrees(m: &Module, w: &MemCallWitness) -> Function {
    let src = f(m);
    let (out, verdict) = rebuild_mem_call(m, 32, src, w).expect("accepted");
    assert_eq!(verdict.exact, w.rewrites.len());
    check_pass(m, 32, src, &out, &PassWitness::MemCall(w.clone())).expect("check_pass");
    assert!(
        !out.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::Call { .. })),
        "the call is gone"
    );
    let view = interpretable_module(m);
    let inputs = seeded_inputs(m, src, 32, 64, 7).expect("scalar parameters");
    let (a, _) = run_samples(&view, src, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&view, &out, &inputs, DifferentialBudget::default());
    let report = compare_samples(&a, &t);
    assert!(report.mismatch.is_none(), "{:?}", report.mismatch);
    assert!(report.compared > 0, "some inputs are compared");
    out
}

#[test]
fn memmove_becomes_memcopy_overlap_and_agrees_on_overlapping_ranges() {
    // Up by one byte (the destination above the source) and down by three.
    for (to, from) in [(1, 0), (0, 3), (5, 2)] {
        let m = module(&program(0, to, from, 6));
        let out = accepted_and_agrees(&m, &witness(&[(13, 100, None)]));
        assert!(out.blocks.iter().flat_map(|b| &b.body).any(|n| matches!(
            n.inst,
            Inst::MemCopy {
                overlap: true,
                bytes,
                ..
            } if bytes == v(100)
        )));
    }
}

#[test]
fn memcpy_becomes_memcopy_and_memset_becomes_memset() {
    // Disjoint, the destination unaligned.
    let m = module(&program(1, 1, 8, 4));
    let out = accepted_and_agrees(&m, &witness(&[(13, 100, None)]));
    assert!(
        out.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::MemCopy { overlap: false, .. }))
    );
    let m = module(&program(2, 3, 0, 4));
    let out = accepted_and_agrees(&m, &witness(&[(13, 100, Some(101))]));
    assert!(
        out.blocks
            .iter()
            .flat_map(|b| &b.body)
            .any(|n| matches!(n.inst, Inst::MemSet { .. }))
    );
}

#[test]
fn calls_off_the_library_form_are_refused() {
    let refused = |m: &Module, w: &MemCallWitness| {
        assert!(
            matches!(
                rebuild_mem_call(m, 32, f(m), w),
                Err(MidTvError::NotMemCall { .. })
            ),
            "{w:?}"
        );
    };
    let copy = witness(&[(13, 100, None)]);
    // A memmove the module defines (its body runs, not the library's).
    let m = module(&program(0, 1, 0, 4).replace(
        "fn @memmove(functy.0) {\n}",
        "fn @memmove(functy.0) {\nbb0(%0: *mut u8, %1: *const u8, %2: u32):\n    ret %0\n}",
    ));
    refused(&m, &copy);
    // A declaration of another name.
    let m = module(&program(0, 1, 0, 4).replace("fn @memmove(", "fn @memmover("));
    refused(&m, &copy);
    // Not the C prototype: a 16-bit count.
    let m = module(
        &program(0, 1, 0, 4)
            .replace(
                "functy.0 = (*mut u8, *const u8, u32)",
                "functy.0 = (*mut u8, *const u8, u16)",
            )
            .replace("%12 = const u32 4", "%12 = const u16 4"),
    );
    refused(&m, &copy);
    // A memset of a run-time count (only a copy's count may be one).
    let m = module(&program(2, 3, 0, 4).replace("%12 = const u32 4", "%12 = copy u32 %1"));
    refused(&m, &witness(&[(13, 100, Some(101))]));
    // A run-time count of another type than the parameter's (a signed
    // count where C's `size_t` is unsigned).
    let m = module(&program(0, 1, 0, 4).replace(
        "%12 = const u32 4",
        "%22 = const i32 3\n\x20   %23 = bitcast u32 %1 to i32\n\x20   %12 = and i32 %23, %22",
    ));
    refused(&m, &copy);
    // The returned pointer is used.
    let m = module(&program(0, 1, 0, 4).replace(
        "%14 = load u64, ptr %2",
        "%14 = load u64, ptr %2\n\x20   %15 = ptrtoint *mut u8 %13 to usize",
    ));
    refused(&m, &copy);
    let m = module(&program(0, 1, 0, 4));
    // A fill byte claimed for a copy.
    refused(&m, &witness(&[(13, 100, Some(101))]));
    // A count name that is not fresh.
    refused(&m, &witness(&[(13, 2, None)]));
    // Not a call.
    refused(&m, &witness(&[(14, 100, None)]));
    // The fill byte missing for memset.
    let m = module(&program(2, 3, 0, 4));
    refused(&m, &witness(&[(13, 100, None)]));
    // Not the C prototype: an 8-bit fill, whose `trunc` to `u8` would not
    // narrow (trust-ir's validator rejects it). The view gives such a
    // declaration no body either.
    for byte in ["u8", "i8"] {
        let m = module(
            &program(2, 3, 0, 4)
                .replace(
                    "functy.1 = (ptr, i32, u32)",
                    &format!("functy.1 = (ptr, {byte}, u32)"),
                )
                .replace(
                    "%9 = bitcast u32 %1 to i32",
                    &format!("%9 = trunc u32 %1 to {byte}"),
                ),
        );
        refused(&m, &witness(&[(13, 100, Some(101))]));
        let view = interpretable_module(&m);
        let memset = view
            .functions
            .iter()
            .find(|f| f.name == "memset")
            .expect("memset");
        assert!(memset.is_declaration(), "{byte} fill has no library body");
    }
}

#[test]
fn a_memmove_spelled_without_overlap_is_refused() {
    // The checker rebuilds `memcopy overlap`; a target that drops `overlap`
    // (memcpy's meaning, under which the overlapping ranges here are
    // undefined) is not the claimed rewrite.
    let m = module(&program(0, 1, 0, 6));
    let src = f(&m);
    let w = witness(&[(13, 100, None)]);
    let (mut out, _) = rebuild_mem_call(&m, 32, src, &w).expect("accepted");
    for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::MemCopy { overlap, .. } = &mut node.inst {
            *overlap = false;
        }
    }
    assert!(matches!(
        check_pass(&m, 32, src, &out, &PassWitness::MemCall(w)),
        Err(MidTvError::TargetDiffers { .. })
    ));
}

#[test]
fn the_differential_sees_swapped_operands() {
    // A target that copies the other way (destination and source swapped)
    // disagrees with the source run in the view: the view's library bodies
    // give the differential something to compare.
    let m = module(&program(0, 1, 0, 6));
    let src = f(&m);
    let (mut out, _) = rebuild_mem_call(&m, 32, src, &witness(&[(13, 100, None)])).expect("ok");
    for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if let Inst::MemCopy { dst, src, .. } = &mut node.inst {
            std::mem::swap(dst, src);
        }
    }
    let view = interpretable_module(&m);
    let inputs = seeded_inputs(&m, src, 32, 64, 7).expect("scalar parameters");
    let (a, _) = run_samples(&view, src, &inputs, DifferentialBudget::default());
    let (t, _) = run_samples(&view, &out, &inputs, DifferentialBudget::default());
    assert!(compare_samples(&a, &t).mismatch.is_some());
}

/// `program` with the count `%1 & mask`: a run-time count from 0 to `mask`.
fn runtime_count(callee: u32, to: u32, from: u32, mask: u32) -> Module {
    module(&program(callee, to, from, 0).replace(
        "%12 = const u32 0",
        &format!("%22 = const u32 {mask}\n\x20   %12 = and u32 %1, %22"),
    ))
}

#[test]
fn a_copy_of_a_run_time_count_becomes_the_instruction_and_agrees() {
    // memmove up and down by overlapping ranges, and a disjoint memcpy; the
    // seeded inputs give counts from 0 to 7.
    for (callee, to, from) in [(0, 1, 0), (0, 0, 3), (1, 1, 8)] {
        let mask = if callee == 1 { 3 } else { 7 };
        let m = runtime_count(callee, to, from, mask);
        let out = accepted_and_agrees(&m, &witness(&[(13, 100, None)]));
        let nodes: Vec<&InstrNode> = out.blocks.iter().flat_map(|b| &b.body).collect();
        assert!(nodes.iter().any(|n| matches!(
            n.inst,
            Inst::Cast {
                op: CastOp::ZExt,
                dst_ty: Ty::Usize,
                operand,
                ..
            } if operand == v(12)
        ) && n.results == [v(100)]));
        assert!(nodes.iter().any(|n| matches!(
            n.inst,
            Inst::MemCopy { overlap, bytes, .. } if bytes == v(100) && overlap == (callee == 0)
        )));
        // trust-ir's validator reports nothing new on the target: the count
        // is a `usize` (a `bitcast` to it would be `CastIncompatible`).
        let mut tgt = m.clone();
        let at = tgt.functions.iter().position(|g| g.name == "f").expect("f");
        tgt.functions[at] = out.clone();
        let findings = |m: &Module| -> Vec<String> {
            trust_ir_build::validate_module(m)
                .iter()
                .map(|e| format!("{e:?}"))
                .collect()
        };
        let before = findings(&m);
        let new: Vec<String> = findings(&tgt)
            .into_iter()
            .filter(|e| !before.contains(e))
            .collect();
        assert!(new.is_empty(), "new validation findings: {new:?}");
    }
}

#[test]
fn a_narrowed_run_time_count_is_refused() {
    // The checker rebuilds the count's `zext` to `usize`; a target that
    // copies only the count's low byte is not the claimed rewrite.
    let m = runtime_count(0, 1, 0, 0x1ff);
    let src = f(&m);
    let w = witness(&[(13, 100, None)]);
    let (mut out, _) = rebuild_mem_call(&m, 32, src, &w).expect("accepted");
    for node in out.blocks.iter_mut().flat_map(|b| &mut b.body) {
        if node.results == [v(100)] {
            node.inst = Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::U8,
                dst_ty: Ty::Usize,
                operand: v(12),
            };
        }
    }
    assert!(matches!(
        check_pass(&m, 32, src, &out, &PassWitness::MemCall(w)),
        Err(MidTvError::TargetDiffers { .. })
    ));
}
