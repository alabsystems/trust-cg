// Corpus: a POINTER-width local carried across a loop back-edge.
//
// `compute_loop_header_params` threads loop-carried SCALAR locals through a header
// phi, and `local_is_scalar` is `bit_width().is_some()` — which
// `trust_ir::Ty::bit_width()` answers `None` for EVERY pointer-like type (widths
// live in `bit_width_with(pointer_bits)`). So a pointer cursor could never become a
// header phi and every loop carrying one failed closed: "loop-carried local _N is
// mutated inside a loop but is neither memory-backed nor threaded through a
// loop-header phi". `core::fmt::write`'s `NonNull<u8>` cursor is one of them, which
// is to say all of `format!` stopped there.
//
// THE REFUSAL WAS CORRECT: without a carrier the in-loop `p = p.add(1)` is dropped
// across the back-edge and every iteration re-reads the first byte.
//
// THIS ROW NOW AGREES. It is kept because it CAUGHT A WRONG FIX, and it is the
// row that has to keep agreeing if this lane is ever touched again.
//
// Three routes were built and measured. All three are recorded, because each
// fails in a different and non-obvious way:
//
//   * SCALAR CELL — A LIVE MISCOMPILE. Adding these locals to
//     `compute_scalar_cell_locals` made the census read one fewer failed root
//     with 0 newly failing, AND this row compiled to `p 6 1 3` against LLVM's
//     `p 63 32 21`: the slot exists but the in-loop update is still not observed,
//     so every row degrades to exactly its "update dropped" value. THE -O0 CENSUS
//     SCORED THAT AS PROGRESS, because a refusal became a compile. Only this
//     differential row caught it.
//
//   * HEADER PHI, admitted by WIDTH. `bit_width_with(..).is_some()` also admits
//     `Ty::FatPtr(_)` (it reports `2 * pointer_bits`). A fat pointer is TWO LANES
//     and a header parameter is ONE value, so that spelling creates params no
//     predecessor can supply. Narrowing to one-lane pointer types is necessary —
//     and was NOT sufficient.
//
//   * HEADER PHI, admitted by TYPE. Two corpus rows still regressed at -O2
//     (`fix_fn_pointer_pair_return`, `union_array_leaf_aggregate`) with
//     "loop-carried local _N has no value on edge bbX -> bbY". NO TYPE-SHAPED
//     PREDICATE CAN FIX THAT: the instrumented refusal shows both failing locals
//     are `std::ptr::NonNull<u8>` — the SAME TYPE as `core::fmt::write`'s `_7`
//     cursor this admission exists to thread.
//
// WHAT WORKS: `ctx.fmt_dead_locals` — NOT the type — is the authority. A local the
// `format!`/`write!` interception decodes at compile time is never bound at
// runtime, so it has no value to thread; excluding exactly those locals restores
// both -O2 rows while `core::fmt::write` still lowers.
//
// The standing in-tree note read this regression as a pre-lowering ORDERING
// problem ("whether a def yields a scalar binding is only known DURING lowering").
// The observation was right and the conclusion was too general: the information
// needed is available in time, in a set built for precisely this purpose.
//
// If this row ever compiles with DIFFERENT values, it reports DIVERGE — which is
// how the miscompile above was found.
//
// EVERY ROW IS A WRONG NUMBER IF THE UPDATE IS DROPPED, not a crash:
//   * `sum_raw`  63 = 1+2+4+8+16+32. Dropped, it re-reads byte 0 and prints 6.
//   * `last_raw` 32 = the final byte, reached only by advancing 5 times. Dropped, 1.
//   * `stride2`  21 = 1+4+16. Dropped, 3 — and a stride of 1 rather than 2 prints 7,
//     so this row pins the ADVANCE AMOUNT, not merely that some advance happened.
#![allow(dead_code)]

#[inline(never)]
unsafe fn sum_raw(mut p: *const u8, n: usize) -> u64 {
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < n {
        acc += *p as u64;
        p = p.add(1);
        i += 1;
    }
    acc
}

#[inline(never)]
unsafe fn last_raw(mut p: *const u8, n: usize) -> u64 {
    let mut i = 0usize;
    while i + 1 < n {
        p = p.add(1);
        i += 1;
    }
    *p as u64
}

#[inline(never)]
unsafe fn stride2(mut p: *const u8, n: usize) -> u64 {
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < n {
        acc += *p as u64;
        p = p.add(2);
        i += 2;
    }
    acc
}

fn main() {
    let a: [u8; 6] = [1, 2, 4, 8, 16, 32];
    let r1 = unsafe { sum_raw(a.as_ptr(), 6) };
    let r2 = unsafe { last_raw(a.as_ptr(), 6) };
    let r3 = unsafe { stride2(a.as_ptr(), 6) };
    println!("p {} {} {}", r1, r2, r3); // 63 32 21
}
