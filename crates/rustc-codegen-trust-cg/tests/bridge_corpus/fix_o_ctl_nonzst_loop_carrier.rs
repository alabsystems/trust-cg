// FORMER CONTROL for `fix_o_zst_loop_carrier.rs`, now a POSITIVE row: a
// NON-zero-sized loop carrier COMPILES and AGREES with LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// This is the shape of the ONE loop-carried root a `library/core` census used
// to report that is not the zero-sized sub-case: `core::fmt::write`'s
// `loop-carried local _7 (type ptr::non_null::NonNull<u8>)`. When this row was
// written it proved the ZST exemption was keyed on ZERO-SIZEDNESS and not
// merely on being a loop carrier, and the bridge REFUSED it with
//
//   loop-carried local _2 (type std::ptr::NonNull<u8>) is mutated inside a loop
//   but is neither memory-backed nor threaded through a loop-header phi
//
// Since da9885c03 (2026-09-15) a ONE-LANE pointer-width carrier is admitted as
// a loop-header phi — the authority is `fmt` interception liveness, not the
// type — and this row, like its twin `fix_q_pointer_loop_carrier`, compiles and
// AGREES with LLVM at both opt levels. The ZST exemption itself is still pinned
// by `fix_o_zst_loop_carrier.rs`. A row that REFUSES here is now the regression
// (it re-opens `core::fmt::write`); a row that compiles and DIVERGES is the
// miscompile the old refusal guarded against (a dropped in-loop update). The
// mechanical pin for both is
// `tests/unsupported_program.rs::nonzst_pointer_loop_carrier_compiles_and_threads_its_update`.

use core::ptr::NonNull;

fn hash(buf: &[u8]) -> u64 {
    let mut p = NonNull::from(&buf[0]);
    let mut acc = 0u64;
    let mut i = 0usize;
    while i < buf.len() {
        acc = acc
            .wrapping_mul(31)
            .wrapping_add(unsafe { *p.as_ptr() } as u64);
        p = unsafe { NonNull::new_unchecked(p.as_ptr().add(1)) };
        i += 1;
    }
    acc
}

fn main() {
    println!("{}", hash(b"carrier"));
}
