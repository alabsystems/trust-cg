// (o) CONTROL — the `[TCG-REFRET-WRAP]` refusal must keep firing. `&mut v` of an
// INTERCEPTED `Vec<u64>` local (a `borrowed_scalars` binding the reference-
// escaping cell widening, 4c961dcbb, deliberately leaves uncelled — see
// `cellable_reference_referent_ty`) reaches a LOCAL callee whose return WRAPS a
// `&mut u64` in a struct; the wrapped form is refused by the pin, never lowered.
// LLVM: `v0=10`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Compiled with the bridge this program must FAIL CLOSED with
//
//   [TCG-REFRET-WRAP] call passes a `&mut`/`&` to a scalarized local and returns
//   a `&mut` scalar reference wrapped in an aggregate/enum (&mut u64)
//
// Measured on trust-cg main `ad7ee9c4e` (aarch64-apple-darwin, driver
// `0cb693917`) at -O0/-O2/-O3, proof certificates on and off. Enforced by
// `tests/unsupported_program.rs::wrapped_mut_scalar_ref_return_still_fails_closed`;
// the bare-`&mut` twin of this control is `fix_ctl_refret_vec_intercepted.rs`.
//
// WHAT THIS ROW DOES AND DOES NOT PROVE. It pins that the guard is still PRESENT
// and still reached for a borrowed-scalar argument: with the guard deleted this
// program COMPILES with proof certificates off, and with them on it loses the
// `[TCG-REFRET-WRAP]` tag the pin asserts (so the pin fails either way). It is
// not itself a miscompile witness — with the guard deleted it prints the correct
// `v0=10` at -O0, because the store goes through the Vec's heap pointer, not
// through the dead temp. The shape the
// guard is load-bearing for, measured with the guard deleted, is a PROJECTED
// field borrow of a scalarized struct, `make(&mut s.a) -> W { p: &mut u64 }`:
// -O0 compiles and prints `a=1` against LLVM's `a=10`.
#![allow(dead_code)]
struct W<'a> {
    p: &'a mut u64,
}
#[inline(never)]
fn make(v: &mut Vec<u64>) -> W<'_> {
    W { p: &mut v[0] }
}
fn main() {
    let mut v = vec![1u64, 2, 3];
    *make(&mut v).p = 10;
    let v0 = v[0];
    println!("v0={}", v0);
}
