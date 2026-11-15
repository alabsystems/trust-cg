// (o) The `IterMut<T>::next` shape: `Some({ptr}.as_mut())` calls
// `NonNull::<T>::as_mut(&mut tmp) -> &'a mut T` with `tmp: NonNull<T>` a
// SCALARIZED temp (a single-pointer transparent newtype). Inside `core` the
// callee is LOCAL, so `direct_scalar_ref_select_return` refused every such call
// by name; here a LOCAL wrapper reproduces the exact predicate. With the
// reference-escaping cell widening (4c961dcbb) the referent is celled, `&mut
// tmp` is the cell pointer, and the callee's returned `&mut T` (derived from the
// VALUE inside the NonNull, not from the address of `tmp`) is a genuine address.
// LLVM: `a=42 b=100 s=142`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Distinct from `fix_refret_cell_nonprimitive.rs`: that referent is an integer
// newtype and the callee hands back the ARGUMENT's address; here the referent is
// a POINTER-valued newtype and the callee hands back the address it HOLDS.
// Measured on trust-cg main `ad7ee9c4e` (aarch64-apple-darwin, driver
// `0cb693917`): matches LLVM at -O0/-O2/-O3; with the pre-widening primitive-only
// narrowing restored it is refused by name ("promoted mutable scalar reference
// return is unsupported") — a capability pin for the `library/core` roots.
#![allow(dead_code)]
use std::ptr::NonNull;
struct Two {
    a: u64,
    b: u64,
}
#[inline(never)]
fn as_mut_local<'a>(p: &mut NonNull<u64>) -> &'a mut u64 {
    unsafe { p.as_mut() }
}
#[inline(never)]
fn bump(two: &mut Two) -> u64 {
    let mut tmp = NonNull::from(&mut two.a);
    let r = as_mut_local(&mut tmp);
    *r += 35;
    two.a + two.b
}
fn main() {
    let mut two = Two { a: 7, b: 100 };
    let s = bump(&mut two);
    let (a, b) = (two.a, two.b);
    println!("a={} b={} s={}", a, b, s);
}
