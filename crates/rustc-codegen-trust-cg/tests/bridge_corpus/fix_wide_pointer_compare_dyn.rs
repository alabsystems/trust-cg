// Corpus: comparison operators on TRAIT-OBJECT raw pointers.
//
// `==` / `!=` / `<` on `*const dyn Trait` compare the `(data, vtable)` PAIRS,
// unsigned and data first. The bridge carries a trait-object pointer as two
// lanes; a comparison must read both.
//
// WHAT EACH ROW WOULD CATCH. `whole` and `first` share their DATA address (a
// `repr(C)` struct and its first field) and differ only in vtable (`S` vs
// `u32`), so a comparison that reads the data half alone says they are equal:
//  * `dyn_ops(whole, first)`: `==` false, `!=` true;
//  * `dyn_ops(whole, whole)`: `==` true, `!=` false;
//  * `dyn_lt`: with equal data halves the order is the vtables' order, so
//    exactly one of `a < b` and `b < a` holds (printed as their sum, which
//    does not depend on where the linker places either vtable).
#![allow(dead_code, ambiguous_wide_pointer_comparisons)]

use std::fmt::Debug;
use std::hint::black_box as bb;

#[derive(Debug)]
#[repr(C)]
struct S {
    a: u32,
    b: u32,
}

#[inline(never)]
fn dyn_ops(a: *const dyn Debug, b: *const dyn Debug) -> (bool, bool) {
    (a == b, a != b)
}

#[inline(never)]
fn dyn_lt(a: *const dyn Debug, b: *const dyn Debug) -> bool {
    a < b
}

fn main() {
    let st = bb(S { a: 1, b: 2 });
    let whole: *const dyn Debug = &st;
    let first: *const dyn Debug = &st.a;
    let (de, dn) = dyn_ops(whole, first);
    let (se, sn) = dyn_ops(whole, whole);
    let (de, dn, se, sn) = (de as u8, dn as u8, se as u8, sn as u8);
    println!("dyn_ops {} {} {} {}", de, dn, se, sn);
    let one_way = dyn_lt(whole, first) as u8 + dyn_lt(first, whole) as u8;
    let reflexive = dyn_lt(whole, whole) as u8;
    println!("dyn_lt {} {}", one_way, reflexive);
}
