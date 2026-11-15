// (o) Two more non-primitive scalar-leaf referents through the reference-return
// shape: a `Wrapping<u32>` newtype (maps to `U32`) and a `*mut u64` raw pointer
// (maps to a pointer-like leaf). Before the reference-escaping cell widening
// (4c961dcbb) both fell through every placement model (not primitive, not
// memory-backed, pointer-like excluded from the RawPtr cell rule) and were
// refused by name; now each is celled and the store through the returned `&mut`
// lands. The raw pointer is initialised from a call and re-pointed through a
// plain copy so every assignment to the celled local is a shape the cell store
// lowers. LLVM: `w=42 a=1 b=42`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The RAW-POINTER referent is the part no other corpus row covers: a store of a
// new POINTER through the returned `&mut *mut u64` must re-aim `p`. A store lost
// in a dead temp would leave `p` aimed at `cell_a` and print `a=41 b=2` (derived
// from the program; no measured build lowers it that way). Measured on trust-cg
// main `ad7ee9c4e` (aarch64-apple-darwin, driver `0cb693917`): matches LLVM at
// -O0/-O2/-O3; with the pre-widening primitive-only narrowing restored it is
// refused by name ("promoted mutable scalar reference return is unsupported").
#![allow(dead_code)]
use std::num::Wrapping;
#[inline(never)]
fn id_w(w: &mut Wrapping<u32>) -> &mut Wrapping<u32> {
    w
}
#[inline(never)]
fn id_p(p: &mut *mut u64) -> &mut *mut u64 {
    p
}
fn main() {
    let mut w = Wrapping(5u32);
    let r = id_w(&mut w);
    *r = Wrapping(42);
    let seen_w = w.0;
    let mut cell_a = 1u64;
    let mut cell_b = 2u64;
    let mut p: *mut u64 = core::ptr::null_mut();
    let qa: *mut u64 = &mut cell_a;
    p = qa;
    let rp = id_p(&mut p);
    let qb: *mut u64 = &mut cell_b;
    *rp = qb;
    let pp = p;
    unsafe {
        *pp += 40;
    }
    println!("w={} a={} b={}", seen_w, cell_a, cell_b);
}
