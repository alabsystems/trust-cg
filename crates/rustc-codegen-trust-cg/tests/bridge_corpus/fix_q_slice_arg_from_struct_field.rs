// A `&[T]` call ARGUMENT that is a FIELD of an aggregate, not a whole local —
// `f(copy (_3.0: u8), move (_3.1: &[u8]))`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// UNPATCHED this fails closed with "direct call slice fat-pointer arg 1 is not a
// whole-slice place or const-slice literal". On `library/core` it is exactly two
// roots — `slice::memchr::memchr_aligned` (arg 1, `move (_3.1: &[u8])`) and
// `str::validations::run_utf8_validation` (arg 0, `move (_12.0: &[u8])`).
//
// WHY `const_eval_select`, and not a hand-written struct field. Ordinary source
// `f(pair.second)` is spilled to a temp by rustc at every optimization level, so
// the bridge sees a whole-local argument and the arm is never reached — measured
// at `-Copt-level=0/1/2/3` on a by-value tuple parameter AND a by-value struct
// parameter, all four COMPILED unpatched. `const_eval_select!`'s `@capture`
// packs its captures into ONE tuple and the intrinsic's lowering substitutes the
// tuple's FIELDS straight into the branch call's argument list with no temp —
// which is precisely how both `library/core` roots arise. This fixture uses the
// intrinsic directly so it reproduces that MIR, rather than approximating it.
//
// A slice field of a memory-backed aggregate is ALREADY stored as the two lanes
// `{ data @ off, len @ off+8 }`, so the field's own byte address IS the
// `{ data, len }` slot the callee's parameter ABI wants; nothing is rebuilt.
//
// A wrong answer is SILENT in BOTH lanes — a wrong `data` reads the wrong bytes,
// a wrong `len` is an out-of-bounds read — so the checksum below consumes BOTH
// (the length seeds the accumulator and bounds the loop), the three slices have
// DIFFERENT lengths and DIFFERENT contents, and the scalar captured alongside is
// non-zero so a field picked from the wrong tuple offset is visible in the value.

#![feature(core_intrinsics)]
#![allow(internal_features)]

#[inline(never)]
fn checksum(s: &[u8]) -> u64 {
    // Uses BOTH lanes: the length seeds and bounds, every data byte is folded.
    let mut acc: u64 = s.len() as u64;
    let mut i = 0usize;
    while i < s.len() {
        acc = acc.wrapping_mul(31).wrapping_add(s[i] as u64);
        i += 1;
    }
    acc
}

const fn ct(x: u8, s: &[u8]) -> u64 {
    // The const branch is never taken at runtime; it must still type-check.
    (x as u64).wrapping_add(s.len() as u64)
}

fn rt(x: u8, s: &[u8]) -> u64 {
    checksum(s).wrapping_add(x as u64)
}

#[inline(never)]
fn pick(x: u8, s: &[u8]) -> u64 {
    core::intrinsics::const_eval_select((x, s), ct, rt)
}

fn main() {
    let a: [u8; 3] = [1, 2, 3];
    let b: [u8; 5] = [9, 8, 7, 6, 5];
    let c: [u8; 1] = [255];
    println!("{}", pick(std::hint::black_box(7u8), &a));
    println!("{}", pick(std::hint::black_box(200u8), &b));
    println!("{}", pick(std::hint::black_box(0u8), &c));
    // The same slices through the ordinary whole-local argument path: the two
    // must agree, which is what pins the field address to the right lanes.
    println!("{}", checksum(std::hint::black_box(&a[..])));
    println!("{}", checksum(std::hint::black_box(&b[..])));
    println!("{}", checksum(std::hint::black_box(&c[..])));
}
