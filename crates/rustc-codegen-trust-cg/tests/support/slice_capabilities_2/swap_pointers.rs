// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

#[derive(Debug)]
enum E {
    A(u64),
    B(u32, u64),
}
#[inline(never)]
fn rev<'a>(v: &mut [&'a E]) {
    v.reverse();
}
fn val(e: &E) -> u64 {
    match e {
        E::A(x) => *x,
        E::B(a, b) => *a as u64 + *b,
    }
}
fn main() {
    let a = E::A(3);
    let b = E::A(5);
    let c = E::A(11);
    let mut v = [&a, &b, &c];
    rev(&mut v);
    let mut x: usize = std::hint::black_box(4);
    let mut y: usize = 9;
    std::mem::swap(&mut x, &mut y);
    let mut p: *const u8 = std::ptr::null();
    let mut q: *const u8 = b"hi".as_ptr();
    std::mem::swap(&mut p, &mut q);
    let s = val(v[0]) * 100
        + val(v[2])
        + (x as u64) * 7
        + y as u64
        + p.is_null() as u64 * 3
        + q.is_null() as u64 * 5;
    std::process::exit((s % 251) as i32);
}
