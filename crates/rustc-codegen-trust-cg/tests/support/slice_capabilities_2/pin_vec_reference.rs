// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
#[inline(never)]
fn total(all: &[&Vec<u32>]) -> u32 {
    let mut s = 0;
    for v in all {
        s += v.len() as u32 * 10 + v[0];
    }
    s
}
#[inline(never)]
fn root(k: u32) -> u32 {
    let mut a = Vec::new();
    a.push(k);
    a.push(2);
    let mut b = Vec::new();
    b.push(5u32);
    let arr = [&a, &b];
    total(&arr)
}
fn main() {
    std::process::exit(root(bb(3)) as i32);
}
