// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Name(u32);
#[inline(never)]
fn find(all: &[&Name], n: Name) -> usize {
    let mut i = 0;
    while i < all.len() {
        if *all[i] == n {
            return i;
        }
        i += 1;
    }
    99
}
#[inline(never)]
fn root(a: u32, b: u32, c: u32) -> usize {
    let x = Name(a);
    let y = Name(b);
    let one = [&x];
    let two = [&x, &y];
    let all: &[&Name] = if c >= 2 { &two } else { &one };
    find(all, Name(b))
}
fn main() {
    let v = std::hint::black_box(7u32);
    let mut s = 0usize;
    for c in 0..4u32 {
        s = s * 131 + root(v, v + c % 2, c);
    }
    std::process::exit((s % 251) as i32);
}
