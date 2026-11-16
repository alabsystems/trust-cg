// Fixture of tests/slice_capabilities_2_linux.rs (pinned refusal).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// `[&g]` where `g` is a `fn` pointer local: `cellable_address_referent` does
// not admit a `fn` pointer referent, so the stored-reference cell pass leaves
// `g` uncelled and `f` keeps "borrowed scalar reference used without deref".
// (Skipping the admission check compiles this crate; LLVM agrees with that
// build, so this pins the admission boundary, not a miscompile.)
use std::hint::black_box as bb;
#[inline(never)]
fn f(a: u32) -> u32 {
    fn inc(x: u32) -> u32 {
        x + 9
    }
    let g: fn(u32) -> u32 = bb(inc);
    let arr = [&g];
    (arr[0])(a)
}
fn main() {
    let mut acc = 0u32;
    for i in 0..6u32 {
        acc = acc.wrapping_mul(31).wrapping_add(f(bb(i)));
    }
    println!("{acc}");
    std::process::exit((acc % 251) as i32);
}
