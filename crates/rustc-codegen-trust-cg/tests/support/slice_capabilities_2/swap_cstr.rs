// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::ffi::CStr;
use std::hint::black_box as bb;
#[inline(never)]
fn sw<'a>(x: &mut &'a CStr, y: &mut &'a CStr) {
    std::mem::swap(x, y);
}
fn main() {
    let a: &CStr = bb(c"hello");
    let b: &CStr = bb(c"to");
    let (mut p, mut q) = (a, b);
    sw(&mut p, &mut q);
    std::process::exit((p.to_bytes().len() * 10 + q.to_bytes().len()) as i32);
}
