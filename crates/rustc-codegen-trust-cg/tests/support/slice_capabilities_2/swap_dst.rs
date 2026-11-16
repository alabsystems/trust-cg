// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
struct Hdr<T: ?Sized> {
    n: u32,
    d: T,
}
#[inline(never)]
fn sw<'a>(x: &mut &'a Hdr<[u8]>, y: &mut &'a Hdr<[u8]>) {
    std::mem::swap(x, y);
}
fn main() {
    let a = Hdr {
        n: bb(1),
        d: [1u8, 2, 3],
    };
    let b = Hdr {
        n: bb(2),
        d: [9u8; 5],
    };
    let (mut p, mut q): (&Hdr<[u8]>, &Hdr<[u8]>) = (&a, &b);
    sw(&mut p, &mut q);
    std::process::exit((p.n * 100 + p.d.len() as u32 * 10 + q.d.len() as u32) as i32);
}
