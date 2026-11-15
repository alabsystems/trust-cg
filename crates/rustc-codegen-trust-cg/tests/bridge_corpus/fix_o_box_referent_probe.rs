// (o) PROBE: a `Box<u32>` referent (a single-pointer newtype chain the scalar
// mapping collapses to one `Ptr`, placed by the `Box::new` interception) whose
// `&mut` reaches a LOCAL `&mut`-returning callee. Recorded so the reference-
// escaping cell widening's (4c961dcbb) admission of Box is MEASURED, not assumed:
// OK or a named refusal are both acceptable; a wrong exit is not. LLVM:
// `seen=9`, exit 0.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Measured on trust-cg main `ad7ee9c4e` (aarch64-apple-darwin, driver
// `0cb693917`), -O0/-O2/-O3: REFUSED by name, `[TCG-SCALAR-CELL-LAYOUT] projected
// cell must be an exact zero-offset, full-allocation primitive scalar field
// chain` — the widened rule admits the Box to the cell and the cell-layout gate
// declines it. (With the pre-widening narrowing restored it is refused earlier,
// by "promoted mutable scalar reference return is unsupported".) A change that
// makes this row COMPILE must also make it print `seen=9`.
#![allow(dead_code)]
#[inline(never)]
fn id_b(b: &mut Box<u32>) -> &mut Box<u32> {
    b
}
fn main() {
    let mut b = Box::new(5u32);
    let r = id_b(&mut b);
    **r = 9;
    let seen = *b;
    println!("seen={}", seen);
    std::process::exit((seen != 9) as i32);
}
