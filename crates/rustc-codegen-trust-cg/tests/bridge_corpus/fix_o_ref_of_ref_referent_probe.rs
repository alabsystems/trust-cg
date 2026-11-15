// (o) PROBE: a REFERENCE-typed referent (`r: &u32`) whose `&mut r` reaches a
// LOCAL `&mut &u32`-returning callee. Celling `r` alone would be a PARTIAL chain
// cell (its own referent `x` has no address), which the reference-chain rule
// documents as a miscompile shape; the reference-escaping cell widening
// (4c961dcbb) must therefore leave this either correctly lowered or refused by
// name — never a stale read. LLVM: `seen=9`, exit 0.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Distinct from `stale_celled_local_copy.rs` / `stale_celled_entry_arg.rs`, whose
// `&mut &S` goes through the NON-local `identity` and whose inner referents are
// memory-backed parameters: here the callee is LOCAL and the inner referent is a
// scalarized LOCAL. Measured on trust-cg main `ad7ee9c4e` (aarch64-apple-darwin,
// driver `0cb693917`), -O0/-O2/-O3: REFUSED by name ("borrowed scalar reference
// used without deref"); with the pre-widening narrowing restored it is refused
// earlier ("promoted mutable scalar reference return is unsupported"). A change
// that makes this row COMPILE must also make it print `seen=9`.
#![allow(dead_code)]
#[inline(never)]
fn id_r<'a, 'b>(r: &'a mut &'b u32) -> &'a mut &'b u32 {
    r
}
fn main() {
    let x = 5u32;
    let y = 9u32;
    let mut r: &u32 = &x;
    let rr = id_r(&mut r);
    *rr = &y;
    let seen = *r;
    println!("seen={}", seen);
    std::process::exit((seen != 9) as i32);
}
