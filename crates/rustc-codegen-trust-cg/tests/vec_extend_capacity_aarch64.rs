// Other hosts compile no native test; a Darwin host must meet every prerequisite.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// `Vec::extend` from an iterator chain leaves std's capacity, and one from a
// bare integer `Range` of every width and signedness compiles and matches LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The bridge drives an `extend` chain and pushes each element, so the Vec grew
// push by push (4, 8, 16, ...). std's `SpecExtend` does not:
// * a `TrustedLen` chain (`extend_trusted`) reserves its exact count before
//   anything is pulled: 13 elements into `Vec::new()` leave capacity 13;
// * any other chain (`extend_desugared`) reserves `size_hint().0 + 1` when an
//   element meets a full Vec. For an exact hint that is the final length; for
//   a zero lower bound (`filter`, `take_while`) it is one element, a push.
// Measured on trust-cg main 6dd3c1dff (2026-10-09, against LLVM, -O0/-O1, both
// panic strategies): every exact chain diverged (`a.iter().copied()` 16
// against 13 from `Vec::new()`, 20 against 15 from a 5-capacity Vec holding
// two), so the `trusted` and `desugared` programs fail on that backend; the
// zero-lower-bound chains and the separately lowered sources (a `Range`, an
// owned `Vec`, a slice) already matched (`controls`). At -O2/-O3 these calls
// reach std's `extend_trusted` / `extend_desugared`, which the bridge refuses
// by name; those cells must match or refuse exactly so.
//
// Each case extends four Vecs (empty, a 5-capacity one and a 15-capacity one
// holding two elements, a 40-capacity one) and prints `capacity,len`
// (`cleared_halves` also prints the sum).
//
// `cleared_halves` extends from a `Chain` one of whose halves core's own
// `next` / `next_back` / `nth` had set to `None`. MEASURED at 14e9bc711
// (debug bridge, Trust 9192, this test run against that backend): its 4
// -O0/-O1 cells were killed by SIGSEGV, the drive advancing the null `ptr` of
// a cleared `slice::Iter` half; its -O2/-O3 cells refused by name, as now.
//
// `range_widths` and `const_ranges` extend from a bare integer `Range` of
// each of the ten integer types, which the bridge fills by counting up from
// `start` in `I64` and moving each value to the element type. `range_widths`
// passes its endpoints at run time; `const_ranges` passes constants, which
// mir-opt folds into one `const Range` operand from -O1. MEASURED at
// fb96d7a17 (debug bridge, Trust 9192, `no-proof-certs`, the programs
// compiled against that backend and LLVM): all 8 -O0/-O1 cells of the two
// were refused. Object emission refused the `u64` and `usize` fills
// (`[TCG-IR-LOWER]`, a `CastOp::Trunc` from `I64` to `U64`, though the widths
// are equal), and lowering refused every type's constant range at -O1
// ("Vec::extend range source is not a place operand"). The fill now moves a
// 64-bit value by `Bitcast` and narrows a narrower one by `Trunc`, and a
// constant range's endpoints are read from its allocation.
//
// PROOF GATE: compiled with `no-proof-certs`; an execution differential, not a
// certification claim.

use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

const TARGET: &str = "aarch64-apple-darwin";
const OPTS: [u32; 4] = [0, 1, 2, 3];
const PANICS: [&str; 2] = ["abort", "unwind"];
/// The levels every cell must compile at and match LLVM.
const MUST_MATCH: [u32; 2] = [0, 1];
/// The refusals an -O2/-O3 cell may end in: std's own extend bodies.
const NAMED_REFUSALS: [&str; 2] = [
    "extend_trusted is not an intercepted Vec method",
    "extend_desugared is not an intercepted Vec method",
];

struct Program {
    name: &'static str,
    src: &'static str,
    /// The LLVM oracle's stdout (every program exits 0), so a broken oracle
    /// cannot pass.
    stdout: &'static str,
}

const PROGRAMS: &[Program] = &[
    Program {
        name: "trusted",
        src: r##"use std::hint::black_box as bb;
fn main() {
    let a = [bb(1u32), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().copied()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().copied()); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().cloned()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().cloned()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().cloned()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().cloned()); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter()); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend((bb(0u32)..13).map(|x| x * 3)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend((bb(0u32)..13).map(|x| x * 3)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend((bb(0u32)..13).map(|x| x * 3)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend((bb(0u32)..13).map(|x| x * 3)); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend((bb(0u32)..=12)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend((bb(0u32)..=12)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend((bb(0u32)..=12)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend((bb(0u32)..=12)); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().enumerate().map(|(i, x)| x + i as u32)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().enumerate().map(|(i, x)| x + i as u32)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().enumerate().map(|(i, x)| x + i as u32)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().enumerate().map(|(i, x)| x + i as u32)); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().zip(a.iter()).map(|(x, y)| x + y)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().zip(a.iter()).map(|(x, y)| x + y)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().zip(a.iter()).map(|(x, y)| x + y)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().zip(a.iter()).map(|(x, y)| x + y)); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().copied().take(bb(9))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().take(bb(9))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().take(bb(9))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().copied().take(bb(9))); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().copied().skip(bb(2))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().skip(bb(2))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().skip(bb(2))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().copied().skip(bb(2))); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().copied().rev()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().rev()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().rev()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().copied().rev()); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.to_vec().into_iter().map(|x| x + 1)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.to_vec().into_iter().map(|x| x + 1)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.to_vec().into_iter().map(|x| x + 1)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.to_vec().into_iter().map(|x| x + 1)); print!("{},{} ", v.capacity(), v.len()); }
    println!();
}
"##,
        stdout: "13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n9,9 11,11 15,11 40,9 \n11,11 13,13 15,13 40,11 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n",
    },
    Program {
        name: "desugared",
        src: r##"use std::hint::black_box as bb;
fn main() {
    let a = [bb(1u32), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().copied().inspect(|_| {})); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().inspect(|_| {})); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().inspect(|_| {})); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().copied().inspect(|_| {})); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().rev().skip(bb(3)).copied()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().rev().skip(bb(3)).copied()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().rev().skip(bb(3)).copied()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().rev().skip(bb(3)).copied()); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().copied().inspect(|_| {}).take(bb(30))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().inspect(|_| {}).take(bb(30))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().inspect(|_| {}).take(bb(30))); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().copied().inspect(|_| {}).take(bb(30))); print!("{},{} ", v.capacity(), v.len()); }
    println!();
}
"##,
        stdout: "13,13 15,15 15,15 40,13 \n10,10 12,12 15,12 40,10 \n13,13 15,15 15,15 40,13 \n",
    },
    Program {
        name: "controls",
        src: r##"use std::hint::black_box as bb;
fn main() {
    let a = [bb(1u32), 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];
    { let mut v: Vec<u32> = Vec::new(); v.extend((bb(0u32)..13).filter(|x| x % 3 != 0)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend((bb(0u32)..13).filter(|x| x % 3 != 0)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend((bb(0u32)..13).filter(|x| x % 3 != 0)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend((bb(0u32)..13).filter(|x| x % 3 != 0)); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.iter().copied().take_while(|x| *x < 100)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().take_while(|x| *x < 100)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.iter().copied().take_while(|x| *x < 100)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.iter().copied().take_while(|x| *x < 100)); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend((bb(0u32)..13)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend((bb(0u32)..13)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend((bb(0u32)..13)); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend((bb(0u32)..13)); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(a.to_vec()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(a.to_vec()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(a.to_vec()); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(a.to_vec()); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(&a[..]); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(&a[..]); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(&a[..]); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(&a[..]); print!("{},{} ", v.capacity(), v.len()); }
    println!();
    { let mut v: Vec<u32> = Vec::new(); v.extend(&a); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(&a); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(&a); print!("{},{} ", v.capacity(), v.len()); }
    { let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(&a); print!("{},{} ", v.capacity(), v.len()); }
    println!();
}
"##,
        stdout: "8,8 10,10 15,10 40,8 \n16,13 20,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n13,13 15,15 15,15 40,13 \n",
    },
    // A `Chain` whose half core's own `Chain` bodies cleared before the
    // extend: `next` clears an exhausted `a`, `next_back` an exhausted `b`,
    // `nth` an `a` it runs past. A cleared half yields nothing and counts
    // nothing toward the reservation; its payload is not a cursor (the null
    // `ptr` of a `slice::Iter`, a `Range`'s undefined bytes).
    Program {
        name: "cleared_halves",
        src: r##"use std::hint::black_box as bb;
fn main() {
    let s = [bb(1u32), 2, 3];
    let t = [bb(4u32), 5, 6, 7, 8];
    { let mut it = s.iter().chain(t.iter()); for _ in 0..4 { it.next(); } let mut v: Vec<u32> = Vec::new(); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); for _ in 0..4 { it.next(); } let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); for _ in 0..4 { it.next(); } let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); for _ in 0..4 { it.next(); } let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    println!();
    { let mut it = (bb(0u32)..3).chain(bb(10u32)..15); for _ in 0..4 { it.next(); } let mut v: Vec<u32> = Vec::new(); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = (bb(0u32)..3).chain(bb(10u32)..15); for _ in 0..4 { it.next(); } let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = (bb(0u32)..3).chain(bb(10u32)..15); for _ in 0..4 { it.next(); } let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = (bb(0u32)..3).chain(bb(10u32)..15); for _ in 0..4 { it.next(); } let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    println!();
    { let mut it = s.iter().chain(t.iter()); for _ in 0..6 { it.next_back(); } let mut v: Vec<u32> = Vec::new(); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); for _ in 0..6 { it.next_back(); } let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); for _ in 0..6 { it.next_back(); } let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); for _ in 0..6 { it.next_back(); } let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    println!();
    { let mut it = (bb(0u32)..3).chain(bb(10u32)..12); for _ in 0..3 { it.next_back(); } let mut v: Vec<u32> = Vec::new(); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = (bb(0u32)..3).chain(bb(10u32)..12); for _ in 0..3 { it.next_back(); } let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = (bb(0u32)..3).chain(bb(10u32)..12); for _ in 0..3 { it.next_back(); } let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = (bb(0u32)..3).chain(bb(10u32)..12); for _ in 0..3 { it.next_back(); } let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    println!();
    { let mut it = s.iter().chain(t.iter()); it.nth(bb(4)); let mut v: Vec<u32> = Vec::new(); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); it.nth(bb(4)); let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(5)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); it.nth(bb(4)); let mut v: Vec<u32> = { let mut v = Vec::with_capacity(bb(15)); v.push(9u32); v.push(8); v }; v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    { let mut it = s.iter().chain(t.iter()); it.nth(bb(4)); let mut v: Vec<u32> = Vec::with_capacity(bb(40)); v.extend(it); print!("{},{},{} ", v.capacity(), v.len(), v.iter().sum::<u32>()); }
    println!();
}
"##,
        stdout: "4,4,26 10,6,43 15,6,43 40,4,26 \n4,4,50 10,6,67 15,6,67 40,4,50 \n4,2,3 5,4,20 15,4,20 40,2,3 \n4,2,1 5,4,18 15,4,18 40,2,1 \n4,3,21 5,5,38 15,5,38 40,3,21 \n",
    },
    // A bare integer `Range` of every width and signedness, which the bridge
    // extends with a count-up fill rather than the chain drive: each line is
    // one type (`u64`, `usize`, `i64`, `isize`, `u32`, `i32`, `u16`, `i16`,
    // `u8`, `i8`) and prints `capacity,len:` and the elements of a short
    // range, an empty and an inverted one, the type's top and bottom, the
    // inverted `MAX..MIN`, a range across the middle of the type (an unsigned
    // type's sign bit), `0.wrapping_sub(2)..2` (inverted when unsigned, across
    // zero when signed), and a range into a Vec that must grow and one that
    // need not. `range_widths` passes the endpoints at run time.
    Program {
        name: "range_widths",
        src: r##"use std::hint::black_box as bb;
macro_rules! widths {
    ($($t:ident)*) => {$(
        #[inline(never)]
        fn $t() {
            #[inline(never)]
            fn show(v: &Vec<$t>) {
                let c = v.capacity();
                let l = v.len();
                print!("{},{}:", c, l);
                let mut i = 0;
                while i < l { let x = v[i]; print!(" {}", x); i += 1; }
                print!(";");
            }
            { let mut v: Vec<$t> = Vec::new(); v.extend(bb(3 as $t)..bb(8)); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(bb(5 as $t)..bb(5)); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(bb(9 as $t)..bb(2)); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(bb($t::MAX - 3)..bb($t::MAX)); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(bb($t::MIN)..bb($t::MIN + 2)); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(bb($t::MAX)..bb($t::MIN)); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(bb($t::MAX / 2 - 1)..bb($t::MAX / 2 + 2)); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(bb((0 as $t).wrapping_sub(2))..bb(2)); show(&v); }
            { let mut v: Vec<$t> = { let mut v = Vec::with_capacity(bb(5)); v.push(1); v.push(2); v }; v.extend(bb(10 as $t)..bb(16)); show(&v); }
            { let mut v: Vec<$t> = Vec::with_capacity(bb(40)); v.push(7); v.extend(bb(10 as $t)..bb(13)); show(&v); }
            println!();
        }
    )*};
}
widths!(u64 usize i64 isize u32 i32 u16 i16 u8 i8);
fn main() {
    u64(); usize(); i64(); isize(); u32(); i32(); u16(); i16(); u8(); i8();
}
"##,
        stdout: RANGE_WIDTHS_STDOUT,
    },
    // The same ranges with constant endpoints, which mir-opt at -O1 folds
    // into one `const Range { start, end }` operand of the extend call.
    Program {
        name: "const_ranges",
        src: r##"use std::hint::black_box as bb;
macro_rules! widths {
    ($($t:ident)*) => {$(
        #[inline(never)]
        fn $t() {
            #[inline(never)]
            fn show(v: &Vec<$t>) {
                let c = v.capacity();
                let l = v.len();
                print!("{},{}:", c, l);
                let mut i = 0;
                while i < l { let x = v[i]; print!(" {}", x); i += 1; }
                print!(";");
            }
            { let mut v: Vec<$t> = Vec::new(); v.extend(3..8); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(5..5); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend(9..2); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend($t::MAX - 3..$t::MAX); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend($t::MIN..$t::MIN + 2); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend($t::MAX..$t::MIN); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend($t::MAX / 2 - 1..$t::MAX / 2 + 2); show(&v); }
            { let mut v: Vec<$t> = Vec::new(); v.extend((0 as $t).wrapping_sub(2)..2); show(&v); }
            { let mut v: Vec<$t> = { let mut v = Vec::with_capacity(bb(5)); v.push(1); v.push(2); v }; v.extend(10..16); show(&v); }
            { let mut v: Vec<$t> = Vec::with_capacity(bb(40)); v.push(7); v.extend(10..13); show(&v); }
            println!();
        }
    )*};
}
widths!(u64 usize i64 isize u32 i32 u16 i16 u8 i8);
fn main() {
    u64(); usize(); i64(); isize(); u32(); i32(); u16(); i16(); u8(); i8();
}
"##,
        stdout: RANGE_WIDTHS_STDOUT,
    },
];

/// The LLVM oracle's stdout for `range_widths` and `const_ranges`.
const RANGE_WIDTHS_STDOUT: &str = "5,5: 3 4 5 6 7;0,0:;0,0:;4,3: 18446744073709551612 18446744073709551613 18446744073709551614;4,2: 0 1;0,0:;4,3: 9223372036854775806 9223372036854775807 9223372036854775808;0,0:;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n5,5: 3 4 5 6 7;0,0:;0,0:;4,3: 18446744073709551612 18446744073709551613 18446744073709551614;4,2: 0 1;0,0:;4,3: 9223372036854775806 9223372036854775807 9223372036854775808;0,0:;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n5,5: 3 4 5 6 7;0,0:;0,0:;4,3: 9223372036854775804 9223372036854775805 9223372036854775806;4,2: -9223372036854775808 -9223372036854775807;0,0:;4,3: 4611686018427387902 4611686018427387903 4611686018427387904;4,4: -2 -1 0 1;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n5,5: 3 4 5 6 7;0,0:;0,0:;4,3: 9223372036854775804 9223372036854775805 9223372036854775806;4,2: -9223372036854775808 -9223372036854775807;0,0:;4,3: 4611686018427387902 4611686018427387903 4611686018427387904;4,4: -2 -1 0 1;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n5,5: 3 4 5 6 7;0,0:;0,0:;4,3: 4294967292 4294967293 4294967294;4,2: 0 1;0,0:;4,3: 2147483646 2147483647 2147483648;0,0:;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n5,5: 3 4 5 6 7;0,0:;0,0:;4,3: 2147483644 2147483645 2147483646;4,2: -2147483648 -2147483647;0,0:;4,3: 1073741822 1073741823 1073741824;4,4: -2 -1 0 1;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n5,5: 3 4 5 6 7;0,0:;0,0:;4,3: 65532 65533 65534;4,2: 0 1;0,0:;4,3: 32766 32767 32768;0,0:;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n5,5: 3 4 5 6 7;0,0:;0,0:;4,3: 32764 32765 32766;4,2: -32768 -32767;0,0:;4,3: 16382 16383 16384;4,4: -2 -1 0 1;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n8,5: 3 4 5 6 7;0,0:;0,0:;8,3: 252 253 254;8,2: 0 1;0,0:;8,3: 126 127 128;0,0:;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n8,5: 3 4 5 6 7;0,0:;0,0:;8,3: 124 125 126;8,2: -128 -127;0,0:;8,3: 62 63 64;8,4: -2 -1 0 1;10,8: 1 2 10 11 12 13 14 15;40,4: 7 10 11 12;\n";

#[derive(Debug, PartialEq, Eq)]
struct Ending {
    code: Option<i32>,
    signal: Option<i32>,
    stdout: String,
    stderr: String,
}

fn workdir() -> PathBuf {
    let dir = std::env::temp_dir().join(format!("tcg_vec_extend_capacity_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `program` with LLVM (`backend == None`) or the bridge and run it.
fn compile_and_run(
    dir: &Path,
    program: &Program,
    opt: u32,
    panic: &str,
    backend: Option<(&Path, &str)>,
) -> Result<Ending, String> {
    let side = if backend.is_some() { "tcg" } else { "llvm" };
    let stem = format!("{}_O{opt}_{panic}_{side}", program.name);
    let src = dir.join(format!("{stem}.rs"));
    std::fs::write(&src, program.src).expect("write source");
    let exe = dir.join(&stem);
    let mut cmd = toolchain_support::rustc_command_with_edition("2021");
    cmd.args([
        "--target",
        TARGET,
        "--crate-type",
        "bin",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Cpanic={panic}"))
    .arg(format!("-Copt-level={opt}"));
    if let Some((dylib, knobs)) = backend {
        let mut arg = std::ffi::OsString::from("-Zcodegen-backend=");
        arg.push(dylib);
        cmd.arg(arg).arg(knobs);
    }
    cmd.arg("-o").arg(&exe).arg(&src);
    let output = cmd.output().expect("spawn the compiler");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let run = Command::new(&exe).output().expect("run the program");
    Ok(Ending {
        code: run.status.code(),
        signal: run.status.signal(),
        stdout: String::from_utf8_lossy(&run.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&run.stderr).into_owned(),
    })
}

/// One cell: `Ok(refused?)` when it matches LLVM or (above -O1) refuses by
/// name, else `Err(why)`.
fn judge_cell(
    dir: &Path,
    program: &Program,
    opt: u32,
    panic: &str,
    backend: &Path,
    knobs: &str,
) -> Result<bool, String> {
    let cell = format!("{} -O{opt} -Cpanic={panic}", program.name);
    let oracle = compile_and_run(dir, program, opt, panic, None)
        .map_err(|stderr| format!("{cell}: LLVM failed to compile: {stderr}"))?;
    if (oracle.code, oracle.signal, oracle.stdout.as_str()) != (Some(0), None, program.stdout) {
        return Err(format!(
            "{cell}: the LLVM oracle is not the pinned run: {oracle:?}"
        ));
    }
    match compile_and_run(dir, program, opt, panic, Some((backend, knobs))) {
        Ok(bridge) if bridge == oracle => Ok(false),
        Ok(bridge) => Err(format!(
            "{cell}: compiled and DIVERGES -- LLVM {oracle:?}, trust-cg {bridge:?}"
        )),
        Err(stderr)
            if !MUST_MATCH.contains(&opt)
                && NAMED_REFUSALS.iter().any(|name| stderr.contains(name)) =>
        {
            Ok(true)
        }
        Err(stderr) => Err(format!("{cell}: refused: <<<{stderr}>>>")),
    }
}

#[test]
fn vec_extend_from_a_chain_leaves_stds_capacity_aarch64() {
    darwin_native::require("vec_extend_capacity_aarch64", &[]);
    let backend = backend_artifact_support::current_test_backend();
    // Built once on the test's own thread, so its knob trace lands in this
    // test's captured output.
    let knobs = toolchain_support::backend_knobs_arg(&["no-proof-certs"]);
    let dir = workdir();
    let cells: Vec<(&Program, u32, &str)> = PROGRAMS
        .iter()
        .flat_map(|p| {
            OPTS.iter()
                .flat_map(move |&o| PANICS.iter().map(move |&k| (p, o, k)))
        })
        .collect();
    let next = Mutex::new(0usize);
    let verdicts: Mutex<Vec<(usize, Result<bool, String>)>> = Mutex::new(Vec::new());
    std::thread::scope(|scope| {
        for _ in 0..4 {
            scope.spawn(|| {
                loop {
                    let index = {
                        let mut next = next.lock().unwrap();
                        let index = *next;
                        *next += 1;
                        index
                    };
                    let Some(&(program, opt, panic)) = cells.get(index) else {
                        break;
                    };
                    let verdict = judge_cell(&dir, program, opt, panic, &backend, &knobs);
                    verdicts.lock().unwrap().push((index, verdict));
                }
            });
        }
    });
    let _ = std::fs::remove_dir_all(&dir);
    let mut verdicts = verdicts.into_inner().unwrap();
    verdicts.sort_by_key(|(index, _)| *index);
    let (mut matched, mut refused, mut failures) = (0, 0, Vec::new());
    for (_, verdict) in verdicts {
        match verdict {
            Ok(true) => refused += 1,
            Ok(false) => matched += 1,
            Err(why) => failures.push(why),
        }
    }
    assert!(
        failures.is_empty(),
        "{} cell(s) failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    let must_match = PROGRAMS.len() * MUST_MATCH.len() * PANICS.len();
    // The -O0/-O1 cells are fixed; whether an -O2/-O3 cell matches or refuses
    // by name moves with the lane that owns std's extend bodies, so it is
    // reported apart.
    eprintln!(
        "VEC_EXTEND_CAPACITY programs={} cells={} must_match={must_match} opts=0,1,2,3 \
         strategies=abort,unwind",
        PROGRAMS.len(),
        cells.len()
    );
    eprintln!(
        "VEC_EXTEND_CAPACITY_O2_O3 matched={} refused_by_name={refused}",
        matched - must_match
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
