// `?` on a `ControlFlow` — the THIRD std `Try` type's `from_residual`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// UNPATCHED this fails closed with
//   "from_residual for an unmodeled Try type std::ops::ControlFlow
//    (only Result/Option are lowered)"
// on every `run_*` below — measured on `library/core` as 3 roots, all of them
// `Iterator::try_fold` / `try_rfold` monomorphizations whose accumulator type is
// a `ControlFlow`.
//
// `ControlFlow`'s `FromResidual` is the IDENTITY (`Break(b) => Break(b)`, no
// `From` conversion anywhere), so the lowering is "write the `Break` tag, copy
// the `Break` payload". A wrong answer here is SILENT — a mis-copied payload or
// a mis-written tag both produce a well-typed `ControlFlow` with the wrong
// contents — so every row below prints a RUNTIME VALUE, and the three payload
// shapes are covered separately:
//
//   * a scalar `Break` payload   (memory-backed enum slot, Direct tag)
//   * a ZST `Break` payload      (TAG-ONLY enum: the whole value IS its tag)
//   * an aggregate `Break` payload (multi-leaf byte copy at the variant offset)
//
// plus the CONTINUE path in each, which must NOT take the `from_residual` arm at
// all — a fix that wrote `Break` unconditionally would still print a plausible
// number for the break cases and is caught only by the continue cases.

use std::ops::ControlFlow;

#[inline(never)]
fn step_scalar(x: i64) -> ControlFlow<i64, i64> {
    if x > 10 { ControlFlow::Break(x * 2) } else { ControlFlow::Continue(x + 1) }
}

#[inline(never)]
fn run_scalar(start: i64) -> ControlFlow<i64, i64> {
    let a = step_scalar(start)?;
    let b = step_scalar(a)?;
    ControlFlow::Continue(b + 100)
}

#[inline(never)]
fn step_unit(x: i64) -> ControlFlow<(), ()> {
    if x > 10 { ControlFlow::Break(()) } else { ControlFlow::Continue(()) }
}

#[inline(never)]
fn run_unit(start: i64) -> ControlFlow<(), i64> {
    step_unit(start)?;
    step_unit(start + 1)?;
    ControlFlow::Continue(start * 7)
}

#[derive(Clone, Copy)]
struct Pair {
    lo: u32,
    hi: u32,
}

#[inline(never)]
fn step_pair(x: u32) -> ControlFlow<Pair, u32> {
    if x > 10 {
        ControlFlow::Break(Pair { lo: x, hi: x.wrapping_mul(1000) })
    } else {
        ControlFlow::Continue(x + 1)
    }
}

#[inline(never)]
fn run_pair(start: u32) -> ControlFlow<Pair, u32> {
    let a = step_pair(start)?;
    let b = step_pair(a)?;
    ControlFlow::Continue(b + 5)
}

#[inline(never)]
fn code_scalar(start: i64) -> i64 {
    match run_scalar(start) {
        ControlFlow::Continue(c) => c,
        ControlFlow::Break(b) => -1000 - b,
    }
}

#[inline(never)]
fn code_unit(start: i64) -> i64 {
    match run_unit(start) {
        ControlFlow::Continue(c) => c,
        ControlFlow::Break(()) => -9999,
    }
}

#[inline(never)]
fn pair_lo(start: u32) -> u32 {
    match run_pair(start) {
        ControlFlow::Continue(c) => c,
        ControlFlow::Break(p) => p.lo,
    }
}

#[inline(never)]
fn pair_hi(start: u32) -> u32 {
    match run_pair(start) {
        ControlFlow::Continue(_) => 0,
        ControlFlow::Break(p) => p.hi,
    }
}

fn main() {
    // Each outcome is folded to ONE integer and printed with a single-argument
    // `println!`: a multi-argument `format!` and a `for` over an array literal
    // are separate (unrelated) bridge gates, and a fixture must fail for its OWN
    // reason or it proves nothing. Encoding: Continue(c) -> c, Break(b) ->
    // -1000 - b; the aggregate payload's two u32 leaves are printed separately so
    // a half-copied `Pair` cannot hide behind a fold.
    println!("{}", code_scalar(std::hint::black_box(1)));
    println!("{}", code_scalar(std::hint::black_box(11)));
    println!("{}", code_scalar(std::hint::black_box(10)));
    println!("{}", code_unit(std::hint::black_box(1)));
    println!("{}", code_unit(std::hint::black_box(11)));
    println!("{}", code_unit(std::hint::black_box(10)));
    println!("{}", pair_lo(std::hint::black_box(1)));
    println!("{}", pair_hi(std::hint::black_box(1)));
    println!("{}", pair_lo(std::hint::black_box(11)));
    println!("{}", pair_hi(std::hint::black_box(11)));
    println!("{}", pair_lo(std::hint::black_box(10)));
    println!("{}", pair_hi(std::hint::black_box(10)));
}
