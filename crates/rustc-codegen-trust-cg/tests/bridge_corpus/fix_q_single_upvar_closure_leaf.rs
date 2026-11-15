// A SINGLE-UPVAR closure is its upvar, and must MAP like one.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// UNPATCHED `from_fn` below fails closed with
//   "memory leaf type is not a scalar: Tuple([Ref(I32)])"
// On `library/core` this is exactly three roots, all
// `fmt::builders::from_fn::<closure>` instantiations.
//
// The type mapper treats a closure as an anonymous struct of its upvars, but the
// STRUCT arm collapses a single-scalar-leaf aggregate to that leaf while the
// CLOSURE arm always built a tuple. The asymmetry is observable: `FromFn<F>`
// (a newtype over the closure) maps to the upvar's scalar — the struct arm
// flattens straight through the closure — while the closure itself maps to
// `Tuple([<that same scalar>])`, which is not a memory scalar, so every
// place-address walk bottoming out at the closure field failed closed.
//
// A wrong answer here is SILENT: the closure's captured value is read from a
// slot, so a wrong leaf type or offset yields a well-typed wrong number. Every
// row prints a RUNTIME VALUE that depends on the CAPTURE, and the two-upvar rows
// are the CONTROL for the scope of the collapse — they keep the tuple mapping
// and must keep working unchanged.

struct FromFn<F>(F);

#[inline(never)]
fn from_fn<F: Fn(u32) -> u32>(f: F) -> FromFn<F> {
    FromFn(f)
}

#[inline(never)]
fn apply<F: Fn(u32) -> u32>(w: &FromFn<F>, v: u32) -> u32 {
    (w.0)(v)
}

// ONE upvar, captured BY REFERENCE (`&i32`) — the exact `library/core` shape.
#[inline(never)]
fn by_ref_capture(x: &i32, v: u32) -> u32 {
    let w = from_fn(|y| y + (*x as u32));
    apply(&w, v)
}

// ONE upvar, captured BY VALUE (a `u64` scalar), so the collapsed leaf is an
// integer rather than a pointer.
#[inline(never)]
fn by_value_capture(x: u64, v: u32) -> u32 {
    let w = from_fn(move |y| y.wrapping_add(x as u32));
    apply(&w, v)
}

// CONTROL: TWO upvars. The collapse must NOT apply — the closure keeps its tuple
// mapping and its `(*env).N` index scheme, and this row must keep working.
#[inline(never)]
fn two_upvar_capture(x: u32, z: u32, v: u32) -> u32 {
    let w = from_fn(move |y| y.wrapping_mul(x).wrapping_add(z));
    apply(&w, v)
}

fn main() {
    let x: i32 = 5;
    println!("{}", by_ref_capture(&x, std::hint::black_box(7)));
    println!("{}", by_value_capture(std::hint::black_box(1000), std::hint::black_box(7)));
    println!(
        "{}",
        two_upvar_capture(std::hint::black_box(3), std::hint::black_box(4), std::hint::black_box(7))
    );
}
