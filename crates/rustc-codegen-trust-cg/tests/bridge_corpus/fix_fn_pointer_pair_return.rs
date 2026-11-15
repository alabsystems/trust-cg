// The `lower_indirect_call_terminator` SIBLING of the virtual-call defect: an
// INDIRECT call through a `fn(..)` POINTER whose return is a by-value aggregate
// bound into a memory-backed destination.
//
// `fn f(g: fn() -> (i64, i64)) -> i64 { let (a, b) = g(); a + b }` is the exact
// reproducer the diagnosis used; that lane's own refusal text named the fix
// ("extend `lower_indirect_call_terminator` with the direct path's
// aggregate-return destination handling"). A `-> &'static str` fn pointer is the
// fat-pointer twin of the same shape.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

fn origin() -> (i64, i64) {
    (11, 31)
}

fn shifted() -> (i64, i64) {
    (-5, 400)
}

fn short_name() -> &'static str {
    "ab"
}

fn long_name() -> &'static str {
    "a-considerably-longer-name"
}

// The diagnosis's exact program.
#[inline(never)]
fn sum_through(g: fn() -> (i64, i64)) -> i64 {
    let (a, b) = g();
    a + b
}

// The destination read back field-wise rather than destructured.
#[inline(never)]
fn fields_through(g: fn() -> (i64, i64)) -> i64 {
    let t = g();
    t.0 * 1000 + t.1
}

#[inline(never)]
fn name_through(g: fn() -> &'static str) -> (usize, u8) {
    let s = g();
    let mut cs = 0u8;
    for b in s.as_bytes() {
        cs = cs.wrapping_add(*b);
    }
    (s.len(), cs)
}

fn main() {
    println!("{}", sum_through(origin));
    println!("{}", sum_through(shifted));
    println!("{}", fields_through(origin));
    println!("{}", fields_through(shifted));

    let (l0, c0) = name_through(short_name);
    let (l1, c1) = name_through(long_name);
    println!("{l0} {c0} {l1} {c1}");

    // A fn pointer selected at RUNTIME, so no constant folding can turn the
    // indirect call back into a direct one. (An array of fn pointers would be a
    // cleaner selector but stops at an unrelated pre-existing gate — "memory
    // aggregate whole assignment from non-memory source" — which would mask the
    // one this fixture exercises.)
    let mut acc = 0i64;
    let mut i = 0i64;
    while i < 4 {
        let g: fn() -> (i64, i64) = if i % 2 == 0 { origin } else { shifted };
        let (a, b) = g();
        acc = acc.wrapping_add(a * (i + 1)).wrapping_add(b);
        i += 1;
    }
    println!("{acc}");
}
