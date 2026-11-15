// A reference-RETURNING callee handed a `&mut` of a NON-PRIMITIVE scalar local.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Without a real address for the referent, `&mut t` reaches the callee as a
// materialized TEMP that the caller reloads after the call — so the `&mut` the
// callee hands back addresses a DEAD temp and `*r = ..` is silently dropped.
// `direct_scalar_ref_select_return` refused that shape by name ("promoted
// mutable scalar reference return is unsupported", 6 `library/core` roots; the
// shared-aggregate twin another 2). The cure is the ADDRESS, not a narrower
// guard: `compute_scalar_cell_locals`' reference-escaping pass now cells every
// referent the memory model can represent, not only `Int/Uint/Float/Bool/Char`.
//
// A guard-only "fix" compiles this and prints the STALE value (7-ish, not 99).
struct Cur(u32);

#[inline(never)]
fn id(c: &mut Cur) -> &mut Cur {
    c
}

#[inline(never)]
fn value(c: Cur) -> u32 {
    c.0
}

fn main() {
    let mut t = Cur(std::hint::black_box(7u32));
    let r = id(&mut t);
    *r = Cur(99);
    println!("{}", value(t));
}
