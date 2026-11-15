// [TCG-DEREF-BASE-ADDR] REGRESSION PIN — a NESTED AGGREGATE read out of a
// slice-tail DST's sized prefix (`let c = h.s.i;` on `h: &mut H<[u32]>`), next to
// the SCALAR prefix store (`h.s.x = 1`) the slice-assign lane made compile.
//
// # What this fixture is for
//
// `lower_memory_aggregate_use`'s nested-aggregate-field arm (`dst = move
// (src.field…)`, both sides memory-backed) walked the source projection over the
// source LOCAL's own type, from the source local's own slot. For a `Deref`-led
// source (`((*h).s.i)`) that is the REFERENCE's layout, not the pointee's: the
// walker skips the leading `Deref`, then asks the two-lane `&H<[u32]>` (or a thin
// `&T`, a `Primitive`) for a field, and the BACKEND PANICKED with
// `FieldsShape::offset: Primitive's have no fields`. Before the prefix store
// compiled, `f` was refused BY NAME (`memory slice assignment into projected
// place`); once it compiled, the read beside it reached this walk and crashed the
// compiler. Measured by the r20 fail-closed refuter on 931189533 + the
// slice-assign lane: 53 of 194 generated rows, this program among them, at
// `-Copt-level=0` and `-Copt-level=2`. The pure read `g` ICEs the same way.
// On `main` at ad7ee9c4e, with NO lane applied, this exact file already ICEs at
// `-Copt-level=0`, `2` and `3` (`slice_tail::force_slots` gives every slice-tail
// DST reference a slot, so the arm is reached without the prefix store), so on
// `main` the gate closes a pre-existing crash as well as the one the lane widened.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// Remove the no-`Deref` gate on that arm and the bridge compile of this program
// is a backend panic with no `[TCG-…]` diagnostic, which the harness counts as a
// HARD FAIL (`named_refusal` rejects a panic). With the gate, the `Deref`-led
// reads fall through to the paths that address the DATA lane, so the bridge must
// either MATCH LLVM or refuse by name — never crash, never diverge.
#![allow(dead_code)]

#[derive(Clone, Copy)]
enum E {
    A(u32),
    B,
}
#[derive(Clone, Copy)]
struct In {
    y: u16,
    e: E,
}
#[derive(Clone, Copy)]
struct S {
    x: u8,
    i: In,
}
struct H<T: ?Sized> {
    k: u16,
    s: S,
    tail: T,
}

#[derive(Clone, Copy)]
struct Wide {
    a: u32,
    w: i128,
}
#[derive(Clone, Copy)]
struct S2 {
    x: u8,
    i: Wide,
}
struct H2<T: ?Sized> {
    k: u16,
    s: S2,
    tail: T,
}

// The refuter's 10-line program: store into the prefix, then read a nested
// aggregate of the prefix whole.
#[inline(never)]
fn f(h: &mut H<[u32]>) -> u64 {
    h.s.x = 1;
    let c = h.s.i;
    match c.e {
        E::A(v) => v as u64,
        E::B => 9,
    }
}

// The same read with no store in the function (pre-existing ICE shape).
#[inline(never)]
fn g(h: &H<[u32]>) -> u64 {
    let c = h.s.i;
    match c.e {
        E::A(v) => v as u64,
        E::B => 9,
    }
}

// Depth 1: the whole prefix struct.
#[inline(never)]
fn d1(h: &mut H<[u32]>) -> u16 {
    h.s.x = 2;
    let c = h.s;
    c.i.y
}

// An over-aligned (i128) leaf inside the nested prefix aggregate.
#[inline(never)]
fn wide(h: &mut H2<[u32]>) -> u64 {
    h.s.x = 1;
    let v = h.s.i.w;
    v as u64
}

fn main() {
    let mut h: H<[u32; 2]> = H { k: 1, s: S { x: 0, i: In { y: 3, e: E::A(7) } }, tail: [4, 5] };
    let a = f(&mut h);
    let b = g(&h);
    let c = d1(&mut h);
    let x = h.s.x;
    let k = h.k;
    println!("f {} g {} d1 {} x {} k {}", a, b, c, x, k);
    let mut h2: H2<[u32; 1]> = H2 { k: 5, s: S2 { x: 0, i: Wide { a: 2, w: 3 } }, tail: [8] };
    let w = wide(&mut h2);
    let x2 = h2.s.x;
    println!("wide {} x {}", w, x2);
}
