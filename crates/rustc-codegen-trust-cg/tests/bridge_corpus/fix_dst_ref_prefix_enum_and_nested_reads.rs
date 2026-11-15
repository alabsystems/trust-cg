// [TCG-DEREF-BASE-ADDR] REGRESSION PIN — the OTHER readers of a slice-tail DST's
// sized prefix: a DISCRIMINANT, an enum PAYLOAD after a prefix store, and a
// whole prefix aggregate read into a SCALARIZED temp.
//
// # What this fixture is for
//
// A slot-backed `h: &H<[u8]>` keeps `{ data, len }` in a 16-byte slot. Several
// memory-slot readers walked a `Deref`-led place `(*h).f…` from that SLOT over
// `h`'s OWN type, so the first `Field` was folded over the REFERENCE's
// `ScalarPair` (field 0 = the data word, field 1 = the LENGTH) instead of the
// pointee. `memory_place_walk_base` already knew this for the scalar paths; these
// did not ask it. Measured at the unpatched lane tip, both opt levels, every one
// a silent wrong answer:
//
//   * `disc`  (`lower_memory_projected_discriminant`): `disc 0 0` for `55 1009`;
//   * `wrap`  (`lower_memory_nested_aggregate_field_use`): `nested 3 <data ptr> 4`
//     for `nested 3 31 41` — `b` is the tail LENGTH;
//   * `bump_and_read`: `disc_store 0 100` for `155 100` — this one was REFUSED on
//     the tip and became a wrong answer the moment the prefix store `h.r.hi = v`
//     compiled, which is the shape that refuted slice-assign v2.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// Revert either reader to `(memory_slot_ptr(local), local_rust_ty(local))` and
// the bridge compiles this and prints the garbage above; the harness's
// `assert_eq!(bridge.stdout, oracle.stdout)` fails with "STDOUT differs from
// LLVM". With the fix every row COMPILES and MATCHES at both opt levels.
#![allow(dead_code)]

#[derive(Clone, Copy)]
enum E {
    A(u64),
    B,
    C(u32),
}
struct H<T: ?Sized> {
    n: u64,
    e: E,
    tail: T,
}

#[inline(never)]
fn disc(h: &H<[u8]>) -> u64 {
    match h.e {
        E::A(x) => x,
        E::B => 7,
        E::C(y) => y as u64 + 1000,
    }
}

struct R {
    lo: u64,
    hi: u64,
}
struct G<T: ?Sized> {
    r: R,
    e: E,
    tail: T,
}

#[inline(never)]
fn bump_and_read(h: &mut G<[u8]>, v: u64) -> u64 {
    h.r.hi = v;
    match h.e {
        E::A(x) => x + h.r.hi,
        E::B => 7,
        E::C(y) => y as u64 + 1000,
    }
}

#[derive(Clone, Copy)]
struct Inner {
    a: u64,
    b: u64,
}
struct Outer {
    x: u8,
    inner: Inner,
}
struct W<T: ?Sized> {
    i: Inner,
    tail: T,
}

#[inline(never)]
fn wrap(h: &W<[u16]>) -> Outer {
    Outer { x: 3, inner: h.i }
}

fn main() {
    let o: H<[u8; 3]> = H {
        n: 1,
        e: E::A(55),
        tail: [1, 2, 3],
    };
    let p: H<[u8; 3]> = H {
        n: 1,
        e: E::C(9),
        tail: [1, 2, 3],
    };
    let a = disc(&o);
    let b = disc(&p);
    println!("disc {} {}", a, b);

    let mut g: G<[u8; 3]> = G {
        r: R { lo: 1, hi: 2 },
        e: E::A(55),
        tail: [1, 2, 3],
    };
    let s = bump_and_read(&mut g, 100);
    let hi = g.r.hi;
    println!("disc_store {} {}", s, hi);

    let w: W<[u16; 4]> = W {
        i: Inner { a: 31, b: 41 },
        tail: [5; 4],
    };
    let out = wrap(&w);
    let (x, ia, ib) = (out.x, out.inner.a, out.inner.b);
    println!("nested {} {} {}", x, ia, ib);
}
