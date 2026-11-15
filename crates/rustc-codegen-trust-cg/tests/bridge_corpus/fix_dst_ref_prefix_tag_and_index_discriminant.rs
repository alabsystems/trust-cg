// [TCG-DEREF-BASE-ADDR] REGRESSION PIN — the two discriminant arms the sibling
// fixture `fix_dst_ref_prefix_enum_and_nested_reads` does not reach: a TAG-ONLY
// enum (`enum K { X, Y, Z }`, modelled as its bare tag) and a RUNTIME-INDEXED
// enum element (`h.arr[k]`), both in the sized prefix of a slice-tail DST behind
// `h: &H<[u8]>`.
//
// # What this fixture is for
//
// Measured at the unpatched lane tip, both opt levels, this program PANICS the
// backend (`index out of bounds: the len is 2 but the index is 2`): `pick`'s
// runtime-index discriminant walked `(*h).arr[k]` from `h`'s own SLOT over the
// REFERENCE's two-field `ScalarPair` layout, and `Field(2)` does not exist
// there. Taken one function at a time:
//
//   * `tag` alone printed `tag 30 30 30` where LLVM prints `tag 30 20 10` — a
//     SILENT wrong answer: `lower_reference_deref_discriminant`'s tag-only arm
//     loaded the tag through `h`'s one bound value (its lane tuple);
//   * `bump_tag` alone was REFUSED on the tip, and slice-assign v2 turned it
//     into `tagstore 0` for `tagstore 130` the moment its `h.r.hi = v` store
//     compiled;
//   * `pick` now COMPILES — a new capability, and this row is what says it is a
//     correct one.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// Remove the base-address guard from `lower_reference_deref_discriminant` and
// the bridge prints `tag 0 0 0 | idx 7 33 1004 | tagstore 0` (measured at
// `-Copt-level=0`); the harness's `assert_eq!(bridge.stdout, oracle.stdout)`
// fails with "STDOUT differs from LLVM". Walk
// `lower_memory_projected_discriminant` over the local's own type again and the
// backend panics as above, which `named_refusal` rejects as a crash. (With the
// fix the `-O0` row COMPILES and MATCHES; the `-O2` row is an INCOMPLETE on the
// host-wide `[TCG-PROOF-465]` gap in `main`.)
#![allow(dead_code)]

#[derive(Clone, Copy)]
enum K {
    X,
    Y,
    Z,
}
#[derive(Clone, Copy)]
enum E {
    A(u64),
    B,
    C(u32),
}
struct H<T: ?Sized> {
    n: u64,
    k: K,
    arr: [E; 3],
    tail: T,
}
struct R {
    lo: u64,
    hi: u64,
}
struct G<T: ?Sized> {
    r: R,
    k: K,
    tail: T,
}

#[inline(never)]
fn tag(h: &H<[u8]>) -> u32 {
    match h.k {
        K::X => 10,
        K::Y => 20,
        K::Z => 30,
    }
}
#[inline(never)]
fn pick(h: &H<[u8]>, k: usize) -> u64 {
    match h.arr[k] {
        E::A(x) => x,
        E::B => 7,
        E::C(y) => y as u64 + 1000,
    }
}
#[inline(never)]
fn bump_tag(h: &mut G<[u8]>, v: u64) -> u64 {
    h.r.hi = v;
    match h.k {
        K::X => 10 + h.r.hi,
        K::Y => 20 + h.r.hi,
        K::Z => 30 + h.r.hi,
    }
}

fn main() {
    let o: H<[u8; 2]> = H {
        n: 5,
        k: K::Z,
        arr: [E::B, E::A(33), E::C(4)],
        tail: [1, 2],
    };
    let p: H<[u8; 2]> = H {
        n: 5,
        k: K::Y,
        arr: [E::B, E::B, E::B],
        tail: [1, 2],
    };
    let q: H<[u8; 2]> = H {
        n: 5,
        k: K::X,
        arr: [E::B, E::B, E::B],
        tail: [1, 2],
    };
    let a = tag(&o);
    let b = tag(&p);
    let c = tag(&q);
    println!("tag {} {} {}", a, b, c);
    let x = pick(&o, 0);
    let y = pick(&o, 1);
    let z = pick(&o, 2);
    println!("idx {} {} {}", x, y, z);
    let mut g: G<[u8; 2]> = G {
        r: R { lo: 1, hi: 2 },
        k: K::Z,
        tail: [1, 2],
    };
    let t = bump_tag(&mut g, 100);
    println!("tagstore {}", t);
}
