// [TCG-DEREF-BASE-ADDR] REGRESSION PIN — a WHOLE-AGGREGATE READ of a sized prefix
// through a slice-tail DST reference, next to the scalar prefix STORE the
// slice-assign lane admits.
//
// # What this fixture is for
//
// `lower_memory_aggregate_use`'s whole-aggregate deref-READ arm addresses the
// source through `value_for_scalar_binding(r)` — `r`'s ONE bound value. It used
// to decide whether that value is the pointee's address by ENUMERATING the two
// builtin fat forms (`!is_slice_or_str_fat_ptr_ty && !is_trait_object_reference_
// ty`), which calls `&H<[u32]>` — a reference to a struct whose last field is a
// `[u32]` TAIL — "not fat". That reference's value is its `{ data, len }` lane
// tuple, not the pointee, so `get_i` read 24 bytes of unrelated stack.
//
// `get_i` beside `set_a` is VERBATIM the witness that refuted slice-assign v2:
// v2 made the `set_a` store compile (correctly, through the DATA lane) and left
// this read arm on the enumeration, so a program that used to be refused became
// a silent wrong answer. `bump` is the `str`-tailed twin.
//
// # HOW THIS FAILS IF THE FIX IS REVERTED
//
// Put the enumeration back at that arm (`if !is_slice_or_str_fat_ptr_ty(ref_ty)
// && !is_trait_object_reference_ty(ref_ty)`) and the bridge COMPILES this and
// prints `get_i <stack address> 3 <garbage>` where LLVM prints `get_i 4242 2 3`
// (measured at `-Copt-level=0`, 2026-09-27); the harness's
// `assert_eq!(bridge.stdout, oracle.stdout)` fails with "STDOUT differs from
// LLVM". With the fix the read falls through to the whole-assignment path, which
// addresses a slot-backed DST reference from its DATA lane
// (`memory_place_walk_base`), and the row COMPILES and MATCHES.
#![allow(dead_code)]

#[derive(Clone, Copy)]
struct Inner {
    a: u64,
    b: u64,
    c: u32,
}
struct H<T: ?Sized> {
    i: Inner,
    tail: T,
}

#[inline(never)]
fn get_i(h: &H<[u32]>) -> Inner {
    h.i
}
#[inline(never)]
fn set_a(h: &mut H<[u32]>, v: u64) {
    h.i.a = v;
}

#[derive(Clone, Copy)]
struct Pair {
    a: u64,
    b: u64,
}
struct S<T: ?Sized> {
    p: Pair,
    n: u32,
    tail: T,
}

// Scalar prefix STORE then whole-prefix READ through ONE `str`-tailed reference.
#[inline(never)]
fn bump(h: &mut S<str>, v: u64) -> Pair {
    h.p.b = v;
    h.p
}

fn main() {
    let mut o: H<[u32; 3]> = H {
        i: Inner { a: 1, b: 2, c: 3 },
        tail: [7, 8, 9],
    };
    let r: &mut H<[u32]> = &mut o;
    set_a(r, 4242);
    let g = get_i(r);
    let (a, b, c) = (g.a, g.b, g.c);
    println!("get_i {} {} {}", a, b, c);

    let mut s: S<[u8; 3]> = S {
        p: Pair { a: 11, b: 12 },
        n: 3,
        tail: *b"abc",
    };
    let raw: *mut S<[u8]> = &mut s;
    let q: &mut S<str> = unsafe { &mut *(raw as *mut S<str>) };
    let p = bump(q, 99);
    let (pa, pb, n) = (p.a, p.b, s.n);
    println!("str {} {} {}", pa, pb, n);
}
