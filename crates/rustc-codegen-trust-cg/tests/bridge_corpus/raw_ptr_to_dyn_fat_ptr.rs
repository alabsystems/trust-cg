// Corpus: a THIN raw pointer / `NonNull` whose POINTEE is ITSELF a `&dyn Trait`
// `{data, vtable}` fat pointer — the `core::ptr::NonNull<&dyn fmt::Debug>` /
// `*mut &dyn fmt::Debug` / `core::slice::iter::Iter<&dyn fmt::Debug>` shape.
//
// `&&dyn Trait` already typed its pointee as the real 16-byte two-lane image;
// the RAW-pointer arm of the type mapping never asked the same question, so
// `*const &dyn Trait` failed closed on `Ty::dyn …` where `&&dyn Trait` worked.
//
// What a regression would look like:
//   * a DROPPED vtable lane -> `first`/`second` dispatch the wrong impl (or the
//     same impl twice), so the printed values collapse;
//   * a stride taken from the trust-ir pointee type (8) rather than from
//     `layout_size_of` (16) -> `.add(1)` lands in the middle of element 0 and
//     `second` reads a torn fat pointer;
//   * a lane written at an assumed `+8` rather than at `fat_ptr_metadata_offset`
//     -> the mixed struct's later scalar fields shift (the `3b9b89a8` class).
#![allow(dead_code)]

use core::ptr::NonNull;

trait Shape {
    fn val(&self) -> i64;
}
struct Sq(i64);
struct Ci(i64);
impl Shape for Sq {
    fn val(&self) -> i64 {
        self.0 * self.0
    }
}
impl Shape for Ci {
    fn val(&self) -> i64 {
        self.0 * 3 + 1
    }
}

struct Pair<'a> {
    a: &'a dyn Shape,
    b: &'a dyn Shape,
}

#[inline(never)]
fn first(p: *const &dyn Shape) -> i64 {
    unsafe { (*p).val() }
}

#[inline(never)]
fn second(p: *const &dyn Shape) -> i64 {
    unsafe { (*p.add(1)).val() }
}

#[inline(never)]
fn nn_read(p: NonNull<&dyn Shape>) -> i64 {
    unsafe { p.as_ref().val() }
}

#[inline(never)]
fn nn_next(p: NonNull<&dyn Shape>) -> i64 {
    unsafe { p.add(1).as_ref().val() }
}

#[inline(never)]
fn nn_same(p: NonNull<&dyn Shape>, q: NonNull<&dyn Shape>) -> bool {
    p == q
}

#[inline(never)]
fn via_pair(p: &Pair<'_>) -> (i64, i64, i64, i64, bool, bool) {
    let raw = &p.a as *const &dyn Shape;
    let nn = NonNull::from_ref(&p.a);
    (
        first(raw),
        second(raw),
        nn_read(nn),
        nn_next(nn),
        nn_same(nn, nn),
        nn_same(nn, unsafe { nn.add(1) }),
    )
}

#[inline(never)]
fn sum_slice(xs: &[&dyn Shape]) -> i64 {
    let mut t = 0i64;
    let mut i = 0usize;
    while i < xs.len() {
        t = t * 10 + xs[i].val();
        i += 1;
    }
    t
}

#[inline(never)]
fn hint(xs: &[&dyn Shape]) -> usize {
    xs.iter().size_hint().0
}

// BOTH metadata kinds plus scalars on either side of each, read normally AND
// through a raw pointer to the `&dyn` field.
struct Mixed<'a> {
    tag: i64,
    d: &'a dyn Shape,
    mid: i64,
    s: &'a [i64],
    end: i64,
    txt: &'a str,
    last: i64,
}

#[inline(never)]
fn read_mixed(m: &Mixed<'_>) -> i64 {
    m.tag * 1000000
        + m.d.val() * 10000
        + m.mid * 1000
        + m.s.len() as i64 * 100
        + m.s[1] * 10
        + m.end
        + m.txt.len() as i64 * 100000
        + m.last
}

#[inline(never)]
fn mixed_via_raw(m: &Mixed<'_>) -> i64 {
    unsafe { (*(&m.d as *const &dyn Shape)).val() }
}

fn main() {
    let a = Sq(6);
    let b = Ci(9);
    let p = Pair { a: &a, b: &b };
    let (w, x, y, z, s1, s2) = via_pair(&p);
    println!("a {w} {x} {y} {z} {s1} {s2}");

    let arr: [&dyn Shape; 2] = [&a, &b];
    println!("b {} {}", sum_slice(&arr), hint(&arr));

    let c = Sq(7);
    let v = [11i64, 22, 33];
    let m = Mixed {
        tag: 3,
        d: &c,
        mid: 4,
        s: &v,
        end: 5,
        txt: "abcd",
        last: 6,
    };
    println!("c {} {}", read_mixed(&m), mixed_via_raw(&m));
}
