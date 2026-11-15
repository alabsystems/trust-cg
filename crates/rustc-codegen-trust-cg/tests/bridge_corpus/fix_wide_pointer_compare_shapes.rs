// Corpus: comparison operators on WIDE raw pointers whose operands reach the
// comparison through the program shapes other than a plain parameter. The
// operators and the parameter, field, literal and `NonNull` operands are
// `fix_wide_pointer_compare.rs`.
//
// Each comparison reads both lanes, `(data, length)`, of each operand, however
// the operand was produced: a derived impl's `&self` field, an `Option`
// payload, a generic `*const T` instantiated with an unsized `T`, a local
// written through `&mut`, a value carried around a loop, a tuple / enum / array
// element, a `match` join, the `Ord` methods of a raw pointer, a local a
// closure captures by `&mut` and by `&`, and a `Cell`'s value.
//
// WHAT EACH ROW WOULD CATCH. Every pair shares its DATA address and differs only
// in length (or the order of the lengths decides the answer), so a comparison
// that reads the data half alone prints a different number.
#![allow(dead_code, ambiguous_wide_pointer_comparisons)]

use std::cell::Cell;
use std::hint::black_box as bb;

#[derive(PartialEq, PartialOrd, Clone, Copy)]
struct D {
    p: *const [u8],
}

#[inline(never)]
fn derive_ops(x: &D, y: &D) -> [bool; 3] {
    [x == y, x < y, x != y]
}

#[inline(never)]
fn option_eq(a: Option<*const [u8]>, b: Option<*const [u8]>) -> bool {
    a == b
}

#[inline(never)]
fn generic_ops<T: ?Sized>(a: *const T, b: *const T) -> [bool; 2] {
    [a == b, a > b]
}

#[inline(never)]
fn set(r: &mut *const [u8], v: *const [u8]) {
    *r = v;
}

#[inline(never)]
fn written_through_mut(a: *const [u8], b: *const [u8], c: *const [u8]) -> [bool; 2] {
    let mut p = a;
    set(&mut p, b);
    [p == c, p != a]
}

#[inline(never)]
fn loop_carried(s: &[u8], t: *const [u8]) -> usize {
    let mut p: *const [u8] = s;
    let mut n = 0;
    for i in 0..s.len() {
        if p == t {
            n += 1 + i * 10;
        }
        p = &s[..s.len() - 1 - i];
    }
    n
}

enum E {
    A(*const [u8]),
    B(u32),
}

#[inline(never)]
fn element_ops(t: &(*const [u8], *const [u8]), e: &E, a: [*const [u8]; 3], i: usize) -> [bool; 3] {
    let from_enum = match e {
        E::A(p) => *p == t.1,
        E::B(_) => false,
    };
    [t.0 == t.1, from_enum, a[i] == a[2]]
}

#[inline(never)]
fn joined(k: u8, a: &str, b: &str) -> bool {
    let p: *const str = match k {
        0 => a,
        1 => &a[..1],
        _ => b,
    };
    p <= b
}

#[inline(never)]
fn ord_methods(a: *const [u8], b: *const [u8]) -> (i8, usize) {
    (a.cmp(&b) as i8, std::cmp::max(a, b).len())
}

#[inline(never)]
fn closure_captured(a: *const [u8], b: *const [u8], c: *const [u8]) -> [bool; 4] {
    let mut p = a;
    let mut set = |v: *const [u8]| p = v;
    set(b);
    let cmp = || p < c;
    [p == c, p == b, p != a, cmp()]
}

#[inline(never)]
fn cell_value(x: &Cell<*const [u8]>, b: *const [u8], c: *const [u8]) -> [bool; 2] {
    let before = x.get() == c;
    x.set(b);
    [before, x.get() == c]
}

fn bits<const N: usize>(flags: [bool; N]) -> u32 {
    let mut out = 0;
    for (i, f) in flags.iter().enumerate() {
        out |= (*f as u32) << i;
    }
    out
}

fn main() {
    let v = bb([1u8, 2, 3, 4]);
    let one: *const [u8] = &v[..1];
    let two: *const [u8] = &v[..2];
    let three: *const [u8] = &v[..3];
    // Every printed value is bound to a local first: the whole-program bridge
    // formats only call-stable places.
    let d0 = bits(derive_ops(&D { p: one }, &D { p: two }));
    let d1 = bits(derive_ops(&D { p: two }, &D { p: two }));
    println!("derive_ops {} {}", d0, d1);
    let o0 = option_eq(bb(Some(one)), bb(Some(two))) as u8;
    let o1 = option_eq(bb(Some(two)), bb(Some(two))) as u8;
    let o2 = option_eq(bb(None), bb(Some(two))) as u8;
    println!("option_eq {} {} {}", o0, o1, o2);
    let s = bb("abc");
    let g0 = bits(generic_ops::<[u8]>(bb(one), bb(two)));
    let g1 = bits(generic_ops::<[u8]>(bb(two), bb(one)));
    let g2 = bits(generic_ops::<str>(bb(&s[..2]), bb(&s[..1])));
    let g3 = bits(generic_ops::<u8>(bb(&v[0]), bb(&v[1])));
    println!("generic_ops {} {} {} {}", g0, g1, g2, g3);
    let w0 = bits(written_through_mut(bb(one), bb(two), bb(three)));
    let w1 = bits(written_through_mut(bb(one), bb(two), bb(two)));
    let w2 = bits(written_through_mut(bb(one), bb(one), bb(three)));
    println!("written_through_mut {} {} {}", w0, w1, w2);
    let l0 = loop_carried(bb(&v), bb(two));
    let l1 = loop_carried(bb(&v), bb(&v[1..3]));
    println!("loop_carried {} {}", l0, l1);
    let e0 = bits(element_ops(&(one, two), &E::A(one), [one, two, two], bb(0)));
    let e1 = bits(element_ops(&(two, two), &E::A(two), [one, two, two], bb(1)));
    let e2 = bits(element_ops(&(one, two), &E::B(7), [two, one, one], bb(1)));
    println!("element_ops {} {} {}", e0, e1, e2);
    let j0 = joined(bb(0), s, &s[..2]) as u8;
    let j1 = joined(bb(1), s, &s[..2]) as u8;
    let j2 = joined(bb(2), s, &s[..2]) as u8;
    println!("joined {} {} {}", j0, j1, j2);
    let (c0, m0) = ord_methods(bb(one), bb(two));
    let (c1, m1) = ord_methods(bb(two), bb(one));
    let (c2, m2) = ord_methods(bb(two), bb(two));
    println!("ord_methods {} {} {} {} {} {}", c0, m0, c1, m1, c2, m2);
    let k0 = bits(closure_captured(bb(one), bb(two), bb(three)));
    let k1 = bits(closure_captured(bb(one), bb(one), bb(one)));
    println!("closure_captured {} {}", k0, k1);
    let x = Cell::new(one);
    let x0 = bits(cell_value(&x, bb(two), bb(three)));
    let y = Cell::new(three);
    let y0 = bits(cell_value(&y, bb(two), bb(two)));
    println!("cell_value {} {}", x0, y0);
}
