// Corpus: comparison operators on WIDE raw pointers.
//
// `==`, `!=`, `<`, `<=`, `>`, `>=` on `*const [T]` / `*const str` /
// `*const CStr` compare the `(data, metadata)` PAIRS,
// unsigned and data first; `std::ptr::eq` on wide pointers is `==` on them.
// The bridge's one-value type for such a pointer is its data half alone, so
// a comparison must read both lanes of each operand.
//
// WHAT EACH ROW WOULD CATCH. Every pair below shares its DATA address and
// differs only in metadata (or differs in data while the metadata says the
// opposite), so a comparison that reads the data half alone prints a
// different answer:
//  * `raw_ops`: all six operators on `*const [u32]` parameters;
//  * `ptr_eq_slice` / `ptr_eq_str`: `std::ptr::eq` on `&[T]` / `&str`
//    (inlined at -O2 into a reborrow comparison);
//  * `cstr_ops`: a slice-tail DST pointer (`*const CStr`);
//  * `nonnull_ops`: `NonNull<[u8]>`'s `PartialEq` / `Ord`;
//  * `field_ops`: operands read out of a by-value struct's fields;
//  * `literal_eq`: one operand is a `str` literal constant;
//  * `loop_count`: an operand carried around a loop, shrinking each turn;
//  * `addr_eq_ctl`: `std::ptr::addr_eq`, which ignores the metadata (a
//    control: it must say `true`).
#![allow(dead_code, ambiguous_wide_pointer_comparisons)]

use std::cmp::Ordering;
use std::ffi::CStr;
use std::hint::black_box as bb;
use std::ptr::NonNull;

#[inline(never)]
fn raw_ops(a: *const [u32], b: *const [u32]) -> [bool; 6] {
    [a == b, a != b, a < b, a <= b, a > b, a >= b]
}

#[inline(never)]
fn ptr_eq_slice(a: &[u32], b: &[u32]) -> bool {
    std::ptr::eq(a, b)
}

#[inline(never)]
fn ptr_eq_str(a: &str, b: &str) -> bool {
    std::ptr::eq(a, b)
}

#[inline(never)]
fn cstr_ops(a: *const CStr, b: *const CStr) -> (bool, bool) {
    (a == b, a < b)
}

#[inline(never)]
fn nonnull_ops(a: NonNull<[u8]>, b: NonNull<[u8]>) -> (bool, Ordering) {
    (a == b, a.cmp(&b))
}

struct Pair {
    a: *const [u8],
    b: *const [u8],
}

#[inline(never)]
fn field_ops(p: Pair) -> (bool, bool) {
    (p.a == p.b, p.a > p.b)
}

#[inline(never)]
fn literal_eq(p: *const str) -> bool {
    p == ("abc" as *const str)
}

#[inline(never)]
fn loop_count(s: &[u8], t: *const [u8]) -> usize {
    let mut n = 0;
    let mut cur: &[u8] = s;
    while !cur.is_empty() {
        if std::ptr::eq(cur, t) {
            n += 1;
        }
        cur = &cur[..cur.len() - 1];
    }
    n
}

#[inline(never)]
fn addr_eq_ctl(a: &[u32], b: &[u32]) -> bool {
    std::ptr::addr_eq(a, b)
}

fn bits<const N: usize>(flags: [bool; N]) -> u32 {
    let mut out = 0;
    for (i, f) in flags.iter().enumerate() {
        out |= (*f as u32) << i;
    }
    out
}

fn ord(o: Ordering) -> i32 {
    o as i32
}

fn main() {
    let v = bb([1u32, 2, 3]);
    // Every printed value is bound to a local first: the whole-program bridge
    // formats only call-stable places.
    let r0 = bits(raw_ops(&v[..1], &v[..2]));
    let r1 = bits(raw_ops(&v[..2], &v[..1]));
    let r2 = bits(raw_ops(&v[1..], &v[..3]));
    let r3 = bits(raw_ops(&v[..2], &v[..2]));
    println!("raw_ops {} {} {} {}", r0, r1, r2, r3);
    let p0 = ptr_eq_slice(&v[..1], &v[..2]) as u8;
    let p1 = ptr_eq_slice(&v[..2], &v[..2]) as u8;
    println!("ptr_eq_slice {} {}", p0, p1);
    let s: &str = bb("abc");
    let q0 = ptr_eq_str(&s[..1], &s[..2]) as u8;
    let q1 = ptr_eq_str(&s[..2], &s[..2]) as u8;
    println!("ptr_eq_str {} {}", q0, q1);
    let bytes = bb(*b"abc\0\0");
    let c4: *const CStr = std::ptr::slice_from_raw_parts(bytes.as_ptr(), 4) as *const CStr;
    let c5: *const CStr = std::ptr::slice_from_raw_parts(bytes.as_ptr(), 5) as *const CStr;
    let (e45, l45) = cstr_ops(c4, c5);
    let (e54, l54) = cstr_ops(c5, c4);
    let (e45, l45, e54, l54) = (e45 as u8, l45 as u8, e54 as u8, l54 as u8);
    println!("cstr_ops {} {} {} {}", e45, l45, e54, l54);
    let mut w = bb([1u8, 2, 3]);
    let n1 = NonNull::from(&mut w[..1]);
    let n2 = NonNull::from(&mut w[..2]);
    let (e12, o12) = nonnull_ops(n1, n2);
    let (e21, o21) = nonnull_ops(n2, n1);
    let (e12, o12, e21, o21) = (e12 as u8, ord(o12), e21 as u8, ord(o21));
    println!("nonnull_ops {} {} {} {}", e12, o12, e21, o21);
    let b = bb([7u8, 8, 9]);
    let (fe1, fg1) = field_ops(Pair {
        a: &b[..1],
        b: &b[..2],
    });
    let (fe2, fg2) = field_ops(Pair {
        a: &b[..2],
        b: &b[..1],
    });
    let (fe1, fg1, fe2, fg2) = (fe1 as u8, fg1 as u8, fe2 as u8, fg2 as u8);
    println!("field_ops {} {} {} {}", fe1, fg1, fe2, fg2);
    // A stack copy never shares the literal's address (literal identity itself
    // is unspecified, so it is not compared).
    let stack = bb(*b"abc");
    let on_stack: &str = unsafe { std::str::from_utf8_unchecked(&stack) };
    let le = literal_eq(on_stack) as u8;
    println!("literal_eq {}", le);
    let l = bb([1u8, 2, 3, 4]);
    let (lc0, lc1) = (loop_count(&l, &l[..2]), loop_count(&l, &l[1..3]));
    println!("loop_count {} {}", lc0, lc1);
    let ae = addr_eq_ctl(&v[..1], &v[..2]) as u8;
    println!("addr_eq_ctl {}", ae);
}
