// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
#[derive(Clone, Copy, PartialEq, Debug)]
struct Name(u32);
struct Holder<'a> {
    a: &'a Name,
    b: &'a u64,
    k: u8,
}
#[inline(never)]
fn sum(h: &Holder) -> u64 {
    h.a.0 as u64 * 10 + *h.b + h.k as u64
}
#[inline(never)]
fn first(all: &[&Name], n: Name) -> usize {
    let mut i = 0;
    while i < all.len() {
        if *all[i] == n {
            return i;
        }
        i += 1;
    }
    99
}
#[inline(never)]
fn tup(t: (&u32, &bool, u8)) -> u32 {
    *t.0 + *t.1 as u32 * 100 + t.2 as u32
}
#[inline(never)]
fn root(a: u32, b: u32, c: u32) -> usize {
    let x = Name(a);
    let y = Name(b);
    let one = [&x];
    let two = [&x, &y];
    let all: &[&Name] = if c >= 2 { &two } else { &one };
    first(all, Name(b))
}
#[inline(never)]
fn mutate(a: u32) -> u32 {
    let mut x = a;
    let mut y = a + 1;
    {
        let arr = [&mut x, &mut y];
        for r in arr {
            *r *= 3;
        }
    }
    x * 10 + y
}
#[inline(never)]
fn addr_eq(a: u32) -> bool {
    let x = a;
    let arr = [&x, &x];
    std::ptr::eq(arr[0], arr[1]) && std::ptr::eq(arr[0], &x)
}
#[inline(never)]
fn chars(a: char, b: bool, f: f64) -> f64 {
    let arr = [&f];
    let t = (&a, &b);
    *arr[0] + *t.0 as u32 as f64 + *t.1 as u8 as f64
}
fn main() {
    let mut s = 0usize;
    for c in 0..4u32 {
        let v = bb(7u32);
        s = s * 131 + root(v, v + c % 2, c);
    }
    let n = Name(bb(4));
    let w = bb(9u64);
    let h = Holder { a: &n, b: &w, k: 3 };
    let flag = bb(true);
    let q = bb(5u32);
    println!(
        "{} {} {} {} {} {}",
        s,
        sum(&h),
        tup((&q, &flag, 2)),
        mutate(bb(2)),
        addr_eq(bb(1)),
        chars('a', true, 1.5)
    );
}
