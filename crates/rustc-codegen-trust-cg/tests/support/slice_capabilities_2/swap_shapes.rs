// Fixture of tests/slice_capabilities_2_linux.rs (bridge vs LLVM, O0-O3).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

use std::hint::black_box as bb;
#[derive(Debug, PartialEq)]
enum E {
    A(u64),
    B { x: u32, y: u8 },
}
#[inline(never)]
fn rev<'a>(v: &mut [&'a E]) {
    v.reverse();
}
#[inline(never)]
fn revm(v: &mut [*mut u16]) {
    v.reverse();
}
#[inline(never)]
fn swp<T>(a: &mut T, b: &mut T) {
    std::mem::swap(a, b);
}
#[inline(never)]
fn rot(v: &mut [&u64], k: usize) {
    v.rotate_left(k);
}
struct Z;
fn ev(e: &E) -> u64 {
    match e {
        E::A(x) => *x,
        E::B { x, y } => *x as u64 * 3 + *y as u64,
    }
}
fn main() {
    let k = bb(7u64);
    let es = [
        E::A(k),
        E::B { x: 3, y: 1 },
        E::A(k * 2),
        E::B { x: 9, y: 4 },
        E::A(5),
    ];
    let mut v = [&es[0], &es[1], &es[2], &es[3], &es[4]];
    rev(&mut v);
    let mut s = 0u64;
    for e in v.iter() {
        s = s * 31 + ev(e);
    }
    println!("{}", s);
    let mut w = [1u16, 2, 3, 4];
    let base = w.as_mut_ptr();
    let mut ps = [
        base,
        unsafe { base.add(1) },
        unsafe { base.add(2) },
        unsafe { base.add(3) },
    ];
    revm(&mut ps);
    unsafe {
        *ps[0] += 10;
    }
    println!("{} {} {} {}", w[0], w[1], w[2], w[3]);
    let (mut a, mut b) = (bb(3u64), bb(4u64));
    {
        let (mut ra, mut rb) = (&mut a, &mut b);
        swp(&mut ra, &mut rb);
        *ra += 100;
    }
    println!("{} {}", a, b);
    let z1 = Z;
    let z2 = Z;
    let (mut x, mut y) = (&z1 as *const Z, &z2 as *const Z);
    swp(&mut x, &mut y);
    println!("{}", x == &z2 as *const Z);
    let nums = [0u64, 1, 4, 9, 16, 25];
    let mut rs = [&nums[0], &nums[1], &nums[2], &nums[3], &nums[4], &nums[5]];
    rs.swap(bb(0), bb(4));
    println!("{} {} {}", rs[0], rs[3], rs[4]);
    let mut o1: Option<&u64> = Some(&nums[1]);
    let mut o2: Option<&u64> = None;
    swp(&mut o1, &mut o2);
    println!("{} {}", o1.is_none(), *o2.unwrap());
}
