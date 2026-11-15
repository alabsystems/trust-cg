// A library crate of `r3-bridge-multicgu.rs`, built with overflow checks on.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Its copies of `core`'s `i32::abs` and `u32::pow` (`LocalCopy` instances
// whose rustc symbols carry no instantiating crate, so its user's copies have
// the same symbols) inherit THIS crate's overflow checks: they must trap here
// while the user's copies, built without overflow checks, wrap. `larger` is a
// generic the user instantiates both at a type this crate also instantiates
// and exports (shared generics) and at one it does not.
#![no_std]

#[inline(never)]
pub fn abs_via_ptr(x: i32) -> i32 {
    let f: fn(i32) -> i32 = i32::abs;
    core::hint::black_box(f)(x)
}

#[inline(never)]
pub fn abs_direct(x: i32) -> i32 {
    x.abs()
}

#[inline(never)]
pub fn pow_via_ptr(x: u32, y: u32) -> u32 {
    let f: fn(u32, u32) -> u32 = u32::pow;
    core::hint::black_box(f)(x, y & 7)
}

#[inline(never)]
pub fn mix(x: u32, y: u32) -> u32 {
    x.wrapping_add(y).rotate_left(y & 31)
}

pub fn larger<T: PartialOrd + Copy>(a: T, b: T) -> T {
    if a < b { b } else { a }
}

#[inline(never)]
pub fn larger_u32(a: u32, b: u32) -> u32 {
    larger(a, b)
}
