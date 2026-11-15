// A library crate of `r6-bridge-wasm32.rs` that LLVM builds on BOTH sides
// (`wasm32-differential-extern-llvm`): the Rust-ABI boundary between this
// backend's code and LLVM's, crossed in both directions, and the statics
// this backend's code must address through their one location.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc's wasm32 Rust ABI passes a `Memory` aggregate wider than a pointer
// through memory (a pointer to a caller-made copy) and returns one wider than
// two pointers, or one it does not cast, through a caller buffer (`sret`).
// Every by-value type below is such a value that is ONE wasm value's worth of
// bytes — a one-element array or newtype of a 64-bit lane, an `i128` lane, an
// 8-aligned `u32`, a `u64`/`f32` union, a 64-bit atomic — the shapes a
// backend could be tempted to pass as a wasm value. The `apply_*` functions
// call the user's functions through `fn` pointers and a trait object, so the
// user's DEFINITIONS are called by LLVM code as well.
#![no_std]

use core::hint::black_box;
use core::sync::atomic::{AtomicI64, AtomicU64, Ordering};

#[derive(Clone, Copy)]
#[repr(align(8))]
pub struct A8(pub u32);

#[derive(Clone, Copy)]
pub struct W64(pub [u64; 1]);

#[derive(Clone, Copy)]
pub struct F64a(pub [f64; 1]);

#[derive(Clone, Copy)]
pub union V {
    pub a: u64,
    pub b: f32,
}

#[inline(never)]
pub fn al(a: A8, k: u32) -> A8 {
    A8(a.0 ^ k)
}

#[inline(never)]
pub fn w64(a: W64, k: u64) -> W64 {
    W64([a.0[0].wrapping_mul(k)])
}

#[inline(never)]
pub fn arr64(a: [u64; 1]) -> [u64; 1] {
    [a[0].rotate_left(7)]
}

#[inline(never)]
pub fn f64a(a: F64a) -> F64a {
    F64a([a.0[0] * 1.5])
}

#[inline(never)]
pub fn i128a(a: [i128; 1]) -> i128 {
    a[0] >> 3
}

#[inline(never)]
pub fn v_mix(v: V, k: u32) -> V {
    V {
        a: unsafe { v.a } ^ u64::from(k),
    }
}

#[inline(never)]
pub fn make_atomic(v: u64) -> AtomicU64 {
    AtomicU64::new(v.wrapping_mul(3))
}

#[inline(never)]
pub fn take_atomic(a: AtomicI64, k: i64) -> i64 {
    a.fetch_add(k, Ordering::Relaxed);
    a.into_inner()
}

#[inline(never)]
pub fn apply_arr(f: fn([u64; 1]) -> [u64; 1], x: u64) -> u64 {
    black_box(f)(black_box([x]))[0]
}

#[inline(never)]
pub fn apply_al(f: fn(A8, u32) -> A8, x: u32) -> u32 {
    black_box(f)(A8(x), 5).0
}

#[inline(never)]
pub fn apply_v(f: fn(V, u32) -> V, x: u64) -> u64 {
    unsafe { black_box(f)(V { a: x }, 9).a }
}

#[inline(never)]
pub fn apply_atomic(f: fn(AtomicU64) -> AtomicU64, x: u64) -> u64 {
    black_box(f)(AtomicU64::new(x)).into_inner()
}

pub trait Shape {
    fn scale(&self, a: [u64; 1], k: A8) -> A8;
}

#[inline(never)]
pub fn apply_dyn(t: &dyn Shape, x: u64, k: u32) -> u32 {
    black_box(t).scale([x], A8(k)).0
}

// ---- statics: one location each, whichever crate names them ---------------

pub static S: u32 = 5;
pub static T: [u32; 4] = [1, 2, 3, 4];
pub static STR: &str = "hello";
pub static REF: &u32 = &S;
static P: u32 = 9;

#[inline(never)]
pub fn addr_s() -> *const u32 {
    &S
}

#[inline(never)]
pub fn addr_t2() -> *const u32 {
    &T[2]
}

#[inline(never)]
pub fn str_ptr() -> *const u8 {
    STR.as_ptr()
}

#[inline(never)]
pub fn addr_p() -> *const u32 {
    &P
}

/// Instantiated in the user's crate, where it names the private `P`.
#[inline]
pub fn inline_addr_p() -> *const u32 {
    &P
}

/// Instantiated in the user's crate, where it names the private `P`.
pub fn generic_addr_p<X>() -> *const u32 {
    &P
}
