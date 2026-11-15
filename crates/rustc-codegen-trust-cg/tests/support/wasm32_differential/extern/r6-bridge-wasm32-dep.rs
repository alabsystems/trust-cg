// A library crate of `r6-bridge-wasm32.rs` that each side builds with its own
// backend (`wasm32-differential-extern`): Rust-ABI by-memory values passed
// between two crates of this backend, and statics a downstream crate of this
// backend must address through their one location.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
#![no_std]

use core::sync::atomic::{AtomicU64, Ordering};

#[derive(Clone, Copy)]
#[repr(align(8))]
pub struct D8(pub u32);

#[derive(Clone, Copy)]
pub union DV {
    pub a: u64,
    pub b: f32,
}

#[inline(never)]
pub fn d_al(a: D8, k: u32) -> D8 {
    D8(a.0.rotate_left(k % 32))
}

#[inline(never)]
pub fn d_arr64(a: [u64; 1], k: u64) -> [u64; 1] {
    [a[0] ^ k.wrapping_mul(0x9E37_79B9)]
}

#[inline(never)]
pub fn d_v(v: DV) -> u64 {
    unsafe { v.a }.wrapping_add(3)
}

#[inline(never)]
pub fn d_atomic(v: u64) -> AtomicU64 {
    let a = AtomicU64::new(v);
    a.fetch_xor(0xFF, Ordering::Relaxed);
    a
}

/// `u32::pow` and `str::as_ptr` are copied into every crate that calls them
/// under one crate-agnostic symbol; each crate keeps its own copy.
#[inline(never)]
pub fn d_pow(x: u32, s: &str) -> u32 {
    x.wrapping_pow(3) ^ s.len() as u32 ^ u32::from(s.as_ptr().is_null())
}

pub static DS: u32 = 11;
pub static DT: [u16; 3] = [4, 5, 6];
pub static DSTR: &str = "dep";
pub static DREF: &u32 = &DS;
static DP: u64 = 13;

#[inline(never)]
pub fn addr_ds() -> *const u32 {
    &DS
}

#[inline(never)]
pub fn addr_dt1() -> *const u16 {
    &DT[1]
}

#[inline(never)]
pub fn dstr_ptr() -> *const u8 {
    DSTR.as_ptr()
}

#[inline(never)]
pub fn addr_dp() -> *const u64 {
    &DP
}

/// Instantiated in the user's crate, where it names the private `DP`.
#[inline]
pub fn inline_addr_dp() -> *const u64 {
    &DP
}

/// Instantiated in the user's crate, where it names the private `DP`.
pub fn generic_addr_dp<X>() -> *const u64 {
    &DP
}
