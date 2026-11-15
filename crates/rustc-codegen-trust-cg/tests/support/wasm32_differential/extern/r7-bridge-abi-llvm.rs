// A library crate of `r7-bridge-abi.rs` that LLVM builds on BOTH sides
// (`wasm32-differential-extern-llvm`): the C ABI boundary between this
// backend's code and LLVM's, crossed in both directions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// NARROW EXTENDED SCALARS. rustc's wasm32 C ABI passes and returns an 8- or
// 16-bit integer `BackendRepr::Scalar` as one `i32` the SENDER extends: zero
// for an unsigned primitive (`Option<NonZeroU8>`, `Option<#[repr(u8)] enum>`,
// `Result<(), NonZeroU8>`, a newtype around one, `(u8,)`), sign for a signed
// one (`Option<NonZeroI8>`). LLVM's callee and caller here rely on it with
// optimization: `take_*` returns the argument without re-masking it, and
// `call_*` returns the result of a `fn` pointer of the user's crate unmasked,
// so a value extended the wrong way reaches the user's export unchanged.
//
// ONE-FIELD 128-BIT AGGREGATES. rustc casts a `#[repr(C)]` struct around one
// `i128`/`u128` to one 16-byte integer; LLVM passes it as two `i64` halves
// and returns it through a caller buffer (`sret`). `ccu`/`ccw` take and
// return such values; `via_ccu` calls the user's definition through a `fn`
// pointer.
#![no_std]
#![allow(improper_ctypes_definitions)]

use core::num::{NonZeroI8, NonZeroI16, NonZeroU8, NonZeroU16};

#[repr(u8)]
#[derive(Clone, Copy)]
pub enum E8 {
    A = 1,
    B = 0x80,
    C = 0xfe,
}

#[derive(Clone, Copy)]
pub enum Plain {
    A = 3,
    B = 200,
}

#[derive(Clone, Copy)]
pub struct W(pub Option<NonZeroU8>);

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct T(pub Option<NonZeroU8>);

#[repr(C)]
#[derive(Clone, Copy)]
pub struct CU {
    pub v: i128,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct CW {
    pub v: u128,
}

/// The raw `i32` an extended 8-bit argument arrives as, reinterpreted.
macro_rules! raw8 {
    ($v:expr) => {
        unsafe { core::mem::transmute::<_, u8>($v) as u32 }
    };
}

#[inline(never)]
pub extern "C" fn take_nz8(v: Option<NonZeroU8>) -> u32 {
    match v {
        Some(v) => v.get() as u32,
        None => 1000,
    }
}

#[inline(never)]
pub extern "C" fn take_nz16(v: Option<NonZeroU16>) -> u32 {
    match v {
        Some(v) => v.get() as u32,
        None => 100_000,
    }
}

#[inline(never)]
pub extern "C" fn take_nzi8(v: Option<NonZeroI8>) -> i32 {
    match v {
        Some(v) => v.get() as i32,
        None => 1000,
    }
}

#[inline(never)]
pub extern "C" fn take_nzi16(v: Option<NonZeroI16>) -> i32 {
    match v {
        Some(v) => v.get() as i32,
        None => 100_000,
    }
}

#[inline(never)]
pub extern "C" fn take_e8(v: Option<E8>) -> u32 {
    match v {
        Some(e) => e as u32,
        None => 7,
    }
}

#[inline(never)]
pub extern "C" fn take_plain(v: Option<Plain>) -> u32 {
    match v {
        Some(e) => e as u32,
        None => 9,
    }
}

#[inline(never)]
pub extern "C" fn take_res(v: Result<(), NonZeroU8>) -> u32 {
    match v {
        Ok(()) => 1000,
        Err(e) => e.get() as u32,
    }
}

#[inline(never)]
pub extern "C" fn take_w(v: W) -> u32 {
    raw8!(v)
}

#[inline(never)]
pub extern "C" fn take_t(v: T) -> u32 {
    raw8!(v)
}

#[inline(never)]
pub extern "C" fn take_t8(v: (u8,)) -> u32 {
    v.0 as u32
}

#[inline(never)]
pub extern "C" fn take_t16(v: (u16,)) -> u32 {
    v.0 as u32
}

#[inline(never)]
pub fn call_nz8(f: extern "C" fn(u32) -> Option<NonZeroU8>, x: u32) -> u32 {
    f(x).map_or(1000, |v| v.get() as u32)
}

#[inline(never)]
pub fn call_nz16(f: extern "C" fn(u32) -> Option<NonZeroU16>, x: u32) -> u32 {
    f(x).map_or(100_000, |v| v.get() as u32)
}

#[inline(never)]
pub fn call_nzi8(f: extern "C" fn(u32) -> Option<NonZeroI8>, x: u32) -> i32 {
    f(x).map_or(1000, |v| v.get() as i32)
}

#[inline(never)]
pub fn call_e8(f: extern "C" fn(u32) -> Option<E8>, x: u32) -> u32 {
    f(x).map_or(7, |e| e as u32)
}

#[inline(never)]
pub fn call_plain(f: extern "C" fn(u32) -> Option<Plain>, x: u32) -> u32 {
    f(x).map_or(9, |e| e as u32)
}

#[inline(never)]
pub fn call_res(f: extern "C" fn(u32) -> Result<(), NonZeroU8>, x: u32) -> u32 {
    match f(x) {
        Ok(()) => 1000,
        Err(e) => e.get() as u32,
    }
}

#[inline(never)]
pub fn call_w(f: extern "C" fn(u32) -> W, x: u32) -> u32 {
    raw8!(f(x))
}

#[inline(never)]
pub fn call_t(f: extern "C" fn(u32) -> T, x: u32) -> u32 {
    raw8!(f(x))
}

#[inline(never)]
pub fn call_t8(f: extern "C" fn(u32) -> (u8,), x: u32) -> u32 {
    f(x).0 as u32
}

#[inline(never)]
pub fn call_t16(f: extern "C" fn(u32) -> (u16,), x: u32) -> u32 {
    f(x).0 as u32
}

/// LLVM as the caller of the user's `extern "C"` definition taking an
/// extended value: it extends the argument itself.
#[inline(never)]
pub fn pass_nz8(f: extern "C" fn(Option<NonZeroU8>) -> u32, x: u32) -> u32 {
    f(NonZeroU8::new(x as u8))
}

#[inline(never)]
pub extern "C" fn ccu(a: CU, k: u32) -> CU {
    CU {
        v: a.v.wrapping_neg() ^ k as i128,
    }
}

#[inline(never)]
pub extern "C" fn ccw(k: u32, a: CW, b: CW) -> CW {
    CW {
        v: a.v.rotate_left(k % 128) ^ b.v.wrapping_mul(3),
    }
}

#[inline(never)]
pub fn via_ccu(f: extern "C" fn(CU, u32) -> CU, x: i128, k: u32) -> i128 {
    f(CU { v: x }, k).v
}
