// A library crate of `r5-bridge-align-abi.rs`: `extern "C"` functions that
// take and return by-memory values by value, called from its user.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc's wasm32 C ABI passes each of these types through memory (a pointer
// to a caller-made copy) and returns each through a caller buffer (`sret`).
// The functions keep Rust symbols (no `#[no_mangle]`), so the user's cdylib
// does not export them; their convention is still the C ABI's.
#![no_std]

#[repr(C)]
#[derive(Clone, Copy)]
pub union U4 {
    pub a: u32,
    pub c: u16,
}

#[repr(C, align(8))]
#[derive(Clone, Copy)]
pub union Q {
    pub a: u32,
}

#[repr(C, align(32))]
#[derive(Clone, Copy)]
pub struct A32 {
    pub a: u32,
    pub b: u64,
}

#[inline(never)]
pub extern "C" fn dep_take_u4(x: U4, k: u32) -> u32 {
    unsafe { x.a.rotate_left(k % 32) ^ x.c as u32 }
}

#[inline(never)]
pub extern "C" fn dep_ret_u4(k: u32) -> U4 {
    U4 {
        a: k.wrapping_mul(0x9e37_79b9),
    }
}

#[inline(never)]
pub extern "C" fn dep_echo_q(x: Q) -> Q {
    unsafe {
        Q {
            a: x.a ^ 0x0f0f_0f0f,
        }
    }
}

#[inline(never)]
pub extern "C" fn dep_take_a32(x: A32) -> u64 {
    x.b.wrapping_sub(x.a as u64) ^ (&x as *const A32 as usize % 32) as u64
}

#[inline(never)]
pub extern "C" fn dep_ret_a32(k: u32) -> A32 {
    A32 {
        a: !k,
        b: (k as u64) << 17,
    }
}
