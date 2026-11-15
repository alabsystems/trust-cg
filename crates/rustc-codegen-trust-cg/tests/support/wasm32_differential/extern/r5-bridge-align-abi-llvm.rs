// A library crate of `r5-bridge-align-abi.rs` that LLVM builds on BOTH sides
// (`wasm32-differential-extern-llvm`): the ABI boundary between this
// backend's code and LLVM's, crossed in both directions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc's wasm32 ABI passes every value here through memory: a pointer to a
// caller-made copy, which the callee may use as the value's own address, so
// it must be as aligned as the type. Returns go through a caller buffer
// (`sret`); with optimization, the callee builds its result in that buffer.
// The C ABI does this for a heterogeneous or padded `#[repr(C)]` union, a
// padded one-field struct and an over-aligned struct; the Rust ABI does it
// for an aggregate aligned above 16 bytes. The functions below take and
// return them, call functions of the user through `fn` pointers, and hand the
// user a `fn` pointer and a trait object, so each convention is exercised
// with LLVM as the caller and as the callee. An address modulo the type's own
// alignment is 0 on both sides whenever the boundary is honoured.
#![no_std]

use core::hint::black_box;

#[repr(C)]
#[derive(Clone, Copy)]
pub union U4 {
    pub a: u32,
    pub c: u16,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union U8 {
    pub a: u64,
    pub b: [u8; 8],
}

#[repr(C)]
#[derive(Clone, Copy)]
pub union F8 {
    pub f: f64,
    pub u: u64,
}

#[repr(C, align(8))]
#[derive(Clone, Copy)]
pub struct S8 {
    pub a: u32,
}

#[repr(C, align(32))]
#[derive(Clone, Copy)]
pub struct C32 {
    pub a: u32,
    pub b: u64,
}

#[repr(align(64))]
#[derive(Clone, Copy)]
pub struct R64 {
    pub a: u64,
    pub b: u32,
}

#[repr(align(128))]
#[derive(Clone, Copy)]
pub struct R128 {
    pub a: u16,
    pub b: [u8; 3],
}

/// `x`'s address modulo `m`.
#[inline(never)]
pub fn addr_mod<T>(x: &T, m: usize) -> u64 {
    (black_box(x as *const T) as usize % m) as u64
}

pub extern "C" fn l_take_u4(x: U4, k: u32) -> u32 {
    unsafe { x.a ^ k.rotate_left(7) }
}

pub extern "C" fn l_take_u8(x: U8) -> u64 {
    unsafe { x.a ^ x.b[3] as u64 }
}

pub extern "C" fn l_take_f8(x: F8) -> u64 {
    unsafe { x.u.rotate_left(3) }
}

pub extern "C" fn l_take_s8(x: S8) -> u64 {
    x.a as u64 * 3 + (addr_mod(&x, 8) << 40)
}

pub extern "C" fn l_take_c32(x: C32, k: u32) -> u64 {
    x.a as u64 + x.b * 5 + k as u64 + (addr_mod(&x, 32) << 40)
}

pub extern "C" fn l_ret_u4(k: u32) -> U4 {
    U4 { a: k ^ 0x5a5a }
}

pub extern "C" fn l_ret_u8(k: u64) -> U8 {
    U8 {
        a: k.wrapping_mul(0x9e37_79b9),
    }
}

pub extern "C" fn l_ret_c32(k: u32) -> C32 {
    let mut x = C32 { a: k, b: 0 };
    x.b = addr_mod(&x, 32) + 11;
    x
}

pub fn l_take_r64(x: R64) -> u64 {
    x.a ^ (x.b as u64) << 8 ^ addr_mod(&x, 64) << 40
}

pub fn l_take_two(k: u32, x: C32, y: R128) -> u64 {
    k as u64
        + x.b
        + y.a as u64
        + y.b[2] as u64
        + (addr_mod(&x, 32) << 32)
        + (addr_mod(&y, 128) << 48)
}

pub fn l_ret_r64(k: u32) -> R64 {
    let mut x = R64 { a: 0, b: k };
    x.a = addr_mod(&x, 64) + 1000;
    x
}

pub fn l_ret_r128(k: u32) -> R128 {
    R128 {
        a: k as u16,
        b: [1, 2, k as u8],
    }
}

/// Calls the user's C-ABI function through a pointer.
pub fn l_call_c(f: extern "C" fn(U4, C32) -> U8, k: u32) -> u64 {
    unsafe { f(U4 { a: k }, C32 { a: k ^ 1, b: 3 }).a }
}

/// Calls the user's C-ABI function returning a union through a pointer.
pub fn l_call_c_ret(f: extern "C" fn(u32) -> U4, k: u32) -> u32 {
    unsafe { f(k).a ^ f(k ^ 2).a }
}

/// Calls the user's Rust-ABI function through a pointer.
pub fn l_call_rust(f: fn(C32, R64) -> u64, k: u32) -> u64 {
    f(C32 { a: k, b: 2 }, R64 { a: k as u64, b: 5 })
        + f(black_box(C32 { a: 1, b: k as u64 }), R64 { a: 3, b: k })
}

/// Calls the user's Rust-ABI function returning an over-aligned value.
pub fn l_call_rust_ret(f: fn(u32) -> R64, k: u32) -> u64 {
    let x = f(k);
    x.a + x.b as u64 + (addr_mod(&x, 64) << 40)
}

pub fn l_fn_ptr() -> fn(R64) -> u64 {
    black_box(l_take_r64)
}

pub fn l_c_fn_ptr() -> extern "C" fn(C32, u32) -> u64 {
    black_box(l_take_c32)
}

pub trait LTrait {
    fn m(&self, x: C32) -> u64;
    fn r(&self, k: u32) -> R64;
    extern "C" fn c(&self, x: U8) -> U4;
}

pub struct LObj(pub u32);

impl LTrait for LObj {
    fn m(&self, x: C32) -> u64 {
        self.0 as u64 + x.b + (addr_mod(&x, 32) << 40)
    }

    fn r(&self, k: u32) -> R64 {
        let mut x = R64 {
            a: 0,
            b: k + self.0,
        };
        x.a = addr_mod(&x, 64) + 7;
        x
    }

    extern "C" fn c(&self, x: U8) -> U4 {
        U4 {
            a: unsafe { x.a as u32 } ^ self.0,
        }
    }
}

pub static L_OBJ: LObj = LObj(3);

pub fn l_obj() -> &'static dyn LTrait {
    let o: &'static LObj = black_box(&L_OBJ);
    o
}

/// Calls the user's trait object.
pub fn l_use_dyn(d: &dyn LTrait, k: u32) -> u64 {
    d.m(C32 { a: k, b: 5 }) + d.r(k).a + unsafe { d.c(U8 { a: k as u64 }).a } as u64
}
