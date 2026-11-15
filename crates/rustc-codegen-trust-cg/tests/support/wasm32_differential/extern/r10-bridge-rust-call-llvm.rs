// A library crate of `r10-bridge-rust-call.rs` that LLVM builds on BOTH sides
// (`wasm32-differential-extern-llvm`): `extern "rust-call"` callables and
// callers of `extern "rust-call"` fn pointers, so every `rust-call` crossing
// between this backend's code and LLVM's is compared in both directions.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc's `FnAbi` for an `extern "rust-call"` callable lists the argument
// tuple's ELEMENTS (untupled), each by its own `PassMode` (on wasm32 a
// `[f32; 4]` is a pointer to a copy, a `bool` an `i32` the caller extends).
// A callee or caller that passes the tuple as one value disagrees with that
// list, which wasm-ld links to a trapping stub or which reads the wrong
// parameter.
#![no_std]
#![feature(unboxed_closures, fn_traits)]
#![allow(improper_ctypes_definitions)]

#[inline]
pub fn mx(h: u64, v: u64) -> u64 {
    (h ^ v).wrapping_mul(0x100000001b3).rotate_left(5)
}

pub type Repro = extern "rust-call" fn((u64, [f32; 4], u8)) -> u64;

#[inline(never)]
pub extern "rust-call" fn repro(a: (u64, [f32; 4], u8)) -> u64 {
    mx(mx(a.0, a.1[3].to_bits() as u64), a.2 as u64)
}

#[inline(never)]
pub fn get_repro() -> Repro {
    repro
}

/// Calls a pointer the user's crate hands over, whatever compiled the pointee.
#[inline(never)]
pub fn call_repro(f: Repro, k: u64) -> u64 {
    f((k, [1.0, 2.0, 3.0, k as f32], 9))
}

#[inline(never)]
pub extern "rust-call" fn narrow_wide(a: (u32, u64)) -> u64 {
    mx(a.0 as u64, a.1)
}

#[inline(never)]
pub fn get_narrow_wide() -> extern "rust-call" fn((u32, u64)) -> u64 {
    narrow_wide
}

#[inline(never)]
pub fn call_narrow_wide(f: extern "rust-call" fn((u32, u64)) -> u64, k: u64) -> u64 {
    f((k as u32 ^ 0x55, k.rotate_left(17)))
}

#[inline(never)]
pub extern "rust-call" fn float_pair(a: (f64, f64)) -> u64 {
    mx(a.0.to_bits(), a.1.to_bits())
}

#[inline(never)]
pub fn get_float_pair() -> extern "rust-call" fn((f64, f64)) -> u64 {
    float_pair
}

/// `(bool, u64)`: rustc's caller extends the `bool`.
#[inline(never)]
pub extern "rust-call" fn flag(a: (bool, u64)) -> u64 {
    if a.0 { a.1 * 3 } else { 7 }
}

#[inline(never)]
pub fn get_flag() -> extern "rust-call" fn((bool, u64)) -> u64 {
    flag
}

#[inline(never)]
pub fn call_flag(f: extern "rust-call" fn((bool, u64)) -> u64, k: u64) -> u64 {
    f((k > 100, k)).wrapping_add(f((k < 100, k)))
}

/// A user trait with an `extern "rust-call"` method, dispatched dynamically.
pub trait RcTr {
    extern "rust-call" fn m(&self, a: (u64, [f32; 4], u8)) -> u64;
}

pub struct S(pub u64);

impl RcTr for S {
    #[inline(never)]
    extern "rust-call" fn m(&self, a: (u64, [f32; 4], u8)) -> u64 {
        mx(repro(a), self.0)
    }
}

pub static LLVM_S: S = S(77);

#[inline(never)]
pub fn llvm_tr() -> &'static dyn RcTr {
    &LLVM_S
}

#[inline(never)]
pub fn call_tr(t: &dyn RcTr, k: u64) -> u64 {
    t.m((k, [0.5, 1.5, 2.5, 3.5], 4))
}

/// A foreign `extern "rust-call"` item the user's crate declares in an
/// `extern` block.
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "rust-call" fn tcg_w32_rust_call_foreign(a: (u64, [f32; 4], u8)) -> u64 {
    repro(a)
}

/// Calls the address of a `Fn` closure body the user's crate reifies: the
/// environment is one `u64`, the arguments a `(u32, u64)` tuple.
pub type BodyArgs = (u32, u64);

#[inline(never)]
pub fn call_body(p: *const (), env: &u64, k: u64) -> u64 {
    let p: for<'a> extern "rust-call" fn(&'a u64, BodyArgs) -> u64 =
        unsafe { core::mem::transmute(p) };
    p(env, (k as u32, k ^ 0xabc))
}

/// The address of a `Fn` closure's own body, reified here.
#[inline(never)]
pub fn reify_body<F: Fn(u32, u64) -> u64>(_: &F) -> *const () {
    (<F as Fn<BodyArgs>>::call as for<'a> extern "rust-call" fn(&'a F, BodyArgs) -> u64)
        as *const ()
}

#[inline(never)]
pub fn llvm_closure(s: u64) -> impl Fn(u32, u64) -> u64 + Copy {
    move |a: u32, b: u64| mx(a as u64 + s, b)
}
