// wasm32 execution-differential corpus: `extern "rust-call"` crossings.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Every `extern "rust-call"` callable is declared with its argument tuple's
// ELEMENTS, as rustc's `FnAbi` lists them (`rust_call_spread`), on wasm32 as
// on the native targets. Until that (round 10, F2) the bridge declared the
// tuple as ONE parameter and, from 2026-10-03, refused by name every call
// whose tuple could place differently (`[TCG-RUST-CALL-ABI]`). Measured on
// wasm32 before that refusal (2026-10-03, O0 and O2): a pointer to a reified
// `Fn::call` of a closure trapped with `function signature mismatch` where
// LLVM returns a value. These exports must now compile and equal LLVM's
// module, each crossing the boundary with `rt_llvm` (built by LLVM on both
// sides) in both directions:
//
// * `rc_ptr_*`: calls through `extern "rust-call"` fn pointers, LLVM's items
//   called here and this crate's items called by LLVM, with a `[f32; 4]`
//   element (a pointer to a copy), a `(u32, u64)` tuple, a float pair and a
//   `(bool, u64)` tuple whose `bool` the caller extends;
// * `rc_dyn_*`: a user trait's `extern "rust-call"` method through `&dyn`,
//   this crate's impl called by LLVM and LLVM's impl called here;
// * `rc_foreign`: a foreign `extern "rust-call"` item declared in an `extern`
//   block;
// * `rc_body_*`: the address of a `Fn` closure's own body (`<F as
//   Fn<..>>::call`, reified), made by one backend and called by the other.
//
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3 -Ccodegen-units=4
// wasm32-differential-extern-llvm: rt_llvm r10-bridge-rust-call-llvm.rs

#![no_std]
#![feature(unboxed_closures, fn_traits)]
#![allow(improper_ctypes, improper_ctypes_definitions)]

extern crate rt_llvm;

use core::hint::black_box;
use rt_llvm::{BodyArgs, RcTr, mx};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

mod foreign {
    unsafe extern "rust-call" {
        pub fn tcg_w32_rust_call_foreign(a: (u64, [f32; 4], u8)) -> u64;
    }
}

#[inline(never)]
extern "rust-call" fn mine_repro(a: (u64, [f32; 4], u8)) -> u64 {
    mx(
        a.0.wrapping_add(a.1[1].to_bits() as u64),
        (a.1[3].to_bits() as u64) ^ a.2 as u64,
    )
}

#[inline(never)]
extern "rust-call" fn mine_narrow_wide(a: (u32, u64)) -> u64 {
    mx(a.1, a.0 as u64 * 3)
}

#[inline(never)]
extern "rust-call" fn mine_flag(a: (bool, u64)) -> u64 {
    if a.0 { a.1 + 5 } else { 11 }
}

#[no_mangle]
pub extern "C" fn rc_ptr_llvm_repro(k: u32) -> u64 {
    let f = black_box(rt_llvm::get_repro());
    f((k as u64, [1.0, black_box(2.0), 3.0, k as f32], 7))
}

#[no_mangle]
pub extern "C" fn rc_ptr_mine_repro(k: u32) -> u64 {
    rt_llvm::call_repro(black_box(mine_repro as rt_llvm::Repro), k as u64)
}

#[no_mangle]
pub extern "C" fn rc_ptr_llvm_narrow_wide(k: u32) -> u64 {
    let f = black_box(rt_llvm::get_narrow_wide());
    f((k ^ 0x33, (k as u64) << 7))
}

#[no_mangle]
pub extern "C" fn rc_ptr_mine_narrow_wide(k: u32) -> u64 {
    rt_llvm::call_narrow_wide(
        black_box(mine_narrow_wide as extern "rust-call" fn((u32, u64)) -> u64),
        k as u64,
    )
}

#[no_mangle]
pub extern "C" fn rc_ptr_llvm_float_pair(k: u32) -> u64 {
    let f = black_box(rt_llvm::get_float_pair());
    f((k as f64 * 0.5, black_box(2.25)))
}

#[no_mangle]
pub extern "C" fn rc_ptr_llvm_flag(k: u32) -> u64 {
    let f = black_box(rt_llvm::get_flag());
    f((k > 100, k as u64)).wrapping_add(f((black_box(k) < 100, k as u64)))
}

#[no_mangle]
pub extern "C" fn rc_ptr_mine_flag(k: u32) -> u64 {
    rt_llvm::call_flag(
        black_box(mine_flag as extern "rust-call" fn((bool, u64)) -> u64),
        k as u64,
    )
}

#[no_mangle]
pub extern "C" fn rc_direct_llvm_flag(k: u32) -> u64 {
    rt_llvm::flag((black_box(k) & 1 == 1, k as u64))
}

struct Mine(u64);

impl RcTr for Mine {
    #[inline(never)]
    extern "rust-call" fn m(&self, a: (u64, [f32; 4], u8)) -> u64 {
        mx(mine_repro(a), self.0)
    }
}

#[no_mangle]
pub extern "C" fn rc_dyn_mine_by_llvm(k: u32) -> u64 {
    // A local, not a static: a constant `&STATIC as &dyn _` is an unsize of a
    // non-place operand, which the bridge refuses at O2 for a reason unrelated
    // to `rust-call` ("trait-object unsize source is not a place operand").
    let mine = Mine(black_box(19));
    rt_llvm::call_tr(&mine as &dyn RcTr, k as u64)
}

#[no_mangle]
pub extern "C" fn rc_dyn_llvm_by_mine(k: u32) -> u64 {
    let t = black_box(rt_llvm::llvm_tr());
    t.m((k as u64, [4.0, 3.0, 2.0, black_box(1.0)], 6))
}

#[no_mangle]
pub extern "C" fn rc_foreign(k: u32) -> u64 {
    unsafe { foreign::tcg_w32_rust_call_foreign((k as u64, [9.0, 8.0, 7.0, k as f32], 3)) }
}

#[inline(never)]
fn reify_mine<F: Fn(u32, u64) -> u64>(_: &F) -> *const () {
    (<F as Fn<BodyArgs>>::call as for<'a> extern "rust-call" fn(&'a F, BodyArgs) -> u64)
        as *const ()
}

#[no_mangle]
pub extern "C" fn rc_body_mine_by_llvm(k: u32) -> u64 {
    let s = black_box(k as u64 * 5);
    let c = move |a: u32, b: u64| mx(a as u64 * 7 + s, b);
    let p = black_box(reify_mine(&c));
    rt_llvm::call_body(p, &s, k as u64)
}

#[no_mangle]
pub extern "C" fn rc_body_llvm_by_mine(k: u32) -> u64 {
    let s = black_box(k as u64 + 1);
    let c = rt_llvm::llvm_closure(s);
    let p = black_box(rt_llvm::reify_body(&c));
    let p: for<'a> extern "rust-call" fn(&'a u64, BodyArgs) -> u64 =
        unsafe { core::mem::transmute(p) };
    p(&s, (k ^ 0x5a, (k as u64) << 3))
}
