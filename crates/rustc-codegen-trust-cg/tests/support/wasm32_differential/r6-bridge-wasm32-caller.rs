// `#[track_caller]` across crates and backends on wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc's `FnAbi` for a `#[track_caller]` instance has one argument more than
// its MIR, a trailing `&'static Location`, and a wasm function's type is part
// of its link identity: a call whose parameter list differs from the
// definition's is bound to a trapping stub. Every `#[track_caller]` definition
// here takes that argument and every call passes it — calls into the
// LLVM-built `extern/r6-bridge-wasm32-caller-llvm.rs` (`lb_*`), LLVM calling
// this crate's definitions through a trait object and a `fn` pointer
// (`cb_*`), and calls into `extern/r6-bridge-wasm32-caller-dep.rs`, built by
// each side's own backend (`dp_*`), including the share-generics instances of
// `Into::into` and `Option::expect` that a debug build reuses from upstream.
// The Location passed is rustc's: a `#[track_caller]` caller forwards its
// own, and `Location::caller()` (`lc_*`) observes its line and column, also
// through MIR-inlined `#[track_caller]` scopes at `-O`.
#![no_std]
#![allow(dead_code)]
#![feature(closure_track_caller)]

// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3 -Ccodegen-units=4
// wasm32-differential-flags: -Copt-level=1 -Coverflow-checks=on
// wasm32-differential-extern: r6c_dep r6-bridge-wasm32-caller-dep.rs
// wasm32-differential-extern-llvm: r6c_llvm r6-bridge-wasm32-caller-llvm.rs

extern crate r6c_dep;
extern crate r6c_llvm;

use core::hint::black_box;
use core::panic::Location;

use r6c_dep::Dt;
use r6c_llvm::Tc;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

struct Mine(u32);

impl Tc for Mine {
    #[track_caller]
    #[inline(never)]
    fn at(&self, x: u32) -> u32 {
        self.0.wrapping_add(x) ^ Location::caller().line() << 9
    }
}

impl Dt for Mine {
    #[track_caller]
    #[inline(never)]
    fn dm(&self, x: u32) -> u32 {
        self.0.rotate_left(7) ^ x ^ Location::caller().column() << 9
    }
}

#[track_caller]
#[inline(never)]
fn mine_tc(x: u32) -> u32 {
    x.wrapping_mul(0x9E37_79B9) ^ Location::caller().line()
}

/// Forwards its caller's Location into LLVM's and the dependency's
/// definitions.
#[track_caller]
#[inline(never)]
fn mine_forward(x: u32) -> u32 {
    r6c_llvm::tc_line(x) ^ r6c_dep::dtc_forward(x) ^ mine_tc(x)
}

#[inline]
#[track_caller]
fn mine_inline(x: u32) -> u32 {
    let at = Location::caller();
    x ^ at.line() << 3 ^ at.column() << 18
}

#[no_mangle]
pub extern "C" fn lb_direct(x: u32) -> u32 {
    r6c_llvm::tc_line(x) ^ r6c_llvm::tc_line(x.rotate_left(5))
}

#[no_mangle]
pub extern "C" fn lb_generics(x: u32) -> i64 {
    let narrow: u64 = (x as u16).into();
    let own = r6c_llvm::tc_gen(x as u16) ^ r6c_llvm::tc_gen(x) ^ narrow;
    (own ^ r6c_llvm::lib_generics(x) ^ u64::from(Some(x).filter(|v| *v != 13).expect("13"))) as i64
}

#[no_mangle]
pub extern "C" fn lb_dyn(x: u32, y: u32) -> u32 {
    let l = r6c_llvm::Lt(x);
    let d: &dyn Tc = black_box(&l);
    d.at(y) ^ l.at(y.wrapping_add(1))
}

#[no_mangle]
pub extern "C" fn cb_dyn(x: u32, y: u32) -> u32 {
    let m = Mine(x);
    r6c_llvm::apply_tc(black_box(&m), y) ^ r6c_llvm::apply_tc(black_box(&r6c_llvm::Lt(y)), x)
}

#[no_mangle]
pub extern "C" fn cb_ptr(x: u32) -> u32 {
    r6c_llvm::apply_ptr(mine_tc, x) ^ r6c_llvm::apply_ptr(black_box(mine_tc), x ^ 1)
}

#[no_mangle]
pub extern "C" fn dp_direct(x: u32) -> u32 {
    r6c_dep::dtc(x) ^ r6c_dep::dtc_inline(x) ^ r6c_dep::dtc_forward(x.rotate_left(9))
}

#[no_mangle]
pub extern "C" fn dp_generics(x: u32) -> i64 {
    let narrow: u64 = (x as u16).into();
    let own = r6c_dep::dtc_gen(x as u16) ^ r6c_dep::dtc_gen(x) ^ narrow;
    (own ^ r6c_dep::dep_generics(x) ^ u64::from(Some(x).filter(|v| *v != 29).expect("29"))) as i64
}

#[no_mangle]
pub extern "C" fn dp_dyn(x: u32, y: u32) -> u32 {
    let m = Mine(y);
    let d: &dyn Dt = black_box(&x);
    d.dm(y) ^ r6c_dep::dep_dyn(black_box(&m), x) ^ r6c_dep::dep_dyn(black_box(&y), x)
}

#[no_mangle]
pub extern "C" fn lc_forward(x: u32) -> u32 {
    mine_forward(x) ^ mine_forward(x.wrapping_add(3)).rotate_left(1)
}

#[no_mangle]
pub extern "C" fn lc_inline(x: u32) -> u32 {
    mine_inline(x) ^ mine_inline(x ^ 7).rotate_left(2) ^ Location::caller().line()
}

#[inline(never)]
fn apply<F: Fn(u32) -> u32>(f: F, x: u32) -> u32 {
    f(x)
}

/// `mine_tc` through a generic `Fn` bound (its `Fn` shim passes a Location)
/// and through a `fn` pointer this crate calls (its reify shim).
#[no_mangle]
pub extern "C" fn lc_fn_item(x: u32) -> u32 {
    let p: fn(u32) -> u32 = black_box(mine_tc);
    apply(mine_tc, x) ^ p(x.rotate_left(3)) ^ apply(r6c_dep::dtc, x ^ 5)
}

#[track_caller]
#[inline(never)]
fn mine_add(acc: u32, x: u32) -> u32 {
    let at = Location::caller();
    acc.wrapping_add(x) ^ at.line() << 4 ^ at.column() << 16
}

#[inline(never)]
fn apply_dyn(f: &dyn Fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

#[inline(never)]
fn apply_dyn_mut(f: &mut dyn FnMut(u32) -> u32, x: u32) -> u32 {
    f(x)
}

/// A `#[track_caller]` CLOSURE through a generic `Fn` bound: the MIR closure
/// call in `apply` calls the closure body with the Location of that call
/// (`f(x)`), as rustc does.
#[no_mangle]
pub extern "C" fn lc_closure(x: u32) -> u32 {
    apply(
        #[track_caller]
        |v| v ^ Location::caller().line() << 5 ^ Location::caller().column() << 17,
        x,
    ) ^ apply(#[track_caller] |v| v.rotate_left(3) ^ Location::caller().line(), x ^ 9)
}

/// `#[track_caller]` fn items behind `dyn Fn` / `dyn FnMut`: the vtable slot
/// is rustc's `FnPtrShim`, which calls the item with the Location of its own
/// span (the `Fn::call` / `FnMut::call_mut` declaration), not the item's
/// reify shim.
#[no_mangle]
pub extern "C" fn lc_dyn_fn_item(x: u32) -> u32 {
    let mut f = mine_tc;
    apply_dyn(&mine_tc, x)
        ^ apply_dyn_mut(&mut f, x ^ 3).rotate_left(4)
        ^ apply_dyn(&r6c_dep::dtc, x ^ 5).rotate_left(9)
}

/// `fold` over a `#[track_caller]` fn item: `fold` calls it through its
/// `FnMut::call_mut` shim, which passes the Location of its own span.
#[no_mangle]
pub extern "C" fn lc_fold_fn_item(x: u32) -> u32 {
    [x, 2, x ^ 3].iter().copied().fold(1, mine_add) ^ (0..(x & 7)).fold(x, mine_add).rotate_left(3)
}
