// A library crate of `r6-bridge-wasm32-caller.rs` that LLVM builds on BOTH
// sides (`wasm32-differential-extern-llvm`): `#[track_caller]` definitions
// this backend's code calls, and callers of this backend's `#[track_caller]`
// definitions through a trait object and a `fn` pointer.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc's `FnAbi` for a `#[track_caller]` instance has one argument more than
// its MIR: a trailing `&'static Location`. LLVM's definitions here take it,
// LLVM's virtual calls pass it, and `Location::caller()` reads it, so a caller
// that omits it (or a definition that does not take it) fails wasm's call
// signature check and traps.
#![no_std]

use core::panic::Location;

#[inline(never)]
#[track_caller]
pub fn tc_line(x: u32) -> u32 {
    let at = Location::caller();
    x ^ at.line() << 8 ^ at.column() << 20
}

#[track_caller]
pub fn tc_gen<T: Into<u64>>(v: T) -> u64 {
    v.into()
        .wrapping_add(u64::from(Location::caller().line()) << 32)
}

/// Instantiates `tc_gen`, `<u16 as Into<u64>>::into` and `Option::expect`
/// here, so a downstream crate built with share-generics (debug) calls these
/// LLVM-built instances instead of its own copies.
#[inline(never)]
pub fn lib_generics(x: u32) -> u64 {
    let narrow: u64 = (x as u16).into();
    tc_gen(x as u16) ^ tc_gen(x) ^ narrow ^ u64::from(Some(x).filter(|v| *v != 77).expect("77"))
}

pub trait Tc {
    #[track_caller]
    fn at(&self, x: u32) -> u32;
}

pub struct Lt(pub u32);

impl Tc for Lt {
    #[track_caller]
    #[inline(never)]
    fn at(&self, x: u32) -> u32 {
        self.0.wrapping_mul(3) ^ x ^ Location::caller().line() << 4
    }
}

/// A virtual call LLVM makes, passing its own Location.
#[inline(never)]
pub fn apply_tc(t: &dyn Tc, x: u32) -> u32 {
    t.at(x)
}

/// A call through a `fn` pointer, which rustc makes to a `#[track_caller]`
/// function's reify shim.
#[inline(never)]
pub fn apply_ptr(f: fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}
