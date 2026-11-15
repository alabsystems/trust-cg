// The dependency of `r6-bridge-frontend.rs` that LLVM builds on both sides:
// the same `#[track_caller]` items as `r6-bridge-frontend-dep.rs`, so this
// backend's code calls LLVM's definitions (directly, through `fn` pointers and
// through vtables) and LLVM's code calls this backend's `#[track_caller]`
// trait impl through a vtable.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

#![no_std]

use core::panic::Location;

#[track_caller]
#[inline(never)]
pub fn add_one(x: u32) -> u32 {
    x.wrapping_add(1)
}

/// The caller's line and column, packed.
#[track_caller]
#[inline(never)]
pub fn here() -> u32 {
    let l = Location::caller();
    l.line() * 1000 + l.column()
}

/// Forwards its own caller's location to `here`.
#[track_caller]
#[inline(never)]
pub fn nested() -> u32 {
    here()
}

/// `Index::index` is `#[track_caller]`, so every impl of it takes the location.
pub struct Tbl(pub [u32; 4]);

impl core::ops::Index<u32> for Tbl {
    type Output = u32;
    #[inline(never)]
    fn index(&self, i: u32) -> &u32 {
        &self.0[(i & 3) as usize]
    }
}

/// A trait method declared `#[track_caller]`: a virtual call passes the
/// location, and the vtable slot's method takes it.
pub trait Tc {
    #[track_caller]
    fn tc(&self, x: u32) -> u32;
}

pub struct K(pub u32);

impl Tc for K {
    #[inline(never)]
    fn tc(&self, x: u32) -> u32 {
        self.0 ^ x ^ Location::caller().line()
    }
}

/// `<u16 as Into<u64>>::into` (`#[track_caller]`) instantiated here; at
/// `-Copt-level=0` a dependent crate reuses this shared instance.
#[inline(never)]
pub fn widen_l(x: u16) -> u64 {
    x.into()
}

/// A virtual call made in this crate into an implementation the user supplies.
#[inline(never)]
pub fn call_dyn_l(t: &dyn Tc, x: u32) -> u32 {
    t.tc(x)
}
