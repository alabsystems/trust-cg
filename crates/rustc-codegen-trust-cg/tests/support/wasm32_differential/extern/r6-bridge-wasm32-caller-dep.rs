// A library crate of `r6-bridge-wasm32-caller.rs` that each side builds with
// its own backend (`wasm32-differential-extern`): `#[track_caller]`
// definitions, generic instances and trait methods that another crate of the
// same backend calls, directly, through share-generics and through vtables.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
#![no_std]

use core::panic::Location;

#[inline(never)]
#[track_caller]
pub fn dtc(x: u32) -> u32 {
    x.rotate_left(3) ^ Location::caller().line() << 12
}

#[inline]
#[track_caller]
pub fn dtc_inline(x: u32) -> u32 {
    x ^ Location::caller().column() << 16
}

/// Forwards its own caller's Location to `dtc`.
#[inline(never)]
#[track_caller]
pub fn dtc_forward(x: u32) -> u32 {
    dtc(x) ^ dtc_inline(x.wrapping_add(1))
}

#[track_caller]
pub fn dtc_gen<T: Into<u64>>(v: T) -> u64 {
    v.into() ^ u64::from(Location::caller().line()) << 40
}

/// Instantiates `dtc_gen`, `<u16 as Into<u64>>::into` and `Option::expect`
/// here for a downstream crate built with share-generics (debug).
#[inline(never)]
pub fn dep_generics(x: u32) -> u64 {
    let narrow: u64 = (x as u16).into();
    dtc_gen(x as u16) ^ dtc_gen(x) ^ narrow ^ u64::from(Some(x).filter(|v| *v != 55).expect("55"))
}

pub trait Dt {
    #[track_caller]
    fn dm(&self, x: u32) -> u32;
}

impl Dt for u32 {
    #[track_caller]
    #[inline(never)]
    fn dm(&self, x: u32) -> u32 {
        self ^ x.wrapping_mul(5) ^ Location::caller().line() << 6
    }
}

#[inline(never)]
pub fn dep_dyn(d: &dyn Dt, x: u32) -> u32 {
    d.dm(x)
}
