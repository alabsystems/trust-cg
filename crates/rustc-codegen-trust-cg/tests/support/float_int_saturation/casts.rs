// Every float -> integer conversion Rust spells, one exported function per
// (float, integer) pair: `as_*` is the saturating `as` cast (MIR
// `Cast(FloatToInt)`), `unchecked_*` is `to_int_unchecked` (the
// `float_to_int_unchecked` intrinsic). Compiled once by trust-cg and once by
// LLVM; driver.rs calls both builds on the same inputs.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
#![no_std]
#![allow(improper_ctypes_definitions)]

macro_rules! conversions {
    ($($as_name:ident, $unchecked_name:ident: $float:ty => $int:ty;)*) => {$(
        #[unsafe(no_mangle)]
        pub extern "C" fn $as_name(x: $float) -> $int {
            x as $int
        }

        // Safety contract: `x` is finite and its value rounded toward zero fits
        // the destination integer.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $unchecked_name(x: $float) -> $int {
            // SAFETY: the caller's contract above is `to_int_unchecked`'s.
            unsafe { x.to_int_unchecked::<$int>() }
        }
    )*};
}

conversions! {
    as_f32_i8, unchecked_f32_i8: f32 => i8;
    as_f32_i16, unchecked_f32_i16: f32 => i16;
    as_f32_i32, unchecked_f32_i32: f32 => i32;
    as_f32_i64, unchecked_f32_i64: f32 => i64;
    as_f32_i128, unchecked_f32_i128: f32 => i128;
    as_f32_isize, unchecked_f32_isize: f32 => isize;
    as_f32_u8, unchecked_f32_u8: f32 => u8;
    as_f32_u16, unchecked_f32_u16: f32 => u16;
    as_f32_u32, unchecked_f32_u32: f32 => u32;
    as_f32_u64, unchecked_f32_u64: f32 => u64;
    as_f32_u128, unchecked_f32_u128: f32 => u128;
    as_f32_usize, unchecked_f32_usize: f32 => usize;
    as_f64_i8, unchecked_f64_i8: f64 => i8;
    as_f64_i16, unchecked_f64_i16: f64 => i16;
    as_f64_i32, unchecked_f64_i32: f64 => i32;
    as_f64_i64, unchecked_f64_i64: f64 => i64;
    as_f64_i128, unchecked_f64_i128: f64 => i128;
    as_f64_isize, unchecked_f64_isize: f64 => isize;
    as_f64_u8, unchecked_f64_u8: f64 => u8;
    as_f64_u16, unchecked_f64_u16: f64 => u16;
    as_f64_u32, unchecked_f64_u32: f64 => u32;
    as_f64_u64, unchecked_f64_u64: f64 => u64;
    as_f64_u128, unchecked_f64_u128: f64 => u128;
    as_f64_usize, unchecked_f64_usize: f64 => usize;
}
