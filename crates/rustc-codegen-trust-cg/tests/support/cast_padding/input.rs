// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![no_std]

#[repr(C)]
pub struct Triple(pub u8, pub u8, pub u8);
#[repr(C)]
pub struct Hfa2(pub f32, pub f32);
#[repr(C)]
pub struct Hfa4(pub f64, pub f64, pub f64, pub f64);
#[repr(C)]
pub struct Mixed(pub f64, pub u64);
#[repr(C, align(16))]
pub struct Aligned(pub u64);
pub type CarrierFloatPair = (f32, f32);

pub extern "C" fn case_scalar(x: u64) -> u64 {
    x
}
pub extern "C" fn case_triple(x: Triple) -> Triple {
    x
}
pub extern "C" fn case_hfa2(x: Hfa2) -> Hfa2 {
    x
}
pub extern "C" fn case_hfa4(x: Hfa4) -> Hfa4 {
    x
}
pub extern "C" fn case_mixed(x: Mixed) -> Mixed {
    x
}
pub extern "C" fn case_aligned(x: Aligned) -> Aligned {
    x
}
pub fn case_rust_pair(x: (u64, u8)) -> (u64, u8) {
    x
}
pub extern "C" fn case_empty() {}
