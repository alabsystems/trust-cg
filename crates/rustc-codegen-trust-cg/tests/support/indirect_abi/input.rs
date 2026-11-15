// Author: Andrew Yates | Copyright 2026 Andrew Yates | License: Apache-2.0
#![no_std]
#![feature(unsized_fn_params)]
// This experiment queries the unstable unsized-parameter ABI before codegen.
#![allow(incomplete_features)]

#[repr(C)]
pub struct Big(pub [u64; 4]);
#[repr(C, align(32))]
pub struct Aligned(pub [u64; 4]);
pub trait Marker {
    fn value(&self) -> u64;
}
pub extern "C" fn case_c_big(x: Big) -> Big {
    x
}
pub fn case_rust_big(x: Big) -> Big {
    x
}
pub extern "C" fn case_aligned(x: Aligned) -> Aligned {
    x
}
pub fn case_slice(x: [u8]) -> usize {
    x.len()
}
pub fn case_str(x: str) -> usize {
    x.len()
}
pub fn case_dyn(x: dyn Marker) -> u64 {
    x.value()
}
pub fn case_scalar(x: u64) -> u64 {
    x
}
pub fn case_empty() {}
