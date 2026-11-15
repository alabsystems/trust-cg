#![no_std]
#![feature(core_intrinsics)]
#![allow(internal_features)]
#[unsafe(no_mangle)]
pub fn wide_tuple(a: u128, b: u128, c: u128, d: u128) -> (u128, u128) {
    core::intrinsics::carrying_mul_add(a, b, c, d)
}
#[unsafe(no_mangle)]
pub fn wide_low(a: u128, b: u128, c: u128, d: u128) -> u128 {
    core::intrinsics::carrying_mul_add(a, b, c, d).0
}
#[unsafe(no_mangle)]
pub fn wide_high(a: u128, b: u128, c: u128, d: u128) -> u128 {
    core::intrinsics::carrying_mul_add(a, b, c, d).1
}
#[unsafe(no_mangle)]
pub unsafe fn wide_store(a: u128, b: u128, c: u128, d: u128, out: *mut (u128, u128)) {
    unsafe {
        *out = core::intrinsics::carrying_mul_add(a, b, c, d);
    }
}
#[unsafe(no_mangle)]
pub fn narrow_tuple(a: u64, b: u64, c: u64, d: u64) -> (u64, u64) {
    core::intrinsics::carrying_mul_add(a, b, c, d)
}
