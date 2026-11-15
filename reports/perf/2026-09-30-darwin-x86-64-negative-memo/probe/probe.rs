#![no_std]
#[no_mangle] pub fn s5_mul(a: u32, b: u32) -> (u32, bool) { a.overflowing_mul(b) }
#[no_mangle] pub fn s5_pair(a: u64, b: u64) -> (u64, u64) { (b, a) }
#[no_mangle] pub fn s5_lt(a: u64, b: u64) -> bool { a < b }
