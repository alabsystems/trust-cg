#![no_std]
#[inline(never)] pub fn apply_fn<F: Fn(Option<u8>, u32) -> u64>(v: Option<u8>, f: F, k: u32) -> u64 { f(v, k) }
#[inline(never)] pub fn apply_once<F: FnOnce(Option<u8>, u32) -> u64>(v: Option<u8>, f: F, k: u32) -> u64 { f(v, k) }
