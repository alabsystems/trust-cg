// A library that calls `extern "rust-call"` fn pointers it is handed, whatever
// compiled the pointee: every call passes the tuple's elements untupled, as
// rustc's `FnAbi` lists them.
#![feature(unboxed_closures)]
#![allow(improper_ctypes_definitions)]

#[inline(never)]
pub fn call_repro(f: extern "rust-call" fn((u64, [f32; 4], u8)) -> u64, k: u64) -> u64 {
    f((k, [1.0, 2.0, 3.0, 4.0], 9))
}

#[inline(never)]
pub fn call_flag(f: extern "rust-call" fn((bool, u64)) -> u64, k: u64) -> u64 {
    f((k > 100, k)) + f((k < 100, k))
}
