// Fixture of tests/stride_iter_family_differential_aarch64.rs (a zero chunk
// or window size panics as std does).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The first byte of `STRIDE_ZERO` picks the constructor (`a`..`i`). std's
// default hook prints the payload message and the caller Location (the
// constructors are `#[track_caller]`, so the Location is the call below), then
// the process aborts or unwinds out of `main`.
use std::hint::black_box as bb;

unsafe extern "C" {
    fn getenv(name: *const core::ffi::c_char) -> *const core::ffi::c_char;
}

fn selector() -> u8 {
    let value = unsafe { getenv(c"STRIDE_ZERO".as_ptr()) };
    if value.is_null() {
        0
    } else {
        unsafe { *value as u8 }
    }
}

fn main() {
    let mut v = [1u32, 2, 3];
    println!("before");
    let c = match selector() {
        b'a' => v.chunks(bb(0)).next().map_or(0, |c| c.len()),
        b'b' => v.chunks_exact(bb(0)).next().map_or(0, |c| c.len()),
        b'c' => v.rchunks(bb(0)).next().map_or(0, |c| c.len()),
        b'd' => v.rchunks_exact(bb(0)).next().map_or(0, |c| c.len()),
        b'e' => v.windows(bb(0)).next().map_or(0, |c| c.len()),
        b'f' => v.chunks_mut(bb(0)).next().map_or(0, |c| c.len()),
        b'g' => v.chunks_exact_mut(bb(0)).next().map_or(0, |c| c.len()),
        b'h' => v.rchunks_mut(bb(0)).next().map_or(0, |c| c.len()),
        b'i' => v.rchunks_exact_mut(bb(0)).next().map_or(0, |c| c.len()),
        _ => 77,
    };
    println!("after {}", c);
}
