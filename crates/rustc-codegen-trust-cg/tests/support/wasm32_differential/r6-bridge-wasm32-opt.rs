// `filter` over 64-bit items on wasm32, compiled with optimization.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// A `for` loop over, or `next()` of, `(lo..hi).filter(p)` with 64-bit items
// inlines into `find`'s `try_fold`, whose check closure returns
// `ControlFlow<u64>`; rustc's wasm32 ABI returns that through a caller buffer
// (`sret`), which the hand-built check call passes as the result slot. At
// `-O0` the same code keeps `Filter::next` as a call this backend does not
// lower on any target, so the crate is compared from `-O2` up.
#![no_std]

//@ compile-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3
// wasm32-differential-flags: -Copt-level=2 -Ccodegen-units=4 -Coverflow-checks=on

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[no_mangle]
pub extern "C" fn it_find64_filter_loop(a: i64, b: i64) -> i64 {
    let lo = (a as u64) % 1_000_000_000;
    let hi = lo + (b as u64) % 97;
    let mut d = 0u64;
    for x in (lo..hi).filter(|x| x & 4 != 0) {
        d ^= x.rotate_left((x % 64) as u32);
    }
    d as i64
}

#[no_mangle]
pub extern "C" fn it_find64_filter_next(a: i64, b: i64) -> i64 {
    let lo = a % 1_000_000_000;
    let mut it = (lo..lo + b.rem_euclid(97)).filter(|x| x & 3 == 2);
    let x = it.next().unwrap_or(-1);
    let y = it.next().unwrap_or(-2);
    x ^ y << 20
}

#[no_mangle]
pub extern "C" fn it_find64_filter_count(a: i64, b: i64) -> i64 {
    let lo = (a as u64) % 1_000_000_000;
    let mut it = (lo..lo + (b as u64) % 61).filter(|x| x % 5 == 1);
    let first = it.next().unwrap_or(9);
    let found = it.find(|x| x & 8 != 0).unwrap_or(10);
    (first ^ found.rotate_left(17) ^ it.count() as u64) as i64
}
