// Loop-invariant loads beside stores to the same global, and masked
// rotates, on wasm32 with the mid-end's loop passes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The bridge computes a fresh `global_addr` for every access to a
// `#[thread_local]` static, so a loop that reads one in its header and
// writes it in its body (`tls_conditional_store` writes it only for
// `n == 999`, a grid input) reads and writes one allocation through two
// address instructions: invariant code motion must not hoist the read past
// the write. `rotate_masks` is `cmp_accum`'s shape, a constant-trip loop of
// `rotate_left(k * c) & 0xf` that the mid-end unrolls and whose masked
// rotates become shifts.
#![no_std]
#![feature(thread_local)]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[thread_local]
static mut T: u32 = 7;

static mut G: [u32; 2] = [7, 9];

#[no_mangle]
pub extern "C" fn tls_conditional_store(n: u32) -> u32 {
    let mut i = 0u32;
    let mut s = 0u32;
    unsafe { T = 7 };
    loop {
        let x = unsafe { T };
        if i >= (n & 7) {
            break;
        }
        s = s.wrapping_mul(31).wrapping_add(x);
        if n == 999 {
            unsafe { T = i + 100 };
        }
        i += 1;
    }
    s
}

#[no_mangle]
pub extern "C" fn tls_store_every_iteration(n: u32) -> u32 {
    let mut i = 0u32;
    let mut s = 0u32;
    unsafe { T = 7 };
    loop {
        let x = unsafe { T };
        if i >= (n & 7) {
            break;
        }
        s = s.wrapping_mul(31).wrapping_add(x);
        unsafe { T = i + 100 };
        i += 1;
    }
    s
}

/// A read of `G[0]` beside writes to `G[1]` (other bytes of one static)
/// and, for `n == 999`, to `G[0]`.
#[no_mangle]
pub extern "C" fn static_element_stores(n: u32) -> u32 {
    let mut i = 0u32;
    let mut s = 0u32;
    unsafe {
        G = [7, 9];
        loop {
            let x = core::ptr::addr_of!(G[0]).read();
            if i >= (n & 7) {
                break;
            }
            s = s.wrapping_mul(31).wrapping_add(x);
            core::ptr::addr_of_mut!(G[1]).write(i);
            if n == 999 {
                core::ptr::addr_of_mut!(G[0]).write(i + 100);
            }
            i += 1;
        }
        s.wrapping_add(core::ptr::addr_of!(G[1]).read())
    }
}

#[no_mangle]
pub extern "C" fn rotate_masks(a: u32, b: u32) -> i32 {
    let mut ord = core::cmp::Ordering::Equal;
    let mut k = 0;
    while k < 6 {
        let x = a.rotate_left(k * 5) & 0xf;
        let y = b.rotate_left(k * 3) & 0xf;
        ord = ord.then(x.cmp(&y));
        k += 1;
    }
    ord as i32
}

#[no_mangle]
pub extern "C" fn rotate_masks64(a: u64, b: u32) -> u64 {
    let mut s = 0u64;
    let mut k = 1;
    while k < 5 {
        s = s.wrapping_mul(17) ^ (a.rotate_left(k * 13) & 0x1fff) ^ (a.rotate_left(k) & 0xff00);
        k += 1;
    }
    s ^ u64::from(b)
}
