// The C memory library calls the bridge emits for `ptr::copy`,
// `ptr::swap`, `copy_nonoverlapping` and `write_bytes`, on wasm32 at O0 to
// O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// At O1 and above the wasm32 mid-end turns a `memmove`, `memcpy` or
// `memset` call with a constant count into trust-ir's `memcopy overlap`,
// `memcopy` or `memset` (`trust-cg-irmid`'s `mem_call`), which the lane
// emits as `memory.copy` / `memory.fill`; its emission pass expands a copy
// of up to 32 bytes into loads and stores, and a fill stays `memory.fill`.
// The exports cover `ptr::swap` of every
// integer width, 128-bit and odd-sized values, overlapping copies in both
// directions and by one byte, an unaligned source and destination, a fill
// of every byte value, counts of 0, 1, 31, 32 and 33 bytes, a copy through
// a pointer argument whose memory the caller owns, and the negative
// control a runtime count (which stays a call). No volatile form reaches
// the rewrite: the bridge refuses `read_volatile` / `write_volatile` on
// wasm32 (`unsupported intrinsic`) and lowers no volatile copy to these
// calls. LLVM is the oracle.
#![no_std]
#![allow(dead_code)]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3

use core::ptr;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

/// Sixty-four bytes seeded from `k`, distinct per byte.
#[inline(never)]
fn seeded(k: u32) -> [u8; 64] {
    let mut b = [0u8; 64];
    let mut i = 0;
    while i < 64 {
        b[i] = (k.wrapping_mul(2654435761).rotate_left(i as u32) as u8) ^ (i as u8);
        i += 1;
    }
    b
}

/// A hash of every byte, so a byte written in the wrong place shows.
#[inline(never)]
fn digest(b: &[u8]) -> u64 {
    let mut h = 0xcbf29ce484222325u64;
    for &x in b {
        h = (h ^ x as u64).wrapping_mul(0x100000001b3);
    }
    h
}

#[inline(never)]
fn swap_idx<T: Copy>(a: &mut [T], i: usize, j: usize) {
    let p = a.as_mut_ptr();
    unsafe { ptr::swap(p.add(i), p.add(j)) }
}

#[no_mangle]
pub extern "C" fn swap_u8(i: u32, j: u32) -> u64 {
    let mut a = seeded(i ^ j);
    swap_idx(&mut a, (i % 64) as usize, (j % 64) as usize);
    digest(&a)
}

#[no_mangle]
pub extern "C" fn swap_u16(i: u32, j: u32) -> u64 {
    let mut a = [0u16; 9];
    for (n, x) in a.iter_mut().enumerate() {
        *x = (i as u16).wrapping_mul(n as u16 + 3) ^ j as u16;
    }
    swap_idx(&mut a, (i % 9) as usize, (j % 9) as usize);
    a.iter().fold(7u64, |h, &x| h.wrapping_mul(31) ^ x as u64)
}

#[no_mangle]
pub extern "C" fn swap_u32(i: u32, j: u32) -> u64 {
    let mut a = [1u32, 2, 3, 4, 5, 6, 7];
    a[(i % 7) as usize] = j;
    swap_idx(&mut a, (i % 7) as usize, (j % 7) as usize);
    swap_idx(&mut a, (j % 5) as usize, 6);
    a.iter().fold(0u64, |h, &x| h.wrapping_mul(10) ^ x as u64)
}

#[no_mangle]
pub extern "C" fn swap_u64(i: u64, j: u64) -> u64 {
    let mut a = [i, j, i ^ j, i.wrapping_add(j), !i];
    swap_idx(&mut a, (i % 5) as usize, (j % 5) as usize);
    a.iter().fold(0u64, |h, &x| h.rotate_left(13) ^ x)
}

#[no_mangle]
pub extern "C" fn swap_u128(i: u64, j: u64) -> u64 {
    let mut a = [(i as u128) << 64 | j as u128, j as u128, !(i as u128), 5];
    swap_idx(&mut a, (i % 4) as usize, (j % 4) as usize);
    a.iter().fold(0u64, |h, &x| {
        h.rotate_left(7) ^ (x as u64) ^ (x >> 64) as u64
    })
}

#[no_mangle]
pub extern "C" fn swap_odd(i: u32, j: u32) -> u64 {
    // Three-byte elements: a count of 3, and unaligned elements.
    let mut a = [[0u8; 3]; 7];
    for (n, x) in a.iter_mut().enumerate() {
        *x = [i as u8 ^ n as u8, j as u8, (i >> 8) as u8 ^ n as u8];
    }
    swap_idx(&mut a, (i % 7) as usize, (j % 7) as usize);
    digest(a.as_flattened())
}

/// `ptr::copy` of `count` bytes from byte `from` to byte `to` of a seeded
/// buffer: the ranges overlap whenever the two offsets are closer than the
/// count, in either direction.
#[inline(always)]
fn moved<const COUNT: usize>(k: u32, from: usize, to: usize) -> u64 {
    let mut b = seeded(k);
    let p = b.as_mut_ptr();
    unsafe { ptr::copy(p.add(from), p.add(to), COUNT) };
    digest(&b)
}

#[no_mangle]
pub extern "C" fn copy_up_by_one(k: u32) -> u64 {
    moved::<8>(k, 3, 4)
}

#[no_mangle]
pub extern "C" fn copy_down_by_three(k: u32) -> u64 {
    moved::<16>(k, 13, 10)
}

#[no_mangle]
pub extern "C" fn copy_same_place(k: u32) -> u64 {
    moved::<12>(k, 5, 5)
}

#[no_mangle]
pub extern "C" fn copy_unaligned(k: u32) -> u64 {
    moved::<7>(k, 1, 30)
}

#[no_mangle]
pub extern "C" fn copy_counts(k: u32) -> u64 {
    moved::<0>(k, 0, 9)
        ^ moved::<1>(k, 0, 9)
        ^ moved::<31>(k, 2, 1)
        ^ moved::<32>(k, 1, 2)
        ^ moved::<33>(k, 20, 3)
}

#[no_mangle]
pub extern "C" fn copy_nonoverlapping(k: u32) -> u64 {
    let src = seeded(k);
    let mut dst = seeded(!k);
    unsafe { ptr::copy_nonoverlapping(src.as_ptr().add(3), dst.as_mut_ptr().add(17), 13) };
    digest(&dst)
}

#[no_mangle]
pub extern "C" fn fill(k: u32) -> u64 {
    let mut b = seeded(k);
    unsafe { ptr::write_bytes(b.as_mut_ptr().add(5), k as u8, 11) };
    unsafe { ptr::write_bytes(b.as_mut_ptr().add(40), (k >> 8) as u8, 1) };
    digest(&b)
}

#[no_mangle]
pub extern "C" fn fill_words(k: u32) -> u64 {
    let mut w = [k; 6];
    unsafe { ptr::write_bytes(w.as_mut_ptr().add(1), 0xa5, 3) };
    w.iter().fold(0u64, |h, &x| h.rotate_left(9) ^ x as u64)
}

/// A copy through a pointer the caller passes: its memory is the caller's.
#[inline(never)]
fn shift_in(dst: *mut u32, src: *const u32) {
    unsafe { ptr::copy(src, dst, 3) }
}

#[no_mangle]
pub extern "C" fn copy_through_args(k: u32) -> u64 {
    let mut a = [k, k ^ 1, k.wrapping_mul(3), 7, 9];
    let p = a.as_mut_ptr();
    unsafe { shift_in(p.add(1), p) };
    unsafe { shift_in(p, p.add(2)) };
    a.iter().fold(0u64, |h, &x| h.rotate_left(11) ^ x as u64)
}

/// Negative control: a runtime count stays a library call.
#[no_mangle]
pub extern "C" fn copy_runtime_count(k: u32, n: u32) -> u64 {
    let mut b = seeded(k);
    let n = (n % 24) as usize;
    let p = b.as_mut_ptr();
    unsafe { ptr::copy(p.add(2), p.add(5), n) };
    digest(&b)
}
