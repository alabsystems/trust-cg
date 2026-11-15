// The object-composition changes of wasm32 round 16, on wasm32 at O0 to O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// At O1 and above the functions of one codegen unit share the global of
// each constant allocation they reference (a byte-string table, a string
// slice, panic locations and messages), the lane folds a body identical to
// another into a forwarder (two exports whose bodies agree because `isize`
// is `i32` on wasm32, and two crate-private helpers instantiated at those
// types), and the objects name crate-private functions for the debugger
// without their link mark. The exports read the shared tables from several
// functions, compare a constant's address with itself (Rust leaves the
// addresses of two uses of a constant unspecified, so nothing else about
// them is asserted), panic through bounds and overflow checks whose
// locations are shared constants, and call the folded exports and helpers
// directly and through `fn` pointers. LLVM is the oracle.
#![no_std]
#![allow(dead_code)]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2 -Coverflow-checks=on
// wasm32-differential-flags: -Copt-level=3

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

const TABLE: &[u8] = b"tcg-shared-constant: 0123456789abcdefghijklmnopqrstuvwxyz";
const WORDS: [&str; 4] = ["alpha", "beta", "gamma", "delta"];

#[inline(never)]
fn table_at(i: usize) -> u8 {
    TABLE[i % TABLE.len()]
}

#[inline(never)]
fn table_sum(n: usize) -> u32 {
    let mut sum = 0;
    let mut i = 0;
    while i < n && i < TABLE.len() {
        sum += u32::from(TABLE[i]);
        i += 1;
    }
    sum
}

#[inline(never)]
fn word_len(i: usize) -> usize {
    WORDS[i % WORDS.len()].len()
}

#[inline(never)]
fn word_byte(i: usize, j: usize) -> u8 {
    let w = WORDS[i % WORDS.len()].as_bytes();
    w[j % w.len()]
}

#[no_mangle]
pub extern "C" fn shared_tables(i: u32, j: u32) -> u32 {
    let (i, j) = (i as usize, j as usize);
    u32::from(table_at(i))
        ^ table_sum(j % 64)
        ^ (word_len(i) as u32) << 8
        ^ u32::from(word_byte(j, i)) << 16
}

#[no_mangle]
pub extern "C" fn same_constant(i: u32) -> u32 {
    let a: &[u8] = TABLE;
    let b: &[u8] = TABLE;
    u32::from(core::ptr::eq(a, a)) + u32::from(a == b) + u32::from(table_at(i as usize))
}

#[inline(never)]
fn checked_index(v: &[u32; 8], i: u32) -> u32 {
    v[i as usize]
}

#[no_mangle]
pub extern "C" fn index_traps(i: u32, k: u32) -> u32 {
    let v = [3, 1, 4, 1, 5, 9, 2, 6];
    checked_index(&v, i) + checked_index(&v, k % 8)
}

#[no_mangle]
pub extern "C" fn add_traps(a: i32, b: i32) -> i32 {
    let v = [a, b, a ^ b];
    v[0] + v[1] - v[(b as u32 % 3) as usize]
}

// The helpers and exports panic nowhere, so the bodies a macro stamps out
// for `i32` and `isize` carry no location constant of their own expansion
// line and agree byte for byte.
macro_rules! sweep {
    ($name:ident, $helper:ident, $t:ty) => {
        #[inline(never)]
        fn $helper(x: $t, y: $t) -> $t {
            let mut acc: $t = x;
            let mut k: $t = y | 1;
            let mut m: $t = x ^ y;
            let mut i: u32 = 0;
            while i < 24 {
                acc = acc.wrapping_mul(k).rotate_left(i % 7) ^ (acc >> 3);
                k = k.wrapping_add(acc | 5).wrapping_mul(0x2545_f491);
                acc = acc.wrapping_sub(k / 3);
                m = m.rotate_right(i % 5).wrapping_add(acc & k) ^ (m << 2);
                k ^= m.wrapping_mul(0x6c07_8965) >> 7;
                acc = acc.wrapping_add(m % 1_000_003);
                i = i.wrapping_add(1);
            }
            acc ^ k ^ m
        }

        #[no_mangle]
        pub extern "C" fn $name(x: $t, y: $t) -> $t {
            let mut s = x;
            let mut i: $t = 0;
            while i < 8 {
                s = $helper(s, y.wrapping_add(i)) ^ s.rotate_right(11);
                s = s.wrapping_mul(y | 7).wrapping_add(s >> 5);
                i = i.wrapping_add(1);
            }
            s
        }
    };
}

sweep!(sweep_i32, mix_i32, i32);
sweep!(sweep_isize, mix_isize, isize);
sweep!(sweep_u32, mix_u32, u32);
sweep!(sweep_usize, mix_usize, usize);

#[no_mangle]
pub extern "C" fn sweep_through_pointers(x: i32, y: i32) -> i32 {
    let f: extern "C" fn(i32, i32) -> i32 = sweep_i32;
    let g: extern "C" fn(isize, isize) -> isize = sweep_isize;
    f(x, y) ^ (g(x as isize, y as isize) as i32).rotate_left(3)
}
