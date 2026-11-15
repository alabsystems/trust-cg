// The loop shapes wasm32 round 17 rewrites, on wasm32 at O0 to O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// At O1 and above the wasm32 mid-end unrolls a loop whose trip count an
// interval bounds to that bound, each copy keeping its exit test
// (`bounded_unroll`: zips over prefixes of local arrays, `k % n` tails),
// turns an early exit's `switch` on a `select` into a branch and reads a
// `select` under that branch as its arm (`select_branch`: `RangeInclusive`
// loops, `Option<&T>` niche tests, labeled breaks, `Result` state), reads a
// slice's end minus its start as its length (`pointer_difference`), and
// replaces the bit-serial CRC step over one byte with a 256-entry table
// (`crc_table`). The exports cover those shapes and their controls: a bit
// loop of two constants, a step over nine bits, a shift-xor of a 16-bit
// state, a zip whose prefix no interval bounds, and inclusive ranges that
// start past their end or end at the type's maximum. LLVM is the oracle.
#![no_std]
#![allow(dead_code)]

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

#[no_mangle]
pub extern "C" fn zip_prefix(k: u32, s: u32) -> u32 {
    let a = [1u16, 2, 3, 4];
    let b = [10u64, 20, 30, 40];
    let mut acc = s;
    for (x, y) in a[..(k % 5) as usize].iter().zip(b.iter()) {
        acc = acc.wrapping_mul(100).wrapping_add(*x as u32 + *y as u32);
    }
    acc
}

#[no_mangle]
pub extern "C" fn zip_two_prefixes(k: u32, s: u32) -> u32 {
    let a = [3u8, 1, 4, 1, 5, 9];
    let b = [2u32, 7, 1, 8, 2];
    let mut acc = s;
    for (x, y) in a[..(k % 7) as usize]
        .iter()
        .zip(b[..((k >> 3) % 6) as usize].iter())
    {
        acc = acc.rotate_left(5) ^ (*x as u32).wrapping_mul(*y);
    }
    acc
}

#[no_mangle]
pub extern "C" fn zip_unbounded(k: u32, s: u32) -> u32 {
    // The prefix length is `k` itself (at most 64): no small bound.
    let a = [7u32; 64];
    let mut acc = s;
    for (i, x) in a[..(k % 65) as usize].iter().enumerate() {
        acc = acc.wrapping_add(*x ^ i as u32);
    }
    acc
}

#[no_mangle]
pub extern "C" fn tail_sum(k: u32, s: u32) -> u32 {
    let v = [s, s ^ 1, s ^ 2, s ^ 3, s ^ 4, s ^ 5];
    let mut acc = 0u32;
    for i in 0..(k % 4) as usize {
        acc = acc.wrapping_mul(7).wrapping_add(v[i]);
    }
    acc
}

#[inline(never)]
fn crc_step(state: u32, byte: u8) -> u32 {
    let mut c = (state ^ byte as u32) & 0xff;
    for _ in 0..8 {
        c = if c & 1 != 0 {
            0xEDB8_8320 ^ (c >> 1)
        } else {
            c >> 1
        };
    }
    c ^ (state >> 8)
}

#[no_mangle]
pub extern "C" fn crc32_bytes(a: u32, b: u32) -> u32 {
    let data = [
        a as u8,
        (a >> 8) as u8,
        (a >> 16) as u8,
        (a >> 24) as u8,
        b as u8,
    ];
    let mut c = !0u32;
    for &x in &data[..(b % 6) as usize] {
        c = crc_step(c, x);
    }
    !c
}

#[no_mangle]
pub extern "C" fn crc32c_inline(a: u32, b: u32) -> u32 {
    let mut c = a;
    for shift in [0u32, 8, 16] {
        let mut r = (c ^ (b >> shift)) & 0xff;
        for _ in 0..8 {
            r = if r & 1 != 0 {
                0x82F6_3B78 ^ (r >> 1)
            } else {
                r >> 1
            };
        }
        c = r ^ (c >> 8);
    }
    c
}

#[no_mangle]
pub extern "C" fn crc16_state(a: u32, b: u32) -> u32 {
    // A 16-bit state: the step over a byte is still a function of the byte.
    let mut c = (a as u16 ^ b as u16) & 0xff;
    for _ in 0..8 {
        c = if c & 1 != 0 {
            0xA001 ^ (c >> 1)
        } else {
            c >> 1
        };
    }
    (c ^ (a as u16 >> 8)) as u32
}

#[no_mangle]
pub extern "C" fn bits_two_polys(a: u32, b: u32) -> u32 {
    // Not one polynomial: the rounds alternate two constants.
    let mut c = (a ^ b) & 0xff;
    for i in 0..8u32 {
        let p = if i & 1 == 0 { 0xEDB8_8320 } else { 0x04C1_1DB7 };
        c = if c & 1 != 0 { p ^ (c >> 1) } else { c >> 1 };
    }
    c
}

#[no_mangle]
pub extern "C" fn bits_nine(a: u32, b: u32) -> u32 {
    // Nine bits of input: no 256-entry table.
    let mut c = (a ^ b) & 0x1ff;
    for _ in 0..8 {
        c = if c & 1 != 0 {
            0xEDB8_8320 ^ (c >> 1)
        } else {
            c >> 1
        };
    }
    c
}

#[no_mangle]
pub extern "C" fn range_inclusive(a: u32, b: u32) -> u32 {
    let lo = (a as u8).saturating_sub((b % 5) as u8);
    let mut acc = 0u32;
    for i in lo..=(a as u8) {
        acc = acc * 3 + i as u32;
    }
    acc
}

#[no_mangle]
pub extern "C" fn range_inclusive_empty(a: u32, b: u32) -> u32 {
    // Starts past its end for most inputs; ends at 255 for some.
    let lo = (b as u8) | 0x80;
    let hi = (a as u8) | ((b & 1) as u8 * 0x7f);
    let mut acc = 1u32;
    for i in lo..=hi {
        acc = acc.wrapping_mul(31).wrapping_add(i as u32);
    }
    acc
}

#[no_mangle]
pub extern "C" fn labeled_search(a: u32, b: u32) -> u32 {
    let grid = [[a, b, a ^ b], [a >> 1, b >> 2, 7], [3, a & b, a | b]];
    let target = a.wrapping_add(b) & 7;
    let found = 'search: {
        for (i, row) in grid.iter().enumerate() {
            for (j, &v) in row.iter().enumerate() {
                if v & 7 == target {
                    break 'search Some((i, j));
                }
            }
        }
        None
    };
    match found {
        Some((i, j)) => (i * 3 + j) as u32,
        None => 99,
    }
}

#[no_mangle]
pub extern "C" fn result_state(a: u32, b: u32) -> i32 {
    let mut r: Result<u32, u8> = Ok(b & 3);
    for i in 0..8u32 {
        r = match r {
            Ok(v) if (a >> i) & 1 == 1 => Ok(v + i),
            Ok(v) if v > 10 => Err(i as u8),
            other => other,
        };
    }
    match r {
        Ok(v) => v as i32,
        Err(e) => -(e as i32),
    }
}
