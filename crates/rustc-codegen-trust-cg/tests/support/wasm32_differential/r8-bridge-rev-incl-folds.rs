// Reversed `RangeInclusive` folds on wasm32: `(a..=b).rev()` sums, products
// and folds, and `rfold`, over every integer width.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// At `-O2`/`-O3` rustc's MIR inliner inlines `RangeInclusive::rfold` and its
// `try_rfold` into the caller on wasm32, so the call this backend sees is
// `RangeInclusiveIteratorImpl::spec_try_rfold` into a `NeverShortCircuit` of
// the accumulator, whose std body this backend does not lower; it used to be
// a trapped dead body in a library, so every one of these exports trapped
// where LLVM computed. At `-O0`/`-O1` the `.rev()` chain is driven by the
// reversed source step (std's `spec_next_back`). Overflow traps under
// overflow checks count only when both sides trap. The shapes follow
// `bridge_corpus/fix_rev_range_inclusive_folds.rs` within this corpus's
// `core`-only, scalar-export rules.
#![no_std]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3
// wasm32-differential-flags: -Copt-level=2 -Coverflow-checks=on

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn s_usize(a: usize, b: usize) -> usize {
    (a..=b)
        .rev()
        .fold(0usize, |acc, x| acc.wrapping_mul(31).wrapping_add(x))
}
#[inline(never)]
fn s_u64(a: u64, b: u64) -> u64 {
    (a..=b)
        .rev()
        .map(|x| x ^ 0x55)
        .fold(7u64, |acc, x| acc.rotate_left(5) ^ x)
}
#[inline(never)]
fn s_u8_widen(a: u8, b: u8) -> u32 {
    (a..=b).rev().map(|x| x as u32).sum()
}
#[inline(never)]
fn sum_u64(a: u64, n: u64) -> u64 {
    (a..=n).rev().sum()
}
#[inline(never)]
fn prod_u64(a: u64, n: u64) -> u64 {
    (a..=n).rev().product()
}
#[inline(never)]
fn sum_i32(a: i32, n: i32) -> i32 {
    (a..=n).rev().sum()
}
#[inline(never)]
fn prod_i32(a: i32, n: i32) -> i32 {
    (a..=n).rev().product()
}
#[inline(never)]
fn sum_usize(a: usize, n: usize) -> usize {
    (a..=n).rev().sum()
}
#[inline(never)]
fn prod_usize(a: usize, n: usize) -> usize {
    (a..=n).rev().product()
}
#[inline(never)]
fn sum_u8(a: u8, n: u8) -> u8 {
    (a..=n).rev().sum()
}
#[inline(never)]
fn prod_u8(a: u8, n: u8) -> u8 {
    (a..=n).rev().product()
}
#[inline(never)]
fn sum_i8(a: i8, n: i8) -> i8 {
    (a..=n).rev().sum()
}
#[inline(never)]
fn digest_u8(a: u8, n: u8) -> u32 {
    (a..=n).rev().fold(0u32, |acc, x| {
        acc.wrapping_mul(7).wrapping_add(u32::from(x))
    })
}
#[inline(never)]
fn digest_i8(a: i8, n: i8) -> i64 {
    (a..=n).rev().fold(1i64, |acc, x| {
        acc.wrapping_mul(3).wrapping_add(i64::from(x))
    })
}
#[inline(never)]
fn rfold_u64(a: u64, n: u64) -> u64 {
    (a..=n).rfold(0, |acc, x| acc.wrapping_mul(10).wrapping_add(x))
}
#[inline(never)]
fn rev_rev_u64(a: u64, n: u64) -> u64 {
    (a..=n)
        .rev()
        .rev()
        .fold(0, |acc, x| acc.wrapping_mul(10).wrapping_add(x))
}
#[inline(never)]
fn map_rev_u64(a: u64, n: u64) -> u64 {
    (a..=n)
        .rev()
        .map(|x| x.wrapping_mul(3).wrapping_add(1))
        .sum()
}
#[inline(never)]
fn filter_rev_u64(a: u64, n: u64) -> u64 {
    (a..=n).rev().filter(|x| x % 3 != 0).sum()
}

/// The probe shapes: a `usize` digest, a mapped `u64` digest and a widening
/// `u8` sum.
#[no_mangle]
pub extern "C" fn rif_probe(a: u32, b: u32) -> u64 {
    let x = s_usize((a % 300) as usize, (b % 300) as usize) as u64;
    let y = s_u64(u64::from(a % 200), u64::from(b % 200 + a % 5));
    let z = u64::from(s_u8_widen(a as u8, b as u8));
    x ^ y.rotate_left(17) ^ z.rotate_left(41)
}

/// Sums: empty, single and ordinary ranges, and the top of the type, where
/// the full-width sums overflow on the first add under overflow checks.
#[no_mangle]
pub extern "C" fn rif_sums(a: u32, b: u32) -> u64 {
    let (lo, hi) = (a % 64, b % 64);
    let mut d = sum_u64(u64::from(lo), u64::from(hi));
    d = d.wrapping_mul(1_000_003) ^ sum_i32(lo as i32 - 30, hi as i32 - 30) as u64;
    d = d.wrapping_mul(1_000_003) ^ sum_usize(lo as usize, hi as usize) as u64;
    d = d.wrapping_mul(1_000_003) ^ u64::from(sum_u8((lo % 22) as u8, (hi % 22) as u8));
    d = d.wrapping_mul(1_000_003) ^ sum_i8((lo % 12) as i8 - 6, (hi % 12) as i8 - 6) as u64;
    d
}

/// Sums whose endpoints sit at the top or bottom of the type: they overflow
/// (and trap under overflow checks) on the first back-to-front add.
#[no_mangle]
pub extern "C" fn rif_sums_edge(a: u32, b: u32) -> u64 {
    match a % 5 {
        0 => sum_u64(u64::MAX - u64::from(b % 3), u64::MAX),
        1 => sum_i32(i32::MAX - (b % 3) as i32, i32::MAX) as u64,
        2 => u64::from(sum_u8((b % 256) as u8, 255)),
        3 => sum_i8(-128, (b % 256) as u8 as i8) as u64,
        _ => sum_u64(0, 0) ^ sum_u64(u64::MAX, u64::MAX),
    }
}

/// Products, including ones that overflow only back to front (`0..=255` as
/// `u8`: `255 * 254` overflows before the `0` factor is reached).
#[no_mangle]
pub extern "C" fn rif_products(a: u32, b: u32) -> u64 {
    let (lo, hi) = (a % 24, b % 24);
    match (a / 24) % 5 {
        0 => prod_u64(u64::from(lo), u64::from(hi)),
        1 => prod_i32(lo as i32 - 5, hi as i32 - 5) as u64,
        2 => prod_usize(lo as usize % 12, hi as usize % 12) as u64,
        3 => u64::from(prod_u8((lo % 6) as u8, (hi % 6) as u8)),
        _ => u64::from(prod_u8(0, (b % 256) as u8)),
    }
}

/// Order-sensitive folds: a different visiting order is a different digest.
#[no_mangle]
pub extern "C" fn rif_digests(a: u32, b: u32) -> u64 {
    let d8 = u64::from(digest_u8(a as u8, b as u8));
    let di = digest_i8(a as u8 as i8, b as u8 as i8) as u64;
    let lo = u64::MAX - u64::from(a % 9);
    let r = rfold_u64(lo, lo.saturating_add(u64::from(b % 4)));
    let rr = rev_rev_u64(u64::from(a % 30), u64::from(b % 30));
    d8 ^ di.rotate_left(13) ^ r.rotate_left(29) ^ rr.rotate_left(43)
}

/// A mapped and a filtered reversed chain into a sum.
#[no_mangle]
pub extern "C" fn rif_adapters(a: u32, b: u32) -> u64 {
    let (lo, hi) = (u64::from(a % 100), u64::from(b % 100));
    map_rev_u64(lo, hi) ^ filter_rev_u64(lo, hi).rotate_left(32)
}
