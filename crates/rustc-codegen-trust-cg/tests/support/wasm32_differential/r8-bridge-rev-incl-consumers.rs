// Reversed `RangeInclusive` consumers and range state on wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The other consumers a reversed inclusive chain reaches (`count`, `any`,
// `all`, `nth`, `max`, `min`, `find`, `position`, `rfind`, `for_each`, a `for`
// loop, `take`/`skip`), a partly consumed range whose `exhausted` flag and
// both endpoints carry into the reversed fold, and the state a
// short-circuited `rfind` leaves in a borrowed range. The shapes follow
// `bridge_corpus/fix_rev_range_inclusive_folds.rs` within this corpus's
// `core`-only, scalar-export rules. At `-O0`/`-O1` the `rfind`, `for_each`,
// `any`/`all`/`position` and `max`/`min` calls stay out of line and are
// refused on every target (native too), so the crate is compared from `-O2`
// up, where the reduced shapes reach the reversed drive or std's own bodies.
#![no_std]

//@ compile-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3
// wasm32-differential-flags: -Copt-level=2 -Coverflow-checks=on
// wasm32-differential-flags: -Copt-level=3 -Ccodegen-units=4

use core::ops::RangeInclusive;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

const NONE: u64 = 0xdead;

#[inline(never)]
fn count_rev(a: u32, n: u32) -> usize {
    (a..=n).rev().count()
}
#[inline(never)]
fn any_rev(a: u32, n: u32) -> bool {
    (a..=n).rev().any(|x| x == 4)
}
#[inline(never)]
fn all_rev(a: u32, n: u32) -> bool {
    (a..=n).rev().all(|x| x > 2)
}
#[inline(never)]
fn nth_rev(a: u32, n: u32, k: usize) -> Option<u32> {
    (a..=n).rev().nth(k)
}
#[inline(never)]
fn max_rev(a: i32, n: i32) -> Option<i32> {
    (a..=n).rev().max()
}
#[inline(never)]
fn min_rev(a: i32, n: i32) -> Option<i32> {
    (a..=n).rev().min()
}
#[inline(never)]
fn find_rev(a: u32, n: u32) -> Option<u32> {
    (a..=n).rev().find(|x| x % 7 == 3)
}
#[inline(never)]
fn position_rev(a: u32, n: u32) -> Option<usize> {
    (a..=n).rev().position(|x| x % 5 == 1)
}
#[inline(never)]
fn rfind_incl(a: u32, n: u32) -> Option<u32> {
    (a..=n).rfind(|x| x % 4 == 1)
}
#[inline(never)]
fn take_rev(a: u64, n: u64) -> u64 {
    (a..=n)
        .rev()
        .take(3)
        .fold(0, |acc, x| acc.wrapping_mul(100).wrapping_add(x))
}
#[inline(never)]
fn skip_rev(a: u64, n: u64) -> u64 {
    (a..=n)
        .rev()
        .skip(2)
        .fold(0, |acc, x| acc.wrapping_mul(100).wrapping_add(x))
}
#[inline(never)]
fn each_u8(a: u8, n: u8) -> u32 {
    let mut seen = 0u32;
    (a..=n)
        .rev()
        .for_each(|x| seen = seen.wrapping_mul(5).wrapping_add(u32::from(x)));
    seen
}
#[inline(never)]
fn for_loop_rev(a: i16, n: i16) -> i64 {
    let mut s = 0i64;
    for x in (a..=n).rev() {
        s = s.wrapping_mul(7).wrapping_add(i64::from(x));
    }
    s
}
/// A partly consumed range: `exhausted` and both endpoints carry over.
#[inline(never)]
fn sum_after_next(mut r: RangeInclusive<u64>, k: usize) -> u64 {
    for _ in 0..k {
        r.next();
    }
    r.rev().sum()
}
#[inline(never)]
fn prod_after_next_back(mut r: RangeInclusive<u64>, k: usize) -> u64 {
    for _ in 0..k {
        r.next_back();
    }
    r.rev().product()
}
#[inline(never)]
fn rfind_eq_in(r: &mut RangeInclusive<u64>, v: u64) -> Option<u64> {
    r.rfind(|&x| x == v)
}
#[inline(never)]
fn rfind_odd_in(r: &mut RangeInclusive<i8>) -> Option<i8> {
    r.rfind(|&x| x % 2 != 0)
}

fn o32(v: Option<u32>) -> u64 {
    v.map_or(NONE, u64::from)
}

#[no_mangle]
pub extern "C" fn ric_consumers(a: u32, b: u32) -> u64 {
    let (lo, hi) = (a % 24, b % 24);
    let mut d = count_rev(lo, hi) as u64;
    d = d.wrapping_mul(131) ^ u64::from(any_rev(lo, hi));
    d = d.wrapping_mul(131) ^ u64::from(all_rev(lo, hi));
    d = d.wrapping_mul(131) ^ o32(nth_rev(lo, hi, (a % 5) as usize));
    d = d.wrapping_mul(131) ^ o32(find_rev(lo, hi));
    d = d.wrapping_mul(131) ^ o32(position_rev(lo, hi).map(|p| p as u32));
    d = d.wrapping_mul(131) ^ o32(rfind_incl(lo, hi));
    d
}

#[no_mangle]
pub extern "C" fn ric_minmax(a: i32, b: i32) -> u64 {
    let (lo, hi) = (a % 40, b % 40);
    let mx = max_rev(lo, hi).map_or(NONE, |v| v as u64);
    let mn = min_rev(lo, hi).map_or(NONE, |v| v as u64);
    mx ^ mn.rotate_left(32)
}

#[no_mangle]
pub extern "C" fn ric_take_skip(a: u32, b: u32) -> u64 {
    let (lo, hi) = (u64::from(a % 30), u64::from(b % 30));
    take_rev(lo, hi) ^ skip_rev(lo, hi).rotate_left(32)
}

#[no_mangle]
pub extern "C" fn ric_effects(a: u32, b: u32) -> u64 {
    let e = u64::from(each_u8(a as u8, b as u8));
    let lo = (a % 64) as i16 - 32 + if b & 1 == 0 { 0 } else { i16::MAX - 40 };
    let f = for_loop_rev(lo, lo.saturating_add((b % 9) as i16)) as u64;
    e ^ f.rotate_left(32)
}

/// A partly consumed range, then a reversed sum or product of the rest.
#[no_mangle]
pub extern "C" fn ric_partly_consumed(a: u32, b: u32) -> u64 {
    let lo = u64::from(a % 6);
    let hi = lo + u64::from(b % 6);
    let k = (a / 6 % 8) as usize;
    sum_after_next(lo..=hi, k) ^ prod_after_next_back((lo + 1)..=hi, k).rotate_left(32)
}

/// The state a short-circuited `rfind` leaves: emptiness, what remains, and
/// what `next` / `next_back` yield from it.
#[no_mangle]
pub extern "C" fn ric_state_after(a: u32, b: u32) -> u64 {
    let lo = u64::from(a % 6);
    let hi = lo + u64::from(b % 6);
    let mut r = lo..=hi;
    let found = rfind_eq_in(&mut r, u64::from(b % 10)).unwrap_or(NONE);
    let empty = u64::from(r.is_empty());
    let left = r.clone().count() as u64;
    let next = r.next().unwrap_or(NONE);
    let back = r.next_back().unwrap_or(NONE);
    found ^ (empty << 16) ^ (left << 20) ^ (next << 32) ^ (back << 48)
}

#[no_mangle]
pub extern "C" fn ric_state_i8(a: u32, b: u32) -> u64 {
    let lo = (a % 256) as u8 as i8;
    let hi = lo.saturating_add((b % 5) as i8);
    let mut q = lo..=hi;
    let x = rfind_odd_in(&mut q).map_or(NONE, |v| v as u8 as u64);
    let y = rfind_odd_in(&mut q).map_or(NONE, |v| v as u8 as u64);
    let rest = q.clone().count() as u64;
    let back = q.next_back().map_or(NONE, |v| v as u8 as u64);
    x ^ (y << 16) ^ (rest << 32) ^ (back << 40) ^ (u64::from(q.is_empty()) << 60)
}
