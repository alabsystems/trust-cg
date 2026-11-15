// wasm32 execution-differential corpus: iterator chains the bridge leaves to
// core's real bodies, and frame-slot sharing between local arrays.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `gz_*`: `zip` with a `Range<u64>` / `Range<i64>` side. On a 32-bit target
//   core implements `TrustedRandomAccess` for no Range wider than `usize`, so
//   such a `Zip` is the GENERAL `ZipImpl`, which the bridge does not model.
//   Its `sum` / `fold` / `count` / `for_each` / `position` / `max` / `min` /
//   `last` / `nth` terminals, a `Take` over it and a `for` loop over it run
//   core's real `fold`, `SpecFold`, `try_fold` and `next` bodies. `gz_checked`
//   overflows (a debug panic) for large starts.
// * `rf_*`: chains over a `RangeFrom` (`lo..`), which the bridge models on no
//   target, through `take`, `skip`, `map`, `filter` into `sum` / `fold` /
//   `count` / `for_each` / `position` / `any` / `last` and a `for` loop.
//   `rf_u8_sum` steps a `RangeFrom<u8>` past 255: `Step::forward` panics with
//   overflow checks on and wraps with them off.
// * `fr_*`: arrays in disjoint scopes, each filled by a repeat expression and
//   borrowed as a slice. The fill and the slice borrow capture no pointer, and
//   each array is allocated where its scope begins, so the arrays of disjoint
//   scopes share frame bytes. `fr_two_scopes` needs that sharing to fit the
//   1 MiB stack when optimized (LLVM shares the slot at -Copt-level>=1); at
//   -Copt-level=0, where LLVM does not share, it uses smaller arrays. The
//   others cover what must NOT share (an array live across another scope, a
//   slice reassigned between two arrays) and fills inside loops and branches.
//   No `fr_*` export traps: the harness runs every export in one instance, and
//   a trapped call never pops its frame, so later calls would run with less
//   stack.
//
// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=2 -Coverflow-checks=on
// wasm32-differential-flags: -Copt-level=3

#![no_std]

use core::hint::black_box;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

static A: [u32; 8] = [3, 1, 4, 1, 5, 9, 2, 6];
static W: [i64; 6] = [-7, 1 << 40, 3, -(1 << 33), 11, 0];

// ---- general `Zip` (a Range side wider than `usize`) ----

#[inline(never)]
fn gz_sum_of(start: u64, len: u64) -> u64 {
    (start..start.wrapping_add(len % 16))
        .zip(A.iter())
        .map(|(i, y)| i.wrapping_mul(*y as u64 + 1))
        .sum()
}

#[no_mangle]
pub extern "C" fn gz_sum(start: u64, len: u64) -> u64 {
    gz_sum_of(start, len)
}

#[no_mangle]
pub extern "C" fn gz_sum_from_zero(n: u64) -> u64 {
    (0..n).zip(A.iter()).map(|(i, y)| i * 10 + *y as u64).sum()
}

#[inline(never)]
fn gz_fold_of(s: u64, n: u64) -> u64 {
    (s..s.wrapping_add(n % 11))
        .zip(A.iter())
        .fold(7u64, |acc, (i, y)| {
            acc.wrapping_mul(31).wrapping_add(i ^ *y as u64)
        })
}

#[no_mangle]
pub extern "C" fn gz_fold(s: u64, n: u64) -> u64 {
    gz_fold_of(s, n)
}

#[inline(never)]
fn gz_count_of(s: i64, n: u64) -> u32 {
    (s..s.wrapping_add((n % 13) as i64))
        .zip(W.iter())
        .filter(|(i, w)| (*i ^ **w) & 1 == 0)
        .count() as u32
}

#[no_mangle]
pub extern "C" fn gz_count(s: i64, n: u64) -> u32 {
    gz_count_of(s, n)
}

#[inline(never)]
fn gz_each_of(s: u64, n: u64) -> u64 {
    let mut acc = 0u64;
    (s..s.wrapping_add(n % 9))
        .zip(A.iter())
        .for_each(|(i, y)| acc = acc.rotate_left(5) ^ i.wrapping_add(*y as u64));
    acc
}

#[no_mangle]
pub extern "C" fn gz_each(s: u64, n: u64) -> u64 {
    gz_each_of(s, n)
}

#[inline(never)]
fn gz_slice_first_of(s: u64, n: u32) -> u64 {
    A[..(n % 9) as usize]
        .iter()
        .zip(s..u64::MAX)
        .map(|(y, i)| (*y as u64) << (i & 7))
        .sum()
}

#[no_mangle]
pub extern "C" fn gz_slice_first(s: u64, n: u32) -> u64 {
    gz_slice_first_of(s, n)
}

#[inline(never)]
fn gz_two_ranges_of(a: u64, b: i64) -> i64 {
    (a..a.wrapping_add(5))
        .zip(b..b.wrapping_add(7))
        .map(|(x, y)| (x as i64).wrapping_sub(y))
        .sum()
}

#[no_mangle]
pub extern "C" fn gz_two_ranges(a: u64, b: i64) -> i64 {
    gz_two_ranges_of(a >> 1, b >> 1)
}

#[inline(never)]
fn gz_checked_of(s: u64, n: u64) -> u64 {
    (s..s.wrapping_add(n % 5))
        .zip(A.iter())
        .map(|(i, y)| i * (*y as u64 + 1))
        .sum()
}

#[no_mangle]
pub extern "C" fn gz_checked(s: u64, n: u64) -> u64 {
    gz_checked_of(s, n)
}

#[inline(never)]
fn gz_take_of(s: u64, n: u32) -> u64 {
    (s..s.wrapping_add(9))
        .zip(A.iter())
        .take((n % 10) as usize)
        .map(|(i, y)| i ^ *y as u64)
        .sum()
}

#[no_mangle]
pub extern "C" fn gz_take(s: u64, n: u32) -> u64 {
    gz_take_of(s, n)
}

#[inline(never)]
fn gz_position_of(s: u64, k: u64) -> u32 {
    (s..s.wrapping_add(9))
        .zip(A.iter())
        .position(|(i, y)| (i ^ *y as u64) % 5 == k % 5)
        .map_or(99, |p| p as u32)
}

#[no_mangle]
pub extern "C" fn gz_position(s: u64, k: u64) -> u32 {
    gz_position_of(s, k)
}

#[inline(never)]
fn gz_loop_of(s: u64, n: u64) -> u64 {
    let mut t = 0u64;
    for (i, y) in (s..s.wrapping_add(n % 10)).zip(A.iter()) {
        t = t.wrapping_add(i.wrapping_mul(*y as u64));
    }
    t
}

#[no_mangle]
pub extern "C" fn gz_loop(s: u64, n: u64) -> u64 {
    gz_loop_of(s, n)
}

#[inline(never)]
fn gz_max_of(s: u64, n: u64) -> u64 {
    (s..s.wrapping_add(n % 10))
        .zip(A.iter())
        .map(|(i, y)| i.wrapping_mul(*y as u64 + 3) % 1000)
        .max()
        .unwrap_or(7777)
}

#[no_mangle]
pub extern "C" fn gz_max(s: u64, n: u64) -> u64 {
    gz_max_of(s, n)
}

#[inline(never)]
fn gz_filter_min_of(s: i64, n: u64) -> i64 {
    (s..s.wrapping_add((n % 8) as i64))
        .zip(W.iter())
        .filter(|(i, _)| i & 1 == 0)
        .map(|(i, w)| i.wrapping_add(*w))
        .min()
        .unwrap_or(-1)
}

#[no_mangle]
pub extern "C" fn gz_filter_min(s: i64, n: u64) -> i64 {
    gz_filter_min_of(s, n)
}

#[inline(never)]
fn gz_last_of(s: u64, n: u64) -> u64 {
    (s..s.wrapping_add(n % 11))
        .zip(A.iter())
        .last()
        .map_or(4242, |(i, y)| i ^ ((*y as u64) << 8))
}

#[no_mangle]
pub extern "C" fn gz_last(s: u64, n: u64) -> u64 {
    gz_last_of(s, n)
}

#[inline(never)]
fn gz_nth_of(s: u64, k: u32) -> u64 {
    (s..s.wrapping_add(6))
        .zip(A.iter())
        .nth((k % 9) as usize)
        .map_or(4343, |(i, y)| i.wrapping_add(*y as u64 * 100))
}

#[no_mangle]
pub extern "C" fn gz_nth(s: u64, k: u32) -> u64 {
    gz_nth_of(s, k)
}

// ---- `RangeFrom` chains ----

#[inline(never)]
fn rf_take_map_of(lo: u64, t: usize) -> u64 {
    (lo..).take(t).map(|x| x ^ 3).sum()
}

#[no_mangle]
pub extern "C" fn rf_take_map(lo: u64, t: u32) -> u64 {
    rf_take_map_of(lo >> 2, (t % 12) as usize)
}

#[inline(never)]
fn rf_u8_of(lo: u8, t: usize) -> u32 {
    (lo..).take(t).map(|x| x as u32 * 3).sum()
}

#[no_mangle]
pub extern "C" fn rf_u8_sum(lo: u32, t: u32) -> u32 {
    rf_u8_of(lo as u8, (t % 12) as usize)
}

#[inline(never)]
fn rf_skip_of(lo: i64, s: usize, t: usize) -> i64 {
    (lo..)
        .skip(s)
        .take(t)
        .fold(1i64, |a, x| a.wrapping_mul(3).wrapping_add(x))
}

#[no_mangle]
pub extern "C" fn rf_skip_fold(lo: i64, st: u32) -> i64 {
    rf_skip_of(lo >> 3, (st % 7) as usize, (st / 7 % 9) as usize)
}

#[inline(never)]
fn rf_count_of(lo: u32, t: usize) -> u32 {
    (lo..).take(t).filter(|x| x % 3 == 1).count() as u32
}

#[no_mangle]
pub extern "C" fn rf_count(lo: u32, t: u32) -> u32 {
    rf_count_of(lo >> 1, (t % 20) as usize)
}

#[inline(never)]
fn rf_each_of(lo: u64, t: usize) -> u64 {
    let mut acc = 5u64;
    (lo..).take(t).for_each(|x| acc = acc.rotate_left(7) ^ x);
    acc
}

#[no_mangle]
pub extern "C" fn rf_each(lo: u64, t: u32) -> u64 {
    rf_each_of(lo, (t % 10) as usize)
}

#[inline(never)]
fn rf_position_of(lo: u32, k: u32) -> u32 {
    (lo..)
        .take(40)
        .position(|x| x % 7 == k % 7)
        .map_or(999, |p| p as u32)
}

#[no_mangle]
pub extern "C" fn rf_position(lo: u32, k: u32) -> u32 {
    rf_position_of(lo >> 1, k)
}

#[inline(never)]
fn rf_loop_of(lo: i32, t: usize) -> i32 {
    let mut s = 0i32;
    for x in (lo..).take(t) {
        s = s.wrapping_mul(5).wrapping_add(x);
    }
    s
}

#[no_mangle]
pub extern "C" fn rf_loop(lo: i32, t: u32) -> i32 {
    rf_loop_of(lo, (t % 15) as usize)
}

#[inline(never)]
fn rf_last_of(lo: u32, t: usize) -> u32 {
    (lo..).take(t).last().unwrap_or(0xdead)
}

#[no_mangle]
pub extern "C" fn rf_last(lo: u32, t: u32) -> u32 {
    rf_last_of(lo >> 1, (t % 13) as usize)
}

#[inline(never)]
fn rf_map_take_of(lo: u16, t: usize) -> u64 {
    (lo..).map(|x| x as u64 * x as u64).take(t).sum()
}

#[no_mangle]
pub extern "C" fn rf_map_take(lo: u32, t: u32) -> u64 {
    rf_map_take_of(lo as u16, (t % 9) as usize)
}

#[inline(never)]
fn rf_any_of(lo: u64, k: u64) -> u32 {
    (lo..).take(16).any(|x| x == k) as u32
}

#[no_mangle]
pub extern "C" fn rf_any(lo: u64, k: u64) -> u32 {
    rf_any_of(lo, k)
}

// ---- frame-slot sharing ----

#[inline(never)]
fn touch(a: &mut [u8], k: u32) -> u32 {
    let n = a.len();
    a[k as usize % n] = k as u8;
    a[n - 1] as u32 + a[k as usize % n] as u32 + a[(k as usize).wrapping_add(3) % n] as u32
}

#[inline(never)]
fn touch32(a: &mut [i32], k: u32) -> i32 {
    let n = a.len();
    a[k as usize % n] = k as i32;
    a.iter().take(8).fold(a[n - 1], |s, x| s.wrapping_add(*x))
}

/// Each array's bytes. Two of them exceed the 1 MiB stack; one fits.
const BIG: usize = if cfg!(debug_assertions) {
    200_000
} else {
    600_000
};

#[no_mangle]
pub extern "C" fn fr_two_scopes(k: u32) -> u32 {
    let x = {
        let mut a = [0u8; BIG];
        touch(&mut a, k)
    };
    let y = {
        let mut b = [0u8; BIG];
        touch(&mut b, k.wrapping_add(1))
    };
    x + y
}

#[no_mangle]
pub extern "C" fn fr_byte_fills(k: u32) -> u32 {
    let x = {
        let mut a = [7u8; 300];
        touch(&mut a, k)
    };
    let y = {
        let mut b = [9u8; 500];
        touch(&mut b, k.wrapping_add(1))
    };
    x * 3 + y
}

#[no_mangle]
pub extern "C" fn fr_word_fills(k: u32) -> i32 {
    let x = {
        let mut a = [0i32; 400];
        touch32(&mut a, k)
    };
    let y = {
        let mut b = [5i32; 300];
        touch32(&mut b, k ^ 5)
    };
    x.wrapping_mul(7).wrapping_add(y)
}

#[no_mangle]
pub extern "C" fn fr_loop_arrays(k: u32) -> u32 {
    let mut t = 0u32;
    for i in 0..(k % 5) {
        let mut a = [i as u8; 200];
        t = t.wrapping_add(touch(&mut a, k.wrapping_add(i)));
        let mut b = [0u8; 100];
        b[i as usize] = 3;
        t = t.wrapping_add(touch(&mut b, i));
    }
    t
}

#[no_mangle]
pub extern "C" fn fr_branch_arrays(k: u32) -> u32 {
    if k & 1 == 0 {
        let mut a = [0u8; 256];
        touch(&mut a, k)
    } else {
        let mut b = [1u8; 256];
        let r = touch(&mut b, k);
        let mut c = [2u8; 64];
        r + touch(&mut c, r)
    }
}

#[no_mangle]
pub extern "C" fn fr_reborrow(k: u32) -> u32 {
    let mut a = [0u8; 128];
    let mut b = [0u8; 128];
    let mut s: &mut [u8] = &mut a;
    if black_box(k) % 3 == 0 {
        s = &mut b;
    }
    let r = touch(s, k);
    r + touch(&mut a, k.wrapping_add(1)) * 2 + touch(&mut b, k.wrapping_add(2)) * 5
}

#[no_mangle]
pub extern "C" fn fr_held_across(k: u32) -> u32 {
    let mut a = [0u8; 100];
    let r1 = touch(&mut a, k);
    let r2 = {
        let mut b = [4u8; 100];
        touch(&mut b, k.wrapping_add(7))
    };
    r1 + r2 * 3 + touch(&mut a, k.wrapping_add(11))
}
