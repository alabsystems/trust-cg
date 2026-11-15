// 128-bit reversed `RangeInclusive` folds on wasm32, and the wasm lane's
// read of a memory-carried field through a pointer that is then overwritten.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// On wasm32 a `u128` / `i128` (and `NeverShortCircuit` of one) is returned
// through memory, so a reversed inclusive fold into a 128-bit accumulator
// never reaches the bridge's back-to-front `spec_try_rfold` route: std's own
// `spec_try_rfold` body is lowered and called. That body steps the range with
// `mem::replace(&mut self.end, n)` and folds the OLD `end`. The wasm lane
// used to lower `ExtractField` of a memory-carried lane through a pointer as
// an ALIAS of the pointee, so the read observed the write that followed it:
// every item but the last was folded as `end - 1` (`(1..=3).rev().sum()` was
// 4, `(0..=12)` 66 where LLVM computes 78), at every opt level for
// `(&mut r).rfold`, and at `-O2`/`-O3` for `.rev().sum()` / `.fold()`. The
// lane now copies such a lane into a home of its own, as a `Load` does
// (`extract_reads_through`). The `rw_*` exports pin that lowering directly: a
// `u128` / nested field read through `&mut`, then overwritten (by an
// assignment, through a callee) while the value read is still used.
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
fn sum_u128(a: u128, b: u128) -> u128 {
    (a..=b).rev().sum()
}
#[inline(never)]
fn prod_u128(a: u128, b: u128) -> u128 {
    (a..=b).rev().product()
}
#[inline(never)]
fn fold_u128(a: u128, b: u128) -> u128 {
    (a..=b)
        .rev()
        .fold(0u128, |c, x| c.wrapping_mul(3).wrapping_add(x))
}
#[inline(never)]
fn fold_i128(a: i128, b: i128) -> i128 {
    (a..=b)
        .rev()
        .fold(1i128, |c, x| c.wrapping_mul(5).wrapping_sub(x))
}
#[inline(never)]
fn sum_i128(a: i128, b: i128) -> i128 {
    (a..=b).rev().sum()
}
#[inline(never)]
fn rfold_ref_u128(a: u128, b: u128) -> (u128, bool) {
    let mut r = a..=b;
    let v = (&mut r).rfold(0u128, |c, x| c.wrapping_mul(3).wrapping_add(x));
    (v, r.is_empty())
}
#[inline(never)]
fn map_sum_u128(a: u64, b: u64) -> u128 {
    (u128::from(a)..=u128::from(b))
        .rev()
        .map(|x| x << 64 | x)
        .fold(0u128, |c, x| c.rotate_left(7) ^ x)
}

/// The fold of every item, the last one included.
#[no_mangle]
pub extern "C" fn wri_sums(a: u32, b: u32) -> u64 {
    let (lo, hi) = (u128::from(a % 40), u128::from(b % 40));
    let mut d = sum_u128(lo, hi) as u64;
    d = d.wrapping_mul(1_000_003) ^ fold_u128(lo, hi) as u64;
    d = d.wrapping_mul(1_000_003) ^ (fold_u128(lo, hi) >> 64) as u64;
    let (sl, sh) = (i128::from(a % 40) - 20, i128::from(b % 40) - 20);
    d = d.wrapping_mul(1_000_003) ^ sum_i128(sl, sh) as u64;
    d = d.wrapping_mul(1_000_003) ^ fold_i128(sl, sh) as u64;
    d
}

/// Products, and endpoints at the top of the type: the first back-to-front
/// add overflows (a trap under overflow checks).
#[no_mangle]
pub extern "C" fn wri_edges(a: u32, b: u32) -> u64 {
    match a % 4 {
        0 => prod_u128(u128::from(a % 20), u128::from(b % 20)) as u64,
        1 => (prod_u128(u128::from(a % 30), u128::from(b % 30)) >> 64) as u64,
        2 => sum_u128(u128::MAX - u128::from(b % 3), u128::MAX) as u64,
        _ => sum_i128(i128::MIN, i128::MIN + i128::from(b % 2)) as u64,
    }
}

/// `rfold` through `&mut RangeInclusive` (every opt level reaches std's
/// body), its leftover `exhausted` state, and a mapped digest.
#[no_mangle]
pub extern "C" fn wri_rfold_ref(a: u32, b: u32) -> u64 {
    let (v, empty) = rfold_ref_u128(u128::from(a % 30), u128::from(b % 30));
    let m = map_sum_u128(u64::from(a % 25), u64::from(b % 25));
    (v as u64) ^ ((v >> 64) as u64).rotate_left(11) ^ u64::from(empty) << 63 ^ m as u64
}

pub struct Wide {
    lo: u128,
    hi: u128,
    done: bool,
}

#[inline(never)]
fn bump(p: &mut u128, by: u128) {
    *p = p.wrapping_add(by);
}

#[inline(never)]
fn step_back(w: &mut Wide) -> u128 {
    let n = w.hi.wrapping_sub(1);
    let old = w.hi;
    w.hi = n;
    w.done = w.lo == n;
    old.wrapping_mul(1000).wrapping_add(w.hi)
}

#[inline(never)]
fn read_then_call(w: &mut Wide, by: u128) -> u128 {
    let old = w.lo;
    bump(&mut w.lo, by);
    old.wrapping_mul(1000).wrapping_add(w.lo)
}

#[inline(never)]
fn nested(p: &mut (u64, (u128, u32)), v: u128) -> u128 {
    let old = p.1;
    p.1 = (v, 7);
    old.0.wrapping_mul(1000).wrapping_add(p.1.0) ^ u128::from(old.1)
}

/// A memory-carried field read through `&mut`, then overwritten while the
/// value read is live: by an assignment, through a callee, and as a nested
/// aggregate lane.
#[no_mangle]
pub extern "C" fn wri_read_through(a: u64, b: u64) -> u64 {
    let mut w = Wide {
        lo: u128::from(a),
        hi: u128::from(b) << 3,
        done: false,
    };
    let x = step_back(&mut w);
    let y = read_then_call(&mut w, u128::from(b) + 1);
    let mut p = (a, (u128::from(b) << 70 | u128::from(a), 3u32));
    let z = nested(&mut p, u128::from(a ^ b));
    (x as u64)
        ^ ((x >> 64) as u64).rotate_left(9)
        ^ (y as u64).rotate_left(21)
        ^ (z as u64).rotate_left(33)
        ^ ((z >> 64) as u64).rotate_left(45)
        ^ u64::from(w.done)
        ^ (w.lo as u64)
        ^ p.0
}
