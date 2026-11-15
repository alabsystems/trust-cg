// Iterator models on wasm32: `.cloned()` with a user `clone`, the `Option<bool>`
// niche, optimized `try_fold` glue over struct items, generator sources under
// generic helpers, narrow `.enumerate()` items, `<[T]>::swap` over wide
// elements, and `count()` / `position()` past a 32-bit `usize::MAX`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Every export here diverged from LLVM or was refused on wasm32 before:
//
// * `.cloned()` was modeled as `.copied()`, so a hand-written `clone` never
//   ran (`cl_*`); the model now takes only a bitwise clone (derived, core's),
//   and a user `clone` runs through core's real `Cloned::try_fold`. The
//   ungated `#[automatically_derived]` attribute on a hand-written `clone` is
//   not taken as a derive (`cl_marked`).
// * `find` over a `bool`-yielding chain stored `Option<bool>::None` as an
//   ill-typed `const bool 2`, which the lane read back as `Some(false)`
//   (`ob_*`).
// * At `-O2` the `copy_try_fold` / `clone_try_fold` / `map_try_fold` glue over
//   a struct item failed to lower (its `((), C)` argument tuple was read at the
//   MIR field index, not the flat leaf) and became a trap stub (`gl_*`).
// * `Take<Repeat | RepeatWith | FromFn | Successors>` bodies were trap stubs a
//   generic helper still called at `-O2`, and every by-name terminal over
//   those sources was refused (`gen_*`).
// * `.enumerate()` over `u8`/`u16`/`u64`/`bool` items was refused by the
//   wasm32 word pass (`en_*`). The `.copied().enumerate()` form is refused at
//   `-O2` on every target ("closure call receiver is not a place operand"), so
//   these items come from a `.map`.
// * `<[T]>::swap` over a 24-byte or a 4-aligned 16-byte element was refused
//   (`sw_*`).
// * `count()` past `u32::MAX` items wrapped where core panics (`big_*`;
//   `big_count` and `big_chain_count` each drive about 2^32 items for one
//   input of the grid; `Chain::count`'s sum panics only with overflow checks,
//   so the debug and `-O2` configurations differ there). `position()`
//   past `u32::MAX` is not exercised here: LLVM's debug build also walks 2^32
//   items, which is too slow for this corpus. `chain_slices` keeps a slice
//   `chain` count (which cannot overflow per half) compiling under that model.
#![no_std]

// wasm32-differential-flags: -Copt-level=2

use core::num::NonZeroU32;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// ---------------------------------------------------------------------------
// `.cloned()`: a hand-written `clone` must run once per element visited.
// ---------------------------------------------------------------------------

/// Not `Copy`; `clone` returns a different value.
struct Bump(i32);
impl Clone for Bump {
    fn clone(&self) -> Self {
        Bump(self.0.wrapping_add(1000))
    }
}

#[derive(Clone, Copy)]
struct Plain(i32);

#[derive(Clone)]
struct PlainOwned(i32);

#[inline(never)]
fn bump3(a: i32, b: i32) -> [Bump; 3] {
    [Bump(a), Bump(b), Bump(7)]
}

#[no_mangle]
pub extern "C" fn cl_any(a: i32, b: i32) -> u32 {
    bump3(a, b).iter().cloned().any(|n| n.0 == 1007) as u32
}

#[no_mangle]
pub extern "C" fn cl_find(a: i32, b: i32) -> i32 {
    bump3(a, b)
        .iter()
        .cloned()
        .find(|n| n.0 > 500)
        .map_or(-1, |n| n.0)
}

#[no_mangle]
pub extern "C" fn cl_all(a: i32, b: i32) -> u32 {
    bump3(a, b).iter().cloned().all(|n| n.0 >= 1000) as u32
}

#[no_mangle]
pub extern "C" fn cl_for(a: i32, b: i32) -> i32 {
    let mut h = 0i32;
    for n in bump3(a, b).iter().cloned() {
        h = h.wrapping_mul(3).wrapping_add(n.0);
    }
    h
}

/// A derived (bitwise) clone keeps the modeled `.cloned()` drive.
#[no_mangle]
pub extern "C" fn cl_derived(a: i32, b: i32) -> i32 {
    let v = [Plain(a), Plain(b), Plain(5)];
    let any = v.iter().cloned().any(|p| p.0 == 5) as i32;
    let pos = v.iter().cloned().find(|p| p.0 == 5).map_or(-1, |p| p.0);
    let w = [PlainOwned(a), PlainOwned(b)];
    let found = w.iter().cloned().find(|p| p.0 > 0).map_or(-9, |p| p.0);
    any + pos * 4 + found.wrapping_mul(16)
}

/// A hand-written `clone` under `#[automatically_derived]`, on a non-`Copy`
/// and on a `Copy` type: the attribute alone does not make it a derive.
struct Marked(i32);
#[automatically_derived]
impl Clone for Marked {
    fn clone(&self) -> Self {
        Marked(self.0.wrapping_add(1))
    }
}

#[derive(Copy)]
struct MarkedCopy(i32);
#[automatically_derived]
impl Clone for MarkedCopy {
    fn clone(&self) -> Self {
        MarkedCopy(self.0.wrapping_sub(3))
    }
}

#[inline(never)]
fn marked_any(v: &[Marked]) -> bool {
    v.iter().cloned().any(|n| n.0 == 6)
}

#[inline(never)]
fn marked_find(v: &[MarkedCopy]) -> i32 {
    v.iter().cloned().find(|n| n.0 > 2).map_or(-7, |n| n.0)
}

#[no_mangle]
pub extern "C" fn cl_marked(a: i32, b: i32) -> i32 {
    let any = marked_any(&[Marked(a), Marked(5), Marked(b)]) as i32;
    let found = marked_find(&[MarkedCopy(a), MarkedCopy(b), MarkedCopy(6)]);
    any + found.wrapping_mul(2)
}

#[no_mangle]
pub extern "C" fn cl_prim(a: i32, b: i32) -> i64 {
    let v = [a, b, a ^ b];
    let any = v.iter().cloned().any(|x| x & 1 == 0) as i64;
    any + 2 * v.iter().cloned().find(|x| *x > 9).map_or(-1, |x| x as i64)
}

// ---------------------------------------------------------------------------
// `Option<bool>` from `find` / `nth` / `last` over a `bool` chain.
// ---------------------------------------------------------------------------

#[inline(never)]
fn find_true(v: &[bool]) -> Option<bool> {
    v.iter().copied().find(|c| *c)
}

fn ob_code(o: Option<bool>) -> u32 {
    match o {
        None => 3,
        Some(true) => 1,
        Some(false) => 0,
    }
}

#[no_mangle]
pub extern "C" fn ob_find(a: u32, b: u32) -> u32 {
    let v = [a > b, a == b.wrapping_add(7)];
    ob_code(find_true(&v)) + 4 * find_true(&v).is_none() as u32
}

#[no_mangle]
pub extern "C" fn ob_range(a: u32, k: u32) -> u32 {
    let n = a % 9;
    let k = k % 9;
    let f = (0..n).map(|x| x > k).find(|c| *c);
    let r = (0..n).map(|x| x > k).rev().find(|c| !*c);
    ob_code(f) * 10 + ob_code(r)
}

#[no_mangle]
pub extern "C" fn ob_nth_last(a: u32, k: u32) -> u32 {
    let n = a % 7;
    let v = [true, false, true, true, false, false, true];
    let s = &v[..n as usize];
    ob_code(s.iter().copied().nth((k % 9) as usize)) * 10 + ob_code(s.iter().copied().last())
}

// ---------------------------------------------------------------------------
// Optimized `try_fold` glue over struct items (`copy_try_fold`,
// `clone_try_fold`, `map_try_fold`).
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct C(i32);

#[derive(Clone, Copy)]
#[repr(transparent)]
struct T8(u8);

#[derive(Clone, Copy)]
struct Nz(NonZeroU32);

#[no_mangle]
pub extern "C" fn gl_map_any(n: i32) -> u32 {
    (0..(n & 15)).map(|x| C(x)).any(|c| c.0 == 3) as u32
}

#[no_mangle]
pub extern "C" fn gl_copied_any(a: i32, b: i32) -> u32 {
    let v = [C(a), C(b), C(1)];
    v.iter().copied().any(|c| c.0 == 1) as u32 + 2 * v.iter().copied().all(|c| c.0 > 0) as u32
}

#[no_mangle]
pub extern "C" fn gl_cloned_find_map(a: i32, b: i32) -> i32 {
    let v = [C(a), C(b), C(-4)];
    v.iter()
        .cloned()
        .find_map(|c| (c.0 < 0).then_some(c.0 * 2))
        .unwrap_or(77)
}

#[no_mangle]
pub extern "C" fn gl_rev_find(n: i32) -> i32 {
    (0..(n & 15))
        .map(|x| C(x))
        .rev()
        .find(|c| c.0 % 4 == 1)
        .map_or(-1, |c| c.0)
}

#[no_mangle]
pub extern "C" fn gl_incl_t8(a: u32) -> u32 {
    let v = [a as u8, 3, 250, (a >> 8) as u8];
    let hit = v.iter().map(|&x| T8(x)).any(|t| t.0 == 250) as u32;
    let first = (0..=(a % 6))
        .map(|x| T8(x as u8))
        .find(|t| t.0 >= 2)
        .map_or(99, |t| t.0 as u32);
    hit * 100 + first
}

#[no_mangle]
pub extern "C" fn gl_nonzero(a: u32) -> u32 {
    let v = [a | 1, 6, 9];
    v.iter()
        .map(|&x| Nz(NonZeroU32::new(x).unwrap()))
        .find(|z| z.0.get() % 3 == 0)
        .map_or(0, |z| z.0.get())
}

/// A user closure called with a `((), C)` argument tuple.
#[inline(never)]
fn call_unit_c<F: Fn((), C) -> i32>(f: F, c: C) -> i32 {
    f((), c)
}

#[no_mangle]
pub extern "C" fn gl_unit_tuple(a: i32) -> i32 {
    call_unit_c(|(), c| c.0.wrapping_mul(3), C(a))
}

// ---------------------------------------------------------------------------
// Generator sources (`repeat`, `repeat_with`, `from_fn`, `successors`) under
// generic helpers and direct terminals.
// ---------------------------------------------------------------------------

#[inline(never)]
fn take_sum<I: Iterator<Item = u64>>(it: I, n: usize) -> u64 {
    it.take(n).sum()
}

#[inline(never)]
fn take_fold<I: Iterator<Item = u32>>(it: I, n: usize) -> u32 {
    it.take(n).fold(17u32, |a, x| a.rotate_left(3) ^ x)
}

#[inline(never)]
fn take_count<I: Iterator<Item = u32>>(it: I, n: usize) -> usize {
    it.take(n).count()
}

#[inline(never)]
fn take_last<I: Iterator<Item = char>>(it: I, n: usize) -> u32 {
    it.take(n).last().map_or(77, |c| c as u32)
}

#[no_mangle]
pub extern "C" fn gen_repeat(a: u32) -> u64 {
    take_sum(core::iter::repeat(7u64), (a % 5) as usize)
}

#[no_mangle]
pub extern "C" fn gen_repeat_with(a: u32) -> u32 {
    let mut k = a;
    take_fold(
        core::iter::repeat_with(move || {
            k = k.wrapping_mul(31).wrapping_add(1);
            k
        }),
        (a % 9) as usize,
    )
}

#[no_mangle]
pub extern "C" fn gen_from_fn(a: u32) -> u32 {
    let mut k = a;
    take_count(
        core::iter::from_fn(move || {
            k = k.wrapping_add(5);
            (k % 11 != 0).then_some(k)
        }),
        (a % 12) as usize,
    ) as u32
}

#[no_mangle]
pub extern "C" fn gen_successors(a: u32) -> u32 {
    let start = char::from_u32(0x41 + a % 20).unwrap_or('A');
    take_last(
        core::iter::successors(Some(start), |c| char::from_u32(*c as u32 + 2)),
        (a % 6) as usize,
    )
}

#[no_mangle]
pub extern "C" fn gen_direct(a: u32) -> u64 {
    let n = (a % 10) as usize;
    let s: u64 = core::iter::repeat(a as u64 & 0xff).take(n).sum();
    let mut x = a;
    let f = core::iter::from_fn(|| {
        x = x.wrapping_mul(1103515245).wrapping_add(12345);
        Some(x >> 16)
    })
    .take(n)
    .map(|v| v as u64)
    .fold(0u64, |acc, v| acc.wrapping_mul(3) ^ v);
    let c = core::iter::successors(Some(a), |v| v.checked_sub(3))
        .take(n)
        .count() as u64;
    s ^ f.rotate_left(7) ^ (c << 40)
}

// ---------------------------------------------------------------------------
// `.enumerate()` over narrow items.
// ---------------------------------------------------------------------------

#[inline(never)]
fn en_u8(a: &[u8]) -> u64 {
    a.iter()
        .map(|&b| b)
        .enumerate()
        .map(|(i, b)| i as u64 * b as u64)
        .sum()
}

#[inline(never)]
fn en_i8(a: &[i8]) -> i64 {
    a.iter()
        .map(|&b| b)
        .enumerate()
        .map(|(i, b)| (i as i64 + 1) * b as i64)
        .sum()
}

#[inline(never)]
fn en_u16_count(a: &[u16]) -> usize {
    a.iter()
        .map(|&b| b)
        .enumerate()
        .filter(|(i, b)| (*b as usize) > *i)
        .count()
}

#[inline(never)]
fn en_u64(a: &[u64]) -> u64 {
    a.iter()
        .map(|&b| b)
        .enumerate()
        .map(|(i, b)| b.rotate_left(i as u32))
        .sum()
}

#[inline(never)]
fn en_map_u8(a: &[u32]) -> u64 {
    a.iter()
        .map(|&x| x as u8)
        .enumerate()
        .map(|(i, b)| ((i as u64) << 8) | b as u64)
        .sum()
}

#[inline(never)]
fn en_bool(a: &[f32]) -> u32 {
    a.iter()
        .map(|x| *x > 1.0)
        .enumerate()
        .map(|(i, f)| (f as u32) << i)
        .sum::<u32>()
}

#[no_mangle]
pub extern "C" fn en_narrow(v: u64, x: u32) -> u64 {
    let b = v.to_le_bytes();
    let n = (x % 9) as usize;
    let mut i8s = [0i8; 8];
    let mut j = 0;
    while j < 8 {
        i8s[j] = b[j] as i8;
        j += 1;
    }
    let w = [v as u16, (v >> 16) as u16, x as u16, 3];
    en_u8(&b[..n])
        ^ (en_i8(&i8s[..n]) as u64).rotate_left(13)
        ^ ((en_u16_count(&w[..n % 5]) as u64) << 50)
}

#[no_mangle]
pub extern "C" fn en_wide(v: u64, x: u32) -> u64 {
    let a = [v, !v, x as u64];
    let m = [v as u32, x, (v >> 32) as u32];
    let f = [x as f32 * 0.5, -1.5, 2.25];
    en_u64(&a[..(x % 4) as usize])
        ^ en_map_u8(&m[..(x % 4) as usize]) << 7
        ^ (en_bool(&f[..(x % 4) as usize]) as u64) << 21
}

// ---------------------------------------------------------------------------
// `<[T]>::swap` over elements wider than one 8-byte lane or under-aligned.
// ---------------------------------------------------------------------------

#[inline(never)]
fn sw_f64x3(m: &mut [[f64; 3]], a: usize, b: usize) {
    m.swap(a, b)
}

#[inline(never)]
fn sw_f32x4(m: &mut [[f32; 4]], a: usize, b: usize) {
    m.swap(a, b)
}

#[inline(never)]
fn sw_u8x3(m: &mut [(u8, u8, u8)], a: usize, b: usize) {
    m.swap(a, b)
}

#[inline(never)]
fn sw_u32x3(m: &mut [[u32; 3]], a: usize, b: usize) {
    m.swap(a, b)
}

#[no_mangle]
pub extern "C" fn sw_wide(a: u32, b: u32) -> f64 {
    let mut m = [[1.0f64, 2.0, 3.0], [4.0, 5.0, 6.0], [7.0, 8.0, 9.0]];
    sw_f64x3(&mut m, (a % 3) as usize, (b % 3) as usize);
    let mut q = [[1.0f32, 2.0, 3.0, 4.0], [5.0, 6.0, 7.0, 8.0]];
    sw_f32x4(&mut q, (a % 2) as usize, (b % 2) as usize);
    let [[x, _, _], [_, y, _], [_, _, z]] = m;
    let [[_, _, _, p], [r, _, _, _]] = q;
    x * 1000.0 + y * 100.0 + z * 10.0 + (p * 10.0 + r) as f64 / 128.0
}

#[no_mangle]
pub extern "C" fn sw_narrow(a: u32, b: u32) -> u32 {
    let mut t = [(1u8, 2u8, 3u8), (4, 5, 6), (a as u8, 8, 9)];
    sw_u8x3(&mut t, (a % 3) as usize, (b % 3) as usize);
    let mut u = [[a, 2, 3], [4, b, 6]];
    sw_u32x3(&mut u, (a % 2) as usize, (b % 2) as usize);
    let [(t0, _, _), (_, t1, _), (_, _, t2)] = t;
    let [[u0, _, _], [_, u1, _]] = u;
    (t0 as u32) | (t1 as u32) << 8 | (t2 as u32) << 16 | u0.wrapping_mul(3) ^ u1.rotate_left(24)
}

/// An out-of-range index panics (traps under this handler) on both sides.
#[no_mangle]
pub extern "C" fn sw_oob(a: u32, b: u32) -> f64 {
    let mut m = [[1.0f64, 2.0, 3.0], [4.0, 5.0, 6.0]];
    sw_f64x3(&mut m, (a % 4) as usize, (b % 2) as usize);
    let [[x, _, _], [y, _, _]] = m;
    x * 10.0 + y
}

// ---------------------------------------------------------------------------
// `count()` past a 32-bit `usize::MAX`. Only the input `0x7fffffff` takes
// the long path; every other input counts a short range.
// ---------------------------------------------------------------------------

#[no_mangle]
pub extern "C" fn big_count(sel: i32) -> u32 {
    let len = if sel == 0x7fff_ffff {
        (1u64 << 32) + 1
    } else {
        sel as u64 & 0x3ff
    };
    (0..len).count() as u32
}

/// `Chain::count` adds its halves' counts under inherited overflow checks:
/// two `Range<u32>` halves that cannot overflow alone panic in the sum with
/// checks on, and wrap to 1 with them off. Only the input `0x7fffffff` takes
/// the long path.
#[no_mangle]
pub extern "C" fn big_chain_count(sel: i32) -> u32 {
    let (hi, b) = if sel == 0x7fff_ffff {
        (u32::MAX, 2)
    } else {
        (sel as u32 & 0x3ff, sel as u32 >> 22)
    };
    (0u32..hi).chain(0u32..b).count() as u32
}

/// Short counts through every count route.
#[no_mangle]
pub extern "C" fn small_counts(a: u32, b: u32) -> u32 {
    let lo = (a % 50) as u64;
    let hi = lo + (b % 300) as u64;
    let c0 = (lo..hi).count() as u32;
    let c1 = (lo..=hi).map(|x| x ^ 1).count() as u32;
    let c2 = (lo..hi).filter(|x| x % 3 == 1).count() as u32;
    let c3 = (lo..hi).skip((a % 7) as usize).count() as u32;
    let c4 = (a % 40..b % 90).rev().count() as u32;
    let p = (lo..hi).position(|x| x % 17 == 5).map_or(999, |p| p as u32);
    let c5 = (a % 60..b % 70).chain(b % 20..a % 80).count() as u32;
    c0 ^ c1 << 3 ^ c2 << 6 ^ c3 << 9 ^ c4 << 12 ^ p << 20 ^ c5 << 25
}

/// A direct `count()` over a `chain` of two slices: a slice half's count is its
/// length and cannot pass `usize::MAX` alone, so the chain stays modeled.
#[inline(never)]
fn slice_chain_count(a: &[u32], b: &[u32]) -> usize {
    a.iter().chain(b.iter()).count()
}

#[no_mangle]
pub extern "C" fn chain_slices(x: u32, y: u32) -> u32 {
    let v = [1u32, 2, 3, 4, 5, 6, 7, 8, 9];
    let a = &v[..(x % 10) as usize];
    let b = &v[(y % 10) as usize..];
    slice_chain_count(a, b) as u32
}
