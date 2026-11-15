// wasm32 execution-differential corpus: bridge lowerings shared by every target.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Each export exercises a MIR lowering of the rustc bridge that is not specific
// to wasm32 (the same trust-ir feeds the native lanes):
// * signed `<*const T>::offset_from` with a negative distance and an element
//   wider than one byte (an exact SIGNED divide by the element size);
// * integer `pow` in a debug build, whose `overflow_checks()` switch leaves a
//   mono-dead `wrapping_pow` arm naming a callee rustc never collects, and a
//   user generic branching on an associated `const`;
// * f32 signaling-NaN constants (a `const` item, an array element, a struct
//   field, a closure argument) whose bits must survive exactly;
// * `Iterator::sum` / `product` under this debug build's overflow checks (an
//   overflowing step panics), and over core's `Saturating` / `Wrapping`
//   accumulators (saturating / wrapping steps);
// * `.take(k)` bounding a driven iterator chain, whose `usize` remaining count
//   is a 4-byte field on wasm32.
//
// The optimized configurations cover the optimized `pow` (`overflowing_pow`
// with an in-loop join) and the optimized constant paths; the overflow-checked
// one keeps the checked sum/product steps at an optimized level.
//
// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=2 -Coverflow-checks=on
// wasm32-differential-flags: -Copt-level=3

#![no_std]
#![allow(dead_code)]

use core::num::{Saturating, Wrapping};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// --- signed offset_from ---------------------------------------------------

static W64: [i64; 8] = [0; 8];
static W16: [u16; 8] = [0; 8];
static W12: [[u32; 3]; 8] = [[0; 3]; 8];

#[no_mangle]
pub extern "C" fn off64(a: u32, b: u32) -> i64 {
    let p = W64.as_ptr();
    unsafe { p.add((a % 8) as usize).offset_from(p.add((b % 8) as usize)) as i64 }
}
#[no_mangle]
pub extern "C" fn off16(a: u32, b: u32) -> i64 {
    let p = W16.as_ptr();
    unsafe { p.add((a % 8) as usize).offset_from(p.add((b % 8) as usize)) as i64 }
}
#[no_mangle]
pub extern "C" fn off12(a: u32, b: u32) -> i64 {
    let p = W12.as_ptr() as *mut [u32; 3];
    unsafe { p.add((a % 8) as usize).offset_from(p.add((b % 8) as usize)) as i64 }
}
#[no_mangle]
pub extern "C" fn off_unsigned(a: u32, b: u32) -> u64 {
    let (hi, lo) = if a % 8 >= b % 8 {
        (a % 8, b % 8)
    } else {
        (b % 8, a % 8)
    };
    let p = W64.as_ptr();
    unsafe { p.add(hi as usize).offset_from_unsigned(p.add(lo as usize)) as u64 }
}

// --- pow and other mono-dead arms --------------------------------------------

#[no_mangle]
pub extern "C" fn pow_u32(a: u32, b: u32) -> u32 {
    a.pow(b & 31)
}
#[no_mangle]
pub extern "C" fn pow_i64(a: i64, b: u32) -> i64 {
    a.pow(b % 70)
}
#[no_mangle]
pub extern "C" fn pow_u8(a: u32, b: u32) -> u32 {
    (a as u8).pow(b % 9) as u32
}

trait Flag {
    const ON: bool;
}
struct Yes;
struct No;
impl Flag for Yes {
    const ON: bool = true;
}
impl Flag for No {
    const ON: bool = false;
}
#[inline(never)]
fn slow(x: u32) -> u32 {
    x.wrapping_mul(3)
}
#[inline(never)]
fn fast(x: u32) -> u32 {
    x.wrapping_add(1)
}
#[inline(never)]
fn pick<F: Flag>(x: u32) -> u32 {
    if F::ON { fast(x) } else { slow(x) }
}
#[no_mangle]
pub extern "C" fn const_arm(x: u32) -> u32 {
    pick::<Yes>(x) ^ pick::<No>(x)
}

// --- f32 signaling-NaN constants -----------------------------------------------

const SN: f32 = f32::from_bits(0x7f80_0001);
const SN_NEG: f32 = f32::from_bits(0xffa0_0000);
const QN: f32 = f32::from_bits(0x7fc0_0005);

#[derive(Clone, Copy)]
pub struct P {
    a: f32,
    b: u32,
}
#[inline(never)]
fn take(p: P) -> u32 {
    p.a.to_bits() ^ p.b
}
#[inline(never)]
fn arr_at(a: [f32; 3], i: usize) -> u32 {
    a[i % 3].to_bits()
}
#[inline(never)]
fn call2<F: Fn(f32, u32) -> u32>(f: F) -> u32 {
    f(SN, 3)
}

#[no_mangle]
pub extern "C" fn snan32(k: u32) -> u32 {
    let x = if k & 1 == 1 { SN } else { 1.0 };
    x.to_bits()
}
#[no_mangle]
pub extern "C" fn snan32_ops(k: u32) -> u32 {
    let x = match k % 4 {
        0 => SN,
        1 => SN_NEG,
        2 => QN,
        _ => -SN,
    };
    x.to_bits() ^ x.abs().to_bits().rotate_left(7) ^ x.copysign(-1.0).to_bits().rotate_left(13)
}
#[no_mangle]
pub extern "C" fn snan32_arr(k: u32) -> u32 {
    arr_at([1.0, SN, SN_NEG], k as usize)
}
#[no_mangle]
pub extern "C" fn snan32_struct(k: u32) -> u32 {
    if k > 3 { take(P { a: SN, b: 5 }) } else { 0 }
}
#[no_mangle]
pub extern "C" fn snan32_closure(k: u32) -> u32 {
    if k > 3 {
        call2(|x, y| x.to_bits() ^ y)
    } else {
        0
    }
}

// --- sum / product -------------------------------------------------------------

#[no_mangle]
pub extern "C" fn sum2(a: u32, b: u32) -> u32 {
    [a, b].iter().sum()
}
#[no_mangle]
pub extern "C" fn prod2(a: u32, b: u32) -> u32 {
    [a, b].iter().product()
}
#[no_mangle]
pub extern "C" fn sum2_i64(a: i64, b: i64) -> i64 {
    [a, b].iter().sum()
}
#[no_mangle]
pub extern "C" fn sum2_i8(a: i32, b: i32) -> i32 {
    [a as i8, b as i8].iter().sum::<i8>() as i32
}
#[no_mangle]
pub extern "C" fn range_sum(a: u32, b: u32) -> u32 {
    (a..a.wrapping_add(b % 8)).sum()
}
#[no_mangle]
pub extern "C" fn range_prod(n: u32) -> u32 {
    (1..(n % 16) + 1).product()
}
#[no_mangle]
pub extern "C" fn sat_sum(a: u32, b: u32) -> u32 {
    [Saturating(a), Saturating(b)]
        .iter()
        .sum::<Saturating<u32>>()
        .0
}
#[no_mangle]
pub extern "C" fn sat_prod(a: u32, b: u32) -> u32 {
    [Saturating(a), Saturating(b), Saturating(3)]
        .iter()
        .product::<Saturating<u32>>()
        .0
}
#[no_mangle]
pub extern "C" fn sat_sum_u8(a: u32, b: u32) -> u32 {
    [Saturating(a as u8), Saturating(b as u8)]
        .iter()
        .sum::<Saturating<u8>>()
        .0 as u32
}
#[no_mangle]
pub extern "C" fn wrap_sum(a: u32, b: u32) -> u32 {
    [Wrapping(a), Wrapping(b), Wrapping(7)]
        .iter()
        .sum::<Wrapping<u32>>()
        .0
}

// --- take-bounded chains ---------------------------------------------------------

#[no_mangle]
pub extern "C" fn take_sum(a: u32, k: u32) -> u32 {
    [a, 10, 100, 1000].iter().take((k & 7) as usize).sum()
}
#[no_mangle]
pub extern "C" fn take_sum_i16(a: i32, k: u32) -> i32 {
    [a as i16, 10, 30000, 1000]
        .iter()
        .take((k & 7) as usize)
        .sum::<i16>() as i32
}
#[no_mangle]
pub extern "C" fn take_fold(a: u32, k: u32) -> u32 {
    [a, 10, 100, 1000]
        .iter()
        .take((k & 7) as usize)
        .fold(1u32, |x, y| x.wrapping_mul(31).wrapping_add(*y))
}
#[no_mangle]
pub extern "C" fn range_take(a: u32, k: u32) -> u32 {
    ((a & 15)..40)
        .take((k & 31) as usize)
        .fold(0u32, |x, y| x.wrapping_mul(3).wrapping_add(y))
}
#[no_mangle]
pub extern "C" fn take_map_count(a: u32, k: u32) -> u32 {
    [a, 10, 100, 1000, 5]
        .iter()
        .map(|x| x ^ k)
        .take((k & 7) as usize)
        .filter(|x| *x > 50)
        .count() as u32
}
