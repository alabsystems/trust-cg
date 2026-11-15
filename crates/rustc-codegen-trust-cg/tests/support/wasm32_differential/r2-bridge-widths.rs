// wasm32 execution-differential corpus: 32-bit widths in the bridge's models.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Covers, on wasm32:
// * closure bodies returning a small memory aggregate that rustc's wasm32 Rust
//   ABI casts to one integer (`[u8; 4]` from `to_be_bytes`, `[u8; 2]`, a
//   3-byte struct) through `Fn`, `FnMut` and `FnOnce` generic calls and a
//   `dyn Fn` call: the body returns the one `i32` carrier and every caller
//   splits it back into the value's bytes;
// * `split_first` / `split_last` of `&[u64]` and `&[&str]`, whose
//   `Option<(&T, &[T])>` result stores the tail length as a 4-byte `usize`
//   field beside 4-byte pointers;
// * the `zip` cursor's `usize` length and index fields, and a reversed,
//   skipped slice iterator.
//
// `split_first` / `split_last` are refused at -Copt-level=2 by a lowering gap
// shared with the native targets, so the optimized configurations are
// -Copt-level=1 and -Copt-level=s.
//
// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=s

#![no_std]
#![allow(dead_code)]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

static A64: [u64; 9] = [11, 22, 33, 44, 55, 66, 77, 88, 99];
static A32: [u32; 9] = [1, 2, 3, 4, 5, 6, 7, 8, 9];

// --- closures returning a one-integer cast aggregate -------------------------

#[derive(Clone, Copy)]
struct Rgb {
    r: u8,
    g: u8,
    b: u8,
}

#[inline(never)]
fn apply4<F: Fn(u32) -> [u8; 4]>(f: F, x: u32) -> u32 {
    let b = f(x);
    u32::from_le_bytes([b[1], b[0], b[3], b[2]])
}

#[inline(never)]
fn apply3<F: FnMut(u32) -> Rgb>(mut f: F, x: u32) -> u32 {
    let c = f(x);
    let d = f(x ^ 0x5a5a);
    (c.r as u32) << 16 | (c.g as u32) << 8 | c.b as u32 ^ (d.g as u32) << 24
}

#[inline(never)]
fn apply2<F: FnOnce(u16) -> [u8; 2]>(f: F, x: u16) -> u32 {
    let b = f(x);
    (b[0] as u32) << 8 | b[1] as u32
}

#[inline(never)]
fn via_dyn(f: &dyn Fn(u32) -> [u8; 4], x: u32) -> u32 {
    let b = f(x);
    b[0] as u32 * 3 + b[3] as u32
}

#[no_mangle]
pub extern "C" fn clo_ret_bytes4(x: u32, k: u32) -> u32 {
    apply4(move |v| (v ^ k).to_be_bytes(), x)
}

#[no_mangle]
pub extern "C" fn clo_ret_rgb(x: u32) -> u32 {
    apply3(
        |v| Rgb {
            r: v as u8,
            g: (v >> 8) as u8,
            b: (v >> 16) as u8,
        },
        x,
    )
}

#[no_mangle]
pub extern "C" fn clo_ret_bytes2(x: u32) -> u32 {
    apply2(|v| v.to_le_bytes(), x as u16)
}

#[no_mangle]
pub extern "C" fn clo_ret_dyn(x: u32, k: u32) -> u32 {
    let f = move |v: u32| v.wrapping_add(k).to_le_bytes();
    via_dyn(&f, x)
}

// --- `split_first` / `split_last` tails of 8-byte and fat elements -----------

#[inline(never)]
fn first_u64(s: &[u64]) -> u64 {
    match s.split_first() {
        Some((h, t)) => h.wrapping_mul(1000) + t.len() as u64 * 10 + t.last().copied().unwrap_or(5),
        None => 7,
    }
}

#[inline(never)]
fn last_u64(s: &[u64]) -> u64 {
    match s.split_last() {
        Some((h, t)) => {
            h.wrapping_mul(1000) + t.len() as u64 * 10 + t.first().copied().unwrap_or(5)
        }
        None => 7,
    }
}

#[inline(never)]
fn first_str(s: &[&str]) -> u64 {
    match s.split_first() {
        Some((h, t)) => {
            h.len() as u64 * 1000 + t.len() as u64 * 10 + t.last().map_or(5, |x| x.len() as u64)
        }
        None => 7,
    }
}

#[inline(never)]
fn last_str(s: &[&str]) -> u64 {
    match s.split_last() {
        Some((h, t)) => {
            h.len() as u64 * 1000 + t.len() as u64 * 10 + t.first().map_or(5, |x| x.len() as u64)
        }
        None => 7,
    }
}

#[no_mangle]
pub extern "C" fn split_first_u64(k: u32) -> u64 {
    let d = [11u64, 22, 33, 44, 55];
    first_u64(&d[..(k % 6) as usize])
}

#[no_mangle]
pub extern "C" fn split_last_u64(k: u32) -> u64 {
    let d = [11u64, 22, 33, 44, 55];
    last_u64(&d[(k % 6) as usize..])
}

#[no_mangle]
pub extern "C" fn split_first_str(k: u32) -> u64 {
    let d = ["a", "bb", "ccc", "dddd"];
    first_str(&d[..(k % 5) as usize])
}

#[no_mangle]
pub extern "C" fn split_last_str(k: u32) -> u64 {
    let d = ["a", "bb", "ccc", "dddd"];
    last_str(&d[(k % 5) as usize..])
}

// --- `zip` cursor and reversed skips -----------------------------------------

#[no_mangle]
pub extern "C" fn zip_slices_u64(a: u32, b: u32) -> u64 {
    let mut t = 0u64;
    for (x, y) in A64[..(a % 10) as usize]
        .iter()
        .zip(A32[..(b % 10) as usize].iter())
    {
        t = t.wrapping_mul(7).wrapping_add(*x + *y as u64);
    }
    t
}

#[no_mangle]
pub extern "C" fn rev_skip_u64(a: u32, k: u32) -> u64 {
    let mut t = 0u64;
    for x in A64[..(a % 10) as usize]
        .iter()
        .rev()
        .skip((k % 12) as usize)
    {
        t = t.wrapping_mul(7).wrapping_add(*x);
    }
    t
}
