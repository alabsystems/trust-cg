// Crate-private functions returning pairs and 128-bit integers on wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Every `#[inline(never)]` function here is private to the crate and returns
// what rustc's wasm32 ABI returns through a caller buffer (`sret`): a
// `ScalarPair` (two integers, two floats, a `char` and a `bool`, an
// `Option<u64>`, a `Result<u32, i32>`, a slice or `&str`) or an `i128`. At
// `-O1` and above this backend's object lane gives such a function an
// internal entry returning wasm multi-value results for its direct calls
// (mutual recursion included) and keeps the C form for its function
// pointers (a static's, a `black_box`ed one, one compared by address) and
// vtables (a `dyn` trait call, a closure). `wasm32_differential.rs` compares
// every export with LLVM's module and checks that the internal entries were
// used, or withheld where the session withholds `multivalue`.
#![no_std]

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

use core::hint::black_box;

static DATA: [u8; 64] = {
    let mut a = [0u8; 64];
    let mut i = 0;
    while i < 64 {
        a[i] = (i as u8).wrapping_mul(37);
        i += 1;
    }
    a
};

#[inline(never)]
fn slice_of(a: usize, b: usize) -> &'static [u8] {
    let (lo, hi) = if a < b { (a, b) } else { (b, a) };
    &DATA[lo % 64..(hi % 64).max(lo % 64)]
}

#[inline(never)]
fn word(a: u32) -> &'static str {
    if a & 1 == 0 { "even-string" } else { "odd" }
}

#[inline(never)]
fn floats(a: u32) -> (f32, f32) {
    (a as f32 * 0.5, f32::from_bits(0x7fa0_0000 | (a & 0xff)))
}

#[inline(never)]
fn letter(a: u32) -> (char, bool) {
    (char::from_u32(0x41 + a % 26).unwrap_or('?'), a > 10)
}

#[inline(never)]
fn maybe(a: u64) -> Option<u64> {
    if a % 3 == 0 {
        None
    } else {
        Some(a.wrapping_mul(5))
    }
}

#[inline(never)]
fn checked(a: u32) -> Result<u32, i32> {
    if a & 2 == 0 { Ok(a) } else { Err(-(a as i32)) }
}

#[inline(never)]
fn even(n: u32, acc: u64) -> (bool, u32) {
    if n == 0 {
        (true, acc as u32)
    } else {
        odd(n - 1, acc.wrapping_mul(3).wrapping_add(1))
    }
}

#[inline(never)]
fn odd(n: u32, acc: u64) -> (bool, u32) {
    if n == 0 {
        (false, acc as u32)
    } else {
        let (b, c) = even(n - 1, acc ^ 5);
        (!b, c.wrapping_add(1))
    }
}

#[inline(never)]
fn wide(a: u64) -> i128 {
    (a as i128).wrapping_mul(-0x1_0000_0001_i128)
}

#[inline(never)]
fn negate(a: u64) -> i128 {
    -(a as i128)
}

#[inline(never)]
fn wide_pair(a: i128, b: u64) -> (u128, i128) {
    (
        (a as u128).rotate_right(17) ^ wide(b) as u128,
        a.wrapping_mul(b as i128 | 1) / 7,
    )
}

#[inline(never)]
fn select(k: u32) -> fn(u64) -> i128 {
    if k & 1 == 0 { wide } else { negate }
}

static POINTERS: [fn(u64) -> i128; 2] = [wide, negate];

trait Shape {
    fn measure(&self, k: u32) -> (u64, u32);
}

struct Square(u32);
struct Line(u64);

impl Shape for Square {
    fn measure(&self, k: u32) -> (u64, u32) {
        (self.0 as u64 * self.0 as u64 + k as u64, self.0 ^ k)
    }
}

impl Shape for Line {
    fn measure(&self, k: u32) -> (u64, u32) {
        (self.0.rotate_left(k % 64), k.wrapping_mul(3))
    }
}

#[inline(never)]
fn measure(shape: &dyn Shape, k: u32) -> (u64, u32) {
    shape.measure(k)
}

fn fold128(v: i128) -> u64 {
    v as u64 ^ (v >> 64) as u64
}

#[no_mangle]
pub extern "C" fn pairs(x: u32) -> u64 {
    let s = slice_of(x as usize, (x as usize).wrapping_mul(7));
    let mut h = s.len() as u64;
    for b in s {
        h = h.wrapping_mul(31) ^ *b as u64;
    }
    let t = word(x);
    h ^= t.len() as u64 ^ t.as_bytes()[0] as u64;
    let (a, b) = floats(x);
    h ^= a.to_bits() as u64 ^ (b.to_bits() as u64) << 32;
    let (c, d) = letter(x);
    h ^= c as u64 ^ d as u64;
    h ^= maybe(x as u64).unwrap_or(0xdead);
    h ^= match checked(x) {
        Ok(v) => v as u64,
        Err(e) => e as u64 ^ 0x5a5a,
    };
    let (e, f) = even(x % 20, x as u64);
    h ^ e as u64 ^ f as u64
}

#[no_mangle]
pub extern "C" fn wides(x: u32, y: u32) -> u64 {
    let (u, w) = wide_pair(-(x as i128) * 99, y as u64);
    let mut h = fold128(u as i128) ^ fold128(w);
    let f = select(x);
    h ^= fold128(f(y as u64 + 1));
    let g = black_box(wide as fn(u64) -> i128);
    h ^= fold128(g(3) >> 2);
    h ^= (g as usize == select(0) as usize) as u64;
    h ^ fold128((POINTERS[(y & 1) as usize])(x as u64))
}

#[no_mangle]
pub extern "C" fn dynamic(x: u32, y: u32) -> u64 {
    let square = Square(x % 1000);
    let line = Line(0x1234_5678_9abc ^ y as u64);
    let shape: &dyn Shape = if x % 3 == 0 { &square } else { &line };
    let (a, b) = measure(black_box(shape), y);
    let scale = |v: u32| -> (u64, i128) { (v as u64 * 3, wide(v as u64) ^ 1) };
    let c: &dyn Fn(u32) -> (u64, i128) = black_box(&scale);
    let (d, e) = c(x ^ y);
    a ^ b as u64 ^ d ^ fold128(e)
}
