// wasm32 execution-differential corpus for rustc_codegen_trust_cg.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Every `extern "C"` export takes and returns scalars so `compare.mjs` can
// drive it from JavaScript; the bodies exercise what real Rust lowers to on
// wasm32: checked and wrapping arithmetic, overflow and division-by-zero
// panics, `u128`/`i128`, float min/max/conversion, `Option`/`Result`/`char`
// niches, statics (`static`, `static mut`, pointer-bearing), slices, arrays,
// tuples, structs passed and returned by value, enums with payloads, function
// pointers, closures, iterators, `str` parsing and `core::fmt`.

#![no_std]
#![allow(dead_code)]

// The panic handler aborts like the bridge's `panic=abort` lowering (a wasm
// trap), so a checked panic is the same observable outcome on both sides.
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

#[no_mangle]
pub extern "C" fn add_ck(a: i32, b: i32) -> i32 {
    a + b
}
#[no_mangle]
pub extern "C" fn sum_to(n: u32) -> u64 {
    let mut s = 0u64;
    let mut i = 0u32;
    while i < n {
        s += i as u64;
        i += 1;
    }
    s
}
#[no_mangle]
pub extern "C" fn collatz(mut n: u64) -> u32 {
    let mut k = 0;
    while n != 1 && k < 1000 {
        n = if n % 2 == 0 { n / 2 } else { 3 * n + 1 };
        k += 1;
    }
    k
}
#[no_mangle]
pub extern "C" fn fib(n: u32) -> u64 {
    let (mut a, mut b) = (0u64, 1u64);
    for _ in 0..n {
        let t = a.wrapping_add(b);
        a = b;
        b = t;
    }
    a
}
#[no_mangle]
pub extern "C" fn isqrt(x: u64) -> u64 {
    if x < 2 {
        return x;
    }
    let mut lo = 1u64;
    let mut hi = x.min(4294967295);
    while lo < hi {
        let mid = lo + (hi - lo + 1) / 2;
        if mid.saturating_mul(mid) <= x {
            lo = mid
        } else {
            hi = mid - 1
        }
    }
    lo
}
#[no_mangle]
pub extern "C" fn clz(x: u32) -> u32 {
    x.leading_zeros()
}
#[no_mangle]
pub extern "C" fn tz(x: u64) -> u32 {
    x.trailing_zeros()
}
#[no_mangle]
pub extern "C" fn pop(x: u32) -> u32 {
    x.count_ones()
}
#[no_mangle]
pub extern "C" fn rot(x: u32, n: u32) -> u32 {
    x.rotate_left(n) ^ x.swap_bytes()
}
#[no_mangle]
pub extern "C" fn mix(x: u64) -> u64 {
    let mut h = x ^ 0x9e3779b97f4a7c15;
    h = (h ^ (h >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    h = (h ^ (h >> 27)).wrapping_mul(0x94d049bb133111eb);
    h ^ (h >> 31)
}
#[no_mangle]
pub extern "C" fn mulhi(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) >> 64) as u64
}
#[no_mangle]
pub extern "C" fn fdiv(a: f64, b: f64) -> f64 {
    a / b + a * 0.5
}
#[no_mangle]
pub extern "C" fn fmaxx(a: f64, b: f64) -> f64 {
    a.max(b) - b.min(a)
}
#[no_mangle]
pub extern "C" fn fconv(a: f64) -> i32 {
    a as i32
}
#[no_mangle]
pub extern "C" fn sat(a: i32, b: i32) -> i32 {
    a.saturating_add(b).saturating_mul(3)
}
#[no_mangle]
pub extern "C" fn cmp3(a: i32, b: i32) -> i32 {
    match a.cmp(&b) {
        core::cmp::Ordering::Less => -1,
        core::cmp::Ordering::Equal => 0,
        core::cmp::Ordering::Greater => 1,
    }
}
#[no_mangle]
pub extern "C" fn divs(a: i32, b: i32) -> i32 {
    if b == 0 {
        0
    } else {
        a.wrapping_div(b) + a.wrapping_rem(b)
    }
}
#[no_mangle]
pub extern "C" fn chk_div(a: u32, b: u32) -> u32 {
    a / b
}
#[no_mangle]
pub extern "C" fn opt(a: i32, b: i32) -> i32 {
    let o = if b > 0 { Some(a) } else { None };
    o.map(|v| v.wrapping_mul(2)).unwrap_or(-7)
}
#[no_mangle]
pub extern "C" fn res(a: i32, b: i32) -> i32 {
    let r: Result<i32, u8> = if a > b { Ok(a - b) } else { Err(3) };
    match r {
        Ok(v) => v,
        Err(e) => e as i32 * 100,
    }
}
static TABLE: [u32; 8] = [3, 1, 4, 1, 5, 9, 2, 6];
static mut COUNTER: u64 = 0;
#[derive(Clone, Copy)]
struct P {
    x: i32,
    y: i32,
    z: i64,
}
#[inline(never)]
fn mkp(a: i32, b: i32) -> P {
    P {
        x: a,
        y: b,
        z: a as i64 * b as i64,
    }
}
#[inline(never)]
fn norm1(p: P) -> i64 {
    (p.x as i64).abs() + (p.y as i64).abs() + p.z
}
#[no_mangle]
pub extern "C" fn structs(a: i32, b: i32) -> i64 {
    let p = mkp(a, b);
    let q = P { x: p.y, ..p };
    norm1(p) - norm1(q) + norm1(mkp(b, a))
}
enum Shape {
    Circle(u32),
    Rect { w: u32, h: u32 },
    Empty,
}
#[inline(never)]
fn area(s: &Shape) -> u32 {
    match s {
        Shape::Circle(r) => 3 * r * r,
        Shape::Rect { w, h } => w * h,
        Shape::Empty => 0,
    }
}
#[no_mangle]
pub extern "C" fn shapes(k: u32, a: u32) -> u32 {
    let a = a % 1000;
    let s = match k % 3 {
        0 => Shape::Circle(a),
        1 => Shape::Rect { w: a, h: a + 1 },
        _ => Shape::Empty,
    };
    area(&s) + area(&Shape::Rect { w: 2, h: k % 7 })
}
#[inline(never)]
fn slice_sum(xs: &[u32]) -> u64 {
    xs.iter().map(|&x| x as u64).sum()
}
#[no_mangle]
pub extern "C" fn slices(lo: u32, hi: u32) -> u64 {
    let lo = (lo % 9) as usize;
    let hi = (hi % 9) as usize;
    if lo > hi {
        return 0;
    }
    slice_sum(&TABLE[lo..hi]) * 10 + TABLE.len() as u64
}
#[no_mangle]
pub extern "C" fn index(i: u32) -> u32 {
    TABLE[i as usize]
}
#[no_mangle]
pub extern "C" fn wide(a: u64, b: u64) -> u64 {
    let x = a as u128 * b as u128 + 7;
    let y = x / (b as u128 | 1);
    let z = (x % 1_000_000_007) as u64;
    (y as u64) ^ z ^ ((x >> 70) as u64)
}
#[no_mangle]
pub extern "C" fn wides(a: i64, b: i64) -> i64 {
    let x = a as i128 * b as i128 - 5;
    (x >> 3) as i64 ^ (x.signum() as i64) ^ (x.count_ones() as i64)
}
#[inline(never)]
fn i128_pass(a: i128, b: u128) -> i128 {
    a.wrapping_mul(b as i128).wrapping_add(a >> 17)
}
#[no_mangle]
pub extern "C" fn i128call(a: i64, b: u64) -> i64 {
    let r = i128_pass(a as i128 * 1_000_003, b as u128 + (1u128 << 90));
    (r ^ (r >> 64)) as i64
}
fn dbl(x: u32) -> u32 {
    x.wrapping_mul(2)
}
fn inc(x: u32) -> u32 {
    x.wrapping_add(1)
}
fn sq(x: u32) -> u32 {
    x.wrapping_mul(x)
}
#[no_mangle]
pub extern "C" fn fnptrs(x: u32, k: u32) -> u32 {
    let fs: [fn(u32) -> u32; 3] = [dbl, inc, sq];
    let f = fs[(k % 3) as usize];
    f(f(x))
}
#[no_mangle]
pub extern "C" fn closures(x: i32, y: i32) -> i32 {
    let mut acc = 0i32;
    let mut add = |v: i32| acc = acc.wrapping_add(v);
    for i in 0..5 {
        add(x.wrapping_mul(i));
    }
    add(y);
    let c = move |z: i32| z.wrapping_sub(acc);
    c(100)
}
#[no_mangle]
pub extern "C" fn bump(n: u32) -> u64 {
    unsafe {
        COUNTER = COUNTER.wrapping_add(n as u64);
        COUNTER
    }
}
#[no_mangle]
pub extern "C" fn chars(c: u32) -> u32 {
    match char::from_u32(c) {
        Some(ch) => {
            (ch.is_alphabetic() as u32)
                | (ch.is_ascii_digit() as u32) << 1
                | (ch.len_utf8() as u32) << 4
                | (ch.to_ascii_uppercase() as u32) << 8
        }
        None => 0xffff_ffff,
    }
}
#[no_mangle]
pub extern "C" fn parse(n: u32) -> i64 {
    let src = ["123", "-45", "x9", "99999999999", "", "+7"];
    match src[(n % 6) as usize].parse::<i64>() {
        Ok(v) => v,
        Err(_) => -1,
    }
}
#[no_mangle]
pub extern "C" fn floats(a: f32, b: f32) -> f32 {
    let v = [a, b, a * b, a - b];
    v.iter().fold(0.0f32, |s, x| s + x.abs()) / (1.0 + b * b)
}
#[no_mangle]
pub extern "C" fn opts(a: u32, b: u32) -> u32 {
    let x = a
        .checked_sub(b)
        .and_then(|d| d.checked_mul(3))
        .filter(|v| v % 2 == 0);
    x.unwrap_or(1) + (a.checked_div(b).is_some() as u32)
}
#[no_mangle]
pub extern "C" fn tuples(a: u32, b: u32) -> u64 {
    let t = (a, b as u64, (a as u8, b as u16));
    let (x, y, (z, w)) = t;
    x as u64 + y * 3 + z as u64 + w as u64
}
struct Buf {
    b: [u8; 64],
    n: usize,
}
impl core::fmt::Write for Buf {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        for &c in s.as_bytes() {
            if self.n == 64 {
                return Err(core::fmt::Error);
            }
            self.b[self.n] = c;
            self.n += 1;
        }
        Ok(())
    }
}
#[no_mangle]
pub extern "C" fn fmt(a: i32, b: u32) -> u32 {
    use core::fmt::Write;
    let mut w = Buf { b: [0; 64], n: 0 };
    let _ = write!(w, "{}:{:x}/{:>5}", a, b, a as i64 * 3);
    let mut h = 0u32;
    for &c in &w.b[..w.n] {
        h = h.wrapping_mul(31).wrapping_add(c as u32);
    }
    h ^ w.n as u32
}
