// wasm32 execution-differential corpus: call ABI and iterator-state shapes.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
//@ compile-flags: -C overflow-checks=off
//
// Built without overflow checks so `<<` / `>>` on narrow integers lower to
// MIR's masking `Shl` / `Shr` rather than a checked panic. Covers, on wasm32:
// * small by-value aggregates rustc's Rust ABI casts to one integer
//   (`PassMode::Cast`): `[u8; 4]`, `[u8; 2]`, `[u16; 2]`, 3-byte structs,
//   `RangeInclusive<u8>`, `Ipv4Addr`, small enums, as arguments and returns of
//   direct, `fn`-pointer, `dyn` and closure calls;
// * indirect calls (`fn` pointers, `dyn` methods, `dyn Fn`) returning 5-16
//   byte aggregates through a caller-allocated buffer;
// * closures taking scalar-pair aggregates by value;
// * `usize` iterator state: `take`/`skip`/`enumerate` counts, the `zip`
//   `index`/`len` cursor, `step_by` over signed ranges, and `zip` over `Range<u64>` / `Range<i64>` (core's general `Zip` on a
//   32-bit target) and `Range<usize>`;
// * narrow shifts whose amount must be masked to the value's width;
// * a deref that loads a thin (4-byte) pointer out of memory.

#![no_std]
#![allow(dead_code, arithmetic_overflow, clippy::all)]

use core::hint::black_box;
use core::net::Ipv4Addr;
use core::ops::RangeInclusive;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::arch::wasm32::unreachable()
}

static A: [u32; 8] = [3, 1, 4, 1, 5, 9, 2, 6];
static B: [u32; 6] = [7, 2, 8, 1, 8, 2];
static F: [f64; 5] = [1.5, -2.0, 0.25, 8.0, 3.0];

/// Leaves non-zero bytes in the shadow-stack region the next frame reuses, so
/// an access wider than its field reads garbage instead of zeros.
#[inline(never)]
fn dirty(v: u32) -> u32 {
    let a = [v; 32];
    black_box(&a);
    a[3]
}

// ---- iterator `usize` state -------------------------------------------------

#[inline(never)]
fn take_sum(hi: u32, t: usize) -> u32 {
    (0..hi).take(t).sum()
}
#[inline(never)]
fn skip_sum(hi: u32, k: usize) -> u32 {
    (0..hi).skip(k).sum()
}
#[inline(never)]
fn skip_take(lo: u32, hi: u32, k: usize, t: usize) -> u64 {
    (lo..hi).skip(k).take(t).map(|x| x as u64 + 1).sum()
}
#[no_mangle]
pub extern "C" fn it_take_skip(n: u32, k: u32) -> u64 {
    dirty(u32::MAX);
    let a = take_sum(n % 20, (k % 12) as usize) as u64;
    dirty(u32::MAX);
    let b = skip_sum(n % 20, (k % 12) as usize) as u64;
    let c = skip_take(1, 30, (n % 12) as usize, (k % 12) as usize);
    a | (b << 16) | (c << 32)
}
#[no_mangle]
pub extern "C" fn it_take_slice(n: u32, t: u32) -> u64 {
    dirty(u32::MAX);
    let mut s = 0u64;
    for x in A[..(n % 9) as usize].iter().take((t % 10) as usize) {
        s = s * 10 + *x as u64;
    }
    s
}
#[no_mangle]
pub extern "C" fn it_enumerate(n: u32) -> u64 {
    dirty(u32::MAX);
    let mut s = 0u64;
    for (i, x) in A[..(n % 9) as usize].iter().take(6).enumerate() {
        s = s * 31 + (i as u64) * 100 + *x as u64;
    }
    s
}
#[no_mangle]
pub extern "C" fn it_enumerate_map(n: u32) -> u64 {
    A[..(n % 9) as usize]
        .iter()
        .enumerate()
        .map(|(i, x)| (i as u64 + 1) * (*x as u64))
        .sum()
}
#[no_mangle]
pub extern "C" fn it_zip_slices(n: u32, m: u32) -> u64 {
    dirty(u32::MAX);
    let mut s = 0u64;
    for (x, y) in A[..(n % 9) as usize]
        .iter()
        .zip(B[..(m % 7) as usize].iter())
    {
        s = s * 31 + (*x ^ (*y << 4)) as u64;
    }
    s
}
#[no_mangle]
pub extern "C" fn it_zip_map(n: u32, m: u32) -> u64 {
    A[..(n % 9) as usize]
        .iter()
        .zip(B[..(m % 7) as usize].iter())
        .map(|(x, y)| (*x as u64) * 10 + *y as u64)
        .sum()
}
#[no_mangle]
pub extern "C" fn it_zip_dot(n: u32) -> f64 {
    F[..(n % 6) as usize]
        .iter()
        .zip(F[1..].iter())
        .map(|(x, y)| x * y)
        .sum()
}
#[no_mangle]
pub extern "C" fn it_zip_range_u64(lo: u64, hi: u64) -> u64 {
    let mut c = 0u64;
    let mut s = 0u64;
    for (i, y) in (lo % 5..hi % 1000).zip(A.iter()) {
        s = s.wrapping_mul(3).wrapping_add(i ^ *y as u64);
        c += 1;
    }
    (c << 48) | s
}
#[no_mangle]
pub extern "C" fn it_take_zip_range_u64(lo: u64, hi: u64) -> u64 {
    // An adapter wrapping core's general `Zip` (a `Range<u64>` side on wasm32).
    let mut s = 0u64;
    for (y, i) in A.iter().zip(lo % 7..hi % 30).take(5) {
        s = s.wrapping_mul(3).wrapping_add(i ^ *y as u64);
    }
    s
}
#[no_mangle]
pub extern "C" fn it_zip_range_u64_big(k: u32) -> u64 {
    // A u64 range whose bounds do not fit 32 bits.
    let lo = (1u64 << 32) + (k % 7) as u64;
    let mut s = 0u64;
    for (i, y) in (lo..lo + 5).zip(B.iter()) {
        s = s
            .wrapping_mul(1_000_003)
            .wrapping_add(i)
            .wrapping_add(*y as u64);
    }
    s
}
#[no_mangle]
pub extern "C" fn it_zip_range_i64(lo: i64) -> i64 {
    let mut s = 0i64;
    for (i, y) in ((lo % 7) - 3..6).zip(A.iter()) {
        s = s * 7 + i * (*y as i64);
    }
    s
}
#[no_mangle]
pub extern "C" fn it_zip_range_usize(n: u32) -> u64 {
    let mut s = 0u64;
    for (i, y) in (0..(n % 11) as usize).zip(B.iter()) {
        s = s * 13 + (i as u64) * (*y as u64);
    }
    s
}
#[no_mangle]
pub extern "C" fn it_zip_range_u32(n: u32) -> u64 {
    let mut s = 0u64;
    for (i, y) in ((n % 5)..(n % 17)).zip(A.iter()) {
        s = s * 17 + (i as u64) + (*y as u64) * 1000;
    }
    s
}
#[no_mangle]
pub extern "C" fn it_step_by_i64(k: i64) -> i64 {
    let mut s = 0i64;
    for i in ((k % 9) - 20..20i64).step_by(3) {
        s = s * 3 + i;
    }
    s
}
#[no_mangle]
pub extern "C" fn it_step_by_i32(k: i32) -> i64 {
    let mut s = 0i64;
    for i in ((k % 9) - 10..15i32).step_by(4) {
        s = s * 5 + i as i64;
    }
    s
}

// ---- narrow shifts ----------------------------------------------------------

#[inline(never)]
fn shifts(a: u32, b: u32) -> u64 {
    let x8 = a as u8;
    let y8 = a as i8;
    let x16 = a as u16;
    let y16 = a as i16;
    let mut z = a as u16;
    z <<= b;
    let mut w = a as i8;
    w >>= b as u8;
    ((x8 << b) as u64)
        ^ (((x8 >> b) as u64) << 8)
        ^ (((y8 >> b) as u8 as u64) << 16)
        ^ (((x16 << b) as u64) << 24)
        ^ (((y16 >> (b as i16)) as u16 as u64) << 40)
        ^ ((z as u64) << 20)
        ^ ((w as u8 as u64) << 56)
}
#[no_mangle]
pub extern "C" fn sh_narrow(a: u32, b: u32) -> u64 {
    shifts(a, b)
}
#[no_mangle]
pub extern "C" fn sh_narrow_const(a: u32) -> u64 {
    let x = a as u8;
    let y = a as i16;
    ((x << 9) as u64) | (((y >> 17) as u16 as u64) << 8) | (((x >> 12) as u64) << 24)
}

// ---- one-integer `PassMode::Cast` aggregates --------------------------------

#[derive(Clone, Copy)]
struct Rgb {
    r: u8,
    g: u8,
    b: u8,
}
#[derive(Clone, Copy)]
struct Mixed {
    a: u8,
    b: u16,
    c: u8,
}
#[derive(Clone, Copy)]
enum Light {
    Red(u8),
    Green(u8, bool),
    Off,
}

#[inline(never)]
fn bytes_of(v: u32) -> [u8; 4] {
    v.to_le_bytes()
}
#[inline(never)]
fn from_bytes(b: [u8; 4]) -> u32 {
    u32::from_be_bytes(b)
}
#[inline(never)]
fn swap2(b: [u8; 2]) -> [u8; 2] {
    [b[1], b[0].wrapping_add(1)]
}
#[inline(never)]
fn halves(v: u32) -> [u16; 2] {
    [(v >> 16) as u16, v as u16]
}
#[inline(never)]
fn rgb(v: u32) -> Rgb {
    Rgb {
        r: v as u8,
        g: (v >> 8) as u8,
        b: (v >> 16) as u8,
    }
}
#[inline(never)]
fn rgb_mix(c: Rgb, d: Rgb) -> Rgb {
    Rgb {
        r: c.r ^ d.b,
        g: c.g.wrapping_add(d.g),
        b: c.b.wrapping_sub(d.r),
    }
}
#[inline(never)]
fn mixed(m: Mixed) -> Mixed {
    Mixed {
        a: m.c,
        b: m.b.rotate_left(3),
        c: m.a,
    }
}
#[inline(never)]
fn light_of(v: u32) -> Light {
    match v % 3 {
        0 => Light::Red(v as u8),
        1 => Light::Green((v >> 3) as u8, v & 8 != 0),
        _ => Light::Off,
    }
}
#[inline(never)]
fn light_code(l: Light) -> u32 {
    match l {
        Light::Red(x) => 1000 + x as u32,
        Light::Green(x, b) => 2000 + x as u32 * 2 + b as u32,
        Light::Off => 3,
    }
}
#[inline(never)]
fn narrow_u16(v: i64) -> Result<u16, i8> {
    u16::try_from(v).map_err(|_| (v % 100) as i8)
}
#[inline(never)]
fn range_sum(r: RangeInclusive<u8>) -> u32 {
    let mut s = 0u32;
    for x in r {
        s = s * 3 + x as u32;
    }
    s
}
#[inline(never)]
fn octets(ip: Ipv4Addr) -> u32 {
    u32::from(ip).rotate_left(8)
}

#[no_mangle]
pub extern "C" fn cast_bytes(v: u32) -> u32 {
    let b = bytes_of(v);
    let s = swap2([b[1], b[3]]);
    from_bytes(b) ^ ((s[0] as u32) << 8 | s[1] as u32)
}
#[no_mangle]
pub extern "C" fn cast_std_bytes(v: u32, w: u32) -> u64 {
    let a = u32::from_le_bytes(w.to_be_bytes());
    let b = u16::from_le_bytes((v as u16).to_be_bytes());
    let h = halves(v ^ w);
    ((a as u64) << 32) | ((b as u64) << 16) | (h[0] ^ h[1].rotate_left(4)) as u64
}
#[no_mangle]
pub extern "C" fn cast_structs(v: u32, w: u32) -> u64 {
    let c = rgb_mix(rgb(v), rgb(w));
    let m = mixed(Mixed {
        a: v as u8,
        b: (w >> 3) as u16,
        c: (v >> 24) as u8,
    });
    (c.r as u64)
        | (c.g as u64) << 8
        | (c.b as u64) << 16
        | (m.a as u64) << 24
        | (m.b as u64) << 32
        | (m.c as u64) << 48
}
#[no_mangle]
pub extern "C" fn cast_enums(v: u32, w: i64) -> u64 {
    let code = light_code(light_of(v)) as u64;
    let r = match narrow_u16(w) {
        Ok(x) => x as u64,
        Err(e) => 0x10000 + (e as u8) as u64,
    };
    (code << 32) | r
}
#[no_mangle]
pub extern "C" fn cast_range_inclusive(lo: u32, hi: u32) -> u32 {
    let lo = (lo % 40) as u8;
    let hi = (hi % 40) as u8;
    let mut s = range_sum(lo..=hi);
    for x in lo..=hi.saturating_add(2) {
        s = s.wrapping_mul(5).wrapping_add(x as u32);
    }
    s
}
#[no_mangle]
pub extern "C" fn cast_ipv4(v: u32) -> u32 {
    let ip = Ipv4Addr::from(v);
    let o = ip.octets();
    octets(ip) ^ octets(Ipv4Addr::new(o[3], o[2], o[1], o[0]))
}

// ---- indirect calls ---------------------------------------------------------

trait Shape {
    fn pair(&self, k: u32) -> (u64, u8);
    fn tag(&self, k: u32) -> [u8; 3];
    fn wide(&self, k: u32) -> (u32, u64);
}
struct Sq(u32);
struct Tri(u64);
impl Shape for Sq {
    fn pair(&self, k: u32) -> (u64, u8) {
        (self.0 as u64 * k as u64, (k ^ self.0) as u8)
    }
    fn tag(&self, k: u32) -> [u8; 3] {
        [self.0 as u8, k as u8, 7]
    }
    fn wide(&self, k: u32) -> (u32, u64) {
        (k.rotate_left(self.0 % 32), self.0 as u64 | (k as u64) << 32)
    }
}
impl Shape for Tri {
    fn pair(&self, k: u32) -> (u64, u8) {
        (self.0 ^ k as u64, 9)
    }
    fn tag(&self, k: u32) -> [u8; 3] {
        [(self.0 >> 8) as u8, (k >> 8) as u8, k as u8]
    }
    fn wide(&self, k: u32) -> (u32, u64) {
        (k.wrapping_mul(3), self.0.rotate_right(k % 64))
    }
}

fn pa(a: u64, b: u32) -> (u64, u32) {
    (a + 1, b ^ 7)
}
fn pb(a: u64, b: u32) -> (u64, u32) {
    (a ^ 3, b.wrapping_add(1))
}
fn ta(v: u32) -> [u8; 3] {
    [v as u8, (v >> 8) as u8, (v >> 16) as u8]
}
fn tb(v: u32) -> [u8; 3] {
    [(v >> 16) as u8, v as u8, 1]
}
fn tc(b: [u8; 2], k: u32) -> u32 {
    (b[0] as u32) << 8 | b[1] as u32 ^ k
}

#[inline(never)]
fn via_dyn(s: &dyn Shape, k: u32) -> u64 {
    let (a, b) = s.pair(k);
    let t = s.tag(k);
    let (c, d) = s.wide(k);
    a ^ (b as u64) << 56 ^ (t[0] as u64 | (t[1] as u64) << 8 | (t[2] as u64) << 16) ^ c as u64 ^ d
}
#[inline(never)]
fn via_dyn_fn(f: &dyn Fn(u32) -> (u64, u32), k: u32) -> u64 {
    let (a, b) = f(k);
    a ^ (b as u64) << 20
}

#[no_mangle]
pub extern "C" fn ind_fn_ptr(a: u64, k: u32) -> u64 {
    let f: fn(u64, u32) -> (u64, u32) = if k & 1 == 0 { pa } else { pb };
    let g: fn(u32) -> [u8; 3] = if k & 2 == 0 { ta } else { tb };
    let h: fn([u8; 2], u32) -> u32 = black_box(tc);
    let (x, y) = f(a, k);
    let t = g(k);
    x ^ (y as u64) << 1
        ^ (t[0] as u64 | (t[1] as u64) << 8 | (t[2] as u64) << 16)
        ^ h([t[2], t[0]], k) as u64
}
#[no_mangle]
pub extern "C" fn ind_dyn(v: u32, k: u32) -> u64 {
    let sq = Sq(v);
    let tri = Tri(v as u64 * 3);
    let s: &dyn Shape = if k & 1 == 0 { &sq } else { &tri };
    via_dyn(s, k)
}
#[no_mangle]
pub extern "C" fn ind_dyn_fn(v: u32, k: u32) -> u64 {
    let f = |x: u32| (x as u64 * v as u64, x ^ v);
    via_dyn_fn(&f, k)
}

// ---- closures taking aggregates by value ------------------------------------

#[derive(Clone, Copy)]
struct Pr {
    a: u64,
    b: u32,
}
#[inline(never)]
fn apply<F: Fn(Pr) -> u64>(f: F, p: Pr) -> u64 {
    f(p)
}
#[inline(never)]
fn fold_pairs<F: FnMut((u64, u32), u16) -> (u64, u32)>(mut f: F, n: u16) -> (u64, u32) {
    let mut acc = (1u64, 2u32);
    for i in 0..n {
        acc = f(acc, i);
    }
    acc
}
#[inline(never)]
fn apply_rgb<F: Fn(Rgb) -> u32>(f: F, c: Rgb) -> u32 {
    f(c)
}
static V: u32 = 5;

#[no_mangle]
pub extern "C" fn clo_pair_struct(x: u64, k: u32) -> u64 {
    apply(|p: Pr| p.a ^ p.b as u64, Pr { a: x, b: k })
}
#[no_mangle]
pub extern "C" fn clo_pair_tuple(a: u64, k: u32) -> u64 {
    let (x, y) = fold_pairs(
        |(p, q), i| {
            (
                p.wrapping_mul(a | 1) ^ i as u64,
                q.wrapping_add(i as u32) ^ k,
            )
        },
        (k % 30) as u16,
    );
    x ^ (y as u64) << 1
}
#[no_mangle]
pub extern "C" fn clo_option(a: u32, n: u32) -> u64 {
    let e = |o: Option<u64>| match o {
        Some(v) => v ^ 0x55,
        None => 7,
    };
    e(a.checked_shl(n % 40).map(|v| v as u64)) ^ e(None) << 8
}
#[no_mangle]
pub extern "C" fn clo_nested_option(a: u32) -> u32 {
    let f = |o: Option<Option<&u32>>| match o {
        None => 1000,
        Some(None) => 2000,
        Some(Some(r)) => *r,
    };
    f(match a % 3 {
        0 => None,
        1 => Some(None),
        _ => Some(Some(&V)),
    })
}
#[no_mangle]
pub extern "C" fn clo_cast_arg(v: u32) -> u32 {
    let k = v >> 3;
    apply_rgb(
        move |c: Rgb| (c.r as u32) << 16 | (c.g as u32) << 8 | c.b as u32 ^ k,
        rgb(v),
    )
}

// ---- thin-pointer loads -----------------------------------------------------

#[inline(never)]
fn ne_refs(x: &&u32, y: &&u32) -> bool {
    x != y
}
#[no_mangle]
pub extern "C" fn deref_thin(a: u32, b: u32) -> u32 {
    let xs = [a, b, a ^ b, 7];
    let (p, q) = (&a, &b);
    (ne_refs(&p, &q) as u32)
        | xs.iter()
            .rposition(|&v| v > b)
            .map(|i| i as u32 * 2)
            .unwrap_or(77)
}
