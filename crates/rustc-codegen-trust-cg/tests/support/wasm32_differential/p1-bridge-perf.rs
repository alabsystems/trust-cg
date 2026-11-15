// 128-bit multiply overflow, constant aggregate images and bit intrinsics on
// wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// * `checked_mul`/`overflowing_mul`/`saturating_mul`/`wrapping_mul` on
//   `u128`/`i128` reach the wasm lane as one `Inst::Overflow { MulOverflow }`.
//   The operands cover the edge classes of its two-limb lowering: 0, 1, -1,
//   MAX, MIN, the 2^63/2^64 limb boundaries, power-of-two products that land
//   on, one bit below and one bit above the overflow boundary, `MIN * -1`, and
//   mixed patterns.
// * Constant aggregates of two bytes or more are read from their read-only
//   data global: a never-written lookup table (`TABLE[i]`, core's `isqrt`
//   tables) addresses the global directly; a table that is written, borrowed,
//   address-compared, moved into a by-value argument, or carries relocations
//   or padding is copied into its own slot first, and every call must still see
//   the constant's bytes.
// * The integer bit methods (`leading_zeros`, `trailing_ones`, `rotate_left`,
//   `swap_bytes`, `reverse_bits`, `is_power_of_two`, ...) at every width,
//   including `usize`, whose width on wasm32 is 32 bits.
#![no_std]

// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3 -Ccodegen-units=4

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[inline(never)]
fn fold128(x: u128) -> i64 {
    ((x as u64) ^ ((x >> 64) as u64).rotate_left(17)) as i64
}

#[inline(never)]
fn wide(a: i64, b: i64) -> u128 {
    ((a as u64 as u128) << 64) | (b as u64 as u128)
}

const EDGES_U128: [u128; 16] = [
    0,
    1,
    2,
    3,
    u128::MAX,
    u128::MAX - 1,
    1 << 63,
    1 << 64,
    (1 << 64) - 1,
    (1 << 64) + 1,
    1 << 127,
    (1 << 127) - 1,
    0x5555_5555_5555_5555_5555_5555_5555_5555,
    0xffff_ffff_ffff_ffff,
    0x1_0000_0001,
    10_000_000_000_000_000_000,
];

const EDGES_I128: [i128; 16] = [
    0,
    1,
    -1,
    2,
    -2,
    i128::MAX,
    i128::MIN,
    i128::MIN + 1,
    1 << 63,
    -(1 << 63),
    1 << 64,
    -(1 << 64),
    (1 << 64) - 1,
    1 << 126,
    -(1 << 126),
    -3,
];

#[inline(never)]
fn mulo_u128(x: u128, y: u128) -> i64 {
    let (w, o) = x.overflowing_mul(y);
    let c = match x.checked_mul(y) {
        Some(v) => fold128(v),
        None => -1,
    };
    fold128(w)
        ^ c.rotate_left(9)
        ^ fold128(x.saturating_mul(y)).rotate_left(21)
        ^ ((o as i64) << 62)
}

#[inline(never)]
fn mulo_i128(x: i128, y: i128) -> i64 {
    let (w, o) = x.overflowing_mul(y);
    let c = match x.checked_mul(y) {
        Some(v) => fold128(v as u128),
        None => -1,
    };
    fold128(w as u128)
        ^ c.rotate_left(9)
        ^ fold128(x.saturating_mul(y) as u128).rotate_left(21)
        ^ fold128(x.wrapping_mul(y) as u128).rotate_left(33)
        ^ ((o as i64) << 62)
}

/// Both operands from the edge table.
#[no_mangle]
pub extern "C" fn mulo_u128_edges(a: i64, b: i64) -> i64 {
    let x = EDGES_U128[a.rem_euclid(16) as usize];
    let y = EDGES_U128[b.rem_euclid(16) as usize];
    mulo_u128(x, y)
}

#[no_mangle]
pub extern "C" fn mulo_i128_edges(a: i64, b: i64) -> i64 {
    let x = EDGES_I128[a.rem_euclid(16) as usize];
    let y = EDGES_I128[b.rem_euclid(16) as usize];
    mulo_i128(x, y)
}

/// Full 128-bit patterns built from both inputs, and 64-bit operands.
#[no_mangle]
pub extern "C" fn mulo_u128_patterns(a: i64, b: i64) -> i64 {
    mulo_u128(wide(a, b), wide(b, a))
        ^ mulo_u128(a as u64 as u128, b as u64 as u128).rotate_left(5)
        ^ mulo_u128(wide(a, 0), b as u64 as u128).rotate_left(11)
}

#[no_mangle]
pub extern "C" fn mulo_i128_patterns(a: i64, b: i64) -> i64 {
    mulo_i128(wide(a, b) as i128, wide(b, a) as i128)
        ^ mulo_i128(a as i128, b as i128).rotate_left(5)
        ^ mulo_i128(wide(a, 0) as i128, b as i128).rotate_left(11)
}

/// `2^i * 2^j` with `i + j` at 126..=129: below, on and above the boundary
/// (one bit lower for the signed type), times 1 or 3, with either sign.
#[no_mangle]
pub extern "C" fn mulo_pow2_boundary(a: i64, b: i64) -> i64 {
    let i = (a & 127) as u32;
    let j = (128 + (b & 3) as u32 - 2).wrapping_sub(i) & 127;
    let k = if b & 4 != 0 { 3 } else { 1 };
    let x = 1u128 << i;
    let y = (1u128 << j).wrapping_mul(k);
    let sx = if b & 8 != 0 {
        (x as i128).wrapping_neg()
    } else {
        x as i128
    };
    mulo_u128(x, y)
        ^ mulo_i128(sx, y as i128).rotate_left(3)
        ^ mulo_i128(sx, (y as i128).wrapping_neg()).rotate_left(7)
}

// ---- constant aggregates ----

const TABLE: [u32; 64] = {
    let mut t = [0u32; 64];
    let mut i = 0;
    while i < 64 {
        t[i] = (i as u32).wrapping_mul(0x9E37_79B9) ^ (i as u32) << 3;
        i += 1;
    }
    t
};

const PAIRS: [(u8, u8); 256] = {
    let mut t = [(0u8, 0u8); 256];
    let mut i = 0;
    while i < 256 {
        t[i] = ((i as u8).wrapping_mul(7), (i as u8) ^ 0x5a);
        i += 1;
    }
    t
};

const PADDED: [(u8, u32); 6] = [
    (1, 10),
    (2, 20),
    (3, 30),
    (4, 40),
    (5, 50),
    (6, 0xdead_beef),
];

const NAMES: [&str; 4] = ["zero", "one", "two", "three!"];

const OPTS: [Option<u32>; 8] = [
    None,
    Some(1),
    Some(0),
    None,
    Some(u32::MAX),
    Some(7),
    None,
    Some(9),
];

const FLOATS: [f64; 5] = [1.5, -0.0, f64::INFINITY, 2.0e-310, 1.0e300];

#[no_mangle]
pub extern "C" fn tbl_lookup(a: i32, b: i32) -> i32 {
    let t = TABLE;
    let p = PAIRS;
    (t[(a & 63) as usize] ^ t[(b & 63) as usize].rotate_left(5)) as i32
        ^ (p[(a & 255) as usize].0 as i32) << 8
        ^ p[(b & 255) as usize].1 as i32
}

/// A table written after its constant assignment: each call starts from the
/// constant again.
#[no_mangle]
pub extern "C" fn tbl_written(a: i32, b: i32) -> i32 {
    let mut t = TABLE;
    t[(a & 63) as usize] ^= b as u32;
    t[(b & 63) as usize] = t[(b & 63) as usize].wrapping_add(1);
    let mut s = 0u32;
    for v in t.iter() {
        s = s.rotate_left(1) ^ v;
    }
    s as i32
}

#[inline(never)]
fn sum_ref(t: &[u32; 64], n: usize) -> u32 {
    t[..n % 65].iter().fold(0, |acc, v| acc.rotate_left(3) ^ v)
}

#[inline(never)]
fn bump(mut t: [u32; 64], i: usize) -> u32 {
    t[i % 64] = t[i % 64].wrapping_mul(3);
    t.iter().fold(0, |acc, v| acc.wrapping_add(*v))
}

/// Borrowed, address-compared and moved tables keep their own slots.
#[no_mangle]
pub extern "C" fn tbl_borrowed(a: i32, b: i32) -> i32 {
    let t = TABLE;
    let u = TABLE;
    let same = core::ptr::eq(&t, &t) as u32;
    let distinct = !core::ptr::eq(&t, &u) as u32;
    let r = sum_ref(&t, a as usize) ^ bump(TABLE, b as usize) ^ bump(TABLE, b as usize);
    (r ^ same << 30 ^ distinct << 29) as i32
}

#[no_mangle]
pub extern "C" fn tbl_shapes(a: i32, b: i32) -> i64 {
    let pad = PADDED;
    let names = NAMES;
    let opts = OPTS;
    let floats = FLOATS;
    let (x, y) = pad[(a as u32 % 6) as usize];
    let name = names[(b as u32 % 4) as usize];
    let o = opts[(a as u32 % 8) as usize].map_or(-1, |v| v as i64);
    let f = floats[(b as u32 % 5) as usize].to_bits() as i64;
    (x as i64) << 40
        ^ y as i64
        ^ (name.len() as i64) << 33
        ^ (name.as_bytes()[0] as i64) << 50
        ^ o.rotate_left(13)
        ^ f
}

const B2: [u8; 2] = [0x81, 0x7f];
const B3: [u8; 3] = [1, 0xfe, 3];
const B4: [u8; 4] = [9, 0, 0x80, 0xff];
const B8: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];
const B16: [u8; 16] = *b"0123456789abcdef";
const B17: [u8; 17] = *b"0123456789abcdefg";
const H4: [u16; 4] = [3, 500, 0x8000, 0xffff];
const W3: [u32; 3] = [0xdead_beef, 1, 0x8000_0000];
const SMALL_PAD: [(u8, u16); 2] = [(0xa5, 0x1234), (0x5a, 0xfedc)];

#[inline(never)]
fn first_byte(t: &[u8]) -> u8 {
    t[0]
}

/// Small constant images (2 to 17 bytes), read-only and written: each call
/// starts from the constant's bytes.
#[no_mangle]
pub extern "C" fn tbl_small(a: i32, b: i32) -> i64 {
    let (i, j) = (a as u32 as usize, b as u32 as usize);
    let r2 = B2;
    let r3 = B3;
    let r16 = B16;
    let read = (r2[i % 2] as i64) ^ (r3[j % 3] as i64) << 8 ^ (r16[i % 16] as i64) << 16;
    let mut w4 = B4;
    w4[i % 4] ^= b as u8;
    let mut w8 = B8;
    w8[j % 8] = w8[i % 8].wrapping_add(a as u8);
    let mut w17 = B17;
    w17[i % 17] = b as u8;
    let mut h = H4;
    h[i % 4] = b as u16;
    let mut w = W3;
    w[j % 3] ^= a as u32;
    let mut p = SMALL_PAD;
    p[i % 2].1 = p[j % 2].1.wrapping_add(b as u16);
    let b2 = B2;
    let same = core::ptr::eq(&b2, &b2) as i64;
    let written = (w4[j % 4] as i64)
        ^ (w8[i % 8] as i64) << 8
        ^ (w17[j % 17] as i64) << 16
        ^ (h[j % 4] as i64) << 24
        ^ (w[i % 3] as i64) << 32
        ^ (p[j % 2].0 as i64 ^ p[i % 2].1 as i64) << 40
        ^ (first_byte(&b2) as i64) << 56
        ^ same << 63;
    read ^ written.rotate_left(5)
}

/// core's integer square roots read `int_sqrt`'s constant tables.
#[no_mangle]
pub extern "C" fn isqrt_all(a: i64, b: i64) -> i64 {
    let x = a as u64;
    let w = wide(a, b);
    (x as u8).isqrt() as i64
        ^ ((x as u16).isqrt() as i64) << 8
        ^ ((x as u32).isqrt() as i64) << 16
        ^ (x.isqrt() as i64).rotate_left(24)
        ^ fold128(w.isqrt()).rotate_left(40)
        ^ a.checked_isqrt().unwrap_or(-7)
}

// ---- bit intrinsics ----

macro_rules! bits_of {
    ($name:ident, $t:ty) => {
        #[no_mangle]
        pub extern "C" fn $name(a: i64, b: i64) -> i64 {
            let x = wide(a, b) as $t;
            let n = b as u32;
            let r = (x.leading_zeros() as i64)
                ^ (x.trailing_zeros() as i64) << 8
                ^ (x.count_ones() as i64) << 16
                ^ (x.count_zeros() as i64) << 24
                ^ (x.leading_ones() as i64) << 32
                ^ (x.trailing_ones() as i64) << 40
                ^ (x.is_positive_power_of_two() as i64) << 48;
            r ^ fold128(x.rotate_left(n) as u128)
                ^ fold128(x.rotate_right(n ^ 5) as u128).rotate_left(3)
                ^ fold128(x.rotate_left(3) as u128).rotate_left(7)
                ^ fold128(x.rotate_right(200) as u128).rotate_left(11)
                ^ fold128(x.swap_bytes() as u128).rotate_left(13)
                ^ fold128(x.reverse_bits() as u128).rotate_left(19)
                ^ fold128(x.to_be() as u128).rotate_left(23)
        }
    };
}

trait PowerOfTwo {
    fn is_positive_power_of_two(self) -> bool;
}

macro_rules! pow2_unsigned {
    ($($t:ty),*) => {$(
        impl PowerOfTwo for $t {
            fn is_positive_power_of_two(self) -> bool {
                self.is_power_of_two()
            }
        }
    )*};
}

macro_rules! pow2_signed {
    ($($t:ty => $u:ty),*) => {$(
        impl PowerOfTwo for $t {
            fn is_positive_power_of_two(self) -> bool {
                self > 0 && (self as $u).is_power_of_two()
            }
        }
    )*};
}

pow2_unsigned!(u8, u16, u32, u64, u128, usize);
pow2_signed!(i8 => u8, i16 => u16, i32 => u32, i64 => u64, i128 => u128, isize => usize);

bits_of!(bits_u8, u8);
bits_of!(bits_i8, i8);
bits_of!(bits_u16, u16);
bits_of!(bits_i16, i16);
bits_of!(bits_u32, u32);
bits_of!(bits_i32, i32);
bits_of!(bits_u64, u64);
bits_of!(bits_i64, i64);
bits_of!(bits_u128, u128);
bits_of!(bits_i128, i128);
bits_of!(bits_usize, usize);
bits_of!(bits_isize, isize);

/// 32-bit scalars straight from the grid (no 64-bit carrier).
#[no_mangle]
pub extern "C" fn bits32(a: i32, b: i32) -> i32 {
    let x = a as u32;
    (x.leading_zeros() ^ x.trailing_zeros() << 6 ^ x.count_ones() << 12) as i32
        ^ x.rotate_left(b as u32) as i32
        ^ (b as i32).rotate_right(a as u32).swap_bytes()
        ^ x.reverse_bits() as i32
        ^ (x as usize).leading_zeros() as i32
}
