// The shapes wasm32 round 16 rewrites, on wasm32 at O0 to O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// At O1 and above the wasm32 mid-end turns the bridge's
// `__trustcg_array_fill_iW` call of an element with one repeated byte into
// `memset` (`fill_call`), a packed struct's byte-by-byte copy into
// `memcopy` and the stores it was built from into the destination
// (`byte_copy`), respells the bridge's sign-reinterpreting copies before
// inlining (`retype_copy`), promotes a callee's temporaries before it is
// spliced, and promotes an iterator adapter's state stepped through its own
// reload; the lane's 128-bit division helper estimates the quotient of a
// divisor wider than 64 bits by one 128-by-64 division. The exports cover
// array repeats of every element width with a repeated byte (zero, all
// ones, 0x01) and the controls whose element bytes differ, packed structs
// returned, passed, copied and read unaligned, 128-bit division and
// remainder over divisors of every width (signed and unsigned), and zip /
// nth / find iterator chains with closures. LLVM is the oracle.
#![no_std]
#![allow(dead_code)]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

#[no_mangle]
pub extern "C" fn fill_u32(a: u32, b: u32) -> u32 {
    let mut v = [0u32; 64];
    let n = (b % 65) as usize;
    for (i, x) in v.iter_mut().enumerate().take(n) {
        *x = a.wrapping_mul(i as u32 + 1);
    }
    v[(a % 64) as usize] ^ v[63] ^ v[0]
}

#[no_mangle]
pub extern "C" fn fill_bytes(a: u32, b: u32) -> u32 {
    let mut v = [0u8; 100];
    v[(a % 100) as usize] = b as u8;
    v.iter()
        .fold(0u32, |s, x| s.wrapping_mul(31).wrapping_add(u32::from(*x)))
}

#[no_mangle]
pub extern "C" fn fill_ones(a: u32, b: u32) -> u64 {
    let mut v = [-1i64; 20];
    v[(b % 20) as usize] = i64::from(a);
    v[(a % 20) as usize] as u64 ^ v[19] as u64
}

#[no_mangle]
pub extern "C" fn fill_0101(a: u32, b: u32) -> u32 {
    let mut v = [0x0101u16; 33];
    v[(a % 33) as usize] = b as u16;
    u32::from(v[(b % 33) as usize]) + u32::from(v[32])
}

#[no_mangle]
pub extern "C" fn fill_seven(a: u32, b: u32) -> u32 {
    // The control: the element's bytes differ, so the helper call stays.
    let mut v = [7u32; 20];
    v[(a % 20) as usize] = b;
    v[(b % 20) as usize].wrapping_add(v[19])
}

#[repr(packed)]
#[derive(Clone, Copy)]
struct Pk {
    a: u8,
    x: f64,
    b: u16,
    y: f32,
}

#[inline(never)]
fn mkpk(k: u32, x: f64) -> Pk {
    Pk {
        a: k as u8,
        x,
        b: (k >> 8) as u16,
        y: x as f32,
    }
}

#[inline(never)]
fn sumpk(p: Pk) -> f64 {
    let x = p.x;
    let y = p.y;
    let b = p.b;
    p.a as f64 + x * 2.0 + b as f64 * 3.0 + y as f64 * 4.0
}

fn mkpk_inline(k: u32, x: f64) -> Pk {
    Pk {
        a: (k >> 3) as u8,
        x: x * 0.5,
        b: k as u16,
        y: x as f32 - 1.0,
    }
}

#[no_mangle]
pub extern "C" fn packed_sum(a: u32, b: u32) -> u64 {
    sumpk(mkpk(a, f64::from(b) * 0.25)).to_bits()
}

#[no_mangle]
pub extern "C" fn packed_ptr(a: u32, b: u32) -> u64 {
    let p = mkpk(a, f64::from(b) - 3.5);
    let q = core::ptr::addr_of!(p.x);
    unsafe { q.read_unaligned().to_bits() ^ u64::from(p.b) }
}

#[inline(never)]
fn step(s: f64, e: Pk) -> f64 {
    let xx = e.x;
    s * 2.0 + xx + e.y as f64 + f64::from(e.a)
}

#[no_mangle]
pub extern "C" fn packed_three(a: u32, b: u32) -> u64 {
    let e0 = mkpk_inline(a, f64::from(b));
    let e1 = mkpk_inline(b, -f64::from(a));
    let e2 = mkpk_inline(3, 0.5);
    step(step(step(0.0, e0), e1), e2).to_bits()
}

fn fold(x: u128) -> u64 {
    (x as u64) ^ ((x >> 64) as u64).rotate_left(29)
}

#[no_mangle]
pub extern "C" fn div_wide(a: u32, b: u32) -> u64 {
    let n = (u128::from(a) << 96) | (u128::from(b) << 40) | 0x1234_5678_9abc;
    let d = ((u128::from(b | 1)) << (64 + (a % 60))) | u128::from(a) | 1;
    fold(n / d) ^ fold(n % d).rotate_left(7)
}

#[no_mangle]
pub extern "C" fn div_near(a: u32, b: u32) -> u64 {
    // Divisors just above 2^64 and dividends whose quotient fills 64 bits.
    let n = (u128::MAX >> (a % 8)) ^ u128::from(b);
    let d = (1u128 << 64) + u128::from(a) * 0x1_0001;
    fold(n / d) ^ fold(n % d)
}

#[no_mangle]
pub extern "C" fn div_signed(a: u32, b: u32) -> u64 {
    let x = ((i128::from(a as i32)) << 100) - i128::from(b);
    let y = ((i128::from(b as i32)) << (65 + (a % 30))) | 3;
    let q = x.checked_div(y).unwrap_or(5);
    let r = x.checked_rem(y).unwrap_or(9);
    fold(q as u128) ^ fold(r as u128).rotate_left(3)
}

#[inline(never)]
fn mk7(a: f64, b: f64) -> [f64; 7] {
    [a, b, a + b, a * 0.5, -b, 1.25, a - 3.0]
}

#[no_mangle]
pub extern "C" fn zip_dot(a: u32, b: u32) -> u64 {
    let v = mk7(f64::from(a), f64::from(b));
    let w = mk7(f64::from(b), f64::from(a) * 0.75);
    let s: f64 = v.iter().zip(w.iter()).map(|(x, y)| x * y).sum();
    s.to_bits()
}

#[no_mangle]
pub extern "C" fn zip_min(a: u32, b: u32) -> u32 {
    let x = [1u16, 2, 3, 4];
    let y = [10u64, 20, 30, 40, 50];
    let mut acc = b;
    for (p, q) in x[..(a % 5) as usize].iter().zip(y.iter()) {
        acc = acc.wrapping_mul(100) + u32::from(*p) + *q as u32;
    }
    acc
}

#[no_mangle]
pub extern "C" fn nth_or(a: u32, b: u32) -> u32 {
    let v = [a, b, a ^ b, a.wrapping_add(b), 7, b >> 3, a << 2];
    *v.iter().nth((a & 7) as usize).unwrap_or(&0xdead)
}

struct Kw {
    name: &'static str,
    code: u32,
}

static KEYWORDS: [Kw; 5] = [
    Kw {
        name: "let",
        code: 1,
    },
    Kw {
        name: "fn",
        code: 2,
    },
    Kw {
        name: "else",
        code: 4,
    },
    Kw {
        name: "while",
        code: 5,
    },
    Kw {
        name: "return",
        code: 6,
    },
];

#[inline(never)]
fn lookup(word: &str) -> Option<&'static Kw> {
    KEYWORDS.iter().find(|k| k.name == word)
}

#[no_mangle]
pub extern "C" fn find_kw(a: u32, b: u32) -> u32 {
    let words = ["let", "fn", "iff", "else", "", "whilE", "return", "le"];
    let w = words[((a ^ b) as usize) % words.len()];
    match lookup(w) {
        Some(kw) => kw.code << 8 | (kw.name.len() as u32) << 16,
        None => 0xdead,
    }
}
