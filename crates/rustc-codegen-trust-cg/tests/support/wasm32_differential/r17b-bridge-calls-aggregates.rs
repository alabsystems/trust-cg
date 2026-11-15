// The call and aggregate shapes wasm32 round 17 stage B rewrites, on wasm32 at O0 to O3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// At O1 and above the wasm32 mid-end splices a callee whose small aggregate
// the rustc bridge passes or returns by address (a closure's environment,
// an `Option<Ordering>` or `Option<&T>` result in the callee's own slot:
// `Iterator::find`, slice `cmp`, `binary_search_by`, `fetch_update`), reads
// those aggregates lane by lane (`lane_load`), respells the bridge's typed
// pointer comparisons, `u32` bulk-memory counts and out-of-range constants
// (`respell`, constant folding) and reads a packed by-value parameter
// through its address in a clone (`byaddr`). Stage B also turned a `memcpy`
// of a run-time count into `memory.copy` (`mem_call`) and a `memcmp` of a
// small constant length read by a zero test into loads and compares
// (`mem_cmp`); since the merge with OD-155's ruling the default profile
// withholds both (OD-164's and OD-165's merge boundary) and those calls
// stay calls, which LLVM still checks. The exports
// cover those shapes and their controls: a sign read of a three-byte
// `memcmp`, a `memcmp` of a run-time length, a packed parameter of a callee
// that writes through a pointer, and empty and full-length slices. LLVM is
// the oracle.
#![no_std]
#![allow(dead_code)]

// wasm32-differential-flags: -Copt-level=1
// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3

use core::sync::atomic::{AtomicU32, AtomicU64, Ordering};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
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
        code: 3,
    },
    Kw {
        name: "while",
        code: 4,
    },
    Kw {
        name: "return",
        code: 5,
    },
];

#[inline(never)]
fn lookup(word: &str) -> Option<&'static Kw> {
    KEYWORDS.iter().find(|k| k.name == word)
}

#[no_mangle]
pub extern "C" fn kw(k: u32) -> u32 {
    let words = ["let", "fn", "if", "else", "", "whilE", "return", "returns"];
    match lookup(words[(k % 8) as usize]) {
        Some(kw) => kw.code << 8 | kw.name.len() as u32,
        None => 0xdead,
    }
}

static A32: [u32; 6] = [1, u32::MAX, 3, 1 << 31, 5, 6];
static B32: [u32; 6] = [1, u32::MAX, 3, 1 << 30, 5, 7];

#[inline(never)]
fn cmp32(a: &[u32], b: &[u32]) -> i32 {
    match a.cmp(b) {
        core::cmp::Ordering::Less => -1,
        core::cmp::Ordering::Equal => 0,
        core::cmp::Ordering::Greater => 1,
    }
}

#[no_mangle]
pub extern "C" fn cmp_slices(a: u32, b: u32) -> i32 {
    let x = &A32[..(a % 7) as usize];
    let y = &B32[..(b % 7) as usize];
    cmp32(x, y) * 10 + cmp32(y, x)
}

#[no_mangle]
pub extern "C" fn cmp_floats(a: u32, b: u32) -> i32 {
    let fa = [1.0f64, f64::NAN, -0.0, 2.0];
    let fb = [1.0f64, 3.0, 0.0, 2.0];
    match fa[..(a % 5) as usize].partial_cmp(&fb[..(b % 5) as usize]) {
        Some(core::cmp::Ordering::Less) => -1,
        Some(core::cmp::Ordering::Equal) => 0,
        Some(core::cmp::Ordering::Greater) => 1,
        None => 9,
    }
}

#[inline(never)]
fn search(a: &[i32], t: i32) -> Result<usize, usize> {
    a.binary_search_by(|p| p.cmp(&t))
}

#[no_mangle]
pub extern "C" fn bsearch(t: i32, n: u32) -> i32 {
    let mut a = [0i32; 20];
    let n = (n % 21) as usize;
    for (i, slot) in a.iter_mut().enumerate().take(n) {
        *slot = i as i32 * 5 - 30;
    }
    match search(&a[..n], t) {
        Ok(i) => i as i32,
        Err(i) => -(i as i32) - 1,
    }
}

static CELL: AtomicU64 = AtomicU64::new(0);
static FLAGS: AtomicU32 = AtomicU32::new(1);

#[no_mangle]
pub extern "C" fn fetch(a: u32, b: u32) -> u64 {
    CELL.store(a as u64, Ordering::SeqCst);
    let k = b as u64 | 1;
    let _ = CELL.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |v| {
        Some(v.wrapping_mul(k).wrapping_add(7))
    });
    let r = FLAGS.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |v| {
        if v > a { None } else { Some(v ^ b) }
    });
    CELL.load(Ordering::SeqCst) ^ (r.unwrap_or_else(|e| e) as u64) << 40
}

#[inline(never)]
fn copy_run(dst: &mut [u8; 16], src: &[u8], n: usize) -> u32 {
    let n = n.min(src.len()).min(dst.len());
    dst[..n].copy_from_slice(&src[..n]);
    dst.iter().fold(0u32, |h, &x| h.rotate_left(5) ^ x as u32)
}

#[no_mangle]
pub extern "C" fn copy_rt(a: u32, n: u32) -> u32 {
    let mut src = [0u8; 16];
    for (i, s) in src.iter_mut().enumerate() {
        *s = (a >> (i % 4 * 8)) as u8 ^ i as u8;
    }
    let mut dst = [0x55u8; 16];
    copy_run(&mut dst, &src, (n % 18) as usize)
}

#[repr(C, packed)]
#[derive(Clone, Copy)]
struct Pk {
    a: u8,
    x: u64,
    b: u16,
    y: u32,
}

#[inline(never)]
fn mkpk(k: u32, x: u64) -> Pk {
    Pk {
        a: k as u8,
        x,
        b: (k >> 8) as u16,
        y: k.rotate_left(7),
    }
}

#[inline(never)]
fn sumpk(p: Pk) -> u64 {
    let x = p.x;
    let y = p.y;
    let b = p.b;
    (p.a as u64) ^ x.wrapping_mul(3) ^ (b as u64) << 17 ^ (y as u64) << 29
}

#[no_mangle]
pub extern "C" fn packed(k: u32, x: u32) -> u64 {
    sumpk(mkpk(k, x as u64 * 0x9e37_79b9))
}

#[no_mangle]
pub extern "C" fn packed_twice(k: u32, x: u32) -> u64 {
    sumpk(mkpk(k, x as u64)) ^ sumpk(mkpk(k ^ x, k as u64)).rotate_left(3)
}

static mut SINK: u64 = 0;

#[inline(never)]
fn sumpk_writes(p: Pk, out: &mut u64) -> u64 {
    let x = p.x;
    *out = x;
    let y = p.y;
    (p.a as u64) ^ x ^ (y as u64) << 9
}

#[no_mangle]
pub extern "C" fn packed_writes(k: u32, x: u32) -> u64 {
    let mut out = 0u64;
    let r = sumpk_writes(mkpk(k, x as u64), &mut out);
    r ^ out.rotate_left(11)
}

#[inline(never)]
fn eq3(a: &[u8; 8], b: &[u8; 8]) -> bool {
    a[..3] == b[..3]
}

#[inline(never)]
fn ord3(a: &[u8; 8], b: &[u8; 8]) -> i32 {
    match a[..3].cmp(&b[..3]) {
        core::cmp::Ordering::Less => -1,
        core::cmp::Ordering::Equal => 0,
        core::cmp::Ordering::Greater => 1,
    }
}

#[inline(never)]
fn eq_run(a: &[u8; 8], b: &[u8; 8], n: usize) -> bool {
    a[..n] == b[..n]
}

#[no_mangle]
pub extern "C" fn bytes_eq(a: u32, b: u32) -> u32 {
    let x = (a as u64 | (b as u64) << 32).to_le_bytes();
    let y = (a as u64 ^ (b as u64 & 0x10101) << 8).to_le_bytes();
    let s: &str = if a % 3 == 0 { "abcd" } else { "abce" };
    let t = s.as_bytes() == b"abcd";
    eq3(&x, &y) as u32
        | (ord3(&x, &y) + 1) as u32 * 2
        | (eq_run(&x, &y, (b % 9) as usize) as u32) << 4
        | (t as u32) << 5
}

#[no_mangle]
pub extern "C" fn closures(a: u32, n: u32) -> u32 {
    let v = [a, a ^ 3, a.rotate_left(5), 7, a / 3 + 1, 11, a ^ n, n];
    let k = n | 1;
    v[..(n % 9) as usize]
        .iter()
        .map(|x| x.wrapping_mul(k))
        .filter(|x| x % 3 != 0)
        .fold(n, |acc, x| acc.rotate_left(3) ^ x)
}
