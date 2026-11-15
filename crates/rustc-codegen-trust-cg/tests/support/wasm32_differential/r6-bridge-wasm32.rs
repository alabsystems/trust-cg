// Rust-ABI by-memory values across crates and backends, static identity
// across crates, 64-bit atomics by value, and iterator shapes, on wasm32.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// RUST-ABI BY-MEMORY VALUES. rustc's wasm32 Rust ABI passes a `Memory`
// aggregate wider than a pointer through memory (a pointer to a caller-made
// copy) and returns one it does not cast through a caller buffer (`sret`),
// even when its bytes would fit one wasm value: `[u64; 1]`, a newtype of
// `[f64; 1]`, `[i128; 1]`, a `#[repr(align(8))]` `u32`, a `u64`/`f32` union
// and `AtomicU64`/`AtomicI64`. Every function taking or returning one here
// follows that convention whoever calls it: the dependency
// `extern/r6-bridge-wasm32-llvm.rs`, built by LLVM on both sides, is called
// directly (`lb_*`) and calls this crate's functions back through `fn`
// pointers and a trait object (`cb_*`); `extern/r6-bridge-wasm32-dep.rs` is
// built by each side's own backend (`dp_*`). `core`'s own `Atomic*::new`,
// `into_inner` and `From` take and return 64-bit atomics by value (`at_*`).
//
// STATIC IDENTITY. A static is one memory location in the program: a
// reference to an upstream static made in this crate — directly, through a
// `&str` or reference stored in another static, through a `#[inline]` or
// generic upstream function instantiated here, or from this crate's own
// static — addresses the same bytes as the upstream crate's own code
// (`st_*`), for an upstream crate built by LLVM and by this backend.
//
// ITERATORS. `.position()` writes its index into an `Option<usize>` of
// rustc's 4-byte `usize` (`it_pos*`: a wider store would clobber the next
// frame slot, here the searched array); `fold` over `.rev().take(n)`, which
// `-O` inlines into a `try_fold` with a `NeverShortCircuit` result
// (`it_rev_take_*`); short-circuiting drives of a reversed chain, whose
// iterator is used again afterwards (`it_rev_*`); and `find` over 64-bit
// items, whose check closure returns `ControlFlow<u64>` through a caller
// buffer (`it_find64_*`; `r6-bridge-wasm32-opt.rs` has the `filter` loops,
// which this backend lowers only with optimization).
#![no_std]
#![allow(dead_code)]

// wasm32-differential-flags: -Copt-level=2
// wasm32-differential-flags: -Copt-level=3 -Ccodegen-units=4
// wasm32-differential-flags: -Copt-level=1 -Coverflow-checks=on
// wasm32-differential-extern: r6_dep r6-bridge-wasm32-dep.rs
// wasm32-differential-extern-llvm: r6_llvm r6-bridge-wasm32-llvm.rs

extern crate r6_dep;
extern crate r6_llvm;

use core::hint::black_box;
use core::ptr;
use core::sync::atomic::{AtomicI64, AtomicU64, Ordering};

use r6_dep::{D8, DV};
use r6_llvm::{A8, F64a, Shape, V, W64};

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    #[cfg(target_arch = "wasm32")]
    core::arch::wasm32::unreachable();
    #[cfg(not(target_arch = "wasm32"))]
    loop {}
}

// ---- Rust-ABI by-memory values, LLVM as the callee --------------------------

#[no_mangle]
pub extern "C" fn lb_al(x: u32) -> u32 {
    r6_llvm::al(A8(x), 7).0
}

#[no_mangle]
pub extern "C" fn lb_w64(x: i64) -> i64 {
    r6_llvm::w64(W64([x as u64]), 3).0[0] as i64
}

#[no_mangle]
pub extern "C" fn lb_arr64(x: i64) -> i64 {
    r6_llvm::arr64([x as u64])[0] as i64
}

#[no_mangle]
pub extern "C" fn lb_f64a(x: f64) -> f64 {
    r6_llvm::f64a(F64a([x])).0[0]
}

#[no_mangle]
pub extern "C" fn lb_i128a(x: i64) -> i64 {
    r6_llvm::i128a([(x as i128) << 40]) as i64
}

#[no_mangle]
pub extern "C" fn lb_v(x: i64, k: u32) -> i64 {
    unsafe { r6_llvm::v_mix(V { a: x as u64 }, k).a as i64 }
}

#[no_mangle]
pub extern "C" fn lb_atomic(x: i64, k: i64) -> i64 {
    let made = r6_llvm::make_atomic(x as u64).into_inner() as i64;
    made ^ r6_llvm::take_atomic(AtomicI64::new(x), k).rotate_left(9)
}

// ---- Rust-ABI by-memory values, LLVM as the caller --------------------------

#[inline(never)]
fn my_arr(a: [u64; 1]) -> [u64; 1] {
    [a[0] ^ 0x5555_0000_AAAA]
}

#[inline(never)]
fn my_al(a: A8, k: u32) -> A8 {
    A8(a.0.wrapping_mul(k) ^ 0x31)
}

#[inline(never)]
fn my_v(v: V, k: u32) -> V {
    V {
        a: unsafe { v.a }.rotate_left(k),
    }
}

#[inline(never)]
fn my_atomic(a: AtomicU64) -> AtomicU64 {
    a.fetch_add(11, Ordering::Relaxed);
    a
}

struct Scale(u32);

impl Shape for Scale {
    fn scale(&self, a: [u64; 1], k: A8) -> A8 {
        A8((a[0] as u32) ^ k.0.rotate_left(3) ^ self.0)
    }
}

#[no_mangle]
pub extern "C" fn cb_arr(x: i64) -> i64 {
    r6_llvm::apply_arr(my_arr, x as u64) as i64
}

#[no_mangle]
pub extern "C" fn cb_al(x: u32) -> u32 {
    r6_llvm::apply_al(my_al, x)
}

#[no_mangle]
pub extern "C" fn cb_v(x: i64) -> i64 {
    r6_llvm::apply_v(my_v, x as u64) as i64
}

#[no_mangle]
pub extern "C" fn cb_atomic(x: i64) -> i64 {
    r6_llvm::apply_atomic(my_atomic, x as u64) as i64
}

#[no_mangle]
pub extern "C" fn cb_dyn(x: i64, k: u32) -> u32 {
    r6_llvm::apply_dyn(&Scale(k >> 3), x as u64, k)
}

// ---- Rust-ABI by-memory values, both crates by the same backend -------------

#[no_mangle]
pub extern "C" fn dp_abi(x: i64, k: u32) -> i64 {
    let a = r6_dep::d_al(D8(x as u32), k).0 as u64;
    let b = r6_dep::d_arr64([x as u64], u64::from(k))[0];
    let c = r6_dep::d_v(DV { a: b });
    let d = r6_dep::d_atomic(c).into_inner();
    (a ^ b.rotate_left(13) ^ d) as i64
}

#[no_mangle]
pub extern "C" fn dp_pow(x: u32) -> u32 {
    r6_dep::d_pow(x, "abc") ^ x.wrapping_pow(3).rotate_left(1)
}

// ---- 64-bit atomics by value through core -----------------------------------

pub struct Counter {
    hits: AtomicU64,
    misses: AtomicI64,
}

impl Counter {
    #[inline(never)]
    fn new(h: u64) -> Counter {
        Counter {
            hits: AtomicU64::new(h),
            misses: AtomicI64::new(-1),
        }
    }

    #[inline(never)]
    fn bump(&self, d: u64) -> u64 {
        self.hits.fetch_add(d, Ordering::Relaxed)
            ^ self.misses.fetch_sub(1, Ordering::Relaxed) as u64
    }
}

#[no_mangle]
pub extern "C" fn at_local(a: i64, b: i64) -> i64 {
    let x = AtomicU64::new(b as u64);
    let r = x.fetch_add(a as u64, Ordering::SeqCst);
    let y = AtomicI64::from(a);
    y.fetch_sub(b, Ordering::SeqCst);
    (r ^ x.load(Ordering::SeqCst).rotate_left(7)) as i64 ^ y.into_inner()
}

#[no_mangle]
pub extern "C" fn at_counter(a: i64) -> i64 {
    let c = Counter::new(a as u64);
    (c.bump(3) ^ c.bump(a as u64).rotate_left(5) ^ c.hits.into_inner()) as i64
}

// ---- static identity ----------------------------------------------------------

static R: &u32 = &r6_llvm::S;
static DR: &u32 = &r6_dep::DS;

#[no_mangle]
pub extern "C" fn st_llvm() -> u32 {
    let mut m = u32::from(ptr::eq(&r6_llvm::S, black_box(r6_llvm::addr_s())));
    m |= u32::from(ptr::eq(&r6_llvm::T[2], black_box(r6_llvm::addr_t2()))) << 1;
    m |= u32::from(ptr::eq(
        r6_llvm::STR.as_ptr(),
        black_box(r6_llvm::str_ptr()),
    )) << 2;
    m |= u32::from(ptr::eq(r6_llvm::REF, black_box(r6_llvm::addr_s()))) << 3;
    m |= u32::from(ptr::eq(
        r6_llvm::inline_addr_p(),
        black_box(r6_llvm::addr_p()),
    )) << 4;
    m |= u32::from(ptr::eq(
        r6_llvm::generic_addr_p::<u8>(),
        black_box(r6_llvm::addr_p()),
    )) << 5;
    m |= u32::from(ptr::eq(R, black_box(r6_llvm::addr_s()))) << 6;
    m | (r6_llvm::S + *r6_llvm::REF + r6_llvm::T[3] + **black_box(&R)) << 8
}

#[no_mangle]
pub extern "C" fn st_dep() -> u32 {
    let mut m = u32::from(ptr::eq(&r6_dep::DS, black_box(r6_dep::addr_ds())));
    m |= u32::from(ptr::eq(&r6_dep::DT[1], black_box(r6_dep::addr_dt1()))) << 1;
    m |= u32::from(ptr::eq(
        r6_dep::DSTR.as_ptr(),
        black_box(r6_dep::dstr_ptr()),
    )) << 2;
    m |= u32::from(ptr::eq(r6_dep::DREF, black_box(r6_dep::addr_ds()))) << 3;
    m |= u32::from(ptr::eq(
        r6_dep::inline_addr_dp(),
        black_box(r6_dep::addr_dp()),
    )) << 4;
    m |= u32::from(ptr::eq(
        r6_dep::generic_addr_dp::<u16>(),
        black_box(r6_dep::addr_dp()),
    )) << 5;
    m |= u32::from(ptr::eq(DR, black_box(r6_dep::addr_ds()))) << 6;
    m | (r6_dep::DS + u32::from(r6_dep::DT[2]) + **black_box(&DR)) << 8
}

// ---- iterators ----------------------------------------------------------------

#[inline(never)]
fn mk_or(a: u32) -> [u32; 3] {
    [a | 1, a | 2, a | 4]
}

#[inline(never)]
fn mk_mod(a: u32) -> [u32; 3] {
    [a % 3, (a / 3) % 3, (a / 9) % 3]
}

#[no_mangle]
pub extern "C" fn it_pos(a: u32) -> u32 {
    let v = mk_or(a);
    let p = v.iter().position(|&x| x == 7);
    v[0].wrapping_add(v[1])
        .wrapping_add(v[2])
        .wrapping_add(p.unwrap_or(9) as u32)
}

#[no_mangle]
pub extern "C" fn it_pos_rpos(a: u32) -> u32 {
    let v = mk_mod(a);
    let p = v.iter().position(|&x| x == 2);
    let q = v.iter().rposition(|&x| x == 0);
    p.unwrap_or(99) as u32 | (q.unwrap_or(77) as u32) << 8
}

#[no_mangle]
pub extern "C" fn it_pos_range(a: u32, b: u32) -> u32 {
    let lo = a % 1000;
    let v = mk_mod(b);
    let p = (lo..lo + 20).position(|x| x % 7 == 3);
    v[1] ^ p.map_or(55, |i| i as u32) << 4
}

#[no_mangle]
pub extern "C" fn it_rev_take_range(lo: u32, hi: u32, t: u32) -> u32 {
    (lo % 64..hi % 128)
        .rev()
        .take((t % 9) as usize)
        .fold(0u32, |acc, x| acc.wrapping_mul(3).wrapping_add(x))
}

#[no_mangle]
pub extern "C" fn it_rev_take_slice(lo: u32, t: u32) -> u32 {
    let a = [lo, lo ^ 1, lo.rotate_left(3), 7, 9, lo >> 2];
    a.iter()
        .rev()
        .take((t % 8) as usize)
        .fold(0u32, |acc, x| acc.wrapping_mul(5) ^ *x)
}

#[no_mangle]
pub extern "C" fn it_rev_take_u64(lo: i64, hi: i64) -> i64 {
    let (lo, hi) = (lo as u64 % 64, hi as u64 % 128);
    (lo..hi)
        .rev()
        .take(4)
        .fold(0u64, |acc, x| acc.rotate_left(7) ^ x) as i64
}

#[no_mangle]
pub extern "C" fn it_rev_map_take(lo: u32, t: u32) -> u32 {
    (lo % 50..lo % 50 + 30)
        .rev()
        .map(|x| x.wrapping_mul(0x9E37))
        .take((t % 11) as usize)
        .fold(1u32, |acc, x| acc.rotate_left(5) ^ x)
}

#[no_mangle]
pub extern "C" fn it_rev_find_state(lo: u32, n: u32) -> u32 {
    let lo = lo % 50;
    let hi = lo + n % 40;
    let mut it = (lo..hi).rev().take(7);
    let a = it.find(|&x| x % 3 == 0).unwrap_or(1000);
    let b = it.next().unwrap_or(2000);
    let c = it.fold(0u32, |acc, x| acc.wrapping_mul(31).wrapping_add(x));
    a ^ (b << 11) ^ c.rotate_left(5)
}

#[no_mangle]
pub extern "C" fn it_rev_slice_state(a: u32, k: u32) -> u32 {
    let v = [a, a >> 3, a ^ 0x55, k, k.rotate_left(9), 3];
    let mut it = v.iter().rev();
    let hit = it.position(|&x| x & 1 == 1).map_or(99, |i| i as u32);
    let any = it.any(|&x| x > 100);
    let rest = it.fold(0u32, |acc, &x| acc.wrapping_add(x));
    hit | u32::from(any) << 8 | rest << 9
}

#[no_mangle]
pub extern "C" fn it_find64_range(a: i64, b: i64) -> i64 {
    let lo = (a as u64) % 1_000_000_000;
    (lo..lo + (b as u64) % 97)
        .find(|x| x % 13 == 5)
        .unwrap_or(7) as i64
}

#[no_mangle]
pub extern "C" fn it_find64_map(a: u32, b: u32) -> i64 {
    let d = [a, b, a ^ b, 7, 9];
    d.iter()
        .map(|&x| u64::from(x) << 20)
        .find(|v| v & (1 << 22) != 0)
        .unwrap_or(3) as i64
}
