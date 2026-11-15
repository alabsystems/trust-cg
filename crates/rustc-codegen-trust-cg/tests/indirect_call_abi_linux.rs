//! Native Linux regression for ledger row L06-P15: an indirect call (a fn
//! pointer, a `&dyn Trait` method) passes its arguments exactly as a direct
//! call does, including 128-bit integers and narrow integers on the stack.
//! Every lane is compared against the same calls made by LLVM.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates
//! License: Apache-2.0
//!
//! Direct and indirect calls classify the same ABI and apply the same register
//! class, natural stack-width and 128-bit alignment rules. The bridge's current `IndirectArgPlan` carries
//! Rust-ABI by-reference aggregates as pointers to fresh caller copies and
//! restores their byte image in the callee. This regression independently
//! checks those paths against LLVM; it does not qualify every Rust ABI shape.
//!
//! WHAT IS CHECKED, AT O0 AND O2. The fixture crate (`-Cpanic=abort`,
//! staticlib objects) is compiled by the bridge and by LLVM and linked with an
//! LLVM-compiled Rust driver that defines the callees (`#[no_mangle]` Rust ABI,
//! plus one `extern "C"` callee). Each fixture case calls a callee through a
//! `black_box`ed fn pointer (or a `&dyn Trait` method, or directly, as a
//! control) and stores the result through an out-pointer; the driver makes the
//! same call directly and prints one line per case, `ok` only when the two
//! agree. Every case must print `ok` for both compilers, and the bridge and
//! LLVM executables must print identical output. The signatures cover a
//! stack-passed `i128` and `u128`, an `i128` after eight arguments with narrow
//! neighbours, five `i128` arguments (the fifth on the stack), eight narrow
//! and float stack arguments, a 23-argument integer/float/`i128` mix, a
//! register-sized array and a bridge-compiled callee.
//!
//! The second test compiles `CROSS_FIXTURE` as an rlib, by the bridge and by
//! LLVM, and links an LLVM-compiled crate against it (`--extern`) that calls
//! its exported functions (by path and `#[no_mangle]`), the fn pointers it
//! hands out, its ordinary `dyn Trait` vtable entries and a generic,
//! and passes its own fn items and ordinary trait objects in; the
//! fixture also calls into the driver by name. The arguments are the
//! by-reference shapes (`[f32; 4]`, a 12-byte struct, `Result<u64, u32>`,
//! `[u64; 2]`, `(u64, u32, u32)`, `[f64; 2]`, `TypeId`, a 24-byte struct,
//! `[u64; 3]`, a 32-byte enum), some after seven integer arguments. The
//! bridge and LLVM executables must print the same 22 lines. Unsupported
//! Fn-trait vtable argument shapes have separate exact refusal tests and
//! independently executable LLVM controls in `rust_call_shims_linux`.
//!
//! EVIDENCE BOUNDARY. The frontend runs with `-Ztrust-verify=off` and the
//! backend with the `no-proof-certs` knob. The LLVM-compiled driver and GNU
//! `ld` are trusted. This is native testing evidence for these signatures
//! only; it does not qualify rustc's full Rust ABI.
//!
//! The artifacts directory is removed when the test passes; setting
//! `INDIRECT_CALL_ABI_LINUX_KEEP_ARTIFACTS=1` retains it.

#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TARGET: &str = "aarch64-unknown-linux-gnu";
const OPT_LEVELS: [u32; 2] = [0, 2];
const KEEP_ARTIFACTS: &str = "INDIRECT_CALL_ABI_LINUX_KEEP_ARTIFACTS";
/// The cases the driver checks, in order.
const CASES: usize = 14;

/// The fixture: `case_*` entries the driver calls. Each writes its result
/// through `out` so no 128-bit value crosses the `extern "C"` boundary.
const FIXTURE: &str = r#"#![crate_type = "staticlib"]
#![allow(improper_ctypes, improper_ctypes_definitions)]
use std::hint::black_box as bb;
extern "Rust" {
    fn drv_i128_7(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i128) -> i128;
    fn drv_u128_7(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: u128) -> u128;
    fn drv_i128_8n(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: u8, j: i128, k: u16) -> i128;
    fn drv_i128_x5(a: i128, b: i128, c: i128, d: i128, e: i128) -> i128;
    fn drv_narrow(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: u8, j: i8, k: u16, l: i16, m: bool, n: f32) -> i64;
    fn drv_sink(a: i64, b: f64, c: i128, d: u8, e: f32, f: i64, g: f64, h: i64, i: f64, j: i64, k: f64,
                l: i64, m: f64, n: i64, o: f64, p: i64, q: f64, r: i64, s: f64, t: u16, u: i128, v: f32, w: bool) -> f64;
    fn drv_small_arr(a: [u16; 4], b: [u8; 3]) -> [u8; 3];
}
extern "C" {
    fn drv_c_i128_7(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i128) -> i128;
}
const BIG: i128 = -0x1234_5678_9abc_def0_1122_3344_5566_7788;
const UBIG: u128 = 0xfedc_ba98_7654_3210_0f0e_0d0c_0b0a_0908;
fn put(out: *mut [u64; 2], v: u128) {
    unsafe { *out = [v as u64, (v >> 64) as u64] }
}
#[inline(never)]
fn local_i128_7(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i128) -> i128 {
    h.wrapping_mul(3) + (a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f + 7 * g) as i128
}
pub trait Op {
    fn run(&self, a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, h: i128) -> i128;
}
pub struct P(pub i64);
impl Op for P {
    #[inline(never)]
    fn run(&self, a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, h: i128) -> i128 {
        h.wrapping_mul(7) + (self.0 + a + 2 * b + 3 * c + 4 * d + 5 * e + 6 * f) as i128
    }
}
#[no_mangle]
pub extern "C" fn case_fp_i128_7(out: *mut [u64; 2], k: i64) {
    let f: unsafe fn(i64, i64, i64, i64, i64, i64, i64, i128) -> i128 = bb(drv_i128_7);
    put(out, unsafe { f(k, 2, 3, 4, 5, 6, 7, BIG) } as u128);
}
#[no_mangle]
pub extern "C" fn case_direct_i128_7(out: *mut [u64; 2], k: i64) {
    put(out, unsafe { drv_i128_7(k, 2, 3, 4, 5, 6, 7, BIG) } as u128);
}
#[no_mangle]
pub extern "C" fn case_fp_u128_7(out: *mut [u64; 2], k: i64) {
    let f: unsafe fn(i64, i64, i64, i64, i64, i64, i64, u128) -> u128 = bb(drv_u128_7);
    put(out, unsafe { f(k, 2, 3, 4, 5, 6, 7, UBIG) });
}
#[no_mangle]
pub extern "C" fn case_fp_i128_8n(out: *mut [u64; 2], k: i64) {
    let f: unsafe fn(i64, i64, i64, i64, i64, i64, i64, i64, u8, i128, u16) -> i128 = bb(drv_i128_8n);
    put(out, unsafe { f(k, 2, 3, 4, 5, 6, 7, 8, 201, -0x1_0000_0000_0000_0003, 65001) } as u128);
}
#[no_mangle]
pub extern "C" fn case_fp_i128_x5(out: *mut [u64; 2], k: i64) {
    let f: unsafe fn(i128, i128, i128, i128, i128) -> i128 = bb(drv_i128_x5);
    put(out, unsafe { f(k as i128, BIG, 1 << 100, -(1 << 90), BIG ^ 0x55) } as u128);
}
#[no_mangle]
pub extern "C" fn case_fp_narrow(out: *mut [u64; 2], k: i64) {
    let f: unsafe fn(i64, i64, i64, i64, i64, i64, i64, i64, u8, i8, u16, i16, bool, f32) -> i64 = bb(drv_narrow);
    put(out, unsafe { f(k, 2, 3, 4, 5, 6, 7, 8, 250, -100, 60001, -30001, true, 2.5) } as u128);
}
#[no_mangle]
pub extern "C" fn case_fp_sink(out: *mut [u64; 2], k: i64) {
    // A modest i128 keeps every mixed contribution observable in the f64 sum.
    // Other cases independently check high limbs and 128-bit stack alignment.
    let f: unsafe fn(i64, f64, i128, u8, f32, i64, f64, i64, f64, i64, f64, i64, f64, i64, f64, i64, f64, i64, f64, u16, i128, f32, bool) -> f64 = bb(drv_sink);
    let r = unsafe { f(k, 1.5, -77, 250, 0.25, 6, 7.5, 8, 9.5, 10, 11.5, 12, 13.5, 14, 15.5, 16, 17.5, 18, 19.5, 65535, 77, -2.5, true) };
    put(out, r.to_bits() as u128);
}
#[no_mangle]
pub extern "C" fn case_fp_small_arr(out: *mut [u64; 2], k: i64) {
    let f: unsafe fn([u16; 4], [u8; 3]) -> [u8; 3] = bb(drv_small_arr);
    let r = unsafe { f([k as u16, 700, 9, 65000], [4, 90, 0x55]) };
    put(out, u32::from_le_bytes([r[0], r[1], r[2], 0]) as u128);
}
#[no_mangle]
pub extern "C" fn case_c_fp_i128_7(out: *mut [u64; 2], k: i64) {
    let f: unsafe extern "C" fn(i64, i64, i64, i64, i64, i64, i64, i128) -> i128 = bb(drv_c_i128_7);
    put(out, unsafe { f(k, 2, 3, 4, 5, 6, 7, BIG) } as u128);
}
#[no_mangle]
pub extern "C" fn case_local_fp_i128_7(out: *mut [u64; 2], k: i64) {
    let f: fn(i64, i64, i64, i64, i64, i64, i64, i128) -> i128 = bb(local_i128_7);
    put(out, f(k, 2, 3, 4, 5, 6, 7, BIG) as u128);
}
#[inline(never)] fn as_dyn_op(p: &P) -> &dyn Op { p }
#[no_mangle]
pub extern "C" fn case_dyn_i128_6(out: *mut [u64; 2], k: i64) {
    let p = P(1000);
    let d: &dyn Op = bb(as_dyn_op(&p));
    put(out, d.run(k, 2, 3, 4, 5, 6, BIG) as u128);
}
#[no_mangle]
pub extern "C" fn case_table_i128_7(out: *mut [u64; 2], k: i64) {
    let table: [unsafe fn(i64, i64, i64, i64, i64, i64, i64, i128) -> i128; 2] = bb([drv_i128_7, drv_i128_7]);
    put(out, unsafe { table[(k & 1) as usize](k, 2, 3, 4, 5, 6, 7, BIG ^ 0x3333) } as u128);
}
#[no_mangle]
pub extern "C" fn case_fp_i128_7_neg(out: *mut [u64; 2], k: i64) {
    let f: unsafe fn(i64, i64, i64, i64, i64, i64, i64, i128) -> i128 = bb(drv_i128_7);
    put(out, unsafe { f(k, -2, -3, -4, -5, -6, -7, i128::MIN + 12345) } as u128);
}
#[no_mangle]
pub extern "C" fn case_fp_u128_max(out: *mut [u64; 2], k: i64) {
    let f: unsafe fn(i64, i64, i64, i64, i64, i64, i64, u128) -> u128 = bb(drv_u128_7);
    put(out, unsafe { f(k, 0, 0, 0, 0, 0, 0, u128::MAX - 5) });
}
"#;

/// The cross-backend fixture: a Rust library the bridge compiles and an
/// LLVM-compiled Rust crate (`CROSS_DRIVER`) links against (`--extern`), so
/// every exported function, escaped fn pointer and vtable entry below is
/// called with rustc's own Rust-ABI convention by LLVM code, and every call
/// the bridge makes into the driver reaches LLVM code.
const CROSS_FIXTURE: &str = r#"#![allow(improper_ctypes_definitions, dead_code)]
use std::hint::black_box as bb;
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct S12 { pub a: u32, pub b: u32, pub c: u32 }
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct S24 { pub a: u64, pub b: u64, pub c: u64 }
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Big { A(u64, u64, u64), B(u32), C }
pub trait Tr { fn m(&self, a: [f32; 4], s: S12) -> f64; }
pub struct Imp(pub f64);
impl Tr for Imp {
    #[inline(never)] fn m(&self, a: [f32; 4], s: S12) -> f64 {
        self.0 + a[0] as f64 + a[1] as f64 * 10.0 + a[2] as f64 * 100.0 + a[3] as f64 * 1000.0
            + s.a as f64 + s.b as f64 * 0.5 + s.c as f64 * 0.25
    }
}
static IMP: Imp = Imp(0.5);
#[inline(never)] fn w4(a: [f32; 4]) -> f32 { a[0] + 2.0 * a[1] + 3.0 * a[2] + 4.0 * a[3] }
#[inline(never)] pub fn sum4(a: [f32; 4]) -> f32 { w4(a) }
#[no_mangle] #[inline(never)]
pub fn sum4_nm(a: [f32; 4]) -> f32 { w4(a) + 0.5 }
#[inline(never)] pub fn s24(k: u64, s: S24, t: [u64; 3]) -> u64 {
    k ^ s.a.wrapping_mul(3) ^ s.b.rotate_left(7) ^ s.c ^ t[0] ^ t[1].wrapping_mul(5) ^ t[2]
}
#[inline(never)] pub fn big(e: Big, f: Big) -> u64 {
    let g = |b: Big| match b {
        Big::A(x, y, z) => x.wrapping_mul(31) ^ y ^ z.rotate_left(3),
        Big::B(v) => v as u64 * 7,
        Big::C => 99,
    };
    g(e).wrapping_mul(1000003) ^ g(f)
}
#[inline(never)] pub fn mix(a: u8, s: S12, r: Result<u64, u32>, v: [u64; 2], w: (u64, u32, u32), z: [f64; 2]) -> u64 {
    let rr = match r { Ok(x) => x, Err(e) => e as u64 * 11 };
    (a as u64) ^ (s.a as u64) << 1 ^ (s.b as u64) << 7 ^ (s.c as u64) << 13 ^ rr.rotate_left(17)
        ^ v[0] ^ v[1].rotate_left(9) ^ w.0 ^ (w.1 as u64) << 3 ^ (w.2 as u64) << 21
        ^ z[0].to_bits() ^ z[1].to_bits().rotate_left(1)
}
#[inline(never)] pub fn many(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, x: [f32; 4], s: S12, v: [u64; 2]) -> u64 {
    a ^ b << 1 ^ c << 2 ^ d << 3 ^ e << 4 ^ f << 5 ^ g << 6 ^ (w4(x) as u64) << 20
        ^ (s.a as u64 + s.b as u64 * 3 + s.c as u64 * 9) ^ v[0] ^ v[1] << 11
}
#[inline(never)] pub fn ret_s12(k: u32) -> S12 { S12 { a: k, b: k * 3, c: k ^ 0x5555 } }
#[inline(never)] pub fn ret_arr2(k: u64) -> [u64; 2] { [k.rotate_left(5), !k] }
#[inline(never)] pub fn tid_eq(a: std::any::TypeId, b: std::any::TypeId) -> bool { a == b }
#[inline(never)] pub fn gen<T: Copy + Into<u64>>(x: [T; 4]) -> u64 {
    x[0].into() ^ x[1].into() << 8 ^ x[2].into() << 16 ^ x[3].into() << 24
}
#[inline(never)] fn local_sum4(a: [f32; 4]) -> f32 { w4(a) * 2.0 }
#[inline(never)] fn other(a: [f32; 4]) -> f32 { a[3] - a[0] + 0.25 }
#[inline(never)] fn other3(k: u64, s: S12, v: [u64; 2]) -> u64 { k ^ s.a as u64 ^ (s.c as u64) << 9 ^ v[1] }
#[inline(never)] pub fn get_fp() -> fn([f32; 4]) -> f32 { local_sum4 }
#[inline(never)] pub fn get_fp2() -> fn([f32; 4]) -> f32 { other }
#[inline(never)] pub fn get_fp3() -> fn(u64, S12, [u64; 2]) -> u64 { other3 }
#[inline(never)]
pub fn as_dyn(i: &'static Imp) -> &'static dyn Tr { i }
#[inline(never)]
pub fn get_dyn() -> &'static dyn Tr { as_dyn(bb(&IMP)) }
#[inline(never)] pub fn call_dyn(t: &dyn Tr, a: [f32; 4], s: S12) -> f64 { t.m(a, s) }
#[inline(never)] pub fn call_fp(f: fn([f32; 4]) -> f32, a: [f32; 4]) -> f32 { f(a) }
#[inline(never)] pub fn call_fp_arr(f: fn([f32; 4], [u8; 3]) -> [u8; 3], x: u8) -> [u8; 3] {
    f([1.5, 77.0, 2.0, 3.5], [x, 90, 0x55])
}
#[inline(never)] pub fn call_fp3(f: fn(u64, S12, [u64; 2]) -> u64, k: u64) -> u64 { f(k, S12 { a: 1, b: 2, c: 3 }, [k, !k]) }
#[inline(never)] pub fn apply<F: Fn([f32; 4]) -> f32>(f: F, a: [f32; 4]) -> f32 { f(a) }
#[inline(never)] pub fn gen_u32(x: [u32; 4]) -> u64 { gen(x) }
#[inline(never)] pub fn apply_once<F: FnOnce(S12) -> u64>(f: F, s: S12) -> u64 { f(s) }
extern "Rust" {
    fn drv_take(a: [f32; 4], s: S12, v: [u64; 2], w: S24) -> u64;
}
#[inline(never)] pub fn call_driver(k: u64) -> u64 {
    unsafe { drv_take([k as f32, 0.5, 1.5, 2.5], S12 { a: k as u32, b: 7, c: 9 }, [k, k * 2], S24 { a: 1, b: k, c: 3 }) }
}
#[inline(never)] pub fn internal(k: u64) -> u64 {
    let a = [k as f32, 1.0, 2.0, 3.0];
    let s = S12 { a: k as u32, b: 5, c: 6 };
    let fp: fn([f32; 4]) -> f32 = bb(local_sum4);
    let fp2: fn([f32; 4]) -> f32 = bb(get_fp2());
    let d: &dyn Tr = bb(get_dyn());
    let opt = Some([k as u32, 2, 3]).map(|t: [u32; 3]| t[0] + t[1] * t[2]).unwrap_or(0) as u64;
    let r = ret_s12(k as u32);
    let r2 = ret_arr2(k);
    let ap = apply(bb(fp), a) as u64 ^ apply(|b: [f32; 4]| b[1] + k as f32, a) as u64;
    let ao = apply_once(move |s: S12| s.a as u64 + k, S12 { a: 3, b: 4, c: 5 });
    (local_sum4(a) as u64) ^ (sum4(a) as u64) << 8 ^ (fp(a) as u64) << 16 ^ (fp2(a) as u64) << 24
        ^ (d.m(a, s) as u64) << 32 ^ opt << 40 ^ many(1, 2, 3, 4, 5, 6, 7, a, s, [k, 3])
        ^ (r.a ^ r.b ^ r.c) as u64 ^ r2[0] ^ r2[1] ^ gen([k as u32, 1, 2, 3])
        ^ call_fp3(get_fp3(), k) ^ ap << 44 ^ ao << 50
}
"#;

/// The LLVM-compiled crate: calls the fixture's functions by path, through the
/// fn pointers and vtables the fixture hands out, and passes its own fn items,
/// ordinary trait objects in; defines the one function the fixture calls.
/// One line per call; the bridge and LLVM executables must print the same.
const CROSS_DRIVER: &str = r#"extern crate fixture;
use fixture::*;
use std::hint::black_box as bb;
#[no_mangle]
pub fn drv_take(a: [f32; 4], s: S12, v: [u64; 2], w: S24) -> u64 {
    (a[0].to_bits() as u64) ^ (a[3].to_bits() as u64) << 32 ^ (s.a ^ s.b << 3 ^ s.c << 9) as u64
        ^ v[0] ^ v[1] << 1 ^ w.a ^ w.b << 2 ^ w.c << 4
}
struct DImp(f64);
impl Tr for DImp {
    fn m(&self, a: [f32; 4], s: S12) -> f64 { self.0 * 3.0 + a[1] as f64 - a[2] as f64 + s.b as f64 }
}
fn dsum(a: [f32; 4]) -> f32 { a[0] * 0.5 + a[1] * 0.25 + a[2] + a[3] }
fn darr(a: [f32; 4], b: [u8; 3]) -> [u8; 3] {
    [b[0].wrapping_add(a[1] as u8), b[1] ^ a[3] as u8, b[2].wrapping_mul(a[0] as u8 + 1)]
}
fn main() {
    let k: u64 = bb(std::env::args().count() as u64 + 41);
    let a = [k as f32, -1.5, 2.25, 8.0];
    let s = S12 { a: k as u32, b: 17, c: 0xabcd };
    println!("sum4 {:#x}", sum4(bb(a)).to_bits());
    println!("sum4_nm {:#x}", sum4_nm(bb(a)).to_bits());
    println!("s24 {:#x}", s24(k, bb(S24 { a: k, b: k * 7, c: 99 }), bb([k, 5, 6])));
    println!("big {:#x}", big(bb(Big::A(k, 2, 3)), bb(Big::B(k as u32))));
    println!("big2 {:#x}", big(bb(Big::C), bb(Big::A(9, k, 1))));
    println!("mix {:#x}", mix(3, bb(s), bb(Ok(k * 1000)), bb([k, 77]), bb((k, 5, 6)), bb([1.5, -(k as f64)])));
    println!("mix_err {:#x}", mix(4, bb(s), bb(Err(k as u32)), bb([1, 2]), bb((3, 4, 5)), bb([0.0, 2.0])));
    println!("many {:#x}", many(1, 2, 3, 4, 5, 6, k, bb(a), bb(s), bb([k, 9])));
    let r = ret_s12(bb(k as u32));
    println!("ret_s12 {} {} {}", r.a, r.b, r.c);
    let r2 = ret_arr2(bb(k));
    println!("ret_arr2 {:#x} {:#x}", r2[0], r2[1]);
    let (u8_id, u16_id) = (std::any::TypeId::of::<u8>(), std::any::TypeId::of::<u16>());
    println!("tid {} {}", tid_eq(bb(u8_id), bb(u8_id)), tid_eq(bb(u8_id), bb(u16_id)));
    println!("gen {:#x}", gen_u32(bb([k as u32, 7, 8, 9])));
    println!("get_fp {:#x}", get_fp()(bb(a)).to_bits());
    println!("get_fp2 {:#x}", get_fp2()(bb(a)).to_bits());
    println!("get_fp3 {:#x}", get_fp3()(k, bb(s), bb([k, 5])));
    println!("dyn_fixture {:#x}", get_dyn().m(bb(a), bb(s)).to_bits());
    println!("call_dyn_drv {:#x}", call_dyn(&DImp(0.75), bb(a), bb(s)).to_bits());
    println!("call_dyn_fix {:#x}", call_dyn(get_dyn(), bb(a), bb(s)).to_bits());
    println!("call_fp_drv {:#x}", call_fp(dsum, bb(a)).to_bits());
    println!("call_fp_arr {:?}", call_fp_arr(darr, bb(4)));
    println!("call_driver {:#x}", call_driver(bb(k)));
    println!("internal {:#x}", internal(bb(k)));
}
"#;

/// Lines `CROSS_DRIVER` prints.
const CROSS_LINES: usize = 22;

/// The LLVM-compiled driver: the callees, and a check of every case against
/// the same call made directly.
const DRIVER: &str = r#"
#![allow(improper_ctypes_definitions)]
#[no_mangle] #[inline(never)]
pub fn drv_i128_7(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i128) -> i128 {
    h.wrapping_mul(5) + (a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g) as i128
}
#[no_mangle] #[inline(never)]
pub fn drv_u128_7(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: u128) -> u128 {
    h.wrapping_mul(3).wrapping_add((a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g) as u128)
}
#[no_mangle] #[inline(never)]
pub fn drv_i128_8n(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: u8, j: i128, k: u16) -> i128 {
    j.wrapping_mul(7) + (a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g + 8*h) as i128 + (i as i128) * 1000 + (k as i128) * 100000
}
#[no_mangle] #[inline(never)]
pub fn drv_i128_x5(a: i128, b: i128, c: i128, d: i128, e: i128) -> i128 {
    a.wrapping_add(b.wrapping_mul(3)).wrapping_add(c.wrapping_mul(5)).wrapping_add(d.wrapping_mul(7)).wrapping_add(e.wrapping_mul(11))
}
#[no_mangle] #[inline(never)]
pub fn drv_narrow(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i64, i: u8, j: i8, k: u16, l: i16, m: bool, n: f32) -> i64 {
    a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g + 8*h + (i as i64) * 1000 + (j as i64) * 100_000 + (k as i64) * 7 + (l as i64) * 13 + (m as i64) * 3 + (n * 4.0) as i64
}
#[no_mangle] #[inline(never)]
pub fn drv_sink(a: i64, b: f64, c: i128, d: u8, e: f32, f: i64, g: f64, h: i64, i: f64, j: i64, k: f64,
                l: i64, m: f64, n: i64, o: f64, p: i64, q: f64, r: i64, s: f64, t: u16, u: i128, v: f32, w: bool) -> f64 {
    (a as f64) + 2.0*b + 3.0*(c as f64) + 4.0*(d as f64) + 5.0*(e as f64) + 6.0*(f as f64) + 7.0*g + 8.0*(h as f64)
      + 9.0*i + 10.0*(j as f64) + 11.0*k + 12.0*(l as f64) + 13.0*m + 14.0*(n as f64) + 15.0*o + 16.0*(p as f64)
      + 17.0*q + 18.0*(r as f64) + 19.0*s + 20.0*(t as f64) + 21.0*(u as f64) + 22.0*(v as f64) + 23.0*(w as u8 as f64)
}
#[no_mangle] #[inline(never)]
pub fn drv_small_arr(a: [u16; 4], b: [u8; 3]) -> [u8; 3] {
    [(a[0] as u8).wrapping_add(b[0]), (a[1] >> 2) as u8 ^ b[1], (a[3] >> 8) as u8 ^ b[2] ^ (a[2] as u8)]
}
#[no_mangle] #[inline(never)]
pub extern "C" fn drv_c_i128_7(a: i64, b: i64, c: i64, d: i64, e: i64, f: i64, g: i64, h: i128) -> i128 {
    h.wrapping_mul(9) + (a + 2*b + 3*c + 4*d + 5*e + 6*f + 7*g) as i128
}
const BIG: i128 = -0x1234_5678_9abc_def0_1122_3344_5566_7788;
const UBIG: u128 = 0xfedc_ba98_7654_3210_0f0e_0d0c_0b0a_0908;
extern "C" {
    fn case_fp_i128_7(out: *mut [u64; 2], k: i64);
    fn case_direct_i128_7(out: *mut [u64; 2], k: i64);
    fn case_fp_u128_7(out: *mut [u64; 2], k: i64);
    fn case_fp_i128_8n(out: *mut [u64; 2], k: i64);
    fn case_fp_i128_x5(out: *mut [u64; 2], k: i64);
    fn case_fp_narrow(out: *mut [u64; 2], k: i64);
    fn case_fp_sink(out: *mut [u64; 2], k: i64);
    fn case_fp_small_arr(out: *mut [u64; 2], k: i64);
    fn case_c_fp_i128_7(out: *mut [u64; 2], k: i64);
    fn case_local_fp_i128_7(out: *mut [u64; 2], k: i64);
    fn case_dyn_i128_6(out: *mut [u64; 2], k: i64);
    fn case_table_i128_7(out: *mut [u64; 2], k: i64);
    fn case_fp_i128_7_neg(out: *mut [u64; 2], k: i64);
    fn case_fp_u128_max(out: *mut [u64; 2], k: i64);
}
fn get(case: unsafe extern "C" fn(*mut [u64; 2], i64), k: i64) -> u128 {
    let mut out = [0u64; 2];
    unsafe { case(&mut out, k) };
    out[0] as u128 | (out[1] as u128) << 64
}
fn main() {
    let k = std::hint::black_box(11i64);
    let arr = drv_small_arr([k as u16, 700, 9, 65000], [4, 90, 0x55]);
    let expect: [(&str, unsafe extern "C" fn(*mut [u64; 2], i64), u128); 14] = [
        ("fp_i128_7", case_fp_i128_7, drv_i128_7(k, 2, 3, 4, 5, 6, 7, BIG) as u128),
        ("direct_i128_7", case_direct_i128_7, drv_i128_7(k, 2, 3, 4, 5, 6, 7, BIG) as u128),
        ("fp_u128_7", case_fp_u128_7, drv_u128_7(k, 2, 3, 4, 5, 6, 7, UBIG)),
        ("fp_i128_8n", case_fp_i128_8n, drv_i128_8n(k, 2, 3, 4, 5, 6, 7, 8, 201, -0x1_0000_0000_0000_0003, 65001) as u128),
        ("fp_i128_x5", case_fp_i128_x5, drv_i128_x5(k as i128, BIG, 1 << 100, -(1 << 90), BIG ^ 0x55) as u128),
        ("fp_narrow", case_fp_narrow, drv_narrow(k, 2, 3, 4, 5, 6, 7, 8, 250, -100, 60001, -30001, true, 2.5) as u128),
        ("fp_sink", case_fp_sink, drv_sink(k, 1.5, -77, 250, 0.25, 6, 7.5, 8, 9.5, 10, 11.5, 12, 13.5, 14, 15.5, 16, 17.5, 18, 19.5, 65535, 77, -2.5, true).to_bits() as u128),
        ("fp_small_arr", case_fp_small_arr, u32::from_le_bytes([arr[0], arr[1], arr[2], 0]) as u128),
        ("c_fp_i128_7", case_c_fp_i128_7, drv_c_i128_7(k, 2, 3, 4, 5, 6, 7, BIG) as u128),
        ("local_fp_i128_7", case_local_fp_i128_7, (BIG.wrapping_mul(3) + (k + 4 + 9 + 16 + 25 + 36 + 49) as i128) as u128),
        ("dyn_i128_6", case_dyn_i128_6, (BIG.wrapping_mul(7) + (1000 + k + 4 + 9 + 16 + 25 + 36) as i128) as u128),
        ("table_i128_7", case_table_i128_7, drv_i128_7(k, 2, 3, 4, 5, 6, 7, BIG ^ 0x3333) as u128),
        ("fp_i128_7_neg", case_fp_i128_7_neg, drv_i128_7(k, -2, -3, -4, -5, -6, -7, i128::MIN + 12345) as u128),
        ("fp_u128_max", case_fp_u128_max, drv_u128_7(k, 0, 0, 0, 0, 0, 0, u128::MAX - 5)),
    ];
    let mut bad = 0;
    for (name, case, want) in expect {
        let got = get(case, k);
        if got == want {
            println!("{name} ok {got:032x}");
        } else {
            bad += 1;
            println!("{name} MISMATCH got {got:032x} want {want:032x}");
        }
    }
    std::process::exit(if bad == 0 { 0 } else { 3 });
}
"#;

// Every compile, CG and LLVM alike, starts from the shared build-compiler
// constructor (edition 2021, `-Ztrust-verify=off` on Trust).
fn rustc_command() -> Command {
    toolchain_support::rustc_command()
}

fn run_bounded(command: &mut Command, seconds: u32, log: &Path) -> (Output, String) {
    let mut bounded = Command::new("timeout");
    bounded.args(["--kill-after=5", &seconds.to_string()]);
    bounded.arg(command.get_program()).args(command.get_args());
    for (key, value) in command.get_envs() {
        if let Some(value) = value {
            bounded.env(key, value);
        } else {
            bounded.env_remove(key);
        }
    }
    let output = bounded.output().expect("execute bounded native step");
    let transcript = format!(
        "command: {command:?}\nstatus: {}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::write(log, &transcript).expect("retain complete step log");
    (output, transcript)
}

fn checked(command: &mut Command, seconds: u32, log: &Path) -> Output {
    let (output, transcript) = run_bounded(command, seconds, log);
    assert!(
        output.status.success(),
        "{transcript}\nartifacts: {}",
        log.display()
    );
    output
}

/// Compile `source` as staticlib objects into `objects` (the bridge when
/// `backend` is given); returns the compile's output.
fn compile(
    source: &Path,
    objects: &Path,
    opt: u32,
    backend: Option<&Path>,
    log: &Path,
) -> (Output, String) {
    std::fs::create_dir(objects).unwrap();
    let mut command = rustc_command();
    command.args(["--crate-type", "staticlib", "--crate-name", "fixture"]);
    if let Some(backend) = backend {
        command.arg(format!("-Zcodegen-backend={}", backend.display()));
        command.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    command
        .args(["-Ccodegen-units=1", "-Cpanic=abort", "--target", TARGET])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(objects)
        .arg(source);
    run_bounded(&mut command, 300, log)
}

/// Objects of `dir` except the allocator shim (the driver brings its own).
fn fixture_objects(dir: &Path, log: &Path) -> Vec<PathBuf> {
    let mut objects: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    objects.sort();
    objects
        .into_iter()
        .filter(|object| {
            let symbols = checked(
                Command::new("nm").arg("--defined-only").arg(object),
                30,
                log,
            );
            !String::from_utf8_lossy(&symbols.stdout)
                .lines()
                .any(|line| line.ends_with(" __rust_alloc"))
        })
        .collect()
}

/// Build, link and run one lane; returns the driver's stdout.
fn lane(
    artifacts: &Path,
    source: &Path,
    driver: &Path,
    opt: u32,
    backend: Option<&Path>,
) -> String {
    let compiler = if backend.is_some() { "cg" } else { "llvm" };
    let lane = artifacts.join(format!("{compiler}_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let objects = lane.join("objects");
    let (output, transcript) = compile(source, &objects, opt, backend, &lane.join("compile.log"));
    assert!(
        output.status.success(),
        "{compiler} O{opt} fixture compile failed: {transcript}"
    );
    let linked = fixture_objects(&objects, &lane.join("nm.log"));
    assert!(!linked.is_empty(), "{compiler} O{opt}: no fixture objects");
    let library = lane.join("libfixture.a");
    checked(
        Command::new("ar").arg("crs").arg(&library).args(&linked),
        60,
        &lane.join("ar.log"),
    );
    let executable = lane.join("abi.elf");
    checked(
        rustc_command()
            .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=0"])
            .arg("-L")
            .arg(&lane)
            .args(["-l", "static=fixture"])
            .arg("-o")
            .arg(&executable)
            .arg(driver),
        300,
        &lane.join("link.log"),
    );
    let (run, transcript) = run_bounded(&mut Command::new(&executable), 60, &lane.join("run.log"));
    assert_eq!(
        run.status.code(),
        Some(0),
        "{compiler} O{opt}: an indirect call passed or returned a wrong value: {transcript}"
    );
    let stdout = String::from_utf8(run.stdout).expect("driver output");
    assert_eq!(stdout.lines().count(), CASES, "{compiler} O{opt}: {stdout}");
    assert!(
        stdout
            .lines()
            .all(|line| line.split(' ').nth(1) == Some("ok")),
        "{compiler} O{opt}: {stdout}"
    );
    println!("{compiler} O{opt}: {CASES} cases agree with the direct LLVM call");
    stdout
}

#[test]
fn indirect_calls_pass_arguments_like_direct_calls_linux() {
    if toolchain_support::skip_without_backend_knobs("indirect_call_abi_linux") {
        return;
    }
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-indirect-abi-linux.XXXXXX"])
        .output()
        .expect("mktemp artifacts");
    assert!(temp.status.success());
    let artifacts = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!(
        "native indirect-call ABI artifacts: {}",
        artifacts.display()
    );
    let backend = backend_artifact_support::current_test_backend();
    let source = artifacts.join("fixture.rs");
    std::fs::write(&source, FIXTURE).unwrap();
    let driver = artifacts.join("driver.rs");
    std::fs::write(&driver, DRIVER).unwrap();

    for opt in OPT_LEVELS {
        let cg = lane(&artifacts, &source, &driver, opt, Some(&backend));
        let llvm = lane(&artifacts, &source, &driver, opt, None);
        assert_eq!(cg, llvm, "O{opt}: the bridge and LLVM executables disagree");
    }

    if std::env::var_os(KEEP_ARTIFACTS).is_some_and(|value| value == "1") {
        eprintln!("retained artifacts: {}", artifacts.display());
    } else {
        std::fs::remove_dir_all(&artifacts).expect("remove the artifacts of a passing run");
    }
}

/// Build the cross-backend fixture as an rlib (the bridge when `backend` is
/// given), link the LLVM-compiled driver crate against it, run it and return
/// its stdout.
fn cross_lane(artifacts: &Path, opt: u32, backend: Option<&Path>) -> String {
    let compiler = if backend.is_some() { "cg" } else { "llvm" };
    let lane = artifacts.join(format!("cross_{compiler}_O{opt}"));
    std::fs::create_dir(&lane).unwrap();
    let rlib = lane.join("libfixture.rlib");
    let mut command = rustc_command();
    command.args(["--crate-type", "rlib", "--crate-name", "fixture"]);
    if let Some(backend) = backend {
        command.arg(format!("-Zcodegen-backend={}", backend.display()));
        command.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    command
        .args(["-Ccodegen-units=1", "-Cpanic=abort", "--target", TARGET])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&rlib)
        .arg(artifacts.join("cross_fixture.rs"));
    checked(&mut command, 300, &lane.join("compile.log"));
    let executable = lane.join("cross.elf");
    checked(
        rustc_command()
            .args(["--target", TARGET, "-Cpanic=abort"])
            .arg(format!("-Copt-level={opt}"))
            .arg("--extern")
            .arg(format!("fixture={}", rlib.display()))
            .arg("-o")
            .arg(&executable)
            .arg(artifacts.join("cross_driver.rs")),
        300,
        &lane.join("link.log"),
    );
    let (run, transcript) = run_bounded(&mut Command::new(&executable), 60, &lane.join("run.log"));
    assert_eq!(
        run.status.code(),
        Some(0),
        "{compiler} O{opt}: the cross-backend driver failed: {transcript}"
    );
    let stdout = String::from_utf8(run.stdout).expect("driver output");
    assert_eq!(
        stdout.lines().count(),
        CROSS_LINES,
        "{compiler} O{opt}: {stdout}"
    );
    println!("{compiler} O{opt}: {CROSS_LINES} cross-backend calls ran");
    stdout
}

/// rustc passes a `BackendRepr::Memory` aggregate larger than a pointer BY
/// REFERENCE (`PassMode::Indirect`): `[f32; 4]`, a 12-byte struct,
/// `Result<u64, u32>`, `[u64; 2]`, `(u64, u32, u32)`, `[f64; 2]`, `TypeId`, and
/// (already by reference in AAPCS64) a 24-byte struct, `[u64; 3]` and a
/// 32-byte enum. The bridge declares such a parameter as the pointer rustc
/// passes (`IndirectArgPlan`), so an LLVM-compiled crate can call its
/// exported functions, the fn pointers it hands out and its vtable entries,
/// and the bridge can call LLVM-compiled functions, fn pointers and trait
/// objects, with every value arriving intact. Before L06-P15 the bridge
/// passed the 9-16 byte ones in two registers: an LLVM caller of
/// `sum4([f32; 4])` read -3.4e22 where LLVM returns 30.
#[test]
fn rust_abi_memory_arguments_cross_backend_linux() {
    if toolchain_support::skip_without_backend_knobs("indirect_call_abi_linux") {
        return;
    }
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-cross-abi-linux.XXXXXX"])
        .output()
        .expect("mktemp artifacts");
    assert!(temp.status.success());
    let artifacts = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!(
        "native cross-backend ABI artifacts: {}",
        artifacts.display()
    );
    let backend = backend_artifact_support::current_test_backend();
    std::fs::write(artifacts.join("cross_fixture.rs"), CROSS_FIXTURE).unwrap();
    std::fs::write(artifacts.join("cross_driver.rs"), CROSS_DRIVER).unwrap();
    for opt in OPT_LEVELS {
        let cg = cross_lane(&artifacts, opt, Some(&backend));
        let llvm = cross_lane(&artifacts, opt, None);
        assert_eq!(
            cg, llvm,
            "O{opt}: the bridge-compiled library disagrees with LLVM"
        );
    }
    if std::env::var_os(KEEP_ARTIFACTS).is_some_and(|value| value == "1") {
        eprintln!("retained artifacts: {}", artifacts.display());
    } else {
        std::fs::remove_dir_all(&artifacts).expect("remove the artifacts of a passing run");
    }
}

/// Const-propagated fn pointers remain pointer values, including their
/// relocation to code rather than a data cell holding a code address. Pin the
/// exact-value Rust/unsafe/C cases and neighbouring loaded pointer/FnDef paths
/// against independent LLVM execution at every optimization level.
const CONST_FN_POINTER_FIXTURE: &str = r#"use std::hint::black_box;

#[inline(never)] fn add(x:u64)->u64 { x.wrapping_mul(7).wrapping_add(19) }
#[inline(never)] unsafe fn unsafe_add(x:u64)->u64 { x.wrapping_mul(11).wrapping_add(23) }
#[inline(never)] extern "C" fn c_add(x:u64)->u64 { x.wrapping_mul(13).wrapping_add(29) }
const RUST: fn(u64)->u64=add;
const UNSAFE: unsafe fn(u64)->u64=unsafe_add;
const C: extern "C" fn(u64)->u64=c_add;

#[inline(never)] fn const_rust(x:u64)->u64 { RUST(x) }
#[inline(never)] fn const_unsafe(x:u64)->u64 { unsafe {UNSAFE(x)} }
#[inline(never)] fn const_c(x:u64)->u64 { C(x) }
#[inline(never)] fn dynamic(x:u64)->u64 { let p=black_box(RUST); p(x) }
#[inline(never)] fn item<F:Fn(u64)->u64>(f:F,x:u64)->u64 {f(x)}

fn main(){
    let x=black_box(0x81_1234_5678u64);
    if const_rust(x)!=x.wrapping_mul(7).wrapping_add(19){std::process::exit(1)}
    if const_unsafe(x)!=x.wrapping_mul(11).wrapping_add(23){std::process::exit(2)}
    if const_c(x)!=x.wrapping_mul(13).wrapping_add(29){std::process::exit(3)}
    if dynamic(x)!=x.wrapping_mul(7).wrapping_add(19){std::process::exit(4)}
    if item(add,x)!=x.wrapping_mul(7).wrapping_add(19){std::process::exit(5)}
}
"#;

#[test]
fn constant_fn_pointers_use_code_addresses_linux() {
    if toolchain_support::skip_without_backend_knobs("indirect_call_abi_linux") {
        return;
    }
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-const-fn-pointer-linux.XXXXXX"])
        .output()
        .expect("mktemp artifacts");
    assert!(temp.status.success());
    let artifacts = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!(
        "native constant fn-pointer artifacts: {}",
        artifacts.display()
    );
    let backend = backend_artifact_support::current_test_backend();
    let source = artifacts.join("fixture.rs");
    std::fs::write(&source, CONST_FN_POINTER_FIXTURE).unwrap();
    for opt in 0..=3 {
        for backend in [None, Some(backend.as_path())] {
            let tag = if backend.is_some() { "cg" } else { "llvm" };
            let exe = artifacts.join(format!("{tag}_O{opt}"));
            let mut command = rustc_command();
            command.args([
                "--crate-type=bin",
                "--crate-name=const_fn_pointer",
                "--emit=link,mir",
                "-Ccodegen-units=1",
                "-Cpanic=abort",
                "-Coverflow-checks=off",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            if let Some(backend) = backend {
                command.arg(format!("-Zcodegen-backend={}", backend.display()));
                command.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
            }
            command.arg(&source).arg("-o").arg(&exe);
            checked(
                &mut command,
                300,
                &artifacts.join(format!("{tag}_O{opt}_compile.log")),
            );
            let mir = std::fs::read_to_string(exe.with_extension("mir")).unwrap();
            for name in ["RUST", "UNSAFE", "C"] {
                assert!(
                    mir.contains(&format!("_0 = const {name}(")),
                    "fixture no longer reaches a constant fn-pointer call: {name}, O{opt}"
                );
            }
            checked(
                &mut Command::new(&exe),
                30,
                &artifacts.join(format!("{tag}_O{opt}_run.log")),
            );
        }
    }
    if std::env::var_os(KEEP_ARTIFACTS).is_some_and(|value| value == "1") {
        eprintln!("retained artifacts: {}", artifacts.display());
    } else {
        std::fs::remove_dir_all(&artifacts).expect("remove the artifacts of a passing run");
    }
}
