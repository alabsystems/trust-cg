#![cfg(all(target_os = "macos", target_arch = "aarch64"))]
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;
#[path = "support/x86_rosetta.rs"]
mod x86_rosetta_support;

// Integration test: every argument FAMILY whose placement the bridge's
// `NativeC` claim covers, checked ACROSS the backend boundary — an rlib built
// by one backend, a bin built by the other — in all four rlib x bin cells, on
// aarch64-apple-darwin natively and on x86_64-apple-darwin under Rosetta
// (`support/x86_rosetta.rs`), at O0-O3 (`SIGFAM_LEVELS`, a comma-separated
// list, narrows it for a quick run; a row's own level range bounds it; a row's
// `mixed_levels` adds, on the AArch64 lane, cells whose library and binary are
// built at two different levels). Built on an Apple-silicon macOS host only,
// where both lanes run; it is a required target of
// `scripts/check_darwin_aarch64_bridge.py`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE RULE this file holds: every cell equals the LLVM oracle (LLVM rlib x LLVM
// bin), and the oracle equals the value recorded in the row. A compile failure
// is a failure. A row's `crosses` names a body the
// caller must link from the callee crate at every level the row runs; a caller
// that stops importing it fails the row. One callee crate per row, so a
// refusal or a wrong value in one row cannot hide another.
//
// The families (round 10 of the §17 argument-lane work; measured with
// `targo --unverified`, no proof claim; test rung):
//
// * PAIRS — rustc's `PassMode::Pair` is two independent scalars, so with one
//   register of its class left lane 0 takes it and lane 1 the stack: `(u64,
//   u64)`, `Option<u64>`, `&[u8]` at x7 / R9, `(f64, f64)` / `(f32, f32)` at
//   d7 / xmm7.
// * NARROW CASTS — a Rust-ABI `Cast` of 1-4 bytes is ONE integer rustc packs
//   at its natural size on the Darwin stack (`narrow_cast_param_plan`): before
//   it, 7 of these rows were wrong on aarch64 in both mixed cells at O0 and O2.
// * CLOSURE BODIES — exported under `-Zshare-generics` (O0) because the rlib
//   also calls each one, so the other backend calls the body by symbol: pair,
//   slice, option and narrow-cast arguments at register exhaustion, and
//   `(u32, u32)` / `(f32, f32)` pairs a whole slot would put in ONE register.
//   Before the closure-argument builder these were refused at O0, or (with the
//   refusal bypassed) wrong.
// * IN-CRATE closure calls through every call-site family: a generic `F: Fn`,
//   `iter().enumerate().map(..)`, `.filter(..).map(..)`, `fold`, a `dyn Fn`
//   vtable call from the other backend (pair and narrow-cast elements through
//   the `Fn`-trait dispatch spread), a `dyn` trait method with a narrow cast at
//   exhaustion and in registers.
// * BY-VALUE ENVIRONMENTS — an exported `FnOnce` closure body whose environment
//   is a `Pair`, a scalar, a narrow `Cast` or a pointer to a copy; and an
//   environment that is ONE `f64` / `f32` (rustc's `Scalar(Float)`, passed and
//   returned in a floating-point register) through every by-value crossing: an
//   `impl FnOnce` maker, a generic `F: Fn` argument, `dyn Fn` vtables from
//   either crate and a `dyn FnMut`. Refused at every one of them before
//   `closure_slot_ty`.
// * `extern "rust-call"` CALLABLES — declared with their argument tuple's
//   elements, as rustc's `FnAbi` lists them (`rust_call_spread`): an exported
//   `rust-call` fn whose untupled elements reach register exhaustion (a pair at
//   x7 / R9), an `i128` element (an even register pair on AArch64), and a `dyn
//   Fn` vtable whose `i128` element crosses both ways (the fuzz shape the
//   dispatch spread refused by name until it built elements through the one
//   closure-argument builder); a `rust-call` fn POINTER crossing both ways and
//   a user `rust-call` trait method through `&dyn`. Before F2 the bridge
//   declared the tuple as one parameter and refused every such callable
//   another backend could reach by symbol or vtable, while a `rust-call` fn
//   pointer was silently WRONG in 16 of 24 cells per direction.
//
// Programs are `#![no_std]` so the same source runs on both targets (the Trust
// package ships `rust-std` for its host only). The iterator rows' LLVM rlibs
// reference `core::panicking`, so their LLVM-rlib x bridge-bin cells also hold
// that a bridge-compiled no_std bin defines the `#[panic_handler]`'s
// `rust_begin_unwind` (the cell failed to link before, named as an exception).

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Mutex;

use x86_rosetta_support::X86Exec;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Backend {
    Llvm,
    TrustCg,
}

impl Backend {
    fn tag(self) -> &'static str {
        match self {
            Backend::Llvm => "l",
            Backend::TrustCg => "t",
        }
    }
}

/// One row: a callee crate, a caller `fn main()`, and the oracle's exit code.
struct Row {
    name: &'static str,
    callee: &'static str,
    caller: &'static str,
    oracle: i32,
    /// The row needs `#![feature(unboxed_closures)]` in both crates.
    rust_call: bool,
    /// Any other crate features the CALLEE needs, comma-separated ("" for none).
    features: &'static str,
    /// The highest `-Copt-level` the row runs at. Below 3 only where a level
    /// above hits a MIR-lowering refusal unrelated to argument placement,
    /// measured identical on origin/main (the row names it).
    max_level: u32,
    /// On the host (AArch64) lane only: `(library, binary)` level pairs the
    /// row runs IN ADDITION to its one-level cells, the callee rlib compiled at
    /// the first level and the caller bin at the second, all four cells each.
    /// The x86-64 lane links each level against its own `core`
    /// (`x86_link_core`), so a library and a binary at different levels there
    /// would link two different `core`s; it runs one level per cell.
    mixed_levels: &'static [(u32, u32)],
    /// A substring of a symbol the caller must IMPORT from the callee crate
    /// (`nm -u` of the caller compiled by LLVM to an object) at every level the
    /// row runs: the row's own evidence that the body it names crosses the
    /// backend boundary, so a rustc change that instantiates or inlines it in
    /// the caller fails the row instead of leaving it testing nothing.
    crosses: Option<&'static str>,
}

const fn row(name: &'static str, callee: &'static str, caller: &'static str, oracle: i32) -> Row {
    Row {
        name,
        callee,
        caller,
        oracle,
        rust_call: false,
        features: "",
        max_level: 3,
        mixed_levels: &[],
        crosses: None,
    }
}

/// A row whose LLVM rlib uses `core`'s iterators, and so references
/// `core::panicking` (whose `panic_fmt` calls the bin's `rust_begin_unwind`).
const fn iter_row(
    name: &'static str,
    callee: &'static str,
    caller: &'static str,
    oracle: i32,
) -> Row {
    row(name, callee, caller, oracle)
}

const CALLEE_PRELUDE: &str = "#![no_std]\n#![allow(dead_code)]\nuse core::hint::black_box as bb;\n";

fn rows() -> Vec<Row> {
    vec![
        // ---- pairs at the last register of their class ----
        row(
            "p7",
            "#[inline(never)] pub fn p7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, p: (u64, u64), z: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + p.0 * 11 + p.1 * 13 + z * 17 }",
            "fn main() { exit(callee::p7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), (black_box(8), black_box(9)), black_box(10))) }",
            13,
        ),
        row(
            "p5",
            "#[inline(never)] pub fn p5(a: u64, b: u64, c: u64, d: u64, e: u64, p: (u64, u64), z: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + p.0 * 11 + p.1 * 13 + z * 17 }",
            "fn main() { exit(callee::p5(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), (black_box(8), black_box(9)), black_box(10))) }",
            179,
        ),
        row(
            "o7",
            "#[inline(never)] pub fn o7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, o: Option<u64>, z: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + o.map_or(99, |v| v * 11) + z * 17 }",
            "fn main() { exit(callee::o7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(Some(8)), black_box(10))) }",
            147,
        ),
        row(
            "o5",
            "#[inline(never)] pub fn o5(a: u64, b: u64, c: u64, d: u64, e: u64, o: Option<u64>, z: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + o.map_or(99, |v| v * 11) + z * 17 }",
            "fn main() { exit(callee::o5(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(Some(8)), black_box(10))) }",
            62,
        ),
        row(
            "s7",
            "#[inline(never)] pub fn s7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, s: &[u8], z: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + s.len() as u64 * 11 + s.first().map_or(0, |x| *x as u64) * 13 + z * 17 }",
            "fn main() { let v = [black_box(9u8), 1, 2]; exit(callee::s7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), &v[..], black_box(10))) }",
            209,
        ),
        row(
            "s5",
            "#[inline(never)] pub fn s5(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8], z: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + s.len() as u64 * 11 + s.first().map_or(0, |x| *x as u64) * 13 + z * 17 }",
            "fn main() { let v = [black_box(9u8), 1, 2]; exit(callee::s5(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), &v[..], black_box(10))) }",
            124,
        ),
        row(
            "f7",
            "#[inline(never)] pub fn f7(a: f64, b: f64, c: f64, d: f64, e: f64, f: f64, g: f64, p: (f64, f64), z: f64) -> u64 { (a + b * 2.0 + c * 3.0 + d * 4.0 + e * 5.0 + f * 6.0 + g * 7.0 + p.0 * 11.0 + p.1 * 13.0 + z * 17.0) as u64 }",
            "fn main() { exit(callee::f7(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0), black_box(5.0), black_box(6.0), black_box(7.0), (black_box(8.0), black_box(9.0)), black_box(10.0))) }",
            13,
        ),
        row(
            "g7",
            "#[inline(never)] pub fn g7(a: f32, b: f32, c: f32, d: f32, e: f32, f: f32, g: f32, p: (f32, f32), z: f32) -> u64 { (a + b * 2.0 + c * 3.0 + d * 4.0 + e * 5.0 + f * 6.0 + g * 7.0 + p.0 * 11.0 + p.1 * 13.0 + z * 17.0) as u64 }",
            "fn main() { exit(callee::g7(black_box(1.0), black_box(2.0), black_box(3.0), black_box(4.0), black_box(5.0), black_box(6.0), black_box(7.0), (black_box(8.0), black_box(9.0)), black_box(10.0))) }",
            13,
        ),
        // ---- narrow Rust-ABI casts after eight integer registers ----
        row(
            "c1",
            "#[inline(never)] pub fn c1(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: [u8; 1], y: u8) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + x[0] as u64 * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::c1(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box([9]), black_box(10))) }",
            182,
        ),
        row(
            "c2",
            "#[inline(never)] pub fn c2(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: [u8; 2], y: u16) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + (x[0] as u64 + x[1] as u64 * 3) * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::c2(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box([9, 4]), black_box(10))) }",
            63,
        ),
        row(
            "c2h",
            "#[inline(never)] pub fn c2h(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: [u16; 1], y: u16) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + x[0] as u64 * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::c2h(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box([9]), black_box(10))) }",
            182,
        ),
        row(
            "c3",
            "#[derive(Clone, Copy)] pub struct B3 { pub a: u8, pub b: u8, pub c: u8 }\n#[inline(never)] pub fn c3(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: B3, y: u32) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + (x.a as u64 + x.b as u64 * 3 + x.c as u64 * 5) * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::c3(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box(callee::B3 { a: 9, b: 4, c: 6 }), black_box(10))) }",
            142,
        ),
        row(
            "c3h",
            "#[derive(Clone, Copy)] pub struct H3 { pub a: u16, pub b: u8 }\n#[inline(never)] pub fn c3h(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: H3, y: u8) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + (x.a as u64 + x.b as u64 * 3) * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::c3h(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box(callee::H3 { a: 9, b: 4 }), black_box(10))) }",
            63,
        ),
        row(
            "c4",
            "#[inline(never)] pub fn c4(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: [u8; 4], y: u32) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + (x[0] as u64 + x[3] as u64 * 3) * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::c4(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box([9, 0, 0, 4]), black_box(10))) }",
            63,
        ),
        row(
            "c4f",
            "#[inline(never)] pub fn c4f(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: [f32; 1], y: u32) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + x[0] as u64 * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::c4f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box([9.0]), black_box(10))) }",
            182,
        ),
        row(
            "c5",
            "#[derive(Clone, Copy)] pub struct B5 { pub a: [u8; 5] }\n#[inline(never)] pub fn c5(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: B5, y: u32) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + (x.a[0] as u64 + x.a[4] as u64 * 3) * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::c5(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box(callee::B5 { a: [9, 0, 0, 0, 4] }), black_box(10))) }",
            63,
        ),
        row(
            "c1q",
            "#[inline(never)] pub fn c1q(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: [u8; 1], y: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + x[0] as u64 * 11 + y * 13 }",
            "fn main() { exit(callee::c1q(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box([9]), black_box(10))) }",
            182,
        ),
        row(
            "r4",
            "#[inline(never)] pub fn r4(a: u64, b: u64, x: [u8; 4], y: u32) -> u64 { a + b * 2 + (x[0] as u64 + x[3] as u64 * 3) * 11 + y as u64 * 13 }",
            "fn main() { exit(callee::r4(black_box(1), black_box(2), black_box([9, 0, 0, 4]), black_box(10))) }",
            115,
        ),
        row(
            "cc",
            "#[derive(Clone, Copy)] pub struct B3 { pub a: u8, pub b: u8, pub c: u8 }\n#[inline(never)] pub fn cc(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: [u8; 2], z: [u8; 1], w: B3, y: u16) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + (x[0] as u64 + x[1] as u64 * 3) * 11 + z[0] as u64 * 19 + (w.a as u64 + w.c as u64 * 5) * 23 + y as u64 * 13 }",
            "fn main() { exit(callee::cc(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box([9, 4]), black_box([7]), black_box(callee::B3 { a: 2, b: 0, c: 3 }), black_box(10))) }",
            85,
        ),
        row(
            "cptr",
            "#[inline(never)] pub fn c4(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, x: [u8; 4], y: u32) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + h * 8 + (x[0] as u64 + x[3] as u64 * 3) * 11 + y as u64 * 13 }",
            "fn main() { let f: fn(u64, u64, u64, u64, u64, u64, u64, u64, [u8; 4], u32) -> u64 = black_box(callee::c4); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box([9, 0, 0, 4]), black_box(10))) }",
            63,
        ),
        row(
            "dyn_cast",
            "pub trait Tk { fn m(&self, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, x: [u8; 4], y: u32) -> u64; }\npub struct H(pub u64);\nimpl Tk for H { #[inline(never)] fn m(&self, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, x: [u8; 4], y: u32) -> u64 { self.0 * 29 + a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + (x[0] as u64 + x[3] as u64 * 3) * 11 + y as u64 * 13 } }",
            "fn main() { let h = callee::H(black_box(5)); let t: &dyn callee::Tk = black_box(&h); exit(t.m(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box([9, 0, 0, 4]), black_box(10))) }",
            144,
        ),
        row(
            "reg_cast",
            "pub trait Tr { fn m(&self, a: u64, x: [u8; 3], y: u32) -> u64; }\npub struct H(pub u64);\nimpl Tr for H { #[inline(never)] fn m(&self, a: u64, x: [u8; 3], y: u32) -> u64 { self.0 * 29 + a + (x[0] as u64 + x[2] as u64 * 3) * 11 + y as u64 * 13 } }",
            "fn main() { let h = callee::H(black_box(5)); let t: &dyn callee::Tr = black_box(&h); exit(t.m(black_box(1), black_box([9, 0, 4]), black_box(10))) }",
            5,
        ),
        // ---- closure bodies called by symbol from the other backend (O0) ----
        row(
            "ka",
            "#[inline(never)] pub fn mka(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, (u64, u64)) -> u64 { move |a, b, c, d, e, f, p| a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + p.0 * 11 + p.1 * 13 + k * 17 }\n#[inline(never)] pub fn use_mka() -> u64 { mka(bb(1))(1, 2, 3, 4, 5, 6, (bb(7), 8)) }",
            "fn main() { let f = callee::mka(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), (black_box(8), black_box(9)))) }",
            215,
        ),
        row(
            "kx",
            "#[inline(never)] pub fn mkx(k: u64) -> impl Fn(u64, u64, u64, u64, (u64, u64), u64) -> u64 { move |a, b, c, d, p, z| a + b * 2 + c * 3 + d * 4 + p.0 * 11 + p.1 * 13 + z * 19 + k * 17 }\n#[inline(never)] pub fn use_mkx() -> u64 { mkx(bb(1))(1, 2, 3, 4, (bb(7), 8), 9) }",
            "fn main() { let f = callee::mkx(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), (black_box(8), black_box(9)), black_box(6))) }",
            17,
        ),
        row(
            "ks",
            "#[inline(never)] pub fn mks(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, &[u8]) -> u64 { move |a, b, c, d, e, f, s| a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + s.len() as u64 * 11 + s.first().map_or(0, |x| *x as u64) * 13 + k * 17 }\n#[inline(never)] pub fn use_mks() -> u64 { let v = [bb(9u8), 1]; mks(bb(1))(1, 2, 3, 4, 5, 6, &v[..]) }",
            "fn main() { let f = callee::mks(black_box(10)); let v = [black_box(9u8), 1, 2]; exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), &v[..])) }",
            160,
        ),
        row(
            "ko",
            "#[inline(never)] pub fn mko(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, Option<u64>, u64) -> u64 { move |a, b, c, d, e, f, o, z| a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + o.map_or(99, |v| v * 11) + z * 19 + k * 17 }\n#[inline(never)] pub fn use_mko() -> u64 { mko(bb(1))(1, 2, 3, 4, 5, 6, Some(bb(7)), 9) }",
            "fn main() { let f = callee::mko(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(Some(8)), black_box(6))) }",
            212,
        ),
        row(
            "ku",
            "#[inline(never)] pub fn mku(k: u64) -> impl Fn((u32, u32)) -> u64 { move |p| p.0 as u64 * 11 + p.1 as u64 * 13 + k * 17 }\n#[inline(never)] pub fn use_mku() -> u64 { mku(bb(1))((bb(7), 8)) }",
            "fn main() { let f = callee::mku(black_box(10)); exit(f((black_box(8), black_box(9)))) }",
            124,
        ),
        row(
            "kf",
            "#[inline(never)] pub fn mkf(k: u64) -> impl Fn((f32, f32)) -> u64 { move |p| (p.0 * 11.0 + p.1 * 13.0) as u64 + k * 17 }\n#[inline(never)] pub fn use_mkf() -> u64 { mkf(bb(1))((bb(7.0), 8.0)) }",
            "fn main() { let f = callee::mkf(black_box(10)); exit(f((black_box(8.0), black_box(9.0)))) }",
            124,
        ),
        row(
            "kc",
            "#[inline(never)] pub fn mkc(k: u64) -> impl Fn(u64, u64, u64, u64, u64, u64, u64, [u8; 4], u32) -> u64 { move |a, b, c, d, e, f, g, x, y| a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + (x[0] as u64 + x[3] as u64 * 3) * 11 + y as u64 * 13 + k * 17 }\n#[inline(never)] pub fn use_mkc() -> u64 { mkc(bb(1))(1, 2, 3, 4, 5, 6, 7, [bb(9), 0, 0, 4], 10) }",
            "fn main() { let f = callee::mkc(black_box(10)); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box([9, 0, 0, 4]), black_box(10))) }",
            169,
        ),
        // ---- in-crate closure calls through every call-site family ----
        row(
            "pair_closure",
            "#[inline(never)] fn call2<F: Fn((u32, u32)) -> u64>(f: &F, p: (u32, u32)) -> u64 { f(p) }\npub fn pair_closure(k: u64) -> u64 { let c = move |p: (u32, u32)| p.0 as u64 * 11 + p.1 as u64 * 13 + k; call2(&c, (bb(4), 7)) }",
            "fn main() { exit(callee::pair_closure(black_box(10))) }",
            145,
        ),
        row(
            "opt_closure",
            "#[inline(never)] fn call_opt<F: Fn(Option<u32>, (u16, u8)) -> u64>(f: &F, a: Option<u32>, b: (u16, u8)) -> u64 { f(a, b) }\npub fn opt_closure(k: u64) -> u64 { let c = move |a: Option<u32>, b: (u16, u8)| a.map_or(99, |v| v as u64 * 11) + b.0 as u64 * 13 + b.1 as u64 * 17 + k; call_opt(&c, Some(bb(4)), (bb(5), 6)) }",
            "fn main() { exit(callee::opt_closure(black_box(10))) }",
            221,
        ),
        iter_row(
            "enum_map",
            "pub fn enum_map(k: u64) -> u64 { let v = [bb(3u64), 5, 7, k]; v.iter().enumerate().map(|(i, x)| i as u64 * x + 1).sum() }",
            "fn main() { exit(callee::enum_map(black_box(10))) }",
            53,
        ),
        // O0 and O1 only: from O2 the bridge refuses the inlined filter chain
        // ("closure call receiver is not a place operand"), on origin/main too.
        Row {
            max_level: 1,
            ..iter_row(
                "filter_map_pair",
                "pub fn filter_map_pair(k: u64) -> u64 { let v = [bb(3u64), 5, 7, k, 11]; v.iter().enumerate().filter(|(i, _)| i % 2 == 0).map(|(i, x)| i as u64 * 7 + *x).sum() }",
                "fn main() { exit(callee::filter_map_pair(black_box(10))) }",
                63,
            )
        },
        iter_row(
            "fold_scalar",
            "pub fn fold_scalar(k: u64) -> u64 { let v = [bb(3u64), 5, 7, k]; v.iter().fold(1u64, |acc, x| acc * 3 + x) }",
            "fn main() { exit(callee::fold_scalar(black_box(10))) }",
            238,
        ),
        row(
            "slice_closure",
            "#[inline(never)] fn calls<F: Fn(u64, &[u8]) -> u64>(f: &F, a: u64, s: &[u8]) -> u64 { f(a, s) }\npub fn slice_closure(k: u64) -> u64 { let c = move |a: u64, s: &[u8]| a * 3 + s.len() as u64 * 11 + s.first().map_or(0, |x| *x as u64) * 13 + k; let v = [bb(9u8), 2, 3]; calls(&c, bb(4), &v[..]) }",
            "fn main() { exit(callee::slice_closure(black_box(10))) }",
            172,
        ),
        row(
            "clo_cast",
            "#[inline(never)] fn callc<F: Fn(u64, u64, u64, u64, u64, u64, u64, [u8; 4], u32) -> u64>(f: &F, x: [u8; 4]) -> u64 { f(1, 2, 3, 4, 5, 6, 7, x, 10) }\npub fn clo_cast(k: u64) -> u64 { let c = move |a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, x: [u8; 4], y: u32| a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + g * 7 + (x[0] as u64 + x[3] as u64 * 3) * 11 + y as u64 * 13 + k * 17; callc(&c, [bb(9), 0, 0, 4]) }",
            "fn main() { exit(callee::clo_cast(black_box(10))) }",
            169,
        ),
        // O0 only: from O1 the bin inlines `dyn_fn_pair` and the bridge refuses
        // its constant unsize ("trait-object unsize source is not a place
        // operand"). origin/main refuses the same text at O2; at O1 it refused
        // the bin earlier, at the `Fn`-trait dispatch spread this change
        // generalizes. Until F2 the trust-cg rlib was refused by name as well
        // (its vtable's `call_once` `VTableShim` was declared TUPLED); now its
        // cells run too.
        Row {
            max_level: 0,
            ..row(
                "dyn_fn_pair",
                "pub fn dyn_fn_pair() -> &'static dyn Fn(u64, (u32, u32), [u8; 3]) -> u64 { &|a: u64, p: (u32, u32), x: [u8; 3]| a * 3 + p.0 as u64 * 11 + p.1 as u64 * 13 + (x[0] as u64 + x[2] as u64 * 5) * 17 }",
                "fn main() { let f = callee::dyn_fn_pair(); exit(f(black_box(2), (black_box(4), black_box(7)), black_box([9, 0, 4]))) }",
                132,
            )
        },
        // ---- `extern "rust-call"` callables, untupled as rustc's `FnAbi` lists them ----
        Row {
            rust_call: true,
            ..row(
                "rc_p7",
                "#[inline(never)] pub extern \"rust-call\" fn rc_p7(t: (u64, u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64 { t.0 + t.1 * 2 + t.2 * 3 + t.3 * 4 + t.4 * 5 + t.5 * 6 + t.6 * 7 + (t.7).0 * 11 + (t.7).1 * 13 + t.8 * 17 }",
                "fn main() { exit(callee::rc_p7((black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), (black_box(8), black_box(9)), black_box(10)))) }",
                13,
            )
        },
        Row {
            rust_call: true,
            ..row(
                "rc_p5",
                "#[inline(never)] pub extern \"rust-call\" fn rc_p5(t: (u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64 { t.0 + t.1 * 2 + t.2 * 3 + t.3 * 4 + t.4 * 5 + (t.5).0 * 11 + (t.5).1 * 13 + t.6 * 17 }",
                "fn main() { exit(callee::rc_p5((black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), (black_box(8), black_box(9)), black_box(10)))) }",
                179,
            )
        },
        Row {
            rust_call: true,
            ..row(
                "rc_i128",
                "#[inline(never)] pub extern \"rust-call\" fn rc_i128(t: (u64, i128, u64)) -> u64 { t.0 * 3 + ((t.1 >> 64) as u64) * 11 + (t.1 as u64) * 5 + t.2 * 7 }",
                "fn main() { exit(callee::rc_i128((black_box(1), black_box((2i128 << 64) | 3), black_box(4)))) }",
                68,
            )
        },
        row(
            "dyn_i128",
            "#[inline(never)] pub fn call_g(f: &dyn Fn(u64, i128, u64) -> u64) -> u64 { f(bb(1), bb((2i128 << 64) | 3), bb(4)) }",
            "fn main() { let k = black_box(3u64); let c = move |a: u64, b: i128, x: u64| a * k + ((b >> 64) as u64) * 11 + (b as u64) * 5 + x * 7; exit(callee::call_g(&c)) }",
            68,
        ),
        // A `rust-call` fn POINTER crossing the boundary both ways, and a user
        // `extern "rust-call"` trait method through `&dyn`: the pointer's callee
        // and every call through it agree on the untupled elements. Before F2
        // the pointer rows were silently WRONG in 16 of 24 cells per direction
        // (a64 O0 lxt 136 against 13) and the trait row refused in every cell.
        Row {
            rust_call: true,
            ..row(
                "rc_fnptr_rev",
                "#[inline(never)] pub extern \"rust-call\" fn rc(t: (u64, u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64 { t.0 + t.1 * 2 + t.2 * 3 + t.3 * 4 + t.4 * 5 + t.5 * 6 + t.6 * 7 + (t.7).0 * 11 + (t.7).1 * 13 + t.8 * 17 }\n#[inline(never)] pub fn get() -> extern \"rust-call\" fn((u64, u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64 { bb(rc as extern \"rust-call\" fn((u64, u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64) }",
                "fn main() { let p = callee::get(); exit(p((black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), (black_box(8), black_box(9)), black_box(10)))) }",
                13,
            )
        },
        Row {
            rust_call: true,
            ..row(
                "rc_fnptr_fwd",
                "#[inline(never)] pub fn callp(p: extern \"rust-call\" fn((u64, u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64) -> u64 { p((bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), bb(7), (bb(8), bb(9)), bb(10))) }",
                "extern \"rust-call\" fn mine(t: (u64, u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64 { t.0 + t.1 * 2 + t.2 * 3 + t.3 * 4 + t.4 * 5 + t.5 * 6 + t.6 * 7 + (t.7).0 * 11 + (t.7).1 * 13 + t.8 * 17 + 2 }\nfn main() { exit(callee::callp(black_box(mine as extern \"rust-call\" fn((u64, u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64))) }",
                15,
            )
        },
        Row {
            rust_call: true,
            ..row(
                "rc_trait_dyn",
                "pub trait RC { extern \"rust-call\" fn m(&self, t: (u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64; }\npub struct S(pub u64);\nimpl RC for S { #[inline(never)] extern \"rust-call\" fn m(&self, t: (u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64 { self.0 * 29 + t.0 + t.1 * 2 + t.2 * 3 + t.3 * 4 + t.4 * 5 + t.5 * 6 + (t.6).0 * 11 + (t.6).1 * 13 + t.7 * 17 } }\n#[inline(never)] pub fn call_rc(r: &dyn RC) -> u64 { r.m((bb(1), bb(2), bb(3), bb(4), bb(5), bb(6), (bb(8), bb(9)), bb(10))) }",
                "struct T(u64);\nimpl callee::RC for T { extern \"rust-call\" fn m(&self, t: (u64, u64, u64, u64, u64, u64, (u64, u64), u64)) -> u64 { self.0 * 31 + t.0 + t.1 * 2 + t.2 * 3 + t.3 * 4 + t.4 * 5 + t.5 * 6 + (t.6).0 * 11 + (t.6).1 * 13 + t.7 * 17 } }\nfn main() { let s = callee::S(black_box(5)); let a = callee::call_rc(&s); let r: &dyn callee::RC = black_box(&s); let b = r.m((black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), (black_box(8), black_box(9)), black_box(10))); let t = T(black_box(3)); let c = callee::call_rc(&t); exit(a + b * 3 + c * 7) }",
                82,
            )
        },
        // ---- by-value closure environments of every mode ----
        row(
            "env_pair",
            "pub struct P2(pub u64, pub u64);\n#[inline(never)] pub fn mkp(a: u64, b: u64) -> impl FnOnce(u64) -> u64 { let p = P2(a, b); move |x| { let p = p; p.0 * 11 + p.1 * 13 + x } }\n#[inline(never)] pub fn use_mkp() -> u64 { mkp(bb(1), 2)(3) }",
            "fn main() { exit(callee::mkp(black_box(4), black_box(5))(black_box(6))) }",
            115,
        ),
        row(
            "env_scalar",
            "pub struct NC(pub u64);\n#[inline(never)] pub fn mkn(v: u64) -> impl FnOnce(u64) -> u64 { let n = NC(v); move |x| { let n = n; n.0 * 11 + x } }\n#[inline(never)] pub fn use_mkn() -> u64 { mkn(bb(1))(3) }",
            "fn main() { exit(callee::mkn(black_box(5))(black_box(6))) }",
            61,
        ),
        // O0 and O1 only: from O2 the inlined closure body hits the bridge's
        // "slice pointer metadata before known array length" refusal, on
        // origin/main too (the row is about the O0 export anyway).
        Row {
            max_level: 1,
            ..row(
                "env_slice",
                "pub struct SS<'a>(pub &'a [u8]);\n#[inline(never)] pub fn mkslice<'a>(s: &'a [u8]) -> impl FnOnce(u64) -> u64 + 'a { let s = SS(s); move |x| { let s = s; s.0.len() as u64 * 11 + s.0.first().map_or(0, |b| *b as u64) * 13 + x } }\n#[inline(never)] pub fn use_mkslice(s: &[u8]) -> u64 { mkslice(s)(3) }",
                "fn main() { let v = [black_box(9u8), 1, 2]; exit(callee::mkslice(&v[..])(black_box(6))) }",
                156,
            )
        },
        row(
            "env_c3",
            "pub struct B3 { pub a: u8, pub b: u8, pub c: u8 }\n#[inline(never)] pub fn mkb3(a: u8) -> impl FnOnce(u64) -> u64 { let t = B3 { a, b: 4, c: 6 }; move |x| { let t = t; t.a as u64 * 11 + t.b as u64 * 13 + t.c as u64 * 17 + x } }\n#[inline(never)] pub fn use_mkb3() -> u64 { mkb3(bb(1))(3) }",
            "fn main() { exit(callee::mkb3(black_box(5))(black_box(6))) }",
            215,
        ),
        row(
            "env_t12",
            "pub struct T12 { pub a: u32, pub b: u32, pub c: u32 }\n#[inline(never)] pub fn mkt(a: u32) -> impl FnOnce(u64) -> u64 { let t = T12 { a, b: 4, c: 6 }; move |x| { let t = t; t.a as u64 * 11 + t.b as u64 * 13 + t.c as u64 * 17 + x } }\n#[inline(never)] pub fn use_mkt() -> u64 { mkt(bb(1))(3) }",
            "fn main() { exit(callee::mkt(black_box(5))(black_box(6))) }",
            215,
        ),
        row(
            "env_refs",
            "pub struct R2<'a>(&'a u64, &'a u64);\n#[inline(never)] fn run<F: FnOnce() -> u64>(f: F) -> u64 { f() }\npub fn env_refs(k: u64) -> u64 { let a = bb(3u64); let b = bb(4u64); let r = R2(&a, &b); run(move || { let r = r; *r.0 * 11 + *r.1 * 13 + k }) }",
            "fn main() { exit(callee::env_refs(black_box(10))) }",
            95,
        ),
        // A non-capturing closure coerced to a `fn` pointer, crossing both ways,
        // with a `(u64, u64)` pair at the last integer register: the pointer
        // lands on the closure's module-local fn-pointer entry
        // (`closure_fn_pointer_entry`), which forwards to the body's declaration.
        // This identity now binds on both object paths. All four backend
        // combinations must compile, run and match the oracle at every level.
        row(
            "clo_fnptr",
            "pub type P = fn(u64, u64, u64, u64, u64, u64, (u64, u64)) -> u64;\n#[inline(never)] pub fn fp() -> P { |a, b, c, d, e, f, p| a + b + c + d + e + f + p.0 * 5 + p.1 * 3 }\n#[inline(never)] pub fn callp(p: P) -> u64 { p(bb(1), 2, 3, 4, 5, 6, (bb(7), 8)) }",
            "fn main() { let mine: callee::P = |a, b, c, d, e, f, p| a + b + c + d + e + f + p.0 * 2 + p.1; exit(callee::fp()(black_box(1), 2, 3, 4, 5, 6, (black_box(7), 8)) + callee::callp(black_box(mine))) }",
            123,
        ),
        // ---- the three shapes main's refusal route listed as KNOWN OPEN WRONG
        // CODE (fourth verifier round, 2026-10-03, AArch64 Linux): a closure
        // body taking a whole `Pair` that holds a `bool`, linked across the
        // boundary; an `#[inline(never)]` closure in an exported generic
        // parent, with a `&str` at register exhaustion; and a by-value closure
        // type reaching the other crate through a field typed by a
        // `type_alias_impl_trait` alias. Under the per-signature rule each body
        // is declared as rustc passes its arguments, so each must agree ----
        Row {
            features: "stmt_expr_attributes",
            ..row(
                "bool_pair_body",
                "#[inline(never)] pub fn mkb(k: u64) -> impl Fn(u64, (u64, bool)) -> u64 { #[inline(never)] move |a: u64, p: (u64, bool)| a + p.0 * 3 + if p.1 { k * 7 } else { 1 } }\n#[inline(never)] pub fn use_mkb() -> u64 { let f = mkb(bb(2)); f(bb(1), (bb(5), bb(false))) }",
                "fn main() { let f = callee::mkb(black_box(4)); exit(f(black_box(1), (black_box(5), black_box(true))) + f(black_box(2), (black_box(6), black_box(false))) + callee::use_mkb()) }",
                82,
            )
        },
        // `main` measured this shape WRONG only with the library and the binary
        // at DIFFERENT levels: its pre-merge bridge (`65e816a73`) builds a
        // library at O0 whose closure body an LLVM binary at O2 or O3 links,
        // and that cell exits a value other than LLVM's 85 (43, 121, 157, 245
        // over two runs); with both crates at one level it agrees at O0 and
        // refuses [TCG-ARG-ABI] at O1-O3 (measured 2026-10-10 on
        // aarch64-apple-darwin). So the row also runs every pair of two
        // different levels (`mixed_levels`, host lane only).
        Row {
            features: "stmt_expr_attributes",
            mixed_levels: &[
                (0, 1),
                (0, 2),
                (0, 3),
                (1, 0),
                (1, 2),
                (1, 3),
                (2, 0),
                (2, 1),
                (2, 3),
                (3, 0),
                (3, 1),
                (3, 2),
            ],
            ..row(
                "inline_never_parent",
                "#[inline] pub fn par<T: Copy + Into<u64>>(k: T, s: &'static str) -> u64 { let c = #[inline(never)] move |a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, t: &'static str| a + b + c + d + e + f + t.len() as u64 * 3 + k.into(); bb(&c)(1, 2, 3, 4, 5, 6, s) }\n#[inline(never)] pub fn use_par() -> u64 { par(bb(7u32), \"hello\") }",
                "fn main() { exit(callee::par(black_box(9u32), black_box(\"hey!\")) + callee::use_par()) }",
                85,
            )
        },
        // `mkw` returns a struct whose field is typed by the alias and holds a
        // `FnOnce` closure whose by-value environment is a `Pair`; the caller
        // moves the closure out of the field and calls it. The closure is
        // `#[inline(never)]`, so its body stays in the callee crate and the
        // caller links it by symbol at O0-O3 (`crosses`, the v0-mangled
        // `callee::mkw::{closure#0}`). `main`'s pre-merge bridge (`65e816a73`)
        // SIGSEGVs in the bridge-library x LLVM-binary cell at every level and
        // refuses both bridge binaries [TCG-ARG-ABI] (measured 2026-10-10 on
        // aarch64-apple-darwin).
        Row {
            features: "type_alias_impl_trait, stmt_expr_attributes",
            crosses: Some("6callee3mkw0"),
            ..row(
                "tait_field",
                "pub struct P2(pub u64, pub u64);\npub type F = impl FnOnce(u64) -> u64;\npub struct W { pub f: F }\n#[define_opaque(F)] pub fn mkw(k: u64) -> W { let p = P2(k, 6); W { f: #[inline(never)] move |x: u64| { let p = p; p.0 * 11 + p.1 * 13 + x } } }\n#[inline(never)] pub fn use_w(w: W) -> u64 { (w.f)(bb(5)) }",
                "fn main() { let w = callee::mkw(black_box(11)); exit((w.f)(black_box(3)) + callee::use_w(callee::mkw(black_box(2)))) }",
                56,
            )
        },
        // ---- a closure environment that is ONE float: rustc's `Scalar(Float)`,
        // passed and returned in a floating-point register (`closure_slot_ty`).
        // Before, every by-value crossing of it was refused `[TCG-ARG-ABI]` /
        // `[TCG-RET-ABI]` (the slot's integer lane is a general-purpose
        // register), on origin/main too: an exported `impl FnOnce` maker, a
        // generic `F: Fn` argument (the rlib also instantiates one), a `dyn Fn`
        // vtable from either crate (its `call_once` shim takes the closure by
        // value) and a `dyn FnMut` whose one `f64` the body mutates ----
        row(
            "env_f64",
            "#[inline(never)] pub fn mkf64(s: f64) -> impl FnOnce(f64) -> f64 { move |x: f64| x * s }\n#[inline(never)] pub fn use_mkf64() -> u64 { mkf64(bb(2.0))(bb(3.0)) as u64 }",
            "fn main() { exit(callee::mkf64(black_box(2.5))(black_box(3.0)) as u64) }",
            7,
        ),
        row(
            "env_f32",
            "#[inline(never)] pub fn mkf32(s: f32) -> impl FnOnce(f32) -> f32 { move |x: f32| x * s }\n#[inline(never)] pub fn use_mkf32() -> u64 { mkf32(bb(2.0))(bb(3.0)) as u64 }",
            "fn main() { exit(callee::mkf32(black_box(2.5))(black_box(3.0)) as u64) }",
            7,
        ),
        row(
            "fn_env_f64",
            "#[inline(never)] pub fn apply64<F: Fn(f64) -> f64>(f: F) -> u64 { f(bb(3.0)) as u64 }\n#[inline(never)] pub fn use_apply64(s: f64) -> u64 { apply64(move |x: f64| x * s) }",
            "fn main() { let s = black_box(2.5f64); exit(callee::apply64(move |x: f64| x * s) + callee::use_apply64(black_box(1.5))) }",
            11,
        ),
        row(
            "fn_env_f32",
            "#[inline(never)] pub fn apply32<F: Fn(f32) -> f32>(f: F) -> u64 { f(bb(3.0)) as u64 }\n#[inline(never)] pub fn use_apply32(s: f32) -> u64 { apply32(move |x: f32| x * s) }",
            "fn main() { let s = black_box(2.5f32); exit(callee::apply32(move |x: f32| x * s) + callee::use_apply32(black_box(1.5))) }",
            11,
        ),
        row(
            "dyn_env_f64",
            "#[inline(never)] pub fn apply_dyn64(f: &dyn Fn(f64) -> f64) -> u64 { f(bb(3.0)) as u64 }\n#[inline(never)] pub fn own_dyn64(s: f64) -> u64 { let f = move |x: f64| x * s; apply_dyn64(&f) }",
            "fn main() { let s = black_box(2.5f64); let f = move |x: f64| x * s; exit(callee::apply_dyn64(&f) + callee::own_dyn64(black_box(1.5))) }",
            11,
        ),
        row(
            "dyn_env_f32",
            "#[inline(never)] pub fn apply_dyn32(f: &dyn Fn(f32) -> f32) -> u64 { f(bb(3.0)) as u64 }\n#[inline(never)] pub fn own_dyn32(s: f32) -> u64 { let f = move |x: f32| x * s; apply_dyn32(&f) }",
            "fn main() { let s = black_box(2.5f32); let f = move |x: f32| x * s; exit(callee::apply_dyn32(&f) + callee::own_dyn32(black_box(1.5))) }",
            11,
        ),
        // A one-`f32` environment passed BY VALUE after eight `f64`s: the float
        // registers are exhausted, so rustc's `f32` goes on the stack (4 bytes
        // on Darwin, an eightbyte under AAPCS64 and System V).
        row(
            "fn_env_f32_stack",
            "#[inline(never)] pub fn apply_st<F: Fn(f32) -> f32>(a: f64, b: f64, c: f64, d: f64, e: f64, g: f64, h: f64, i: f64, f: F) -> u64 { (a + b + c + d + e + g + h + i) as u64 + f(bb(3.0)) as u64 }\n#[inline(never)] pub fn use_apply_st(s: f32) -> u64 { apply_st(1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, move |x: f32| x * s) }",
            "fn main() { let s = black_box(2.5f32); exit(callee::apply_st(black_box(1.0), 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, move |x: f32| x * s) + callee::use_apply_st(black_box(1.5))) }",
            83,
        ),
        row(
            "fnmut_env_f64",
            "#[inline(never)] pub fn apply_mut64(f: &mut dyn FnMut(f64) -> f64) -> u64 { (f(bb(3.0)) + f(bb(4.0))) as u64 }",
            "fn main() { let mut acc = black_box(1.5f64); let mut f = move |x: f64| { acc += x; acc }; exit(callee::apply_mut64(&mut f)) }",
            13,
        ),
    ]
}

/// The caller-side prelude (`exit`, `black_box`, a panic handler); see
/// `x86_rosetta_support::no_std_caller`.
fn caller_source(row: &Row) -> String {
    let src = x86_rosetta_support::no_std_caller(row.caller);
    if row.rust_call {
        src.replacen("#![no_std]", "#![no_std]\n#![feature(unboxed_closures)]", 1)
    } else {
        src
    }
}

fn callee_source(row: &Row) -> String {
    let mut features = String::new();
    if row.rust_call {
        features.push_str("#![feature(unboxed_closures)]\n");
    }
    if !row.features.is_empty() {
        features.push_str(&format!("#![feature({})]\n", row.features));
    }
    format!("{features}{CALLEE_PRELUDE}{}\n", row.callee)
}

/// How one target runs its compiles and its binaries.
struct Lane {
    target: &'static str,
    /// `true`: x86-64 through `x86_rosetta_support` (natively or under
    /// Rosetta, with the opt level's own `core`); `false`: the host itself.
    x86: bool,
}

impl Lane {
    fn compile_args(&self, opt: &str) -> Vec<OsString> {
        if self.x86 {
            x86_rosetta_support::x86_execution(opt).compile_args()
        } else {
            vec![
                "--target".into(),
                self.target.into(),
                "-Clink-arg=-lSystem".into(),
            ]
        }
    }

    fn run(&self, bin: &Path, opt: &str) -> Result<i32, String> {
        let out = if self.x86 {
            x86_rosetta_support::x86_execution(opt)
                .run(bin)
                .ok_or_else(|| "no x86-64 execution route".to_owned())?
        } else {
            Command::new(bin)
                .output()
                .map_err(|e| format!("run {bin:?}: {e}"))?
        };
        out.status
            .code()
            .ok_or_else(|| format!("exited via signal: {:?}", out.status))
    }
}

fn levels() -> Vec<String> {
    std::env::var("SIGFAM_LEVELS")
        .ok()
        .filter(|v| !v.trim().is_empty())
        .map(|v| v.split(',').map(|l| l.trim().to_owned()).collect())
        .unwrap_or_else(|| ["0", "1", "2", "3"].map(str::to_owned).to_vec())
}

fn compile(
    lane: &Lane,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    args: &[OsString],
) -> Result<(), String> {
    let mut cmd = toolchain_support::rustc_command();
    if backend == Backend::TrustCg {
        let mut b = OsString::from("-Zcodegen-backend=");
        b.push(dylib);
        cmd.arg(b);
        cmd.arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    cmd.args(lane.compile_args(opt))
        .args([
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .args(args);
    let out = cmd.output().map_err(|e| format!("spawn rustc: {e}"))?;
    if out.status.success() {
        Ok(())
    } else {
        Err(String::from_utf8_lossy(&out.stderr).into_owned())
    }
}

/// The lines of a compiler's stderr a failure report quotes, each shortened.
fn brief(stderr: &str) -> String {
    stderr
        .lines()
        .filter(|l| l.contains("error") || l.contains("[TCG-") || l.contains("rust_begin_unwind"))
        .map(|l| l.chars().take(600).collect::<String>())
        .take(4)
        .collect::<Vec<_>>()
        .join(" | ")
}

/// The failure, if any, of a row's `crosses` check: the row's caller, compiled
/// by LLVM to an object at `opt` against the row's LLVM callee rlib, must leave
/// a symbol containing `symbol` undefined (`nm -u`), i.e. link it from the
/// callee crate.
fn crossing_failure(
    lane: &Lane,
    dylib: &Path,
    dir: &Path,
    tag: &str,
    symbol: &str,
    opt: &str,
) -> Option<String> {
    let rlib_dir = dir.join(format!("rlib-{}", Backend::Llvm.tag()));
    let obj = dir.join("caller-crossing.o");
    let mut ext = OsString::from("callee=");
    ext.push(rlib_dir.join("libcallee.rlib"));
    let args: Vec<OsString> = vec![
        "--crate-type".into(),
        "bin".into(),
        "--emit=obj".into(),
        "--extern".into(),
        ext,
        "-L".into(),
        rlib_dir.into(),
        "-o".into(),
        obj.clone().into(),
        dir.join("caller.rs").into(),
    ];
    if let Err(e) = compile(lane, dylib, Backend::Llvm, opt, &args) {
        return Some(format!(
            "{tag}: the LLVM caller object for the crossing check failed: {}",
            brief(&e)
        ));
    }
    let nm = match Command::new("nm").arg("-u").arg(&obj).output() {
        Ok(out) if out.status.success() => String::from_utf8_lossy(&out.stdout).into_owned(),
        Ok(out) => {
            return Some(format!(
                "{tag}: nm -u {obj:?} failed: {}",
                String::from_utf8_lossy(&out.stderr).trim()
            ));
        }
        Err(e) => return Some(format!("{tag}: run nm: {e}")),
    };
    if nm.lines().any(|l| l.contains(symbol)) {
        return None;
    }
    let imports: Vec<&str> = nm
        .lines()
        .map(str::trim)
        .filter(|l| l.contains("6callee"))
        .collect();
    Some(format!(
        "{tag}: the caller imports no `{symbol}` symbol from the callee crate (it imports {imports:?}), \
         so the body the row names no longer crosses the backend boundary"
    ))
}

/// Every cell of one row with the callee rlib at `lib_opt` and the caller bin
/// at `bin_opt`; returns the failures.
fn run_row(
    lane: &Lane,
    dylib: &Path,
    root: &Path,
    row: &Row,
    (lib_opt, bin_opt): (&str, &str),
) -> Vec<String> {
    let (dir, at) = if lib_opt == bin_opt {
        (
            root.join(format!("{}-O{lib_opt}", row.name)),
            format!("O{lib_opt}"),
        )
    } else {
        (
            root.join(format!("{}-L{lib_opt}-B{bin_opt}", row.name)),
            format!("lib O{lib_opt} / bin O{bin_opt}"),
        )
    };
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create row dir");
    let callee_rs = dir.join("callee.rs");
    let caller_rs = dir.join("caller.rs");
    std::fs::write(&callee_rs, callee_source(row)).expect("write callee");
    std::fs::write(&caller_rs, caller_source(row)).expect("write caller");
    let mut failures = Vec::new();
    let tag = format!("{} {at} `{}`", lane.target, row.name);
    let mut rlibs = Vec::new();
    for backend in [Backend::Llvm, Backend::TrustCg] {
        let out_dir = dir.join(format!("rlib-{}", backend.tag()));
        std::fs::create_dir_all(&out_dir).expect("create rlib dir");
        let args: Vec<OsString> = vec![
            "--crate-type".into(),
            "rlib".into(),
            "--crate-name".into(),
            "callee".into(),
            "--out-dir".into(),
            out_dir.clone().into(),
            callee_rs.clone().into(),
        ];
        let result = compile(lane, dylib, backend, lib_opt, &args);
        match result {
            Ok(()) => rlibs.push((backend, out_dir.join("libcallee.rlib"))),
            Err(e) if backend == Backend::Llvm => {
                return vec![format!("{tag}: the LLVM callee rlib failed: {}", brief(&e))];
            }
            Err(e) => failures.push(format!(
                "{tag}: the trust-cg callee rlib failed: {}",
                brief(&e)
            )),
        }
    }
    if let Some(symbol) = row.crosses {
        failures.extend(crossing_failure(lane, dylib, &dir, &tag, symbol, bin_opt));
    }
    let mut oracle = None;
    for (rlib_backend, rlib) in &rlibs {
        for bin_backend in [Backend::Llvm, Backend::TrustCg] {
            let cell = format!("{}x{}", rlib_backend.tag(), bin_backend.tag());
            let bin = dir.join(format!("bin-{cell}"));
            let mut ext = OsString::from("callee=");
            ext.push(rlib);
            let args: Vec<OsString> = vec![
                "--crate-type".into(),
                "bin".into(),
                "--extern".into(),
                ext,
                "-L".into(),
                rlib.parent().expect("rlib dir").into(),
                "-o".into(),
                bin.clone().into(),
                caller_rs.clone().into(),
            ];
            let result = compile(lane, dylib, bin_backend, bin_opt, &args);
            if let Err(e) = result {
                failures.push(format!("{tag} {cell}: failed to compile: {}", brief(&e)));
                continue;
            }
            match lane.run(&bin, bin_opt) {
                Ok(code) if cell == "lxl" => {
                    oracle = Some(code);
                    if row.oracle != 0 && code != row.oracle {
                        failures.push(format!(
                            "{tag}: the ORACLE (LLVM x LLVM) exits {code}, the row records {}",
                            row.oracle
                        ));
                    }
                }
                Ok(code) => {
                    // Cells are visited after `lxl` (the LLVM rlib comes first).
                    let want = oracle.unwrap_or(row.oracle);
                    if code != want {
                        failures.push(format!("{tag} {cell}: exit {code}, oracle {want}"));
                    }
                }
                Err(e) => failures.push(format!("{tag} {cell}: {e}")),
            }
        }
    }
    if row.oracle == 0 {
        failures.push(format!(
            "{tag}: the row records no oracle; the LLVM x LLVM cell exits {oracle:?}"
        ));
    }
    if failures.is_empty() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    failures
}

/// The backend under test: the one this Cargo test build produced, or — to
/// measure another build against the same rows (a failing-first run against
/// an older dylib) — the path in `SIGFAM_DYLIB`.
fn backend_under_test() -> PathBuf {
    match std::env::var_os("SIGFAM_DYLIB") {
        Some(path) => {
            eprintln!("SIGFAM_DYLIB: measuring {path:?}, not this test build's backend");
            PathBuf::from(path)
        }
        None => backend_artifact_support::current_test_backend(),
    }
}

fn run_lane(lane: Lane, test: &str) {
    let only: Option<Vec<String>> = std::env::var("SIGFAM_ROWS")
        .ok()
        .filter(|v| !v.trim().is_empty())
        .map(|v| v.split(',').map(|r| r.trim().to_owned()).collect());
    let rows: Vec<Row> = rows()
        .into_iter()
        .filter(|r| only.as_ref().is_none_or(|o| o.iter().any(|n| n == r.name)))
        .collect();
    assert!(
        !rows.is_empty(),
        "[SIGFAM-EMPTY-ROWS] {test}: SIGFAM_ROWS selected no original signature-family row"
    );
    let selected: Vec<u32> = levels().iter().filter_map(|l| l.parse().ok()).collect();
    // `(row, library level, binary level)`: every row at each selected level
    // up to its `max_level`, then (host lane only) its `mixed_levels` pairs
    // whose two levels are both selected and admitted.
    let mut work: Vec<(usize, String, String)> = levels()
        .into_iter()
        .flat_map(|l| (0..rows.len()).map(move |i| (i, l.clone(), l.clone())))
        .filter(|(i, l, _)| {
            l.parse::<u32>()
                .is_ok_and(|level| level <= rows[*i].max_level)
        })
        .collect();
    if !lane.x86 {
        for (i, row) in rows.iter().enumerate() {
            for &(lib, bin) in row.mixed_levels {
                let admitted = |level: u32| level <= row.max_level && selected.contains(&level);
                if admitted(lib) && admitted(bin) {
                    work.push((i, lib.to_string(), bin.to_string()));
                }
            }
        }
    }
    assert!(
        !work.is_empty(),
        "[SIGFAM-EMPTY-WORK] {test}: SIGFAM_LEVELS selected no admitted row/level work"
    );
    if lane.x86 {
        // One core per requested level, built only after real work is selected.
        // Apple silicon has a Rosetta route; its absence remains a hard failure.
        for opt in levels() {
            if let X86Exec::Unavailable(why) = x86_rosetta_support::x86_execution(&opt) {
                panic!("no x86-64 execution route on this Apple-silicon host: {why}");
            }
        }
    }
    let dylib = backend_under_test();
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR"))
        .join("signature_placement_families")
        .join(lane.target);
    std::fs::create_dir_all(&root).expect("create root");
    let next = Mutex::new(work.into_iter());
    let failures = Mutex::new(Vec::new());
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .clamp(1, 6);
    std::thread::scope(|scope| {
        for _ in 0..workers {
            scope.spawn(|| {
                loop {
                    let item = next.lock().unwrap().next();
                    let Some((i, lib_opt, bin_opt)) = item else {
                        break;
                    };
                    let f = run_row(&lane, &dylib, &root, &rows[i], (&lib_opt, &bin_opt));
                    failures.lock().unwrap().extend(f);
                }
            });
        }
    });
    let mut failures = failures.into_inner().unwrap();
    failures.sort();
    assert!(
        failures.is_empty(),
        "{test}: {} cell(s) disagreed with the LLVM oracle or failed:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}

#[test]
fn signature_placement_families_agree_aarch64() {
    run_lane(
        Lane {
            target: host_target_support::AARCH64_TARGET,
            x86: false,
        },
        "aarch64",
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn signature_placement_families_agree_x86_64() {
    run_lane(
        Lane {
            target: x86_rosetta_support::X86_TARGET,
            x86: true,
        },
        "x86_64",
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// The Rosetta route's own guard: its `core` is built from the compiler's own
/// commit, by the build compiler (an rlib from another compiler is refused by
/// rustc as E0514, so a program linking it would not even build), and a
/// `#![no_std]` program linked against it runs under the route with the exit
/// code it computes.
#[test]
fn x86_rosetta_core_is_built_from_the_compiler_commit() {
    let exec = x86_rosetta_support::x86_execution("0");
    let X86Exec::Rosetta { core_dir } = &exec else {
        panic!("an Apple-silicon host executes x86-64 through Rosetta, got {exec:?}");
    };
    let core_dir = core_dir.clone();
    for rlib in ["libcore.rlib", "libcompiler_builtins.rlib"] {
        assert!(
            x86_rosetta_support::rlib_is_from_build_compiler(&core_dir.join(rlib)),
            "{rlib} at {core_dir:?} does not embed the build compiler's version {:?}",
            x86_rosetta_support::embedded_compiler_version()
        );
    }
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("x86_rosetta_selftest");
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create dir");
    let src = dir.join("main.rs");
    std::fs::write(
        &src,
        x86_rosetta_support::no_std_caller("fn main() { exit(black_box(40u64) + 2) }"),
    )
    .expect("write");
    let bin = dir.join("main");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(exec.compile_args())
        .args([
            "-Cpanic=abort",
            "-Copt-level=0",
            "--crate-type",
            "bin",
            "-o",
        ])
        .arg(&bin)
        .arg(&src);
    let out = cmd.output().expect("spawn rustc");
    assert!(
        out.status.success(),
        "a no_std x86-64 program did not build against the route's core:\n{}",
        String::from_utf8_lossy(&out.stderr)
    );
    let run = exec.run(&bin).expect("an execution route");
    assert_eq!(
        run.status.code(),
        Some(42),
        "the x86-64 program's exit code"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::None,
    );
}
