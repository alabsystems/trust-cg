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

// Integration test: rustc's `PassMode::Indirect { on_stack: false }` ARGUMENT on
// x86-64 — ONE POINTER to a copy the caller makes — checked ACROSS the backend
// boundary in all four rlib x bin combinations at every optimization level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc's Rust ABI passes every sized `BackendRepr::Memory` argument larger than
// a pointer as `PassMode::Indirect { on_stack: false }`: the caller copies the
// value and passes its ADDRESS in the next integer register (or an 8-byte stack
// slot). The bridge used to pass the bytes — System V register lanes up to 16
// bytes, a `byval` stack copy above — and nothing refused it: the argument gate
// compared only register placements. Measured 2026-09-27 on x86-64 Darwin
// (`struct T12 { u32, u32, u32 }`, O0/O2): LLVM rlib + bridge bin SIGSEGV (139
// against 237), bridge rlib + LLVM bin silently 197 / 71, and every same-backend
// cell agreed — a whole-program differential cannot see this class. The
// indirect argument lane (`indirect_arg_param_plan`) now declares the pointer,
// copies the pointee into the callee's slot at entry, and passes a fresh copy at
// every call site.
//
// Rows: the `Memory` shapes (`{u32; 3}` struct, `[u32; 3]`, `[u8; 16]`, 24- and
// 40-byte structs, a non-`ScalarPair` float struct between two `f64`s, a
// `Memory` enum in all three variants, `Option<T12>`, a struct with a slice
// field); register exhaustion (the pointer on the stack after six integers; in
// R9 with a scalar after it; beside a `PassMode::Pair` slice in both orders);
// an sret return beside an indirect argument (the hidden RDI first) and a
// generic identity that is both; a callee that writes its by-value parameter
// while the caller reads its own copy afterwards (a `Copy` operand) or never
// again (a moved non-`Copy` operand); recursion; a fn pointer and a `static` fn
// pointer; a const operand and a `*p` operand; a closure body defined in the
// rlib; a generic method call; a `dyn` method called from the other backend in
// both directions (the virtual lane's `param_tys`); generics instantiated in
// the rlib (shared at O0); a `#[track_caller]` callee (its hidden `&Location`
// comes AFTER the pointer); and three controls the lane must leave alone:
// `core::fmt::write` (non-generic, compiled into the LLVM sysroot; its 16-byte
// `fmt::Arguments` is a `PassMode::Pair` on this toolchain), an 8-byte `Memory`
// struct (`PassMode::Cast`, one register) and an `extern "C"` 24-byte struct
// (`on_stack: true`, a `byval` copy).
//
// W1 rows — THE SCALAR SUB-LANE. An over-aligned single-scalar newtype
// (`#[repr(C, align(16))] struct A16 { a: u64 }`, `#[repr(align(128))] struct
// CP(u64)` — the `CachePadded` shape — `#[repr(align(16))] struct A8(u8)`, a
// padded `f64`) is ONE scalar to the bridge's type mapper but a padded `Memory`
// value to rustc, which passes it `Indirect` too. Measured before (2026-09-28,
// `al(k, A16, j)`, oracle 67): LLVM rlib + bridge bin SIGSEGV at O0-O3, bridge
// rlib + LLVM bin 174 / 141 / 114 — the bridge used the pointer register as the
// value. The rows cover the direct call, the pointer on the stack at register
// exhaustion, a fn pointer, a `dyn` method in both directions, and a padded
// POINTER (`#[repr(C, align(16))] struct AP { p: *const u64 }`, `#[repr(align(16))]
// struct AR(&'static u64)`), which is one `Ptr` to the bridge and rides the same
// sub-lane. The `w1_*_home_*` rows check that every bridge-built stack HOME of
// such a newtype (the temporary behind `&a` passed to a call, a raw-borrowed
// local's cell, a `&dyn` data pointer) has rustc's alignment and extent: a
// misalignment flag, and an LLVM `-O2` `copy16` whose `movaps` loads the 16
// promised bytes (measured before, 2026-09-28: flags in the bridge cells, and
// a SIGSEGV for the LLVM callee on a bridge local at O2). The newtypes are
// never passed through `black_box` whole:
// `black_box::<A16>` RETURNS one, and a padded scalar RETURN is refused by name
// (`[TCG-RET-ABI]`, a control below), not lowered.
//
// W2 rows — `rust-call` shims in a vtable the BRIDGE emits, called by the other
// backend with rustc's untupled arguments: a `&dyn Fn(u64)` / `&dyn Fn(u64,
// u64)` over a fn item (`FnPtrShim`) and over a closure (whose `Fn::call` slot
// is its untupled body, and whose `FnOnce::call_once` slot is a `VTableShim`).
// Every `extern "rust-call"` shim and method is declared UNTUPLED, as rustc's
// `FnAbi` lists it (`rust_call_spread`), so the slots' parameter lists are
// rustc's. Each slot's declaration is still judged per signature
// (`check_signature_placement`); a vtable holding a closure whose argument or
// by-value environment the bridge cannot place as rustc does is refused by
// name, not admitted wholesale. A closure environment that is ONE `f32` /
// `f64` crosses in a floating-point register (a one-lane float slot,
// `closure_slot_ty`): the family matrix's `env_f*` / `fn_env_f*` / `dyn_env_f*`
// / `fnmut_env_f64` rows, both targets.
//
// `refused_by_name_controls` pins the shapes that are REFUSED rather than
// lowered, each against its LLVM x LLVM oracle so the program itself is valid:
// the padded scalar return (`-> CP`), a padded `f32` rustc casts to an INTEGER
// register, a padded POINTER returned by value (`-> AP` / `-> AR`, before a bus
// error / 0 against 30) and a pointer-carrier union by value (`union UP { p:
// *const u64 }`, before SIGSEGV / 112 against 40 as an argument and a bus error
// / 3 against 33 as a return). It also holds, as controls that must now COMPILE
// and agree in every cell, the shapes the bridge refused by name until it
// declared `rust-call` callables untupled (F2, round 10): a bridge-emitted `dyn
// Fn*` vtable holding a shim whose TUPLED declaration placed differently from
// rustc's untupled arguments (`Fn(T12)` over a fn item or a closure: a pointer;
// `Fn(u64, u64, u64)`: three registers against a 24-byte stack copy — measured
// before as 176 against 151 and 218 against 195); a padded pointer inside a
// `dyn Fn*` call (before SIGSEGV against 41); a `rust-call` fn ITEM reached BY
// SYMBOL — `<&fn-item as Fn<(u64, u64, u64)>>::call` exported under
// `-Zshare-generics` and linked by the other crate's own generic caller (before
// 220 / 190 against 231); a non-generic exported `extern "rust-call"` fn
// (before SIGSEGV / 0 against 117); and a `FnOnce` closure body whose 8-byte
// by-value environment rustc passes in a register (before 209 / SIGSEGV against
// 57; F-env).
//
// Runs natively on an x86-64 or AArch64 Linux or macOS host (the host's own
// target, below) and, on an aarch64-apple-darwin host, ALSO for x86-64 under
// Rosetta (`support/x86_rosetta.rs`: the same callee, shapes and controls as
// `#![no_std]` programs against a `core` built from the compiler's own library
// source). A run qualifies only the lane it ran on, and a Rosetta run
// qualifies Rosetta's execution of the x86-64 code, not a native x86-64
// machine. `tests/tools/m145_xback.py` drives the same callee, shapes and
// controls (extracted from this file) with a given `trustc` and dylib.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

use x86_rosetta_support::XbackLane;

/// The lane's target on THIS host: the matrix runs natively, so an x86-64 host
/// measures x86-64 and an AArch64 host measures AArch64 (the file name keeps
/// its historical `x86`; the lane has covered both since 2026-09-28). A run on
/// one host qualifies only that host's target.
const TARGET: &str = if cfg!(target_arch = "aarch64") {
    host_target_support::AARCH64_TARGET
} else {
    host_target_support::X86_64_TARGET
};

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn lane_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn host_runs_lane_target() -> bool {
    cfg!(any(target_arch = "x86_64", target_arch = "aarch64"))
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m145_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// The bridge's knob argument for this host's target. On AArch64 the
/// per-compile proof certificates refuse every program with `[TCG-PROOF-465]`
/// (the AArch64 opcode inventory has no checker-accepted certificate for the
/// pair opcodes yet — unrelated to argument placement), so the AArch64 run
/// turns them off exactly as `tests/tools/m145_xback.py` does on every host;
/// the x86-64 run keeps them on, as it was measured.
fn backend_knobs() -> Option<String> {
    cfg!(target_arch = "aarch64").then(|| toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
}

/// One lane of this file's matrix.
#[derive(Clone)]
enum Lane {
    /// The host's own target (`TARGET`), natively, the programs as written.
    Host,
    /// x86-64 on an Apple-silicon host, under Rosetta (`XbackLane::Rosetta`).
    /// Its compiles turn the proof certificates off, as the AArch64 lane's do:
    /// with them on, every trust-cg x86-64 object is refused `[TCG-PROOF-465]`
    /// on this host (proof promotion finds the emitted x86-64 opcode inventory
    /// uncovered; measured 2026-09-30), which says nothing about argument
    /// placement.
    X86(XbackLane),
}

impl Lane {
    /// The lanes this host runs: its own target, and on an aarch64-apple-darwin
    /// host x86-64 as well (a missing Rosetta route there is a failure).
    fn all() -> Vec<Lane> {
        let mut lanes = vec![Lane::Host];
        if cfg!(all(target_os = "macos", target_arch = "aarch64")) {
            let x86 = XbackLane::for_host(host_target_support::X86_64_TARGET)
                .unwrap_or_else(|why| panic!("the x86-64 lane on Apple silicon: {why}"));
            lanes.push(Lane::X86(x86));
        }
        lanes
    }

    fn label(&self) -> &'static str {
        match self {
            Lane::Host => TARGET,
            Lane::X86(x86) => x86.label(),
        }
    }

    /// A short tag for artifact paths, so the lanes never share one.
    fn tag(&self) -> &'static str {
        match self {
            Lane::Host => "host",
            Lane::X86(_) => "x86",
        }
    }

    fn target_args(&self, opt: &str) -> Vec<OsString> {
        match self {
            Lane::Host => vec!["--target".into(), TARGET.into()],
            Lane::X86(x86) => x86.compile_args(opt),
        }
    }

    fn knobs(&self) -> Option<String> {
        match self {
            Lane::Host => backend_knobs(),
            Lane::X86(_) => Some(toolchain_support::backend_knobs_arg(&["no-proof-certs"])),
        }
    }

    fn callee_source(&self, src: &str) -> String {
        match self {
            Lane::Host => src.to_owned(),
            Lane::X86(x86) => x86.callee_source(src),
        }
    }

    fn caller_source(&self, program: &str) -> String {
        match self {
            Lane::Host => program.to_owned(),
            Lane::X86(x86) => x86.caller_source(program),
        }
    }

    /// A control's bin, written against `std` with `std::process::exit(code)`.
    fn control_bin_source(&self, program: &str) -> String {
        match self {
            Lane::Host => program.to_owned(),
            Lane::X86(_) => no_std_control_bin(program),
        }
    }

    fn run(&self, bin: &Path, opt: &str) -> i32 {
        match self {
            Lane::Host => {
                let out = Command::new(bin).output().expect("run binary");
                out.status
                    .code()
                    .unwrap_or_else(|| panic!("{bin:?} exited via signal: {:?}", out.status))
            }
            Lane::X86(x86) => x86
                .run(bin, opt)
                .unwrap_or_else(|why| panic!("{} {bin:?}: {why}", x86.label())),
        }
    }
}

/// This test's positive-evidence marker: every lane it ran checked its cells.
/// Proofs-off on an AArch64 host, where both lanes compile with
/// `no-proof-certs` (`backend_knobs`, `Lane::knobs`); a native x86-64 host
/// runs only its own lane, with the certificates on.
fn record_evidence() {
    let proofs_off = cfg!(target_arch = "aarch64");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        if proofs_off {
            positive_evidence::Certs::Off
        } else {
            positive_evidence::Certs::On
        },
    );
}

/// A control bin (`std::process::exit(code)` directly, `std::` paths) as a
/// `#![no_std]` program for the x86-64 Rosetta lane.
fn no_std_control_bin(program: &str) -> String {
    let body = program
        .replace("std::process::exit(", "exit_code(")
        .replace("std::", "core::");
    let whole = x86_rosetta_support::no_std_caller(&format!(
        "fn exit_code(code: i32) -> ! {{ exit(code as u64) }}\n{body}"
    ));
    // Every inner attribute (the prelude's, and a control's own
    // `#![feature(..)]`) above every item.
    let (inner, items): (Vec<&str>, Vec<&str>) = whole
        .lines()
        .partition(|line| line.trim_start().starts_with("#!["));
    format!("{}\n{}\n", inner.join("\n"), items.join("\n"))
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Backend {
    Llvm,
    TrustCg,
}

impl Backend {
    fn tag(self) -> &'static str {
        match self {
            Backend::Llvm => "llvm",
            Backend::TrustCg => "tcg",
        }
    }
}

/// One callee rlib named `krate` compiled by `backend` at `opt`.
fn compile_callee_rlib(
    lane: &Lane,
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    krate: &str,
    src: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{krate}.rs"));
    std::fs::write(&src_path, lane.callee_source(src)).expect("write callee source");
    let out_dir = dir.join(format!("{krate}_{}_O{opt}", backend.tag()));
    std::fs::create_dir_all(&out_dir).expect("create callee out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", krate]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.args(lane.knobs());
    }
    cmd.args(lane.target_args(opt))
        .args([
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("--out-dir")
        .arg(&out_dir)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc for the callee rlib");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    let rlib = out_dir.join(format!("lib{krate}.rlib"));
    if !rlib.is_file() {
        return Err(format!("no rlib produced at {rlib:?}"));
    }
    Ok(rlib)
}

/// One caller bin for `shape`, compiled by `backend` at `opt` against `rlib`.
fn compile_caller_bin(
    lane: &Lane,
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    shape: &str,
    body: &str,
    rlib: &Path,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("caller_{shape}.rs"));
    std::fs::write(
        &src_path,
        lane.caller_source(&format!("{CALLER_HDR}{body}")),
    )
    .expect("write caller source");
    let bin = dir.join(format!(
        "caller_{shape}_{}rlib_{}bin_O{opt}",
        rlib_backend_tag(rlib),
        backend.tag()
    ));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.args(lane.knobs());
    }
    let krate = rlib
        .file_stem()
        .and_then(|s| s.to_str())
        .and_then(|s| s.strip_prefix("lib"))
        .expect("rlib file name");
    let mut extern_arg = OsString::from(format!("{krate}="));
    extern_arg.push(rlib);
    cmd.args(lane.target_args(opt))
        .args([
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg("--extern")
        .arg(&extern_arg)
        .arg("-L")
        .arg(rlib.parent().expect("rlib directory"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc for the caller bin");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

fn rlib_backend_tag(rlib: &Path) -> &'static str {
    let dir = rlib
        .parent()
        .and_then(|d| d.file_name())
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    if dir.contains("_tcg_") { "tcg" } else { "llvm" }
}

/// The callee crate: one `#[inline(never)]` function per shape taking the
/// `Memory` value BY VALUE and folding its fields asymmetrically into a scalar,
/// so a truncated, shifted or garbage field is a different exit code. The caller
/// passes every input through `black_box`, so nothing constant-folds across the
/// boundary.
const CALLEE_SRC: &str = r#"
#[derive(Clone, Copy)] pub struct T12 { pub a: u32, pub b: u32, pub c: u32 }
#[derive(Clone, Copy)] pub struct S24 { pub a: u64, pub b: u64, pub c: u64 }
#[derive(Clone, Copy)] pub struct S40 { pub a: u64, pub b: u32, pub c: u64, pub d: u16, pub e: u64 }
#[derive(Clone, Copy)] pub struct F3 { pub x: f32, pub y: f64, pub z: f32 }
#[derive(Clone, Copy)] pub enum E { A(u64, u64, u64), B(u32), C }
pub struct N12 { pub a: u32, pub b: u32, pub c: u32 }
#[derive(Clone, Copy)] pub struct Small { pub a: u8, pub b: u8, pub c: u16, pub d: u32 }
#[derive(Clone, Copy)] #[repr(C)] pub struct C24 { pub a: u64, pub b: u64, pub c: u64 }
#[inline(never)] pub fn t12(t: T12) -> u64 { t.a as u64 * 3 + t.b as u64 * 5 + t.c as u64 * 7 }
#[inline(never)] pub fn arr3(t: [u32; 3], k: u64) -> u64 { t[0] as u64 * 3 + t[1] as u64 * 5 + t[2] as u64 * 7 + k * 11 }
#[inline(never)] pub fn b16(b: [u8; 16]) -> u64 { b[0] as u64 + b[7] as u64 * 3 + b[15] as u64 * 5 }
#[inline(never)] pub fn s24(s: S24) -> u64 { s.a * 3 + s.b * 5 + s.c * 7 }
#[inline(never)] pub fn s40(s: S40) -> u64 { s.a * 3 + s.b as u64 * 5 + s.c * 7 + s.d as u64 * 11 + s.e * 13 }
#[inline(never)] pub fn f3(p: f64, f: F3, q: f64) -> u64 { (p * 7.0 + f.x as f64 * 2.0 + f.y * 3.0 + f.z as f64 * 5.0 + q * 11.0) as u64 }
#[inline(never)] pub fn en(e: E) -> u64 { match e { E::A(a, b, c) => a * 3 + b * 5 + c * 7, E::B(x) => x as u64 * 11 + 1, E::C => 2 } }
#[inline(never)] pub fn exh6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, t: T12) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + t.a as u64 * 7 + t.b as u64 * 11 + t.c as u64 * 13 }
#[inline(never)] pub fn exh5(a: u64, b: u64, c: u64, d: u64, e: u64, t: T12, g: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + t.a as u64 * 7 + t.b as u64 * 11 + t.c as u64 * 13 + g * 17 }
#[inline(never)] pub fn sret_ind(k: u64, t: T12) -> S24 { S24 { a: k + t.a as u64, b: t.b as u64 * 2, c: t.c as u64 * 3 } }
#[inline(never)] pub fn mutate(mut t: T12) -> u64 { t.a += 100; t.b *= 3; t.c = t.a + t.b; t.c as u64 }
#[inline(never)] pub fn mutate_n(mut n: N12) -> u64 { n.a += 1; n.b += n.a; n.c += n.b; n.c as u64 }
#[inline(never)] pub fn rec(t: S24, n: u64) -> u64 { if n == 0 { t.a + t.b * 2 + t.c * 3 } else { rec(S24 { a: t.b, b: t.c, c: t.a + n }, n - 1) } }
pub static FP: fn(T12) -> u64 = t12;
pub fn mk_closure(k: u64) -> impl Fn(T12) -> u64 { move |t: T12| t.a as u64 * k + t.b as u64 * 3 + t.c as u64 }
pub trait Sum12 { fn sum12(&self, t: T12) -> u64; }
pub struct K(pub u64);
impl Sum12 for K { #[inline(never)] fn sum12(&self, t: T12) -> u64 { self.0 * 10 + t.a as u64 + t.b as u64 * 2 + t.c as u64 * 3 } }
#[inline(never)] pub fn via_dyn(s: &dyn Sum12, t: T12) -> u64 { s.sum12(t) }
#[inline(never)] pub fn via_gen<S: Sum12>(s: &S, t: T12) -> u64 { s.sum12(t) }
pub fn gen_arr<T: Copy + Into<u64>>(a: [T; 3]) -> u64 { a[0].into() * 3 + a[1].into() * 5 + a[2].into() * 7 }
#[inline(never)] pub fn gen_arr_user(x: u32) -> u64 { gen_arr([x, x + 1, x + 2]) }
#[inline(never)] pub fn small(s: Small) -> u64 { s.a as u64 + s.b as u64 * 3 + s.c as u64 * 5 + s.d as u64 * 7 }
#[inline(never)] pub extern "C" fn c24(s: C24) -> u64 { s.a * 3 + s.b * 5 + s.c * 7 }
#[track_caller] #[inline(never)] pub fn tc(t: T12, k: u64) -> u64 { t.a as u64 * 3 + t.c as u64 + k * 5 }
#[inline(never)] pub fn mix_ptr_then_pair(a: u64, b: u64, c: u64, d: u64, t: T12, s: &[u8]) -> u64 { a + b * 2 + c * 3 + d * 4 + t.a as u64 * 7 + t.b as u64 * 11 + t.c as u64 * 13 + s.len() as u64 * 17 + s[0] as u64 }
#[inline(never)] pub fn mix_pair_then_ptr(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8], t: T12) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + s.len() as u64 * 17 + s[0] as u64 + t.a as u64 * 7 + t.b as u64 * 11 + t.c as u64 * 13 }
#[inline(never)] pub fn opt12(o: Option<T12>) -> u64 { match o { Some(t) => t.a as u64 * 3 + t.b as u64 * 5 + t.c as u64 * 7, None => 9 } }
pub struct H<'a> { pub s: &'a [u8], pub k: u64 }
#[inline(never)] pub fn hs(h: H<'_>) -> u64 { h.s.len() as u64 * 10 + h.s[1] as u64 + h.k * 3 }
#[inline(never)] pub fn id<T>(t: T) -> T { t }
#[inline(never)] pub fn id_user(t: T12) -> T12 { id(t) }
#[derive(Clone, Copy)] #[repr(C, align(16))] pub struct A16 { pub a: u64 }
#[derive(Clone, Copy)] #[repr(align(128))] pub struct CP(pub u64);
#[derive(Clone, Copy)] #[repr(align(16))] pub struct A8(pub u8);
#[derive(Clone, Copy)] #[repr(align(16))] pub struct PF(pub f64);
#[inline(never)] pub fn al(k: u64, a: A16, j: u64) -> u64 { k + a.a * 3 + j * 7 }
#[inline(never)] pub fn cp(k: u64, c: CP, a: A8, j: u64) -> u64 { k + c.0 * 3 + a.0 as u64 * 5 + j * 7 }
#[inline(never)] pub fn pf(x: f64, p: PF, y: f64) -> u64 { (x * 3.0 + p.0 * 5.0 + y * 7.0) as u64 }
#[inline(never)] pub fn al_exh(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, x: A16, g: u64) -> u64 { a + b * 2 + c * 3 + d * 4 + e * 5 + f * 6 + x.a * 7 + g * 11 }
pub trait TakeA16 { fn take(&self, a: A16) -> u64; }
impl TakeA16 for K { #[inline(never)] fn take(&self, a: A16) -> u64 { self.0 * 10 + a.a * 3 } }
#[inline(never)] pub fn via_dyn_a16(s: &dyn TakeA16, a: A16) -> u64 { s.take(a) }
#[derive(Clone, Copy)] #[repr(C, align(16))] pub struct AP { pub p: *const u64 }
#[derive(Clone, Copy)] #[repr(align(16))] pub struct AR(pub &'static u64);
#[inline(never)] pub fn rd_ap(a: AP) -> u64 { unsafe { *a.p } }
#[inline(never)] pub fn rd_ar(k: u64, a: AR) -> u64 { k + *a.0 * 3 }
#[inline(never)] pub fn call_dyn1(f: &dyn Fn(u64) -> u64) -> u64 { f(9) }
#[inline(never)] pub fn call_dyn2(f: &dyn Fn(u64, u64) -> u64) -> u64 { f(3, 40) }
#[inline(never)] pub fn mis16(r: &A16) -> u64 { (r as *const A16 as usize % 16 != 0) as u64 }
#[inline(never)] pub fn mis_cp(r: &CP) -> u64 { (r as *const CP as usize % 128 != 0) as u64 }
#[inline(never)] pub fn mis_by_val(x: A16) -> u64 { mis16(&x) }
pub trait Addr16 { fn mis(&self) -> u64; }
impl Addr16 for A16 { #[inline(never)] fn mis(&self) -> u64 { mis16(self) } }
#[inline(never)] pub fn via_dyn_addr(d: &dyn Addr16) -> u64 { d.mis() }
#[inline(never)] pub fn copy16(r: &A16) -> u64 { let mut v = [A16 { a: 0 }; 2]; v[1] = *r; std::hint::black_box(&mut v); v[1].a }
#[derive(Clone, Copy)] #[repr(C)] pub enum TagC { V(i64) }
#[derive(Clone, Copy)] #[repr(u8)] pub enum TagU8 { V(i64) }
#[inline(never)] pub fn tc_read(v: &TagC) -> u64 { match *v { TagC::V(x) => x as u64 } }
#[inline(never)] pub fn tc_make(x: i64) -> TagC { TagC::V(x) }
#[inline(never)] pub fn tc_take(v: TagC) -> u64 { match v { TagC::V(x) => x as u64 * 3 } }
#[inline(never)] pub fn tu_read(v: &TagU8) -> u64 { match *v { TagU8::V(x) => x as u64 } }
#[inline(never)] pub fn tu_make(x: i64) -> TagU8 { TagU8::V(x) }
#[derive(Clone, Copy)] pub struct ZstLead(pub (), pub u64);
#[inline(never)] pub fn zl_make(x: u64) -> ZstLead { ZstLead((), x) }
#[inline(never)] pub fn zl_read(v: &ZstLead) -> u64 { v.1 }
#[inline(never)] pub fn zl_bump(mut v: ZstLead) -> u64 { v.1 += 5; v.1 * 2 }
#[derive(Clone, Copy)] pub enum Reord { V(u8, i64) }
#[inline(never)] pub fn rd_read(v: &Reord) -> u64 { match *v { Reord::V(a, b) => (a as u64).wrapping_mul(1_000_003).wrapping_add(b as u64) } }
#[inline(never)] pub fn rd_make(a: u8, b: i64) -> Reord { Reord::V(a, b) }
#[derive(Clone, Copy)] pub struct RS { pub a: u8, pub b: i64, pub c: u16 }
#[inline(never)] pub fn rs_read(v: &RS) -> u64 { v.a as u64 * 3 + v.b as u64 * 5 + v.c as u64 * 7 }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    use callee::*;\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n\
    fn t() -> T12 { black_box(T12 { a: 1, b: 2, c: 3 }) }\n";

/// `(shape, caller body, expected exit code)`. The expected code is the
/// oracle's (LLVM callee + LLVM caller), checked by hand, and is asserted so a
/// corrupted oracle cannot make every combination agree on a wrong value.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        ("t12", r#"fn main() { exit(t12(t())) }"#, 34),
        (
            "arr3",
            r#"fn main() { exit(arr3(black_box([4, 5, 6]), black_box(2))) }"#,
            101,
        ),
        (
            "b16",
            r#"fn main() { let mut b = [0u8; 16]; b[0] = black_box(9); b[7] = black_box(4); b[15] = black_box(2); exit(b16(black_box(b))) }"#,
            31,
        ),
        (
            "s24",
            r#"fn main() { exit(s24(black_box(S24 { a: 1, b: 2, c: 3 }))) }"#,
            34,
        ),
        (
            "s40",
            r#"fn main() { exit(s40(black_box(S40 { a: 1, b: 2, c: 3, d: 4, e: 5 }))) }"#,
            143,
        ),
        (
            "f3",
            r#"fn main() { exit(f3(black_box(1.0), black_box(F3 { x: 1.5, y: 2.0, z: 0.5 }), black_box(2.0))) }"#,
            40,
        ),
        (
            "enum3",
            r#"fn main() { exit(en(black_box(E::A(1, 2, 3))) + en(black_box(E::B(4))) * 2 + en(black_box(E::C)) * 3) }"#,
            130,
        ),
        (
            "exh6",
            r#"fn main() { exit(exh6(black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), t())) }"#,
            89,
        ),
        (
            "exh5",
            r#"fn main() { exit(exh5(black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), t(), black_box(2))) }"#,
            117,
        ),
        (
            "sret_ind",
            r#"fn main() { let s = sret_ind(black_box(5), t()); exit(s.a + s.b * 10 + s.c * 100) }"#,
            193,
        ),
        (
            "mutate_copy",
            r#"fn main() { let v = t(); let m = mutate(v); exit(m + v.a as u64 * 1000 + v.b as u64 * 100 + v.c as u64) }"#,
            55,
        ),
        (
            "mutate_move",
            r#"fn main() { let n = N12 { a: black_box(1), b: black_box(2), c: black_box(3) }; exit(mutate_n(n) * 10) }"#,
            70,
        ),
        (
            "rec",
            r#"fn main() { exit(rec(black_box(S24 { a: 1, b: 2, c: 3 }), black_box(4))) }"#,
            33,
        ),
        (
            "fnptr",
            r#"fn main() { let f: fn(T12) -> u64 = black_box(t12); exit(f(t()) + FP(t()) * 2) }"#,
            102,
        ),
        (
            "const_arg",
            r#"fn main() { exit(t12(T12 { a: 2, b: 2, c: 2 })) }"#,
            30,
        ),
        (
            "deref_arg",
            r#"fn main() { let v = t(); let r: &T12 = black_box(&v); exit(t12(*r)) }"#,
            34,
        ),
        (
            "closure_rlib",
            r#"fn main() { let f = mk_closure(black_box(7)); exit(f(t())) }"#,
            16,
        ),
        (
            "generic_method",
            r#"fn main() { exit(via_gen(&K(black_box(4)), t())) }"#,
            54,
        ),
        (
            "dyn_bin_to_rlib",
            r#"fn main() { let k = K(black_box(4)); let s: &dyn Sum12 = &k; exit(s.sum12(t()) + via_dyn(&k, t()) * 2) }"#,
            162,
        ),
        (
            "dyn_rlib_to_bin",
            r#"struct M(u64); impl Sum12 for M { fn sum12(&self, t: T12) -> u64 { self.0 + t.a as u64 * 5 + t.b as u64 * 7 + t.c as u64 * 9 } } fn main() { exit(via_dyn(&M(black_box(6)), t())) }"#,
            52,
        ),
        (
            "shared_generic",
            r#"fn main() { exit(gen_arr::<u32>(black_box([2, 3, 4])) + gen_arr_user(black_box(1)) * 2) }"#,
            117,
        ),
        (
            "small_control",
            r#"fn main() { exit(small(black_box(Small { a: 1, b: 2, c: 3, d: 4 }))) }"#,
            50,
        ),
        (
            "track_caller",
            r#"fn main() { exit(tc(t(), black_box(4))) }"#,
            26,
        ),
        (
            "core_fmt_write",
            r#"struct W { buf: [u8; 32], n: usize } impl std::fmt::Write for W { fn write_str(&mut self, s: &str) -> std::fmt::Result { for &b in s.as_bytes() { if self.n < 32 { self.buf[self.n] = b; self.n += 1; } } Ok(()) } } fn main() { let mut w = W { buf: [0; 32], n: 0 }; let r = core::fmt::write(&mut w, format_args!("{}-{}", black_box(42u32), black_box(7u8))); exit(w.n as u64 * 10 + (w.buf[0] - b'0') as u64 + if r.is_ok() { 100 } else { 0 }) }"#,
            144,
        ),
        (
            "mix_ptr_then_pair",
            r#"fn main() { exit(mix_ptr_then_pair(black_box(1), black_box(1), black_box(1), black_box(1), t(), black_box(&b"xyz"[..]))) }"#,
            249,
        ),
        (
            "mix_pair_then_ptr",
            r#"fn main() { exit(mix_pair_then_ptr(black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), black_box(&b"xyz"[..]), t())) }"#,
            3,
        ),
        (
            "option_t12",
            r#"fn main() { exit(opt12(black_box(Some(t()))) + opt12(black_box(None)) * 2) }"#,
            52,
        ),
        (
            "fat_leaf_struct",
            r#"fn main() { exit(hs(black_box(H { s: &b"abc"[..], k: black_box(5) }))) }"#,
            143,
        ),
        (
            "generic_id_sret",
            r#"fn main() { let r = id(t()); let u = id_user(t()); exit(r.a as u64 + r.b as u64 * 10 + r.c as u64 * 100 + u.c as u64) }"#,
            73,
        ),
        (
            "c24_control",
            r#"fn main() { exit(c24(black_box(C24 { a: 1, b: 2, c: 3 }))) }"#,
            34,
        ),
        (
            "w1_a16",
            r#"fn main() { exit(al(black_box(3), A16 { a: black_box(5) }, black_box(7))) }"#,
            67,
        ),
        (
            "w1_cachepadded_a8",
            r#"fn main() { exit(cp(black_box(1), CP(black_box(2)), A8(black_box(3)), black_box(4))) }"#,
            50,
        ),
        (
            "w1_padded_f64",
            r#"fn main() { exit(pf(black_box(1.0), PF(black_box(2.0)), black_box(3.0))) }"#,
            34,
        ),
        (
            "w1_a16_exhaustion",
            r#"fn main() { exit(al_exh(black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), A16 { a: black_box(2) }, black_box(3))) }"#,
            68,
        ),
        (
            "w1_a16_fnptr",
            r#"fn main() { let f: fn(u64, A16, u64) -> u64 = black_box(al); exit(f(black_box(3), A16 { a: black_box(5) }, black_box(7)) + al(black_box(1), A16 { a: 2 }, black_box(0))) }"#,
            74,
        ),
        (
            "w1_a16_dyn_bin_to_rlib",
            r#"fn main() { let k = K(black_box(4)); let s: &dyn TakeA16 = &k; exit(s.take(A16 { a: black_box(5) }) + via_dyn_a16(&k, A16 { a: black_box(6) }) * 2) }"#,
            171,
        ),
        (
            "w1_a16_dyn_rlib_to_bin",
            r#"struct M(u64); impl TakeA16 for M { fn take(&self, a: A16) -> u64 { self.0 + a.a * 7 } } fn main() { exit(via_dyn_a16(&M(black_box(6)), A16 { a: black_box(5) })) }"#,
            41,
        ),
        (
            "w1_padded_pointer_args",
            r#"static X: u64 = 40; static Y: u64 = 7; fn main() { let a = AP { p: black_box(&X as *const u64) }; let r = AR(black_box(&Y)); exit(rd_ap(a) + rd_ar(black_box(2), r)) }"#,
            63,
        ),
        // The HOME of an over-aligned scalar newtype: a `&A16` / `&CP` is promised
        // rustc's alignment and extent, so each bridge-built stack home — the
        // temporary behind `&a` passed to a call (in the bin, and in the rlib's
        // `mis_by_val` over its parameter), a raw-borrowed local's cell, a `&dyn`
        // data pointer — is `padded_scalar_home_extent`'s. Measured before
        // (2026-09-28): the homes were 8 mod 16 (a misalignment flag in the
        // bridge cells) and an LLVM `-O2` `copy16`, whose `movaps` loads the
        // promised 16 aligned bytes, SIGSEGV'd on a bridge local.
        (
            "w1_a16_home_ref",
            r#"fn main() { let a = A16 { a: black_box(5) }; exit(mis16(&a) + mis_by_val(a) * 2 + a.a * 4) }"#,
            20,
        ),
        (
            "w1_cp_home_ref",
            r#"fn main() { let c = CP(black_box(2)); exit(mis_cp(&c) + c.0 * 4) }"#,
            8,
        ),
        (
            "w1_a16_home_cell",
            r#"fn main() { let a = A16 { a: black_box(5) }; let p = &raw const a; exit(unsafe { mis16(&*p) + copy16(&*p) * 4 }) }"#,
            20,
        ),
        (
            "w1_a16_home_dyn",
            r#"fn main() { let a = A16 { a: black_box(5) }; exit(via_dyn_addr(&a) + a.a * 4) }"#,
            20,
        ),
        (
            "w1_a16_home_copy",
            r#"fn main() { let a = A16 { a: black_box(7) }; exit(copy16(&a) * 3) }"#,
            21,
        ),
        (
            "w2_fn_shim_u64",
            r#"fn item1(a: u64) -> u64 { a * 7 + 1 } fn main() { let it = black_box(item1); exit(call_dyn1(&it)) }"#,
            64,
        ),
        (
            "w2_fn_shim_u64x2",
            r#"fn item2(a: u64, b: u64) -> u64 { a * 5 + b } fn main() { let it = black_box(item2); exit(call_dyn2(&it)) }"#,
            55,
        ),
        (
            "w2_closure_u64",
            r#"fn main() { let k = black_box(3u64); exit(call_dyn1(&move |a: u64| a * k + 2)) }"#,
            29,
        ),
        (
            "w2_closure_u64x2",
            r#"fn main() { let k = black_box(3u64); exit(call_dyn2(&move |a: u64, b: u64| a * k + b)) }"#,
            49,
        ),
        // LAYOUT-IMAGE rows (2026-09-28): a single-variant enum whose repr keeps a
        // TAG, and a zero-sized field BEFORE a sized one. Neither is an indirect
        // argument; both are a representation the bridge must take from rustc's
        // layout, and both were wrong across this boundary (measured on AArch64
        // before the fix: `TagC` / `TagU8` built by the bridge and read by LLVM
        // answered 0 — the bridge typed the enum as its payload scalar and dropped
        // the tag — a bridge-built `tc_read(&TagC)` read the tag as the payload,
        // and `z.1 = v` on a `ZstLead` local was lost).
        (
            "tag_c_ref",
            r#"fn main() { exit(tc_read(&TagC::V(black_box(40)))) }"#,
            40,
        ),
        (
            "tag_c_ret_and_arg",
            r#"fn main() { let v = tc_make(black_box(41)); exit(tc_read(&v) + tc_take(v)) }"#,
            164,
        ),
        (
            "tag_u8",
            r#"fn main() { exit(tu_read(&tu_make(black_box(42))) + tu_read(&TagU8::V(black_box(7)))) }"#,
            49,
        ),
        (
            "zst_lead_write",
            r#"fn main() { let mut z = zl_make(black_box(8)); z.1 = black_box(43); exit(zl_read(&z) + zl_bump(z)) }"#,
            139,
        ),
        // rustc REORDERS a `repr(Rust)` aggregate by descending alignment, so a
        // field read through a reference must use rustc's offsets, not
        // declaration-order lanes (a control: it agreed before the fix too).
        (
            "reorder_ref",
            r#"fn main() { let r = Reord::V(black_box(9), black_box(40)); let s = RS { a: black_box(2), b: black_box(3), c: black_box(4) }; exit(rd_read(&r) + rd_read(&rd_make(black_box(1), black_box(2))) + rs_read(&s)) }"#,
            30,
        ),
    ]
}

/// A shape the bridge REFUSES by name instead of lowering, pinned against its
/// LLVM x LLVM oracle so the program itself is valid. `lib_refusal` /
/// `bin_refusal`: the substrings the bridge-compiled rlib / bin must fail with
/// (empty: it must compile, and every cell it takes part in must agree with the
/// oracle). A bridge bin is compiled against both rlibs. `refused_at`: the
/// optimization levels the refusals apply at; at any other level the control
/// must compile in every cell and agree with the oracle (a shape that crosses a
/// backend boundary only through `-Zshare-generics`, which is on by default at
/// `-Copt-level=0` and off at `2`).
struct Control {
    name: &'static str,
    lib: &'static str,
    bin: &'static str,
    oracle: i32,
    lib_refusal: &'static [&'static str],
    bin_refusal: &'static [&'static str],
    refused_at: &'static [&'static str],
}

/// The controls whose programs need `alloc` (a `Box`). The x86-64 Rosetta
/// lane links `#![no_std]` programs against `core` alone, so these run on the
/// host lane only; `refused_by_name_controls` holds the list to
/// the programs.
const NEEDS_ALLOC: &[&str] = &["w1_padded_pointer_dyn_fn"];

const CONTROLS: &[Control] = &[
    Control {
        name: "w1_padded_scalar_return",
        lib: r#"#[derive(Clone, Copy)] #[repr(align(128))] pub struct CP(pub u64);
#[inline(never)] pub fn mkcp(k: u64) -> CP { CP(k * 3 + 1) }"#,
        bin: r#"fn main() { let c = w::mkcp(std::hint::black_box(5)); std::process::exit((c.0 % 251) as i32) }"#,
        oracle: 16,
        lib_refusal: &["[TCG-RET-ABI]", "CP"],
        bin_refusal: &["[TCG-RET-ABI]", "CP"],
        refused_at: &["0", "2"],
    },
    Control {
        name: "w1_padded_f32_cast",
        lib: r#"#[derive(Clone, Copy)] #[repr(align(8))] pub struct F8(pub f32);
#[inline(never)] pub fn f8(k: u64, x: F8) -> u64 { k + (x.0 * 4.0) as u64 }"#,
        bin: r#"fn main() { std::process::exit(w::f8(std::hint::black_box(3), w::F8(std::hint::black_box(2.5))) as i32) }"#,
        oracle: 13,
        lib_refusal: &["[TCG-ARG-ABI]", "F8"],
        bin_refusal: &["[TCG-ARG-ABI]", "F8"],
        refused_at: &["0", "2"],
    },
    Control {
        name: "w2_fn_shim_t12",
        lib: r#"#[derive(Clone, Copy)] pub struct T12 { pub a: u32, pub b: u32, pub c: u32 }
#[inline(never)] pub fn call_dyn_r(f: &dyn Fn(T12) -> u64, t: &T12) -> u64 { f(*t) }"#,
        bin: r#"use w::T12; fn item(t: T12) -> u64 { t.a as u64 * 3 + t.b as u64 * 5 + t.c as u64 * 7 } fn main() { let t = std::hint::black_box(T12 { a: 5, b: 9, c: 13 }); let it = std::hint::black_box(item); std::process::exit((w::call_dyn_r(&it, &t) % 251) as i32) }"#,
        oracle: 151,
        // Before F2: the rlib refused "Fn-trait tuple element 0 `T12` needs a
        // byte-backed tuple" (its `(T12,)` tuple was register-held), the bin
        // refused its vtable (the tupled `FnPtrShim`).
        lib_refusal: &[],
        bin_refusal: &[],
        refused_at: &[],
    },
    Control {
        name: "w2_fn_shim_u64x3",
        lib: r#"#[inline(never)] pub fn call_dyn3(f: &dyn Fn(u64, u64, u64) -> u64) -> u64 { f(1, 20, 300) }"#,
        bin: r#"fn item3(a: u64, b: u64, c: u64) -> u64 { a * 3 + b * 5 + c * 7 } fn main() { let it = std::hint::black_box(item3); std::process::exit((w::call_dyn3(&it) % 251) as i32) }"#,
        oracle: 195,
        // Before F2: the bin refused its vtable (the tupled `FnPtrShim`).
        lib_refusal: &[],
        bin_refusal: &[],
        refused_at: &[],
    },
    // A closure's `Fn::call` slot is its body, and every `dyn Fn*` vtable also
    // carries `FnOnce::call_once` as a by-value `VTableShim` (`Box<dyn Fn(T12)>`
    // passed to a `FnOnce` consumer calls it); both are declared untupled. The
    // rlib's own `dyn Fn(T12)` call builds its `Indirect` element (a pointer to
    // a copy) from the argument tuple, which is memory-backed because it
    // carries a by-value aggregate (rule (3c) of `compute_memory_backed_locals`).
    // Before F2 the vtable was refused as a whole (the tupled `VTableShim`), and
    // the rlib's call "needs a byte-backed tuple".
    Control {
        name: "w2_closure_t12_vtable",
        lib: r#"#[derive(Clone, Copy)] pub struct T12 { pub a: u32, pub b: u32, pub c: u32 }
#[inline(never)] pub fn call_dyn_t12(f: &dyn Fn(T12) -> u64, t: T12) -> u64 { f(t) }"#,
        bin: r#"use w::T12; fn main() { let k = std::hint::black_box(4u64); let c = move |x: T12| x.a as u64 * k + x.b as u64 + x.c as u64 * 2; let t = std::hint::black_box(T12 { a: 1, b: 2, c: 3 }); std::process::exit(w::call_dyn_t12(&c, t) as i32) }"#,
        oracle: 12,
        lib_refusal: &[],
        bin_refusal: &[],
        refused_at: &[],
    },
    // A padded scalar newtype over a POINTER returned by value: rustc returns it
    // through the hidden buffer, like any padded scalar (measured before: the
    // bridge returned the pointer in RAX — bus error / 0 against 30).
    Control {
        name: "w1_padded_pointer_return",
        lib: r#"#[derive(Clone, Copy)] #[repr(C, align(16))] pub struct AP { pub p: *const u64 }
#[derive(Clone, Copy)] #[repr(align(16))] pub struct AR(pub &'static u64);
#[inline(never)] pub fn mk_ap(p: *const u64) -> AP { AP { p } }
#[inline(never)] pub fn mk_ar(p: &'static u64) -> AR { AR(p) }"#,
        bin: r#"use std::hint::black_box as bb; static X: u64 = 40; static Y: u64 = 7; fn main() { let a = w::mk_ap(bb(&X as *const u64)); let r = w::mk_ar(bb(&Y)); std::process::exit((a.p == &X as *const u64) as i32 * 10 + (r.0 as *const u64 == &Y as *const u64) as i32 * 20) }"#,
        oracle: 30,
        lib_refusal: &["[TCG-RET-ABI]", "by-value return"],
        bin_refusal: &["[TCG-RET-ABI]", "by-value return"],
        refused_at: &["0", "2"],
    },
    // A pointer-carrier union is one `Ptr` to the bridge and a padded `Memory`
    // value to rustc: `Indirect` as an argument (measured before: SIGSEGV / 112
    // against 40) and the hidden buffer as a return (bus error / 3 against 33).
    Control {
        name: "w1_pointer_union_arg",
        lib: r#"#[derive(Clone, Copy)] #[repr(C, align(16))] pub union UP { pub p: *const u64 }
#[inline(never)] pub fn rd_up(u: UP) -> u64 { unsafe { *u.p } }"#,
        bin: r#"static X: u64 = 40; fn main() { let u = w::UP { p: std::hint::black_box(&X as *const u64) }; std::process::exit((w::rd_up(u) % 251) as i32) }"#,
        oracle: 40,
        lib_refusal: &["[TCG-ARG-ABI]", "UP` (16 bytes, align 16)"],
        bin_refusal: &["[TCG-ARG-ABI]", "UP` (16 bytes, align 16)"],
        refused_at: &["0", "2"],
    },
    Control {
        name: "w1_pointer_union_return",
        lib: r#"#[derive(Clone, Copy)] #[repr(C, align(16))] pub union UP { pub p: *const u64 }
#[inline(never)] pub fn mk_up(p: *const u64) -> UP { UP { p } }"#,
        bin: r#"static X: u64 = 40; fn main() { let u = w::mk_up(std::hint::black_box(&X as *const u64)); std::process::exit(unsafe { (u.p == &X as *const u64) as i32 * 30 + 3 }) }"#,
        oracle: 33,
        lib_refusal: &["[TCG-RET-ABI]", "UP` (16 bytes, align 16)"],
        bin_refusal: &["[TCG-RET-ABI]", "UP` (16 bytes, align 16)"],
        refused_at: &["0", "2"],
    },
    // The bridge's `dyn Fn*` dispatch spreads the argument tuple itself; a padded
    // POINTER element is rustc's `Indirect` there too (measured before: an LLVM
    // rlib's `&dyn Fn(AP)` called from a bridge bin SIGSEGV'd against 41; until
    // round 10 the spread then refused it by name). Since round 10 the spread
    // builds it through the one closure-argument builder, so the bridge bin over
    // the LLVM rlib compiles and must agree; since F2 the bridge rlib's vtable
    // does too (its `call_once` `VTableShim` is declared untupled, with the
    // pointer rustc passes). The closure is boxed with a capture so the vtable is
    // built at run time at every level (a `&'static` closure is a promoted
    // constant, which the bridge refuses earlier at `-O2`).
    Control {
        name: "w1_padded_pointer_dyn_fn",
        lib: r#"#[derive(Clone, Copy)] #[repr(C, align(16))] pub struct AP { pub p: *const u64 }
#[inline(never)] pub fn get(k: u64) -> Box<dyn Fn(AP) -> u64> { Box::new(move |a: AP| unsafe { *a.p + k }) }"#,
        bin: r#"static X: u64 = 40; fn main() { let f = w::get(std::hint::black_box(1)); let a = w::AP { p: std::hint::black_box(&X as *const u64) }; std::process::exit((f(a) % 251) as i32) }"#,
        oracle: 41,
        lib_refusal: &[],
        bin_refusal: &[],
        refused_at: &[],
    },
    // A `rust-call` fn ITEM reached BY SYMBOL: `<&fn-item as Fn<(u64, u64, u64)>>
    // ::call`, instantiated and EXPORTED by the rlib under `-Zshare-generics`
    // (O0) and linked by the bin's own generic caller. The bridge declared it
    // with a 24-byte tuple, rustc with three registers (measured before: 220 /
    // 190 against 231), and then refused it by name at O0. Since F2 it is
    // declared untupled. At O2 each crate instantiates its own copy.
    Control {
        name: "w2_shared_generic_rust_call",
        lib: r#"#[inline(never)] pub fn triple(a: u64, b: u64, c: u64) -> u64 { a * 10 + b * 3 + c * 7 }
#[inline(never)] pub fn call_it<F: Fn(u64, u64, u64) -> u64>(f: &F) -> u64 { f(std::hint::black_box(1), 2, 3) }
#[inline(never)] pub fn run() -> u64 { call_it(&&triple) }"#,
        bin: r#"#[inline(never)] fn call_it2<F: Fn(u64, u64, u64) -> u64>(f: &F) -> u64 { f(std::hint::black_box(4), 5, 6) } fn main() { let r = w::run() + call_it2(&&w::triple) * 2; std::process::exit((r % 251) as i32) }"#,
        oracle: 231,
        lib_refusal: &[],
        bin_refusal: &[],
        refused_at: &[],
    },
    // A non-generic `extern "rust-call"` fn is an exported symbol at every level
    // (measured before: SIGSEGV / 0 against 117, then refused by name).
    Control {
        name: "w2_rust_call_item_export",
        lib: r#"#![feature(unboxed_closures)]
#[derive(Clone, Copy)] pub struct T12 { pub a: u32, pub b: u32, pub c: u32 }
#[inline(never)] pub extern "rust-call" fn rc3(t: (u64, u64, u64)) -> u64 { t.0 + t.1 * 3 + t.2 * 7 }
#[inline(never)] pub extern "rust-call" fn rct(t: (T12,)) -> u32 { t.0.a + t.0.b * 3 + t.0.c * 7 }"#,
        bin: r#"#![feature(unboxed_closures)]
use std::hint::black_box as bb; fn main() { let v = w::rc3((bb(1), bb(2), bb(3))); let x = w::rct((w::T12 { a: bb(4), b: 5, c: 6 },)); std::process::exit(((v * 2 + x as u64) % 251) as i32) }"#,
        oracle: 117,
        lib_refusal: &[],
        bin_refusal: &[],
        refused_at: &[],
    },
    // A `FnOnce` closure BODY with an 8-byte environment moved in by value,
    // exported under `-Zshare-generics` through a public `impl FnOnce` and linked
    // by the bin's own generic caller: the bridge passed the environment as a
    // pointer, rustc as one `u64` (measured before: 209 / SIGSEGV against 57),
    // and then refused it by name. Since round 10 the environment is argument 0
    // by rustc's own mode, so every cell compiles and must agree.
    Control {
        name: "closure_by_value_env_shared",
        lib: r#"pub struct NC(pub u64);
#[inline(never)] pub fn run<F: FnOnce(u64) -> u64>(f: F) -> u64 { f(std::hint::black_box(2)) }
#[inline(never)] pub fn make(v: u64) -> impl FnOnce(u64) -> u64 { let nc = NC(v); move |x| { let n = nc; n.0 * 3 + x } }
#[inline(never)] pub fn lib_use(v: u64) -> u64 { run(make(v)) }"#,
        bin: r#"#[inline(never)] fn run2<F: FnOnce(u64) -> u64>(f: F) -> u64 { f(std::hint::black_box(5)) } fn main() { let r = w::lib_use(std::hint::black_box(1)) + run2(w::make(std::hint::black_box(7))) * 2; std::process::exit((r % 251) as i32) }"#,
        oracle: 57,
        lib_refusal: &[],
        bin_refusal: &[],
        refused_at: &[],
    },
];

/// Compile `src` as crate `w` (rlib) or as a bin against `rlib`, returning the
/// artifact or rustc's stderr.
fn compile_control(
    lane: &Lane,
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    tag: &str,
    src: &str,
    rlib: Option<&Path>,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{tag}.rs"));
    let src = match rlib {
        None => lane.callee_source(src),
        Some(_) => lane.control_bin_source(src),
    };
    std::fs::write(&src_path, src).expect("write control source");
    let out_dir = dir.join(format!("{tag}_{}_O{opt}", backend.tag()));
    std::fs::create_dir_all(&out_dir).expect("create control out dir");
    let mut cmd = toolchain_support::rustc_command();
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.args(lane.knobs());
    }
    cmd.args(lane.target_args(opt))
        .args([
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"));
    let artifact = match rlib {
        None => {
            cmd.args(["--crate-type", "rlib", "--crate-name", "w", "--out-dir"])
                .arg(&out_dir);
            out_dir.join("libw.rlib")
        }
        Some(rlib) => {
            let mut extern_arg = OsString::from("w=");
            extern_arg.push(rlib);
            let bin = out_dir.join("bin");
            cmd.args(["--crate-type", "bin", "--extern"])
                .arg(&extern_arg)
                .arg("-L")
                .arg(rlib.parent().expect("rlib directory"))
                .arg("-o")
                .arg(&bin);
            bin
        }
    };
    let output = cmd
        .arg(&src_path)
        .output()
        .expect("spawn rustc for a control");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(artifact)
}

fn check_refusal(
    failures: &mut Vec<String>,
    what: &str,
    result: Result<PathBuf, String>,
    needles: &[&str],
) -> Option<PathBuf> {
    match result {
        Ok(artifact) if needles.is_empty() => Some(artifact),
        Ok(_) => {
            failures.push(format!(
                "{what}: compiled, expected a refusal naming {needles:?}"
            ));
            None
        }
        Err(e) if needles.is_empty() => {
            failures.push(format!(
                "{what}: refused, expected it to compile: <<<{}>>>",
                e.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
            ));
            None
        }
        Err(e) => {
            if let Some(missing) = needles.iter().find(|n| !e.contains(**n)) {
                failures.push(format!(
                    "{what}: refused without `{missing}`: <<<{}>>>",
                    e.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                ));
            }
            None
        }
    }
}

#[test]
fn refused_by_name_controls() {
    for control in CONTROLS {
        let boxed = control.lib.contains("Box<") || control.bin.contains("Box<");
        assert_eq!(
            boxed,
            NEEDS_ALLOC.contains(&control.name),
            "control `{}`: NEEDS_ALLOC must list exactly the controls that use `Box`",
            control.name
        );
    }
    if !host_runs_lane_target() {
        eprintln!("skipping: the lane runs natively on an x86_64 or aarch64 Linux or macOS host");
        return;
    }
    if !lane_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let mut failures = Vec::new();
    for lane in Lane::all() {
        let dir = workdir(&format!("ctl_{}", lane.tag()));
        let lane_first = failures.len();
        for opt in ["0", "2"] {
            for control in CONTROLS {
                if matches!(lane, Lane::X86(_)) && NEEDS_ALLOC.contains(&control.name) {
                    continue;
                }
                let tag = control.name;
                let llvm_rlib = compile_control(
                    &lane,
                    &dir,
                    &dylib,
                    Backend::Llvm,
                    opt,
                    &format!("{tag}_lib"),
                    control.lib,
                    None,
                )
                .unwrap_or_else(|e| panic!("LLVM `{tag}` rlib failed at O{opt}: <<<{e}>>>"));
                let oracle = compile_control(
                    &lane,
                    &dir,
                    &dylib,
                    Backend::Llvm,
                    opt,
                    &format!("{tag}_bin_ll"),
                    control.bin,
                    Some(&llvm_rlib),
                )
                .unwrap_or_else(|e| panic!("LLVM `{tag}` bin failed at O{opt}: <<<{e}>>>"));
                let oracle_exit = lane.run(&oracle, opt);
                assert_eq!(
                    oracle_exit, control.oracle,
                    "oracle (LLVM+LLVM) exit for control `{tag}` at O{opt}"
                );
                let refused_here = control.refused_at.contains(&opt);
                let (lib_refusal, bin_refusal): (&[&str], &[&str]) = if refused_here {
                    (control.lib_refusal, control.bin_refusal)
                } else {
                    (&[], &[])
                };
                let tcg_rlib = check_refusal(
                    &mut failures,
                    &format!("O{opt} `{tag}` trust-cg rlib"),
                    compile_control(
                        &lane,
                        &dir,
                        &dylib,
                        Backend::TrustCg,
                        opt,
                        &format!("{tag}_lib"),
                        control.lib,
                        None,
                    ),
                    lib_refusal,
                );
                let mut cells = vec![("LLVM rlib + trust-cg bin", Backend::TrustCg, llvm_rlib)];
                if let Some(tcg_rlib) = tcg_rlib {
                    cells.push(("trust-cg rlib + LLVM bin", Backend::Llvm, tcg_rlib.clone()));
                    cells.push(("trust-cg rlib + trust-cg bin", Backend::TrustCg, tcg_rlib));
                }
                for (label, backend, rlib) in cells {
                    let bin_tag =
                        format!("{tag}_bin_{}_{}", backend.tag(), rlib_backend_tag(&rlib));
                    let result = compile_control(
                        &lane,
                        &dir,
                        &dylib,
                        backend,
                        opt,
                        &bin_tag,
                        control.bin,
                        Some(&rlib),
                    );
                    let needles: &[&str] = if backend == Backend::TrustCg {
                        bin_refusal
                    } else {
                        &[]
                    };
                    let what = format!("O{opt} `{tag}` {label}");
                    if let Some(bin) = check_refusal(&mut failures, &what, result, needles) {
                        let exit = lane.run(&bin, opt);
                        if exit != oracle_exit {
                            failures.push(format!("{what}: exit {exit}, oracle {oracle_exit}"));
                        }
                    }
                }
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
        for failure in &mut failures[lane_first..] {
            *failure = format!("{}: {failure}", lane.label());
        }
    }
    assert!(
        failures.is_empty(),
        "{} refused-by-name control(s) did not behave:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    record_evidence();
}

#[test]
fn indirect_arguments_agree_across_backends() {
    if !host_runs_lane_target() {
        eprintln!("skipping: the lane runs natively on an x86_64 or aarch64 Linux or macOS host");
        return;
    }
    if !lane_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let mut failures = Vec::new();
    for lane in Lane::all() {
        let dir = workdir(&format!("ind_{}", lane.tag()));
        let lane_first = failures.len();
        let krate = "callee";
        for opt in ["0", "1", "2", "3"] {
            let llvm_rlib =
                compile_callee_rlib(&lane, &dir, &dylib, Backend::Llvm, opt, krate, CALLEE_SRC)
                    .unwrap_or_else(|e| panic!("LLVM `{krate}` rlib failed at O{opt}: <<<{e}>>>"));
            let tcg_rlib = match compile_callee_rlib(
                &lane,
                &dir,
                &dylib,
                Backend::TrustCg,
                opt,
                krate,
                CALLEE_SRC,
            ) {
                Ok(rlib) => rlib,
                Err(e) => {
                    failures.push(format!(
                        "O{opt} `{krate}`: trust-cg callee rlib failed closed: <<<{}>>>",
                        e.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
                    ));
                    continue;
                }
            };
            for (shape, body, expected) in shapes() {
                let oracle = compile_caller_bin(
                    &lane,
                    &dir,
                    &dylib,
                    Backend::Llvm,
                    opt,
                    shape,
                    body,
                    &llvm_rlib,
                )
                .unwrap_or_else(|e| panic!("LLVM caller `{shape}` failed at O{opt}: <<<{e}>>>"));
                let oracle_exit = lane.run(&oracle, opt);
                assert_eq!(
                    oracle_exit, expected,
                    "oracle (LLVM+LLVM) exit for `{shape}` at O{opt} is {oracle_exit}, expected {expected}"
                );
                let combos = [
                    (
                        Backend::TrustCg,
                        &llvm_rlib,
                        "LLVM callee + trust-cg caller",
                    ),
                    (Backend::Llvm, &tcg_rlib, "trust-cg callee + LLVM caller"),
                    (
                        Backend::TrustCg,
                        &tcg_rlib,
                        "trust-cg callee + trust-cg caller",
                    ),
                ];
                for (backend, rlib, label) in combos {
                    match compile_caller_bin(&lane, &dir, &dylib, backend, opt, shape, body, rlib) {
                        Ok(bin) => {
                            let exit = lane.run(&bin, opt);
                            if exit != oracle_exit {
                                failures.push(format!(
                                    "O{opt} `{shape}` {label}: exit {exit}, oracle {oracle_exit}"
                                ));
                            }
                        }
                        Err(e) => failures.push(format!(
                            "O{opt} `{shape}` {label}: trust-cg caller failed closed: <<<{}>>>",
                            e.lines().rev().take(6).collect::<Vec<_>>().join(" | ")
                        )),
                    }
                }
            }
        }
        let _ = std::fs::remove_dir_all(&dir);
        for failure in &mut failures[lane_first..] {
            *failure = format!("{}: {failure}", lane.label());
        }
    }
    assert!(
        failures.is_empty(),
        "{} indirect-argument combination(s) disagreed or refused:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
    record_evidence();
}
