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

// Integration test: a Rust-ABI `PassMode::Pair` ARGUMENT at REGISTER
// EXHAUSTION on x86-64 — exactly ONE integer argument register left when the
// pair is reached — checked ACROSS the backend boundary in all four rlib x bin
// combinations at every optimization level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// rustc passes a `PassMode::Pair` as TWO INDEPENDENT scalar arguments, so with
// one integer register left lane 0 takes R9 and lane 1 the stack. A 16-byte
// two-eightbyte AGGREGATE is placed all-or-nothing by the System V classifier:
// with one register left it goes WHOLLY to the stack. The bridge used to
// declare a 16-byte two-INTEGER pair — the slice / `str` fat-pointer family,
// `(u64, u64)`, `Range<usize>`, `Option<u64>`, a two-`u64` struct — as that
// aggregate, because `check_param_abi` classifies a parameter in isolation and
// the pair "already lands in the register pair rustc asks for" — true only
// while two registers remain. Measured 2026-09-23 on this host before the fix:
// 70 of 160 cells (O0, O2) disagreed, every one-register-left shape in BOTH
// directions (e.g. `slice_spill` 230 / 115 against 215, `str_spill` and
// `two_slices` SIGSEGV), while every same-backend cell and both controls
// (`slice_after4`: two registers left; `slice_after6`: none) agreed. On x86-64
// every `Pair` now rides the two-value lane (`scalar_pair_param_plan`).
//
// Rows: direct calls (`&[u8]` with its first byte read, `&str`, `*const [u8]`,
// a `&mut [u8]` the callee writes through, `NonNull<[u8]>`), a trailing scalar
// after the pair (R9 must not be back-filled out of order), two slices, a pair
// after a `&dyn` (two pointer registers), a `&self` method, an sret return (the
// hidden RDI counts), a `fn` pointer (the `FnPtr` ABI source), a trait-object
// method called from the other backend (the virtual lane's `param_tys`), const
// literals, the two controls, and the A2 family (`(u64, u64)`, `Range<usize>`,
// `Option<u64>` both variants, a two-`u64` struct).
//
// Runs natively on an x86-64 Linux or macOS host with the host x86-64
// `rust-std`, and under Rosetta on an aarch64-apple-darwin host
// (`support/x86_rosetta.rs`: the same callee and shapes as `#![no_std]`
// programs against a `core` built from the compiler's own library source). A
// run under Rosetta qualifies Rosetta's execution of the x86-64 code, not a
// native x86-64 machine.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use x86_rosetta_support::XbackLane;

const TARGET: &str = host_target_support::X86_64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

/// The bridge's knob argument on this lane. The Rosetta lane compiles with
/// the proof certificates off (`no-proof-certs`), as the family matrix and
/// `m146` do: with them on, every trust-cg x86-64 rlib of this file is refused
/// `[TCG-PROOF-465]` on an Apple-silicon host (proof promotion finds the emitted
/// x86-64 opcode inventory uncovered; measured 2026-09-30), which says nothing
/// about argument placement. A native x86-64 host keeps them on, as the lane
/// was measured there.
fn backend_knobs(lane: &XbackLane) -> Option<String> {
    matches!(lane, XbackLane::Rosetta)
        .then(|| toolchain_support::backend_knobs_arg(&["no-proof-certs"]))
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("m144_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
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

/// One callee rlib named `krate` compiled by `backend` at `opt`. The shapes of
/// a crate share one compile, so one refusal names every shape in it.
fn compile_callee_rlib(
    lane: &XbackLane,
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
        cmd.args(backend_knobs(lane));
    }
    cmd.args(lane.compile_args(opt))
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
    lane: &XbackLane,
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
        cmd.args(backend_knobs(lane));
    }
    let krate = rlib
        .file_stem()
        .and_then(|s| s.to_str())
        .and_then(|s| s.strip_prefix("lib"))
        .expect("rlib file name");
    let mut extern_arg = OsString::from(format!("{krate}="));
    extern_arg.push(rlib);
    cmd.args(lane.compile_args(opt))
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

fn run_exit_code(lane: &XbackLane, bin: &Path, opt: &str) -> i32 {
    lane.run(bin, opt)
        .unwrap_or_else(|why| panic!("{} {bin:?}: {why}", lane.label()))
}

/// The callee crate: one `#[inline(never)]` function per shape taking the pair
/// BY VALUE and folding its lanes asymmetrically into a scalar, so a swapped,
/// truncated or dirty lane is a different exit code. The caller passes every
/// input through `black_box`, so nothing constant-folds across the boundary.
const CALLEE_SRC: &str = r#"
use core::ptr::NonNull;
use core::ops::Range;
#[inline(never)] pub fn slice_spill(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8]) -> u64 { a + b + c + d + e + s.len() as u64 * 100 }
#[inline(never)] pub fn slice_first(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8]) -> u64 { a + b + c + d + e + s.len() as u64 * 10 + s[0] as u64 }
#[inline(never)] pub fn str_spill(a: u64, b: u64, c: u64, d: u64, e: u64, t: &str) -> u64 { a + b + c + d + e + t.len() as u64 * 100 + t.as_bytes()[0] as u64 }
#[inline(never)] pub fn raw_spill(a: u64, b: u64, c: u64, d: u64, e: u64, p: *const [u8]) -> u64 { a + b + c + d + e + p.len() as u64 * 100 }
#[inline(never)] pub fn mut_spill(a: u64, b: u64, c: u64, d: u64, e: u64, s: &mut [u8]) { s[0] = (a + b + c + d + e) as u8; let n = s.len(); s[n - 1] = n as u8; }
#[inline(never)] pub fn slice_trailing(a: u64, b: u64, c: u64, d: u64, e: u64, s: &[u8], g: u64) -> u64 { a + b + c + d + e + s.len() as u64 * 10 + g * 3 }
#[inline(never)] pub fn two_slices(a: u64, b: u64, c: u64, s: &[u8], t: &[u8]) -> u64 { a + b + c + s.len() as u64 * 10 + t.len() as u64 * 50 + t[0] as u64 }
pub trait Take { fn take(&self) -> u64; }
pub struct T1(pub u64);
impl Take for T1 { fn take(&self) -> u64 { self.0 } }
#[inline(never)] pub fn dyn_then_slice(a: u64, b: u64, c: u64, t: &dyn Take, s: &[u8]) -> u64 { a + b + c + t.take() + s.len() as u64 * 20 }
pub struct H(pub u64);
impl H { #[inline(never)] pub fn m(&self, a: u64, b: u64, c: u64, d: u64, s: &[u8]) -> u64 { self.0 + a + b + c + d + s.len() as u64 * 30 } }
#[inline(never)] pub fn sret_then_slice(a: u64, b: u64, c: u64, d: u64, s: &[u8]) -> [u64; 4] { [a + s.len() as u64, b, c * 2, d + s[0] as u64] }
pub trait Tk { fn m(&self, a: u64, b: u64, c: u64, d: u64, s: &[u8]) -> u64; }
impl Tk for H { fn m(&self, a: u64, b: u64, c: u64, d: u64, s: &[u8]) -> u64 { self.0 * 2 + a + b + c + d + s.len() as u64 * 40 } }
#[inline(never)] pub fn via_dyn_tk(t: &dyn Tk, s: &[u8]) -> u64 { t.m(1, 2, 3, 4, s) }
#[inline(never)] pub fn nn_mk(s: &[u8]) -> NonNull<[u8]> { NonNull::from(s) }
#[inline(never)] pub fn nn_spill(a: u64, b: u64, c: u64, d: u64, e: u64, p: NonNull<[u8]>) -> u64 { a + b + c + d + e + p.len() as u64 * 100 }
#[inline(never)] pub fn slice_after4(a: u64, b: u64, c: u64, d: u64, s: &[u8]) -> u64 { a + b + c + d + s.len() as u64 * 100 }
#[inline(never)] pub fn slice_after6(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, s: &[u8]) -> u64 { a + b + c + d + e + f + s.len() as u64 * 100 }
#[inline(never)] pub fn pair_spill(a: u64, b: u64, c: u64, d: u64, e: u64, p: (u64, u64)) -> u64 { a + b + c + d + e + p.0 * 10 + p.1 * 100 }
#[inline(never)] pub fn range_spill(a: u64, b: u64, c: u64, d: u64, e: u64, r: Range<usize>) -> u64 { a + b + c + d + e + r.start as u64 * 10 + r.end as u64 * 100 }
#[inline(never)] pub fn opt_spill(a: u64, b: u64, c: u64, d: u64, e: u64, o: Option<u64>) -> u64 { a + b + c + d + e + match o { Some(v) => v * 10, None => 7 } }
pub struct S2 { pub x: u64, pub y: u64 }
#[inline(never)] pub fn struct_spill(a: u64, b: u64, c: u64, d: u64, e: u64, s: S2) -> u64 { a + b + c + d + e + s.x * 10 + s.y * 100 }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n";

/// `(shape, caller body, expected exit code)`. The expected code is the
/// oracle's (LLVM callee + LLVM caller) and is asserted so a corrupted oracle
/// cannot make every combination agree on a wrong value.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        (
            "slice_spill",
            r#"fn main() { exit(callee::slice_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(&b"ab"[..]))) }"#,
            215,
        ),
        (
            "slice_first",
            r#"fn main() { exit(callee::slice_first(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(&b"xyz"[..]))) }"#,
            165,
        ),
        (
            "str_spill",
            r#"fn main() { exit(callee::str_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box("abc"))) }"#,
            161,
        ),
        (
            "raw_spill",
            r#"fn main() { let s: &[u8] = black_box(&b"abcd"[..]); exit(callee::raw_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), s as *const [u8])) }"#,
            164,
        ),
        (
            "mut_spill",
            r#"fn main() { let mut b = [0u8; 3]; callee::mut_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(&mut b[..])); exit(b[0] as u64 * 10 + b[2] as u64) }"#,
            153,
        ),
        (
            "slice_trailing",
            r#"fn main() { exit(callee::slice_trailing(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(&b"ab"[..]), black_box(9))) }"#,
            62,
        ),
        (
            "two_slices",
            r#"fn main() { exit(callee::two_slices(black_box(1), black_box(2), black_box(3), black_box(&b"ab"[..]), black_box(&b"xyz"[..]))) }"#,
            45,
        ),
        (
            "dyn_then_slice",
            r#"fn main() { let t = callee::T1(black_box(40)); exit(callee::dyn_then_slice(black_box(1), black_box(2), black_box(3), &t, black_box(&b"ab"[..]))) }"#,
            86,
        ),
        (
            "self_method",
            r#"fn main() { let h = callee::H(black_box(50)); exit(h.m(black_box(1), black_box(2), black_box(3), black_box(4), black_box(&b"ab"[..]))) }"#,
            120,
        ),
        (
            "sret_then_slice",
            r#"fn main() { let r = callee::sret_then_slice(black_box(1), black_box(2), black_box(3), black_box(4), black_box(&b"ab"[..])); exit(r[0] + r[1] * 10 + r[2] + r[3]) }"#,
            130,
        ),
        (
            "fnptr_spill",
            r#"fn main() { let f: fn(u64, u64, u64, u64, u64, &[u8]) -> u64 = black_box(callee::slice_spill); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(&b"ab"[..]))) }"#,
            215,
        ),
        (
            "dyn_method_spill",
            r#"fn main() { let h = callee::H(black_box(5)); let t: &dyn callee::Tk = &h; exit(t.m(black_box(1), black_box(2), black_box(3), black_box(4), black_box(&b"abc"[..]))) }"#,
            140,
        ),
        (
            "const_literal",
            r#"fn main() { exit(callee::slice_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), b"hi") + callee::str_spill(black_box(0), black_box(0), black_box(0), black_box(0), black_box(0), "q")) }"#,
            177,
        ),
        (
            "nn_spill",
            r#"fn main() { exit(callee::nn_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), callee::nn_mk(black_box(&b"ab"[..])))) }"#,
            215,
        ),
        (
            "slice_after4",
            r#"fn main() { exit(callee::slice_after4(black_box(1), black_box(2), black_box(3), black_box(4), black_box(&b"ab"[..]))) }"#,
            210,
        ),
        (
            "slice_after6",
            r#"fn main() { exit(callee::slice_after6(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(&b"ab"[..]))) }"#,
            221,
        ),
        (
            "pair_spill",
            r#"fn main() { exit(callee::pair_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box((6, 7)))) }"#,
            22,
        ),
        (
            "range_spill",
            r#"fn main() { exit(callee::range_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(3..9))) }"#,
            192,
        ),
        (
            "opt_spill",
            r#"fn main() { exit(callee::opt_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(Some(8))) + callee::opt_spill(black_box(1), black_box(1), black_box(1), black_box(1), black_box(1), black_box(None))) }"#,
            107,
        ),
        (
            "struct_spill",
            r#"fn main() { exit(callee::struct_spill(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), callee::S2 { x: black_box(6), y: black_box(7) })) }"#,
            22,
        ),
    ]
}

#[test]
fn pair_arguments_at_register_exhaustion_agree_across_backends_x86_64() {
    let lane = match XbackLane::for_host(TARGET) {
        Ok(lane) => lane,
        Err(why) => {
            eprintln!("skipping: {why}");
            return;
        }
    };
    let dylib = ensure_dylib_built();
    let dir = workdir("exh");
    let mut failures = Vec::new();
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
            let oracle_exit = run_exit_code(&lane, &oracle, opt);
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
                        let exit = run_exit_code(&lane, &bin, opt);
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
    assert!(
        failures.is_empty(),
        "{}: {} pair-argument-at-exhaustion combination(s) disagreed or refused:\n  {}",
        lane.label(),
        failures.len(),
        failures.join("\n  ")
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        if matches!(lane, XbackLane::Rosetta) {
            positive_evidence::Certs::Off
        } else {
            positive_evidence::Certs::On
        },
    );
}
