#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: by-value arguments at REGISTER EXHAUSTION on AArch64 that
// `tests/m147_aarch64_pair_arg_exhaustion_xback.rs` does not cover — rustc's
// `PassMode::Indirect` pointer (the indirect argument lane) as the LAST integer
// register and on the STACK, and two more `PassMode::Pair` kinds — checked
// ACROSS the backend boundary in all four rlib x bin combinations at every
// optimization level.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The argument-ABI gate (`check_param_abi_lanes`) compares each argument IN
// ISOLATION: class, count, per-lane extent and value offset, never register
// numbering or stack offsets. So a placement that is right in isolation and
// wrong after seven or eight earlier arguments passes the gate and is caught
// only across a real backend boundary. Two families were measured that way on
// aarch64-apple-darwin (2026-09-29, `targo --unverified`, no proof claim):
//
// * scalar pairs split between the last register and the stack, fixed by
//   `ab0b74ce0` and pinned by m147 (every pair kind at argument position 7);
//   this file adds `Range<usize>` and a two-`u64` struct, which m147 does not
//   name. At trust-cg 8328b1068, before the fix, both disagreed in both mixed
//   cells at every level (16 of this matrix's 112 cells, e.g. `range7` 208 / 96
//   against 70 at O0);
// * the indirect argument lane's ONE pointer (a 12-byte `struct T12 { u32, u32,
//   u32 }`, which rustc passes as a pointer to a caller-made copy) in x7 with a
//   trailing `u32` on the stack, and on the stack after eight `u64`s: these
//   agree, at 8328b1068 too (the lane's pointer is placed like any pointer), so
//   these rows pin the lane at exhaustion rather than record a fix — with a
//   fn-pointer call (the `FnPtr` ABI source), a trait-object method called from
//   the other backend (the virtual lane's `param_tys`, index offset 1) and a
//   first-argument control.
//
// NOT HERE, because it is still wrong (an open cross-backend miscompile named
// in LIMITATIONS.md, "Register exhaustion"): a Rust-ABI `Cast` aggregate under
// 8 bytes on the Darwin stack (`[u8; 4]`, `struct { u8, u8, u8 }` after eight
// `u64`s and before a trailing scalar: 56 / 53 at O0 against 83; `[u8; 2]`:
// stack garbage that varies by run), which rustc passes as a packed `iN` and
// the bridge declares as a composite Darwin rounds up to an 8-byte slot. It
// joins this matrix with the whole-signature placement comparison that makes
// it fail closed.
//
// Executes only on an AArch64 host with its native `rust-std`.
// `tests/tools/m145_xback.py --test` drives the same callee and shapes
// (extracted from this file) outside the cargo harness.

use std::ffi::OsString;
use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::AARCH64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn aarch64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn host_is_aarch64() -> bool {
    cfg!(target_arch = "aarch64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("a64exh_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> OsString {
    let mut s = OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// On AArch64 the per-compile proof certificates refuse every program with
/// `[TCG-PROOF-465]` (the AArch64 opcode inventory has no checker-accepted
/// certificate for the pair opcodes yet — unrelated to argument placement), so
/// this run turns them off, as `tests/tools/m145_xback.py` does.
fn backend_knobs() -> String {
    toolchain_support::backend_knobs_arg(&["no-proof-certs"])
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

/// One callee rlib compiled by `backend` at `opt`. Every shape shares it, so
/// one refusal names every shape.
fn compile_callee_rlib(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
) -> Result<PathBuf, String> {
    let src_path = dir.join("callee.rs");
    std::fs::write(&src_path, CALLEE_SRC).expect("write callee source");
    let out_dir = dir.join(format!("callee_{}_O{opt}", backend.tag()));
    std::fs::create_dir_all(&out_dir).expect("create callee out dir");
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "rlib", "--crate-name", "callee"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.arg(backend_knobs());
    }
    cmd.args([
        "--target",
        TARGET,
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
    let rlib = out_dir.join("libcallee.rlib");
    if !rlib.is_file() {
        return Err(format!("no rlib produced at {rlib:?}"));
    }
    Ok(rlib)
}

/// One caller bin for `shape`, compiled by `backend` at `opt` against `rlib`.
fn compile_caller_bin(
    dir: &Path,
    dylib: &Path,
    backend: Backend,
    opt: &str,
    shape: &str,
    body: &str,
    rlib: (Backend, &Path),
) -> Result<PathBuf, String> {
    let (rlib_backend, rlib) = rlib;
    let src_path = dir.join(format!("caller_{shape}.rs"));
    std::fs::write(&src_path, format!("{CALLER_HDR}{body}")).expect("write caller source");
    let bin = dir.join(format!(
        "caller_{shape}_{}rlib_{}bin_O{opt}",
        rlib_backend.tag(),
        backend.tag()
    ));
    let mut cmd = toolchain_support::rustc_command();
    cmd.args(["--crate-type", "bin"]);
    if backend == Backend::TrustCg {
        cmd.arg(backend_arg(dylib));
        cmd.arg(backend_knobs());
    }
    let mut extern_arg = OsString::from("callee=");
    extern_arg.push(rlib);
    cmd.args([
        "--target",
        TARGET,
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

/// The exit code, or the signal as a failure: a SIGSEGV is exactly how the
/// measured miscompiles show, so it is a failed cell, not a harness panic.
fn run_exit_code(bin: &Path) -> Result<i32, String> {
    let out = Command::new(bin).output().expect("run binary");
    out.status
        .code()
        .ok_or_else(|| format!("exited via signal: {:?}", out.status))
}

/// The callee crate: one `#[inline(never)]` function per shape taking the
/// argument BY VALUE after enough `u64`s to leave one integer register (or
/// none), folding its fields asymmetrically into a scalar so a swapped,
/// truncated or shifted field is a different exit code. The caller passes every
/// input through `black_box`, so nothing constant-folds across the boundary.
const CALLEE_SRC: &str = r#"
use core::ops::Range;
#[inline(never)] pub fn range7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, r: Range<usize>) -> u64 { a + b + c + d + e + f + g + r.start as u64 * 5 + r.end as u64 * 3 }
pub struct S2 { pub x: u64, pub y: u64 }
#[inline(never)] pub fn struct7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, s: S2) -> u64 { a + b + c + d + e + f + g + s.x * 5 + s.y * 3 }
pub struct T12 { pub a: u32, pub b: u32, pub c: u32 }
#[inline(never)] pub fn mem0(t: T12, y: u32) -> u64 { t.a as u64 + t.c as u64 * 2 + y as u64 * 3 }
#[inline(never)] pub fn mem7(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, t: T12, y: u32) -> u64 { a + b + c + d + e + f + g + t.a as u64 + t.c as u64 * 2 + y as u64 * 3 }
#[inline(never)] pub fn mem8(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, g: u64, h: u64, t: T12, y: u32) -> u64 { a + b + c + d + e + f + g + h + t.a as u64 + t.c as u64 * 2 + y as u64 * 3 }
pub trait Tm { fn m(&self, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, t: T12, y: u32) -> u64; }
pub struct H(pub u64);
impl Tm for H { fn m(&self, a: u64, b: u64, c: u64, d: u64, e: u64, f: u64, t: T12, y: u32) -> u64 { self.0 * 2 + a + b + c + d + e + f + t.a as u64 + t.c as u64 * 2 + y as u64 * 3 } }
"#;

const CALLER_HDR: &str = "use std::hint::black_box;\n\
    fn exit(v: u64) -> ! { std::process::exit((v % 251) as i32) }\n";

/// `(shape, caller body, expected exit code)`. The expected code is the
/// oracle's (LLVM callee + LLVM caller) and is asserted, so a corrupted oracle
/// cannot make every combination agree on a wrong value.
fn shapes() -> Vec<(&'static str, &'static str, i32)> {
    vec![
        (
            "range7",
            r#"fn main() { exit(callee::range7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(3..9))) }"#,
            70,
        ),
        (
            "struct7",
            r#"fn main() { exit(callee::struct7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), callee::S2 { x: black_box(6), y: black_box(2) })) }"#,
            64,
        ),
        (
            "mem0",
            r#"fn main() { exit(callee::mem0(black_box(callee::T12 { a: 5, b: 77, c: 6 }), black_box(10))) }"#,
            47,
        ),
        (
            "mem7",
            r#"fn main() { exit(callee::mem7(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(callee::T12 { a: 5, b: 77, c: 6 }), black_box(10))) }"#,
            75,
        ),
        (
            "mem8",
            r#"fn main() { exit(callee::mem8(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box(callee::T12 { a: 5, b: 77, c: 6 }), black_box(10))) }"#,
            83,
        ),
        (
            "fnptr_mem8",
            r#"fn main() { let f: fn(u64, u64, u64, u64, u64, u64, u64, u64, callee::T12, u32) -> u64 = black_box(callee::mem8); exit(f(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(7), black_box(8), black_box(callee::T12 { a: 5, b: 77, c: 6 }), black_box(10))) }"#,
            83,
        ),
        (
            "dyn_mem7",
            r#"fn main() { let h = callee::H(black_box(5)); let t: &dyn callee::Tm = &h; exit(t.m(black_box(1), black_box(2), black_box(3), black_box(4), black_box(5), black_box(6), black_box(callee::T12 { a: 5, b: 77, c: 6 }), black_box(10))) }"#,
            78,
        ),
    ]
}

#[test]
fn arguments_at_register_exhaustion_agree_across_backends_aarch64() {
    if !host_is_aarch64() {
        eprintln!("skipping: the AArch64 run requires an AArch64 Linux or macOS host");
        return;
    }
    if !aarch64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("exh");
    let mut failures = Vec::new();
    for opt in ["0", "1", "2", "3"] {
        let llvm_rlib = compile_callee_rlib(&dir, &dylib, Backend::Llvm, opt)
            .unwrap_or_else(|e| panic!("LLVM callee rlib failed at O{opt}: <<<{e}>>>"));
        let tcg_rlib = match compile_callee_rlib(&dir, &dylib, Backend::TrustCg, opt) {
            Ok(rlib) => rlib,
            Err(e) => {
                failures.push(format!(
                    "O{opt}: trust-cg callee rlib failed closed: <<<{}>>>",
                    e.lines().rev().take(8).collect::<Vec<_>>().join(" | ")
                ));
                continue;
            }
        };
        for (shape, body, expected) in shapes() {
            let oracle = compile_caller_bin(
                &dir,
                &dylib,
                Backend::Llvm,
                opt,
                shape,
                body,
                (Backend::Llvm, &llvm_rlib),
            )
            .unwrap_or_else(|e| panic!("LLVM caller `{shape}` failed at O{opt}: <<<{e}>>>"));
            let oracle_exit = run_exit_code(&oracle)
                .unwrap_or_else(|e| panic!("oracle (LLVM+LLVM) `{shape}` at O{opt}: {e}"));
            assert_eq!(
                oracle_exit, expected,
                "oracle (LLVM+LLVM) exit for `{shape}` at O{opt} is {oracle_exit}, expected {expected}"
            );
            let combos = [
                (
                    Backend::TrustCg,
                    (Backend::Llvm, llvm_rlib.as_path()),
                    "LLVM callee + trust-cg caller",
                ),
                (
                    Backend::Llvm,
                    (Backend::TrustCg, tcg_rlib.as_path()),
                    "trust-cg callee + LLVM caller",
                ),
                (
                    Backend::TrustCg,
                    (Backend::TrustCg, tcg_rlib.as_path()),
                    "trust-cg callee + trust-cg caller",
                ),
            ];
            for (backend, rlib, label) in combos {
                match compile_caller_bin(&dir, &dylib, backend, opt, shape, body, rlib) {
                    Ok(bin) => match run_exit_code(&bin) {
                        Ok(exit) if exit == oracle_exit => {}
                        Ok(exit) => failures.push(format!(
                            "O{opt} `{shape}` {label}: exit {exit}, oracle {oracle_exit}"
                        )),
                        Err(e) => failures.push(format!("O{opt} `{shape}` {label}: {e}")),
                    },
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
        "{} argument-at-exhaustion combination(s) disagreed or refused:\n  {}",
        failures.len(),
        failures.join("\n  ")
    );
}
