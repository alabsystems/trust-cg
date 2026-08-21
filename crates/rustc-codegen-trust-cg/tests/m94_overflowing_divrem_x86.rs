#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: `x.overflowing_div(y)` / `x.overflowing_rem(y)` -> `(iN, bool)`.
//
// The bridge intercepts the `overflowing_div`/`overflowing_rem` method calls (whose
// `(iN, bool)` return previously failed closed as "unsupported MIR Ty::(iN, bool)") and
// synthesizes the tuple from already-proven primitives: the wrapping quotient/remainder
// plus the `self == MIN && rhs == -1` overflow predicate. x86 IDIV traps on BOTH `/0`
// AND the `MIN/-1` overflow, but Rust's `overflowing_div` must return `(MIN, true)` (and
// `overflowing_rem` `(0, true)`) WITHOUT trapping for `MIN/-1`, while still panicking on
// `/0`. The lowering divides by a SAFE divisor `select(overflowed, 1, rhs)` and overrides
// the result on overflow, so the IDIV never hits the `MIN/-1` trap but `/0` still traps.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Each case is a FULL-PROGRAM differential: the same source is compiled by BOTH the
// trust-cg bridge AND the stock LLVM backend, both run, and the trust-cg exit code MUST
// equal the LLVM exit code (and the LLVM oracle the expected value). A wrong quotient,
// remainder, overflow flag, or a spurious IDIV trap on `MIN/-1` shows up as a mismatch.
//
// NOT covered here (verified manually, cannot run in a value-returning harness):
//   * `/0` MUST still panic (both backends trap by signal — no wrong value);
//   * an overflow `(iN, bool)` tuple RETURNED BY VALUE fails closed (memory-backed
//     destination) rather than miscompiling.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";

fn pinned_toolchain() -> String {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let toolchain = std::fs::read_to_string(crate_dir.join("rust-toolchain.toml"))
        .expect("failed to read rust-toolchain.toml");
    for line in toolchain.lines() {
        let line = line.trim();
        if let Some(raw_channel) = line.strip_prefix("channel") {
            let Some((_, value)) = raw_channel.split_once('=') else {
                continue;
            };
            return value.trim().trim_matches('"').to_owned();
        }
    }
    panic!("rust-toolchain.toml did not contain a channel");
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let candidates = [
        target_dir.join("release").join("librustc_codegen_trust_cg.dylib"),
        target_dir.join("debug").join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m94 test");
    let built = target_dir
        .join("release")
        .join("librustc_codegen_trust_cg.dylib");
    assert!(built.exists(), "expected dylib at {built:?} but none produced");
    built
}

fn x86_64_std_available() -> bool {
    let output = Command::new("rustup")
        .args(["target", "list", "--installed", "--toolchain"])
        .arg(pinned_toolchain())
        .output();
    match output {
        Ok(output) => String::from_utf8_lossy(&output.stdout)
            .lines()
            .any(|line| line.trim() == TARGET),
        Err(_) => false,
    }
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m94_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn write_panic_stubs(dir: &Path, obj: &Path) -> PathBuf {
    let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if sym.contains("panic") {
            let c = sym.strip_prefix('_').unwrap_or(sym);
            stubs.push_str(&format!(
                "void {c}(void) __asm__(\"{sym}\"); void {c}(void){{ abort(); }}\n"
            ));
        }
    }
    let stubs_path = dir.join("stubs.c");
    std::fs::write(&stubs_path, stubs).expect("write stubs");
    stubs_path
}

fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> i32 {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{stem} (opt={opt}, backend={}): failed to compile. stderr: <<<{stderr}>>>",
        if dylib.is_some() { "trust-cg" } else { "llvm" }
    );

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    assert!(!objs.is_empty(), "{stem} (opt={opt}): no object file produced");

    let stubs_path = write_panic_stubs(&dir, &objs[0]);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    assert!(
        link.status.success(),
        "{stem} (opt={opt}): link failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    run.status.code().expect("process terminated by signal")
}

fn differential_program(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    let src = format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box as bb;\n{body}\n"
    );
    for opt in ["0", "3"] {
        let llvm = compile_link_run(stem, &src, opt, None);
        let trust = compile_link_run(stem, &src, opt, Some(&dylib));
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        assert_eq!(
            trust, llvm,
            "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} (miscompile)"
        );
    }
}

/// THE overflow case: `i32::MIN / -1` must yield `(i32::MIN, true)` WITHOUT trapping.
#[test]
fn m94_div_i32_min_neg1_overflows() {
    differential_program(
        "div_i32_min_neg1",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (q, o) = bb(i32::MIN).overflowing_div(bb(-1)); \
            ((if o { 64 } else { 0 }) + (if q == i32::MIN { 42 } else { 0 })) & 0x7f }",
        106,
    );
}

/// `i32::MIN % -1` must yield `(0, true)` WITHOUT trapping.
#[test]
fn m94_rem_i32_min_neg1_overflows() {
    differential_program(
        "rem_i32_min_neg1",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (q, o) = bb(i32::MIN).overflowing_rem(bb(-1)); \
            ((if o { 64 } else { 0 }) + q) & 0x7f }",
        64,
    );
}

/// `i64::MIN / -1` (64-bit width) overflow path.
#[test]
fn m94_div_i64_min_neg1_overflows() {
    differential_program(
        "div_i64_min_neg1",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (q, o) = bb(i64::MIN).overflowing_div(bb(-1i64)); \
            ((if o { 64 } else { 0 }) + (if q == i64::MIN { 42 } else { 0 })) & 0x7f }",
        106,
    );
}

/// `i8::MIN / -1` (8-bit width) overflow path.
#[test]
fn m94_div_i8_min_neg1_overflows() {
    differential_program(
        "div_i8_min_neg1",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (q, o) = bb(i8::MIN).overflowing_div(bb(-1i8)); \
            ((if o { 64 } else { 0 }) + (if q == i8::MIN { 42 } else { 0 })) & 0x7f }",
        106,
    );
}

/// Signed division truncates toward zero; no overflow.
#[test]
fn m94_div_signed_trunc_no_overflow() {
    differential_program(
        "div_signed_trunc",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (q, o) = bb(-17i32).overflowing_div(bb(5)); \
            ((q + 100) + (if o { 1 } else { 0 })) & 0x7f }",
        97, // -17 / 5 = -3 (trunc toward 0); -3 + 100 = 97; overflow false
    );
}

/// Signed remainder takes the sign of the dividend; no overflow.
#[test]
fn m94_rem_signed_sign_of_dividend() {
    differential_program(
        "rem_signed",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (q, o) = bb(-17i32).overflowing_rem(bb(5)); \
            ((q + 100) + (if o { 1 } else { 0 })) & 0x7f }",
        98, // -17 % 5 = -2; -2 + 100 = 98; overflow false
    );
}

/// Unsigned division never overflows.
#[test]
fn m94_div_unsigned_no_overflow() {
    differential_program(
        "div_unsigned",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (q, o) = bb(17u32).overflowing_div(bb(5)); \
            ((q as i32) + (if o { 64 } else { 0 })) & 0x7f }",
        3,
    );
}

/// Unsigned remainder never overflows.
#[test]
fn m94_rem_unsigned_no_overflow() {
    differential_program(
        "rem_unsigned",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let (q, o) = bb(17u32).overflowing_rem(bb(5)); \
            ((q as i32) + (if o { 64 } else { 0 })) & 0x7f }",
        2,
    );
}
