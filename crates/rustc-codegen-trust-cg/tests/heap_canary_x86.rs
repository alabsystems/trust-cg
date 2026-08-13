// Integration test: FAST heap-envelope CANARY for the trust-cg bridge on
// x86_64 — Vec/Box programs COMPILED, LINKED, and RUN through the bridge lane
// only, with exit codes asserted, at BOTH -Copt-level=0 and -Copt-level=3.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// WHY THIS EXISTS (COMPLETE-2): the Vec/Box heap regression fixed by 0456e2a
// ("reachability-GC the emitted mono items — Box/Vec compile again") shipped
// across ~5 commits because the heavier heap suites were evidently not run
// per-commit. This canary is the cheap always-run tripwire: it compiles and
// runs three minimal heap programs (Vec::new/push/len/index sum -> 55,
// Box::new(42i32) deref -> 42, Vec::with_capacity grow+drop -> 55) through
// the BRIDGE ONLY at O0 and O3 and asserts the exit codes. A fail-closed
// regression of the heap envelope (compile error) or a miscompile (wrong
// exit) both trip it in well under a minute.
//
// The LLVM differential for these shapes is already covered by vec_x86.rs and
// heap_types_x86.rs; this file deliberately skips the LLVM lane so it stays
// fast enough to run on every landing.
//
// RULE (codified here per COMPLETE-2): any commit touching the bridge
// lib.rs lowering paths must run this canary plus the default-certs canary
// before push:
//   cargo test --release -p rustc-codegen-trust-cg --test heap_canary_x86

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
    let target_dir = std::env::var_os("CARGO_TARGET_DIR")
        .map(PathBuf::from)
        .unwrap_or_else(|| crate_dir.join("target"));
    let candidates = [
        target_dir
            .join("release")
            .join("librustc_codegen_trust_cg.dylib"),
        target_dir
            .join("debug")
            .join("librustc_codegen_trust_cg.dylib"),
    ];
    for cand in &candidates {
        if cand.exists() {
            return cand.clone();
        }
    }
    let status = Command::new("cargo")
        .arg(format!("+{}", pinned_toolchain()))
        .args(["build"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(
        status.success(),
        "cargo build failed; cannot run heap canary"
    );
    let built = target_dir
        .join("debug")
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

fn host_is_x86_64() -> bool {
    cfg!(target_arch = "x86_64")
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_heapcanary_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the trust-cg bridge at the given `-Copt-level`. Unlike
/// vec_x86.rs's differential helper, this is bridge-lane only (no LLVM
/// compile) so the whole canary stays fast.
fn compile_bridge(dir: &Path, name: &str, src: &str, dylib: &Path, opt_level: &str) -> PathBuf {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"])
        .arg(backend_arg(dylib))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt_level}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    assert!(
        output.status.success(),
        "heap-envelope FAIL-CLOSED regression: trust-cg compile of `{name}` at \
         -Copt-level={opt_level} failed (Vec/Box must keep compiling; see 0456e2a). \
         stderr: <<<{}>>>",
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The canary proper: each heap program must COMPILE (no fail-closed) and RUN
/// to its expected exit code through the bridge at both O0 and O3.
#[test]
fn heap_canary_vec_box_compile_and_run_o0_o3() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("run");

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        // (a) Vec::new + push 1..=10 + len/index sum -> exit 55.
        (
            "vec_new_push_index_sum",
            "fn main() { let mut v: Vec<i64> = Vec::new(); let mut i = 1i64; \
             while i <= 10 { v.push(i); i += 1; } let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } std::process::exit(s as i32); }",
            55,
        ),
        // (b) Box::new(42i32) + deref -> exit 42 (the box42 canary of the
        // executor protocol's canary battery).
        (
            "box_new_deref",
            "fn main() { let b = Box::new(42i32); std::process::exit(*b); }",
            42,
        ),
        // (c) Vec::with_capacity(4) + push past capacity (forces a grow) +
        // sum; the Vec is DROPPED (freed) on the normal return from `build`
        // before main exits, so the __rust_dealloc path runs too.
        (
            "vec_with_capacity_grow_drop",
            "fn build() -> i64 { let mut v: Vec<i64> = Vec::with_capacity(4); \
             let mut i = 1i64; while i <= 10 { v.push(i); i += 1; } \
             let mut s = 0i64; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } s } \
             fn main() { std::process::exit(build() as i32); }",
            55,
        ),
    ];

    for opt_level in ["0", "3"] {
        for (name, src, expected) in shapes {
            let bin = compile_bridge(
                &dir,
                &format!("{name}_o{opt_level}"),
                src,
                &dylib,
                opt_level,
            );
            let exit = run_exit_code(&bin);
            assert_eq!(
                exit, *expected,
                "heap-envelope MISCOMPILE: trust-cg exit code for `{name}` at \
                 -Copt-level={opt_level} is {exit}, expected {expected}"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
