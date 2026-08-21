#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: MEMORY-MODEL lowering of by-value aggregates that cross a
// CALL/RETURN boundary, compiled for x86_64 via the rustc_codegen_trust_cg
// bridge — COMPILED, LINKED, and RUN, with exit codes checked against the
// default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The keystone covered here is a real Rust aggregate (a `Result<i64,i64>` enum,
// a custom multi-variant enum, a multi-field struct) RETURNED FROM A CALL by
// value and then consumed (matched / projected) WITHOUT bespoke interception.
// The bridge gives such a local a real stack slot (`Inst::Alloca` of the layout
// size/align), constructs/reads it through typed `Store`/`Load`s at the layout's
// field/tag offsets, and crosses the call boundary through the backend's
// already-verified System V aggregate ABI (small aggregates in RAX:RDX). This
// was previously a FAIL-CLOSED blocker — the multi-variant enum / multi-field
// struct return type had no single trust-ir scalar representation.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). This is a strict
// differential: a miscompile shows up as a mismatched exit code.

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
    assert!(status.success(), "cargo build failed; cannot run memory-model test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_mm_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with the given backend (None = default LLVM). On success returns
/// `Ok(binary_path)`; on a compile failure returns `Err(stderr)`.
fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
) -> Result<PathBuf, String> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if output.status.success() {
        Ok(bin)
    } else {
        Err(String::from_utf8_lossy(&output.stderr).into_owned())
    }
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    match try_compile(dir, name, src, backend) {
        Ok(bin) => bin,
        Err(stderr) => panic!(
            "compile of `{name}` failed ({} backend). stderr: <<<{stderr}>>>",
            if backend.is_some() { "trust-cg" } else { "llvm" },
        ),
    }
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The full differential: each by-value-aggregate-from-a-call `fn main` is
/// compiled by trust-cg AND LLVM, run, and the exit codes must match each other
/// and the expected value. `#[inline(never)]` on the maker keeps the aggregate
/// crossing a real call/return boundary (not inlined away), so the memory-model
/// path is genuinely exercised.
#[test]
fn by_value_aggregate_returns_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("aggregates");

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // THE KEYSTONE: a by-value `Result<i64,i64>` returned from a call and
        // matched. Static `Ok` arm.
        (
            "result_ok",
            "#[inline(never)] fn make(ok: bool) -> Result<i64,i64> { if ok { Ok(42) } else { Err(7) } } \
             fn main(){ let r = make(true); let v = match r { Ok(x)=>x, Err(e)=>e+100 }; \
             std::process::exit(v as i32); }",
            42,
        ),
        // Static `Err` arm (exercises the second variant's payload + tag value 1).
        (
            "result_err",
            "#[inline(never)] fn make(ok: bool) -> Result<i64,i64> { if ok { Ok(42) } else { Err(7) } } \
             fn main(){ let r = make(false); let v = match r { Ok(x)=>x, Err(e)=>e+100 }; \
             std::process::exit(v as i32); }",
            107,
        ),
        // Runtime-chosen variant (the discriminant is a *runtime* tag load, not a
        // compile-time constant): black_box hides the bool so the maker really
        // branches and `discriminant(_1)` must read the slot's tag word.
        (
            "result_runtime_ok",
            "use std::hint::black_box; \
             #[inline(never)] fn make(ok: bool) -> Result<i64,i64> { if ok { Ok(42) } else { Err(7) } } \
             fn main(){ let r = make(black_box(true)); let v = match r { Ok(x)=>x, Err(e)=>e+100 }; \
             std::process::exit(v as i32); }",
            42,
        ),
        (
            "result_runtime_err",
            "use std::hint::black_box; \
             #[inline(never)] fn make(ok: bool) -> Result<i64,i64> { if ok { Ok(42) } else { Err(7) } } \
             fn main(){ let r = make(black_box(false)); let v = match r { Ok(x)=>x, Err(e)=>e+100 }; \
             std::process::exit(v as i32); }",
            107,
        ),
        // A custom 3-variant enum (unit / single-payload / two-payload) returned
        // by value from a call and matched, runtime-selected.
        (
            "enum3_c",
            "use std::hint::black_box; \
             enum E { A, B(i64), C(i64,i64) } \
             #[inline(never)] fn make(n: i64) -> E { if n==0 {E::A} else if n==1 {E::B(17)} else {E::C(11,22)} } \
             fn main(){ let e = make(black_box(2)); \
             let r = match e { E::A=>1, E::B(x)=>x, E::C(a,b)=>a+b }; \
             std::process::exit(r as i32); }",
            33,
        ),
        (
            "enum3_b",
            "use std::hint::black_box; \
             enum E { A, B(i64), C(i64,i64) } \
             #[inline(never)] fn make(n: i64) -> E { if n==0 {E::A} else if n==1 {E::B(17)} else {E::C(11,22)} } \
             fn main(){ let e = make(black_box(1)); \
             let r = match e { E::A=>1, E::B(x)=>x, E::C(a,b)=>a+b }; \
             std::process::exit(r as i32); }",
            17,
        ),
        // An explicit-discriminant enum (tag value != variant index; tag is a
        // narrow i8 here): the SwitchInt must compare the *discriminant*.
        (
            "enum_explicit",
            "use std::hint::black_box; \
             enum E { A=10, B=20, C=30 } \
             #[inline(never)] fn make(n: i64) -> E { if n==0 {E::A} else if n==1 {E::B} else {E::C} } \
             fn main(){ let e = make(black_box(1)); \
             let r = match e { E::A=>1, E::B=>20, E::C=>3 }; \
             std::process::exit(r); }",
            20,
        ),
        // A multi-field struct returned by value from a call, fields projected
        // and summed (a 16-byte two-eightbyte INTEGER aggregate -> RAX:RDX).
        (
            "struct_pair",
            "use std::hint::black_box; \
             struct P { a: i64, b: i64 } \
             #[inline(never)] fn make(x: i64) -> P { P { a: x, b: x*2 } } \
             fn main(){ let p = make(black_box(5)); std::process::exit((p.a + p.b) as i32); }",
            15,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib));
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM backend exit code for `{name}` is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for `{name}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
