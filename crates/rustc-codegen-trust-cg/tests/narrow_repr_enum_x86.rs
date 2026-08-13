// Integration test: NARROW-REPR (`#[repr(u8)]` / `#[repr(u16)]` / `#[repr(i8)]`)
// fieldless enums matched BY VALUE, compiled for x86_64 via the
// rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN at BOTH `-Copt-level=0`
// and `-Copt-level=3`, with exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Regression for bug #55: a narrow-repr fieldless enum matched by value selected
// the WRONG arm. Two independent defects combined:
//
//   1. The backend `select_switch` compared the discriminant SELECTOR at full GPR
//      width (`cmpl`) while a 1-/2-byte enum tag was loaded with a partial-width
//      `movb`/`movw`, leaving the register's high bits undefined. The compare then
//      tested those garbage bits and fell through to the (unreachable) default
//      arm. The fix zero-extends the selector before the compare, exactly as
//      `select_icmp` does (an equality switch makes Movzx always sound).
//
//   2. At O2/O3 the const-folded variant constructor (`_0 = E::A`) arrived as a
//      bare const `Use` into the memory-backed return slot, which the bridge could
//      not store (it fell closed, breaking the link). The fix const-evaluates a
//      whole-aggregate const enum into the slot's discriminant tag.
//
// `#[repr(u32)]` / `#[repr(u64)]` enums (whose tag fills the GPR) already worked;
// the bug was specific to the NARROW tag widths, so all five reprs are exercised
// here as a differential against LLVM at both opt levels.

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
    assert!(status.success(), "cargo build failed; cannot run narrow-repr enum test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_nrenum_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
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
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend, -Copt-level={opt}). stderr: <<<{}>>>",
        if backend.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr),
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

/// The full differential: each narrow-repr enum `fn main` is compiled by trust-cg
/// AND LLVM at `-Copt-level=0` and `-Copt-level=3`, run, and the exit codes must
/// match each other and the expected value.
#[test]
fn narrow_repr_fieldless_enum_match_by_value_runs_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("shapes");

    // (name, source, expected exit code). Each program returns an enum BY VALUE
    // from a non-inlined `pick`, then matches it in a non-inlined `fm`, so the
    // discriminant crosses a real call boundary and is decoded from the narrow
    // tag — the exact path bug #55 corrupted.
    let shapes: &[(&str, &str, i32)] = &[
        // The keystone: repr(u8) 2-variant fieldless enum, implicit discriminants.
        (
            "repr_u8_implicit",
            "#[repr(u8)] #[derive(Clone,Copy)] enum E { A, B } \
             #[inline(never)] fn pick(i: u32) -> E { match i%2 {0=>E::A,_=>E::B} } \
             #[inline(never)] fn fm(e: E) -> u8 { match e { E::A=>10, E::B=>20 } } \
             fn main(){ std::process::exit(fm(pick(0)) as i32); }",
            10,
        ),
        // repr(u8) with EXPLICIT discriminants where A != index (A=1, B=0): the
        // discriminant decode must use the declared values, not the variant index.
        (
            "repr_u8_explicit",
            "#[repr(u8)] #[derive(Clone,Copy)] enum E { A = 1, B = 0 } \
             #[inline(never)] fn pick(i: u32) -> E { match i%2 {0=>E::A,_=>E::B} } \
             #[inline(never)] fn fm(e: E) -> u8 { match e { E::A=>10, E::B=>20 } } \
             fn main(){ std::process::exit(fm(pick(0)) as i32); }",
            10,
        ),
        // repr(u8), selecting the SECOND arm (B), so a stray-high-bit compare would
        // miss both 0 and 1 and trap rather than return 20.
        (
            "repr_u8_arm_b",
            "#[repr(u8)] #[derive(Clone,Copy)] enum E { A, B } \
             #[inline(never)] fn pick(i: u32) -> E { match i%2 {0=>E::A,_=>E::B} } \
             #[inline(never)] fn fm(e: E) -> u8 { match e { E::A=>10, E::B=>20 } } \
             fn main(){ std::process::exit(fm(pick(1)) as i32); }",
            20,
        ),
        // repr(u8), match INLINE in main (the value returned by `pick`).
        (
            "repr_u8_inline_match",
            "#[repr(u8)] #[derive(Clone,Copy)] enum E { A, B } \
             #[inline(never)] fn pick(i: u32) -> E { match i%2 {0=>E::A,_=>E::B} } \
             fn main(){ let e = pick(0); let r = match e { E::A=>10u8, E::B=>20 }; \
             std::process::exit(r as i32); }",
            10,
        ),
        // repr(u16): a 2-byte tag (also partial-width loaded).
        (
            "repr_u16",
            "#[repr(u16)] #[derive(Clone,Copy)] enum E { A, B } \
             #[inline(never)] fn pick(i: u32) -> E { match i%2 {0=>E::A,_=>E::B} } \
             #[inline(never)] fn fm(e: E) -> u8 { match e { E::A=>10, E::B=>20 } } \
             fn main(){ std::process::exit(fm(pick(0)) as i32); }",
            10,
        ),
        // repr(i8): a SIGNED narrow tag (Movzx is still sound for an equality switch).
        (
            "repr_i8",
            "#[repr(i8)] #[derive(Clone,Copy)] enum E { A, B } \
             #[inline(never)] fn pick(i: u32) -> E { match i%2 {0=>E::A,_=>E::B} } \
             #[inline(never)] fn fm(e: E) -> u8 { match e { E::A=>10, E::B=>20 } } \
             fn main(){ std::process::exit(fm(pick(1)) as i32); }",
            20,
        ),
        // repr(u32): the previously-WORKING wide tag — kept as a guard that the
        // selector zero-extension did not break the already-correct full-width case.
        (
            "repr_u32",
            "#[repr(u32)] #[derive(Clone,Copy)] enum E { A, B } \
             #[inline(never)] fn pick(i: u32) -> E { match i%2 {0=>E::A,_=>E::B} } \
             #[inline(never)] fn fm(e: E) -> u8 { match e { E::A=>10, E::B=>20 } } \
             fn main(){ std::process::exit(fm(pick(0)) as i32); }",
            10,
        ),
        // A 3-variant narrow-repr enum exercising more than two switch cases.
        (
            "repr_u8_three",
            "#[repr(u8)] #[derive(Clone,Copy)] enum E { A, B, C } \
             #[inline(never)] fn pick(i: u32) -> E { match i%3 {0=>E::A,1=>E::B,_=>E::C} } \
             #[inline(never)] fn fm(e: E) -> u8 { match e { E::A=>10, E::B=>20, E::C=>30 } } \
             fn main(){ std::process::exit(fm(pick(2)) as i32); }",
            30,
        ),
    ];

    for opt in ["0", "3"] {
        for (name, src, expected) in shapes {
            let llvm_bin = compile(&dir, &format!("{name}_llvm_o{opt}"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_tcg_o{opt}"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` (-Copt-level={opt}) was {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit for `{name}` (-Copt-level={opt}) was {tcg_exit}, LLVM was {llvm_exit}"
            );
        }
    }
}
