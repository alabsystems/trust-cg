#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: real integer-compute Rust programs compiled to runnable
// x86_64 binaries via the rustc_codegen_trust_cg bridge.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS4 Phase 1 — first CORRECT execution of real integer compute.
//
// These cases exercise the parts of the bridge that turn real Rust into
// running machine code: arithmetic, branches, and (critically) multi-basic-block
// control flow with loops. Loops are the decisive case: a loop header is reached
// from a back-edge predecessor that is lowered *after* the header, which used to
// drop the loop-carried locals' SSA values and produce
// `value Value(N) not defined before use` in trust-cg ISel. The fix threads
// loop-carried scalar locals through trust-ir block parameters at the header.
//
// Each program is a `#![no_std] #![no_main]` crate exposing
// `#[no_mangle] pub extern "C" fn main() -> i32`, compiled with
// `-Cpanic=abort -Coverflow-checks=off` and linked with the C runtime via `cc`,
// so the process exit code IS the computed value (verified with `echo $?`).
//
// The bridge compiles the crate's `main` directly (no `std::rt::lang_start`
// entry wrapper) and drops the unreachable Rust-internal panic shim. To keep the
// link self-contained the harness supplies abort stubs for any `panic_const_*`
// symbols the object references (these checks never fire at the chosen inputs).
//
// Execution assertions only run on an x86_64 host (native Mach-O execution).

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run compute test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_compute_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Compile `src` via the bridge for x86_64, link with `cc` (plus abort stubs for
/// any referenced `panic_const_*` symbols), run, and return the process exit code.
fn compile_link_run(stem: &str, src: &str) -> i32 {
    let dylib = ensure_dylib_built();
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");

    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    let obj_out = dir.join("obj");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin")
        .arg(&backend_arg)
        .args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg("--emit=obj")
        .arg("-o")
        .arg(&obj_out)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{stem}: bridge failed to compile compute program. stderr: <<<{stderr}>>>"
    );

    // The bridge names the object after the `main` CGU; find the emitted .o.
    let obj = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .find(|p| p.extension().is_some_and(|x| x == "o"))
        .unwrap_or_else(|| panic!("{stem}: bridge produced no object file"));

    // Generate abort stubs for any undefined panic_const_* symbols so the object
    // links standalone (these checks never fire at the chosen inputs).
    let nm = Command::new("nm").arg("-u").arg(&obj).output().expect("nm");
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

    let bin = dir.join("bin");
    let link = Command::new("cc")
        .arg("-o")
        .arg(&bin)
        .arg(&obj)
        .arg(&stubs_path)
        .output()
        .expect("cc link");
    assert!(
        link.status.success(),
        "{stem}: link failed. stderr: <<<{}>>>",
        String::from_utf8_lossy(&link.stderr)
    );

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    run.status.code().expect("process terminated by signal")
}

const HDR: &str = "#![no_std]\n#![no_main]\n\
    #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! { loop {} }\n";

fn case(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let src = format!(
        "{HDR}#[no_mangle]\npub extern \"C\" fn main() -> i32 {{\n{body}\n}}\n"
    );
    let got = compile_link_run(stem, &src);
    assert_eq!(
        got, expected,
        "{stem}: trust-cg-compiled binary returned {got}, expected {expected}"
    );
}

#[test]
fn loop_sum_1_to_10_returns_55() {
    case(
        "sum",
        "    let mut sum: i32 = 0;\n    let mut i: i32 = 1;\n\
         while i <= 10 { sum += i; i += 1; }\n    sum",
        55,
    );
}

#[test]
fn factorial_5_returns_120() {
    case(
        "fact",
        "    let mut f: i32 = 1;\n    let mut i: i32 = 1;\n\
         while i <= 5 { f *= i; i += 1; }\n    f & 0xff",
        120,
    );
}

#[test]
fn euclid_gcd_48_36_returns_12() {
    case(
        "gcd",
        "    let mut a: i32 = 48;\n    let mut b: i32 = 36;\n\
         while b != 0 { let t = b; b = a % b; a = t; }\n    a",
        12,
    );
}

#[test]
fn nested_loops_triangular_sum_returns_35() {
    case(
        "nested",
        "    let mut total: i32 = 0;\n    let mut i: i32 = 1;\n\
         while i <= 5 {\n        let mut j: i32 = 1;\n\
         while j <= i { total += j; j += 1; }\n        i += 1;\n    }\n    total",
        35,
    );
}

#[test]
fn branch_heavy_loop_returns_72() {
    case(
        "branch",
        "    let mut acc: i32 = 0;\n    let mut i: i32 = 0;\n\
         while i < 20 {\n        if i % 3 == 0 { acc += i; }\n\
         else if i % 5 == 0 { acc -= 1; }\n        else { acc += 1; }\n        i += 1;\n    }\n\
         acc & 0xff",
        72,
    );
}
