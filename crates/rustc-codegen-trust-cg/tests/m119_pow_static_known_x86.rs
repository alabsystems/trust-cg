#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential regression test for integer `pow` / `wrapping_pow` / `checked_pow`
// on x86_64, run under the DEFAULT per-compile proof gate (certs ON).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// COMPLETENESS FIX UNDER TEST. `{u,i}*::pow` (and `wrapping_pow`/`checked_pow`)
// reach the `is_val_statically_known` intrinsic in their libcore body (it gates a
// const-fold fast path). The bridge did not handle that intrinsic, so the whole
// `pow` family FAILED CLOSED. `is_val_statically_known(_) -> bool` is a const-eval
// HINT: it is ALWAYS SOUND to answer `false` (the contract permits a false
// negative), and in generated runtime code the operand is not a literal, so
// `false` is exactly what LLVM emits too. The bridge now lowers it to a constant
// `false` — declining only the const-fold fast path — which makes the reachable
// `pow` body lowerable. This test pins that the `pow` family now (a) COMPILES under
// the default proof gate (no fail-close) and (b) MATCHES LLVM bit-for-bit, for
// constant and runtime exponents across u32/i32/u64/i64/u8, including
// `wrapping_pow` and `checked_pow`. Oracle: rustc's own LLVM backend at
// -Copt-level 0 and 3; each result is reduced through `(bits-as-unsigned % 113)`.

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
    assert!(status.success(), "cargo build failed; cannot run m119 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m119_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn write_panic_stubs(dir: &Path, objs: &[PathBuf]) -> PathBuf {
    let mut nm = Command::new("nm");
    nm.arg("-u");
    for obj in objs {
        nm.arg(obj);
    }
    let nm = nm.output().expect("nm");
    let mut seen = std::collections::BTreeSet::new();
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if sym.contains("panic") && seen.insert(sym.to_owned()) {
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

/// The outcome of compiling+running one program with one backend.
enum Outcome {
    Exit(i32),
    /// The bridge failed to compile / link (fail-closed). Only trust-cg may fail closed.
    FailedClosed,
}

fn compile_link_run(stem: &str, body: &str, opt: &str, dylib: Option<&Path>) -> Outcome {
    let dir = workdir(stem);
    let src_path = dir.join("prog.rs");
    let src = format!(
        "#![no_std]\n#![no_main]\n\
         #[panic_handler]\nfn ph(_: &core::panic::PanicInfo) -> ! {{ loop {{}} }}\n\
         use core::hint::black_box as bb;\n{body}\n"
    );
    std::fs::write(&src_path, src).expect("write source");

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
        // Default proof gate (no TCG_NO_PROOF_CERTS): pow must compile AND prove.
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--emit=obj")
        .arg("--out-dir")
        .arg(&dir)
        .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    if !output.status.success() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!(
            "{stem} (opt={opt}, LLVM): failed to compile. stderr: <<<{}>>>",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    let objs: Vec<PathBuf> = std::fs::read_dir(&dir)
        .expect("read workdir")
        .filter_map(|e| e.ok().map(|e| e.path()))
        .filter(|p| p.extension().is_some_and(|x| x == "o"))
        .collect();
    if objs.is_empty() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!("{stem} (opt={opt}, LLVM): no object file produced");
    }

    let stubs_path = write_panic_stubs(&dir, &objs);

    let bin = dir.join("bin");
    let mut link = Command::new("cc");
    link.arg("-o").arg(&bin);
    for obj in &objs {
        link.arg(obj);
    }
    link.arg(&stubs_path);
    let link = link.output().expect("cc link");
    if !link.status.success() {
        let _ = std::fs::remove_dir_all(&dir);
        if dylib.is_some() {
            return Outcome::FailedClosed;
        }
        panic!(
            "{stem} (opt={opt}, LLVM): link failed. stderr: <<<{}>>>",
            String::from_utf8_lossy(&link.stderr)
        );
    }

    let run = Command::new(&bin).output().expect("run compiled binary");
    let _ = std::fs::remove_dir_all(&dir);
    Outcome::Exit(run.status.code().expect("process terminated by signal"))
}

/// Exact MATCH at BOTH opt levels under DEFAULT certs (pow must compile — not fail
/// closed — and match LLVM). The pow body composes over already-proven primitives.
fn matches_both_opts(stem: &str, body: &str, expected: i32) {
    if !x86_64_std_available() {
        eprintln!("skipping {stem}: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    if !cfg!(target_arch = "x86_64") {
        eprintln!("skipping {stem} execution: host is not x86_64");
        return;
    }
    let dylib = ensure_dylib_built();
    for opt in ["0", "3"] {
        let llvm = match compile_link_run(stem, body, opt, None) {
            Outcome::Exit(code) => code,
            Outcome::FailedClosed => unreachable!("LLVM never fails closed"),
        };
        assert_eq!(
            llvm, expected,
            "{stem} (opt={opt}): LLVM oracle returned {llvm}, expected {expected}"
        );
        match compile_link_run(stem, body, opt, Some(&dylib)) {
            Outcome::Exit(trust) => assert_eq!(
                trust, llvm,
                "{stem} (opt={opt}): trust-cg returned {trust} but LLVM returned {llvm} (pow MISCOMPILE)"
            ),
            Outcome::FailedClosed => panic!(
                "{stem} (opt={opt}): trust-cg unexpectedly FAILED CLOSED — pow must compile + prove \
                 (the is_val_statically_known completeness fix regressed)"
            ),
        }
    }
}

fn main_prog(body_expr: &str) -> String {
    format!("#[no_mangle] pub extern \"C\" fn main()->i32{{ {body_expr} }}")
}

#[test]
fn u32_pow_constant_exponent() {
    matches_both_opts("u32_pow3", &main_prog("let x:u32=bb(1000); ((x.pow(3) as u64)%113) as i32"), 59);
}
#[test]
fn u32_pow_runtime_exponent() {
    matches_both_opts("u32_pow_rt", &main_prog("let x:u32=bb(7); ((x.pow(bb(5)) as u64)%113) as i32"), 83);
}
#[test]
fn i32_pow_negative_base() {
    matches_both_opts("i32_pow_neg", &main_prog("let x:i32=bb(-3); ((x.pow(7) as u32 as u64)%113) as i32"), 89);
}
#[test]
fn u64_pow() {
    matches_both_opts("u64_pow", &main_prog("let x:u64=bb(11); ((x.pow(6))%113) as i32"), 60);
}
#[test]
fn u32_pow_large_runtime_exponent() {
    matches_both_opts("u32_pow_big", &main_prog("let x:u32=bb(2); ((x.pow(bb(20)) as u64)%113) as i32"), 49);
}
#[test]
fn i64_pow_runtime_exponent() {
    matches_both_opts("i64_pow_rt", &main_prog("let x:i64=bb(5); ((x.pow(bb(8)) as u64)%113) as i32"), 97);
}
#[test]
fn u8_wrapping_pow() {
    matches_both_opts("u8_wpow", &main_prog("let x:u8=bb(3); ((x.wrapping_pow(bb(6)) as u64)%113) as i32"), 104);
}
#[test]
fn u32_checked_pow() {
    matches_both_opts(
        "u32_cpow",
        &main_prog("let b:u32=bb(13); let e:u32=bb(4); ((b.checked_pow(e).unwrap_or(0) as u64)%113) as i32"),
        85,
    );
}
