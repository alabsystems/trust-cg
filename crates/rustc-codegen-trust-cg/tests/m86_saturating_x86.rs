#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential regression test for the saturating_add/sub completeness gap: the core
// `u8::saturating_add` (etc.) body uses the `saturating_add`/`saturating_sub` INTRINSIC
// the bridge did not lower — at -O0 the method was an out-of-line call whose body failed
// (undefined symbol -> link failure), and at -O3 the inlined intrinsic failed closed
// ("unsupported intrinsic `saturating_add`").
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE FIX (rustc-codegen-trust-cg/src/lib.rs): intercept the saturating_add/sub METHOD at
// the call site (-O0) AND the saturating_add/sub INTRINSIC in lower_intrinsic_call (-O3),
// both lowering to Inst::Overflow + a clamp select — unsigned add saturates to the
// all-ones MAX and unsigned sub to 0; signed saturates to T::MAX when lhs>=0 and T::MIN
// when lhs<0 (the overflow direction is the sign of the lhs). i128/u128 fail closed.
//
// Gated O0+O3 vs the LLVM oracle across unsigned/signed add/sub, saturating and not.

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
    assert!(status.success(), "cargo build failed; cannot run m83 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m83_{stem}_{}", std::process::id()));
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

/// Unsigned add saturation (u8 250+100 -> 255) and the non-saturating case.
#[test]
fn m86_u8_saturating_add_matches_llvm() {
    differential_program(
        "u8_add",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = bb(250u8).saturating_add(bb(100u8)); \
            let b = bb(10u8).saturating_add(bb(20u8)); \
            (((a as i32) & 0x40) + (b as i32)) & 0x7f }",
        // a=255 (&0x40=64), b=30: 64+30 = 94
        94,
    );
}

/// Unsigned sub saturation to 0 (u32 underflow).
#[test]
fn m86_u32_saturating_sub_matches_llvm() {
    differential_program(
        "u32_sub",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = bb(5u32).saturating_sub(bb(9u32)); \
            let b = bb(100u32).saturating_sub(bb(40u32)); \
            ((a as i32) + ((b % 100) as i32)) & 0x7f }",
        // a=0, b=60: 0+60 = 60
        60,
    );
}

/// Signed add saturation to MAX and MIN (i8), and the non-saturating case.
#[test]
fn m86_i8_saturating_add_sub_matches_llvm() {
    differential_program(
        "i8",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let d = bb(120i8).saturating_add(bb(50i8)); \
            let e = bb(-120i8).saturating_sub(bb(50i8)); \
            let f = bb(-100i8).saturating_add(bb(40i8)); \
            let mut s = 0i32; \
            if d == 127 { s += 1; } if e == -128 { s += 2; } if f == -60 { s += 4; } s }",
        // d=MAX(127), e=MIN(-128), f=-60: 1+2+4 = 7
        7,
    );
}

/// i64 saturating add at the i64::MAX boundary.
#[test]
fn m86_i64_saturating_add_matches_llvm() {
    differential_program(
        "i64",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = bb(i64::MAX - 5).saturating_add(bb(100i64)); \
            let b = bb(10i64).saturating_add(bb(20i64)); \
            (if a == i64::MAX { 8 } else { 0 } + (b as i32)) & 0x7f }",
        // a saturates to i64::MAX (8), b=30: 8+30 = 38
        38,
    );
}
