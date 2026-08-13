// Differential regression test for MISCOMPILE #75: generic arithmetic via a trait
// operator (`<T as Add/Sub/Mul/Neg>::op`) TRAPPED (SIGILL) on overflow instead of
// WRAPPING under -Coverflow-checks=off.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. The core arithmetic operator impls carry
// `#[rustc_inherit_overflow_checks]`: their overflow check is governed by the
// INSTANTIATING crate's `-Coverflow-checks`, and rustc REMOVES it (the arithmetic
// then wraps) when checks are off. But a `-Zcodegen-backend` pulls the
// monomorphized `<u8 as Add>::add` body via `tcx.instance_mir` with that
// `Assert(Overflow)` still PRESENT — rustc applies the removal in its OWN codegen,
// which the bridge bypasses. Lowering the assert as an unconditional
// conditional-trap then makes generic arithmetic that overflows die on a `ud2`
// (SIGILL) where it must wrap. DIRECT `x + y` and a NON-generic `fn add(u8,u8)`
// were unaffected (the user crate's own MIR already had the assert removed) — only
// the generic trait-method path trapped.
//
// THE FIX (in rustc-codegen-trust-cg/src/lib.rs `lower_assert_terminator`). Skip an
// `Overflow` / `OverflowNeg` assert (branch straight to the success target) when
// `tcx.sess.overflow_checks()` is false, mirroring rustc's own removal. Only the
// overflow-category asserts are gated this way; DivisionByZero / RemainderByZero /
// BoundsCheck / pointer-validity asserts keep their trap, and when overflow checks
// are ON the assert is preserved unchanged.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 0 and 3. `black_box` materializes the operands so the
// overflow is a real runtime event.

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m75 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m75_{stem}_{}", std::process::id()));
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

const ADD: &str = "#[inline(never)] fn add<T: Copy + core::ops::Add<Output=T>>(x: T, y: T) -> T { x + y }\n";
const SUB: &str = "#[inline(never)] fn sub<T: Copy + core::ops::Sub<Output=T>>(x: T, y: T) -> T { x - y }\n";
const MUL: &str = "#[inline(never)] fn mul<T: Copy + core::ops::Mul<Output=T>>(x: T, y: T) -> T { x * y }\n";
const NEG: &str = "#[inline(never)] fn neg<T: Copy + core::ops::Neg<Output=T>>(x: T) -> T { -x }\n";

/// Generic `add::<u8>(200, 100)` must WRAP to 44 (was SIGILL).
#[test]
fn m75_generic_add_u8_overflow_wraps_matches_llvm() {
    differential_program(
        "add_u8",
        &format!("{ADD}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            (add::<u8>(bb(200u8), bb(100u8)) as i32) & 0xff }}"),
        44,
    );
}

/// Generic `neg::<i32>(i32::MIN)` must WRAP to i32::MIN (low byte 0) (was SIGILL).
#[test]
fn m75_generic_neg_i32_min_wraps_matches_llvm() {
    differential_program(
        "neg_i32min",
        &format!("{NEG}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            (neg::<i32>(bb(i32::MIN)) & 0xff) as i32 }}"),
        0,
    );
}

/// Generic `mul::<u8>(20, 20)` must WRAP to 144 (400 mod 256).
#[test]
fn m75_generic_mul_u8_overflow_wraps_matches_llvm() {
    differential_program(
        "mul_u8",
        &format!("{MUL}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            (mul::<u8>(bb(20u8), bb(20u8)) as i32) & 0xff }}"),
        // 20*20 = 400; 400 mod 256 = 144
        144,
    );
}

/// Generic `sub::<u16>(10, 50)` must WRAP (underflow) to 65496 (low byte 216).
#[test]
fn m75_generic_sub_u16_underflow_wraps_matches_llvm() {
    differential_program(
        "sub_u16",
        &format!("{SUB}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            (sub::<u16>(bb(10u16), bb(50u16)) as i32) & 0xff }}"),
        // 10 - 50 wraps to 65536 - 40 = 65496; 65496 & 0xff = 216
        216,
    );
}

/// Composed generic `(x + y) * y` over u8 and u16 with inner overflow.
#[test]
fn m75_generic_composed_overflow_wraps_matches_llvm() {
    differential_program(
        "composed",
        "#[inline(never)] fn poly<T: Copy + core::ops::Add<Output=T> + core::ops::Mul<Output=T>>(x: T, y: T) -> T { (x + y) * y }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let a = poly::<u8>(bb(10u8), bb(30u8)) as i64; \
            let b = poly::<u16>(bb(100u16), bb(2u16)) as i64; \
            let r = a.wrapping_mul(7).wrapping_add(b.wrapping_mul(13)); \
            (r & 0xff) as i32 }",
        44,
    );
}

/// Control: generic add that does NOT overflow still returns the right value.
#[test]
fn m75_generic_add_no_overflow_matches_llvm() {
    differential_program(
        "no_overflow",
        &format!("{ADD}#[no_mangle] pub extern \"C\" fn main() -> i32 {{ \
            (add::<i32>(bb(20), bb(22)) & 0xff) as i32 }}"),
        42,
    );
}
