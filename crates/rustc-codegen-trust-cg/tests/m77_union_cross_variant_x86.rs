#[path = "support/target_dir.rs"]
mod target_dir_support;

// Differential regression test for MISCOMPILE #77: a cross-variant write to a union field was dropped (fields scalarized as separate storage)
// rustc REORDERS was passed with the fields in declaration order, so the callee
// (which reads each field at rustc's byte offset) saw every field wrong.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. rustc lays out a non-`repr(C)` struct's fields in descending
// alignment order, not declaration order: `struct S { a: i32, b: f64 }` becomes
// `b @ 0, a @ 8`. A by-value memory-backed callee parameter reads each field at
// that rustc byte offset. But when the caller's struct value is SCALARIZED (held
// as separate per-field SSA values, the common `let s = S {..}; f(s);` case), the
// bridge materialized the by-value argument slot from a flat DECLARATION-ORDER
// trust-ir tuple (`aggregate_reference_pointee_to_trust_ir_ty`), placing projected
// field `i` at lane `i`. For a reordered struct the lanes disagreed with the
// callee's rustc offsets and every field was read from the wrong place (silent
// wrong value at -Copt-level 0 AND 3). The earlier "mixed INTEGER+SSE eightbyte"
// framing was a red herring — an all-integer reordered struct (`{u8,u32,u16}`)
// miscompiled identically; `{i32,f64}` is simply the smallest case rustc reorders.
//
// THE FIX (in rustc-codegen-trust-cg/src/lib.rs `pack_scalarized_aggregate_byval_slot`).
// Pack each scalar-leaf projected field at its rustc BYTE offset
// (`variant.fields.offset(i)`) into a fresh `slot_ty` lane slot, exactly as the
// memory-backed callee reads it. (`repr(C)` structs and already-ordered structs
// were unaffected and remain correct; a nested-aggregate-field struct still fails
// closed, a pre-existing coverage gap.)
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 0 and 3; each `use_s` uses an ASYMMETRIC reduction over
// the fields so a field swap changes the result. `core::hint::black_box` keeps the
// struct materialized at runtime.

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
    assert!(status.success(), "cargo build failed; cannot run m77 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m77_{stem}_{}", std::process::id()));
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

/// Compile a FULL program `src` (with the given backend), link with abort stubs,
/// run, and return the process exit code.
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
    assert!(
        !objs.is_empty(),
        "{stem} (opt={opt}): no object file produced"
    );

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

/// Compile a complete `#![no_std] #![no_main]` program with BOTH backends at
/// -Copt-level 0 and 3 and require the trust-cg exit code to equal the LLVM exit
/// code AND the documented `expected` (process exit codes are 8-bit).
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


/// `U{u:10}; x.i = 7; x.u` must read 7 — a cross-variant write must alias the
/// overlapping storage (before the fix it returned the stale init value 10).
#[test]
fn m77_union_i32_u32_cross_write_matches_llvm() {
    differential_program(
        "u_i32u32",
        "union U { i: i32, u: u32 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut x = U { u: bb(10u32) }; unsafe { x.i = bb(7i32); } \
            (unsafe { x.u } & 0x7f) as i32 }",
        7,
    );
}

/// i32-active, u32 cross-write: `U{i:20}; x.u = 9; x.i` reads 9.
#[test]
fn m77_union_i32_init_u32_write_matches_llvm() {
    differential_program(
        "u_i32init",
        "union U { i: i32, u: u32 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut x = U { i: bb(20i32) }; unsafe { x.u = bb(9u32); } \
            ((unsafe { x.i }) & 0x7f) as i32 }",
        9,
    );
}

/// 64-bit union i64/u64 cross-write.
#[test]
fn m77_union_i64_u64_cross_write_matches_llvm() {
    differential_program(
        "u_i64u64",
        "union U { i: i64, u: u64 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut x = U { u: bb(0x99u64) }; unsafe { x.i = bb(6i64); } \
            ((unsafe { x.u }) & 0x7f) as i32 }",
        6,
    );
}

/// Interleaved cross-variant + same-variant writes, asymmetric reduction.
#[test]
fn m77_union_interleaved_writes_matches_llvm() {
    differential_program(
        "u_interleaved",
        "union U { i: i32, u: u32 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut x = U { u: bb(0x11u32) }; \
            unsafe { x.i = bb(0x05i32); } let a = unsafe { x.u }; \
            unsafe { x.u = a.wrapping_add(bb(0x02u32)); } let b = unsafe { x.i }; \
            let r = (a as u32).wrapping_mul(3).wrapping_add((b as u32).wrapping_mul(5)); \
            (r & 0x7f) as i32 }",
        50,
    );
}

// #79 (completes #77): a NARROW-variant write into a wider union carrier must
// overwrite only its low bytes and PRESERVE the carrier's high bytes (a plain
// zero/sign-extend dropped them).

/// `U{w:0xAABBCC00}; u.b = 0x42; u.w` must be 0xAABBCC42 (low byte only).
#[test]
fn m77_union_narrow_u8_into_u32_preserves_high_matches_llvm() {
    differential_program(
        "narrow_u8_u32",
        "union U { w: u32, b: u8 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut u = U { w: bb(0xAABBCC00u32) }; u.b = bb(0x42u8); \
            let full = unsafe { u.w }; \
            ((full & 0xff)*3 + ((full>>8)&0xff)*5 + ((full>>16)&0xff)*7 + ((full>>24)&0xff)*11) as i32 & 0xff }",
        45,
    );
}

/// Narrow u16 into a u32 carrier preserves the high half.
#[test]
fn m77_union_narrow_u16_into_u32_matches_llvm() {
    differential_program(
        "narrow_u16_u32",
        "union U { w: u32, h: u16 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut u = U { w: bb(0xDEAD0000u32) }; u.h = bb(0xBEEFu16); \
            let full = unsafe { u.w }; \
            (((full >> 16) & 0xffff) as i32 * 2 + (full & 0xffff) as i32 * 3) & 0xff }",
        39,
    );
}

/// Narrow u8 into a u64 carrier preserves the top 7 bytes.
#[test]
fn m77_union_narrow_u8_into_u64_matches_llvm() {
    differential_program(
        "narrow_u8_u64",
        "union U { q: u64, b: u8 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut u = U { q: bb(0x1122334455667700u64) }; u.b = bb(0x99u8); \
            let q = unsafe { u.q }; \
            ((q & 0xff) as i32 * 3 + ((q >> 56) & 0xff) as i32 * 5) & 0xff }",
        32,
    );
}

/// Two sequential narrow writes each preserve the unwritten high bytes.
#[test]
fn m77_union_sequential_narrow_writes_matches_llvm() {
    differential_program(
        "narrow_seq",
        "union U { w: u32, b: u8 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut u = U { w: bb(0x01020304u32) }; \
            u.b = bb(0xF0u8); let mid = unsafe { u.w }; \
            u.b = bb(0x0Fu8); let fin = unsafe { u.w }; \
            ((mid & 0xff) as i32 * 2 + (fin & 0xff) as i32 * 3 + ((fin >> 16) & 0xff) as i32 * 5) & 0xff }",
        23,
    );
}
