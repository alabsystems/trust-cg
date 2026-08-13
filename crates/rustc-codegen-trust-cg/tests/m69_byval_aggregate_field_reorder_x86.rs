// Differential regression test for MISCOMPILE #69: a by-value struct whose fields
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
    assert!(status.success(), "cargo build failed; cannot run m69 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m69_{stem}_{}", std::process::id()));
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

/// The canonical #69 repro: `struct { a: i32, b: f64 }` rustc-reorders to `b@0,a@8`.
/// Passed by value, `s.a + s.b` must read the ORIGINAL fields (10 + 9 = 19); before
/// the fix both fields read 0.
#[test]
fn m69_i32_f64_byval_matches_llvm() {
    differential_program(
        "i32_f64",
        "#[derive(Clone,Copy)] struct S { a: i32, b: f64 }\n\
         #[inline(never)] fn use_s(s: S) -> i32 { (s.a + (s.b as i32)) & 0xff }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let s = S { a: bb(10), b: bb(9.0f64) }; use_s(s) }",
        19,
    );
}

/// An ALL-INTEGER reordered struct (`{u8,u32,u16}` -> `u32@0,u16@4,u8@6`) with an
/// asymmetric reduction — proves the bug was field reordering, not SSE eightbytes.
#[test]
fn m69_all_integer_reorder_byval_matches_llvm() {
    differential_program(
        "all_int_reorder",
        "#[derive(Clone,Copy)] struct S { a: u8, b: u32, c: u16 }\n\
         #[inline(never)] fn use_s(s: S) -> i32 { \
            (s.a as i32) + (s.b as i32) * 7 + (s.c as i32) * 13 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let s = S { a: bb(1), b: bb(2), c: bb(3) }; use_s(s) & 0xff }",
        // 1 + 2*7 + 3*13 = 54
        54,
    );
}

/// Four mixed-width fields (`{u8,f64,u16,i32}`) with an asymmetric reduction.
#[test]
fn m69_quad_mixed_byval_matches_llvm() {
    differential_program(
        "quad_mixed",
        "#[derive(Clone,Copy)] struct S { a: u8, b: f64, c: u16, d: i32 }\n\
         #[inline(never)] fn use_s(s: S) -> i32 { \
            (s.a as i32) + (s.b as i32) * 3 + (s.c as i32) * 5 + s.d * 7 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let s = S { a: bb(1), b: bb(2.0f64), c: bb(3), d: bb(4) }; use_s(s) & 0xffff }",
        // 1 + 2*3 + 3*5 + 4*7 = 50
        50,
    );
}

/// Heavy reorder, asymmetric, i64 result (`{i16,i64,i32,i8}`).
#[test]
fn m69_four_int_i64_result_byval_matches_llvm() {
    differential_program(
        "four_int_i64",
        "#[derive(Clone,Copy)] struct S { a: i16, b: i64, c: i32, d: i8 }\n\
         #[inline(never)] fn use_s(s: S) -> i64 { \
            (s.a as i64) + s.b * 100 + (s.c as i64) * 10000 + (s.d as i64) * 1000000 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let s = S { a: bb(1), b: bb(2), c: bb(3), d: bb(4) }; \
            (use_s(s) & 0xffffff) as i32 }",
        // 1 + 2*100 + 3*10000 + 4*1000000 = 4_030_201; exit = & 0xFF
        4_030_201 & 0xff,
    );
}

/// A reordered struct RETURNED by value from a helper, then read back.
#[test]
fn m69_returned_struct_byval_matches_llvm() {
    differential_program(
        "returned",
        "#[derive(Clone,Copy)] struct S { a: i32, b: f64 }\n\
         #[inline(never)] fn make(x: i32, y: f64) -> S { S { a: x, b: y } }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let s = make(bb(10), bb(9.0f64)); (s.a + (s.b as i32)) & 0xff }",
        19,
    );
}
