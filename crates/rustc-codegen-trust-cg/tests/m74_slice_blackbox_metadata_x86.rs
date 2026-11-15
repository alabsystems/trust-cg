#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Differential regression test for MISCOMPILE #74: a `&[T]` / `&str` fat pointer
// passed through `black_box` (the identity intrinsic) lost its LENGTH metadata, so
// a later `slice.len()` / index read saw a wrong length.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// ROOT CAUSE. The bridge models `black_box(x)` as the identity `dest = x`, but
// lowered the copy through the SCALAR operand path (`lower_operand`). A `&[T]` /
// `&str` is a FAT pointer `{ data, len }`; the scalar copy moved only the data half
// and dropped the length metadata (tracked separately). So
// `black_box(&array_as_slice).len()` returned 0 (or garbage) at -Copt-level 3, and
// an asymmetric reduction over the slice that the optimizer turned into a
// pointer-walk dereferenced an invalid pointer (SIGSEGV). At -Copt-level 0 the same
// programs fail closed on a SEPARATE, pre-existing limitation (slice fat-pointer
// `Struct([I64,I64])` length/bounds arithmetic is not selected) — a safe compile
// error, not a wrong value — so this regression test gates -Copt-level 3 only.
//
// THE FIX (in rustc-codegen-trust-cg/src/lib.rs `lower_intrinsic_call`). Route
// `black_box`'s `dest = arg` through the full assignment lowering (`lower_assign`
// with `Rvalue::Use`), which dispatches a memory-backed slice/aggregate to its
// whole-value copy (both fat-pointer halves) and keeps the scalar case identical.
//
// The differential oracle is the SAME program compiled by rustc's default LLVM
// backend at -Copt-level 3. `black_box` keeps the slice opaque so the length is a
// real runtime read, and each reduction is ASYMMETRIC so a wrong length or a
// mis-walked element changes the result.

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m74_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn write_panic_stubs(dir: &Path, obj: &Path) -> PathBuf {
    let nm = Command::new("nm").arg("-u").arg(obj).output().expect("nm");
    let mut stubs = String::from("#include <stdlib.h>\n");
    for line in String::from_utf8_lossy(&nm.stdout).lines() {
        let sym = line.trim().trim_start_matches('U').trim();
        if toolchain_support::is_abort_stub_symbol(sym) {
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

    let mut cmd = toolchain_support::rustc_command();
    cmd.arg("--crate-type").arg("bin");
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
    let output = cmd.output().expect("failed to spawn trustc");
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

/// Compile a complete program with BOTH backends at -Copt-level 3 ONLY (O0 fail-
/// closes on the separate slice-arithmetic ISel gap) and require the trust-cg exit
/// code to equal the LLVM exit code AND the documented `expected`.
fn differential_o3(stem: &str, body: &str, expected: i32) {
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
    let opt = "3";
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

/// `black_box(&[i64; 5]).len()` must be 5 (was garbage — the length metadata was
/// dropped by black_box's scalar copy).
#[test]
fn m74_blackbox_scalar_slice_len_matches_llvm() {
    differential_o3(
        "scalar_len",
        "#[inline(never)] fn getlen(s: &[i64]) -> i32 { s.len() as i32 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let arr = [bb(1i64),bb(2),bb(3),bb(4),bb(5)]; getlen(bb(&arr)) & 0xff }",
        5,
    );
}

/// `black_box(&[Struct; 7]).len()` must be 7 (was 0).
#[test]
fn m74_blackbox_struct_slice_len_matches_llvm() {
    differential_o3(
        "struct_len",
        "#[derive(Copy, Clone)] struct P { a: i32, b: i32 }\n\
         #[inline(never)] fn getlen(s: &[P]) -> i32 { s.len() as i32 }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut arr = [P { a: 0, b: 0 }; 7]; let mut i = 0; \
            while i < 7 { arr[i].a = bb(1); arr[i].b = bb(1); i += 1; } \
            getlen(bb(&arr)) & 0xff }",
        7,
    );
}

/// Asymmetric reduction over `black_box(&[Struct; 4])` — exercises the length AND
/// each element read (this shape SIGSEGV'd before the fix because the slice walk
/// dereferenced an invalid pointer built from the dropped metadata).
#[test]
fn m74_blackbox_struct_slice_reduce_matches_llvm() {
    differential_o3(
        "struct_reduce",
        "#[derive(Copy,Clone)] struct P { a: i32, b: i32 }\n\
         #[inline(never)] fn reduce(s: &[P]) -> i32 { \
            let mut acc=0i32; let mut i=0; \
            while i<s.len() { \
                acc=acc.wrapping_add(s[i].a.wrapping_mul(3*i as i32+1)) \
                       .wrapping_add(s[i].b.wrapping_mul(3*i as i32+3)); i+=1; } acc }\n\
         #[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let mut arr=[P{a:0,b:0};4]; let mut i=0; \
            while i<4 { arr[i].a=bb((i+1) as i32); arr[i].b=bb(((i+1)*10) as i32); i+=1; } \
            reduce(bb(&arr)) & 0xff }",
        // sum_i a*(3i+1) + b*(3i+3) = 31+128+291+520 = 970; 970 & 0xff = 202
        202,
    );
}
