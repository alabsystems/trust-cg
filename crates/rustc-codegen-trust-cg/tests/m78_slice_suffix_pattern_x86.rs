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
    assert!(status.success(), "cargo build failed; cannot run m78 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m78_{stem}_{}", std::process::id()));
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


// #78: a from_end ConstantIndex (`[.., last]`) on a runtime-length slice computed
// the index as `min_length - offset` (the pattern minimum) instead of
// `runtime_len - offset`, so it read the FRONT element. The fix loads the slice's
// runtime length from the fat-pointer metadata. O0 fail-closes on a separate
// slice-pattern reference-binding gap (safe), so this gates -Copt-level 3 only.

/// `match s { [.., last] => *last }` must bind the TAIL element (was front).
#[test]
fn m78_slice_last_element_matches_llvm() {
    differential_o3(
        "last",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let arr = [bb(2i32), bb(9), bb(4), bb(8), bb(6)]; let s: &[i32] = &arr; \
            let r = match s { [.., last] => *last, [] => -1 }; (r & 0xff) as i32 }",
        6,
    );
}

/// `[first, .., last]` — first from the front, last from the tail.
#[test]
fn m78_slice_first_and_last_matches_llvm() {
    differential_o3(
        "first_last",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let arr = [bb(2i32), bb(9), bb(4), bb(8), bb(6)]; let s: &[i32] = &arr; \
            let r = match s { [first, .., last] => first.wrapping_mul(1).wrapping_add(last.wrapping_mul(7)), _ => -1 }; \
            (r & 0xff) as i32 }",
        // 2 + 6*7 = 44
        44,
    );
}

/// `[.., a, b]` — two suffix bindings, both from the tail (a at len-2, b at len-1).
#[test]
fn m78_slice_two_suffix_bindings_matches_llvm() {
    differential_o3(
        "two_suffix",
        "#[no_mangle] pub extern \"C\" fn main() -> i32 { \
            let arr = [bb(2i32), bb(9), bb(4), bb(8), bb(6)]; let s: &[i32] = &arr; \
            let r = match s { [.., a, b] => a.wrapping_mul(3).wrapping_add(b.wrapping_mul(5)), _ => -1 }; \
            (r & 0xff) as i32 }",
        // 8*3 + 6*5 = 54
        54,
    );
}
