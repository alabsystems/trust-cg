#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test (m124): the fat-pointer WRITE-THROUGH frontend arm — a WHOLE
// `{ data, len }` slice/`str` fat pointer STORED through a thin `&mut &[T]` /
// `*mut &str` slot. Compiled for x86_64 via the rustc_codegen_trust_cg bridge,
// COMPILED, LINKED, and RUN, with exit codes checked against the default LLVM
// backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// This is the WRITE COMPLEMENT to the STAT-1 ptr-bearing-static READ arm (which
// LOADS `{ data, len }` at `p+0`/`p+8` for `s = copy (*p)`). The write arm
// resolves the SOURCE slice's `{ data, len }` (a `&str`/`&[T]` const literal, a
// fat-pointer place move/copy, or an `&[T; N] -> &[T]` unsize) and STORES both
// halves through `p`: `data` (`Ptr`, preserving the literal's data relocation) at
// `p+0`, `len` (`I64`) at `p+8`. It lands the two blocked shapes:
//
//   * a `static mut S: &str = ".."` / `static mut NUMS: &[i32] = ..` WRITE
//     (`(*p) = "hello"` / `(*p) = &[..]` through the static's writable fat slot);
//   * a `fn set(p: &mut &[T], v: &[T]) { *p = v }` `&mut`-slice-ref WRITE.
//
// Each case is a strict CONTENT differential: the exit code folds BOTH the
// written length AND a read-back element / byte, so a dropped write (reading the
// stale initial value) or a wrong data pointer (reading the wrong literal) shows
// up as a mismatched exit code. Run at `-Copt-level=0` AND `-Copt-level=3` (opt
// parity — the write arm covers the out-of-line O0 forms and the inlined O3
// forms identically).

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
    assert!(status.success(), "cargo build failed; cannot run m124 test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m124_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn try_compile_at(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt_level: &str,
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
    cmd.args(["--target", TARGET, "-Cpanic=abort", opt_level])
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

fn compile_at(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt_level: &str,
) -> PathBuf {
    match try_compile_at(dir, name, src, backend, opt_level) {
        Ok(bin) => bin,
        Err(stderr) => panic!(
            "compile of `{name}` failed ({} backend, {opt_level}). stderr: <<<{stderr}>>>",
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

/// Every fat-pointer WRITE-through shape is compiled by trust-cg AND LLVM, run,
/// and the exit codes must match each other and the expected CONTENT-folded
/// value, at BOTH `-Copt-level=0` and `-Copt-level=3`.
#[test]
fn static_mut_slice_write_runs_and_matches_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("cases");

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // 1. `static mut S: &str` WRITE, length read-back. The write stores the new
        //    literal's `{ &"hello", 5 }` into the static's writable fat slot; the
        //    read reflects the WRITTEN length 5 (not the initial "hi" == 2).
        (
            "static_mut_str_write_len",
            "static mut S: &str = \"hi\"; \
             fn main(){ unsafe { S = \"hello\"; std::process::exit(S.len() as i32) } }",
            5,
        ),
        // 2. `static mut S: &str` WRITE, BYTE-CONTENT read-back — proves the stored
        //    DATA pointer resolves to the RIGHT literal: `"world"[1] == 'o' == 111`
        //    (the stale initial `"hi"[1] == 'i' == 105` would mismatch).
        (
            "static_mut_str_write_byte",
            "static mut S: &str = \"hi\"; \
             fn main(){ unsafe { S = \"world\"; let b = S.as_bytes(); \
             std::process::exit(b[1] as i32) } }",
            111,
        ),
        // 3. `static mut NUMS: &[i32]` WRITE via a `&[T; N] -> &[T]` unsize, length
        //    AND element read-back: `len(4) * 10 + NUMS[2](30) == 70`. A dropped
        //    write reads the stale `&[0]` (len 1). Proves both fat-pointer halves.
        (
            "static_mut_slice_write_len_elem",
            "static mut NUMS: &[i32] = &[0]; \
             fn main(){ unsafe { NUMS = &[10, 20, 30, 40]; \
             std::process::exit((NUMS.len() as i32) * 10 + NUMS[2]) } }",
            70,
        ),
        // 4. `static mut BYTES: &[u8]` byte-slice WRITE: `len(4) * 10 + BYTES[2]
        //    ('c' == 99) == 139`.
        (
            "static_mut_byte_slice_write",
            "static mut BYTES: &[u8] = b\"x\"; \
             fn main(){ unsafe { BYTES = b\"abcd\"; \
             std::process::exit((BYTES.len() as i32) * 10 + BYTES[2] as i32) } }",
            139,
        ),
        // 5. CROSS-FN `static mut` WRITE: the write happens in an out-of-line helper
        //    (`put(v)` stores `v` into `S`); `main` reads the written length back.
        (
            "static_mut_str_write_cross_fn",
            "static mut S: &str = \"hi\"; \
             #[inline(never)] fn put(v: &'static str) { unsafe { S = v; } } \
             fn main(){ put(\"hello\"); std::process::exit(unsafe { S.len() as i32 }) }",
            5,
        ),
        // 6. DOUBLE WRITE — proves the fat slot is genuinely mutable and the LAST
        //    write wins (`S = "aa"` then `S = "bbbbbbb"`, read length 7).
        (
            "static_mut_str_double_write",
            "static mut S: &str = \"hi\"; \
             fn main(){ unsafe { S = \"aa\"; S = \"bbbbbbb\"; \
             std::process::exit(S.len() as i32) } }",
            7,
        ),
        // 7. The `fn set(p: &mut &[T], v: &[T]) { *p = v }` `&mut`-slice-ref WRITE,
        //    driven end-to-end through a `static mut` destination: `main` passes
        //    `&mut R` + a fresh slice, `set` stores `{ data, len }` through `p`, and
        //    `main` reads `len(4) * 10 + R[2](30) == 70` back.
        (
            "refmut_slice_ref_param_write",
            "static mut R: &[i32] = &[0]; \
             #[inline(never)] fn set(p: &mut &'static [i32], v: &'static [i32]) { *p = v; } \
             fn main(){ unsafe { set(&mut R, &[10, 20, 30, 40]); \
             std::process::exit((R.len() as i32) * 10 + R[2]) } }",
            70,
        ),
    ];

    for opt_level in ["-Copt-level=0", "-Copt-level=3"] {
        for (name, src, expected) in shapes {
            let case = format!("{name}_{}", &opt_level[opt_level.len() - 1..]);
            let llvm_bin = compile_at(&dir, &format!("{case}_llvm"), src, None, opt_level);
            let tcg_bin = compile_at(&dir, &format!("{case}_tcg"), src, Some(&dylib), opt_level);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM backend exit code for `{case}` is {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{case}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
