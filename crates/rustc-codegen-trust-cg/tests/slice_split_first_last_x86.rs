// Integration test: SLICE `split_at(n)` -> `(&[T], &[T])` and `first()` /
// `last()` -> `Option<&T>` over a LOCAL ARRAY's slice — compiled for x86_64 via
// the rustc_codegen_trust_cg bridge, COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend at BOTH `-Copt-level=0` AND `3`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The keystones covered here:
//   * `a.split_at(n)` yields a TUPLE of two sub-slices `({data, n}, {data + n,
//     len - n})`; a wrong split index would give a wrong data pointer / length
//     and a different sum — caught by the differential. Both halves are SUMMED
//     (left positive, right negated) so a wrong split offset shows up.
//   * `first()` / `last()` over a NON-EMPTY slice yield `Some(&first)` /
//     `Some(&last)`; over an EMPTY slice they yield `None`. The empty case forces
//     the niche `None` (null pointer) path.
//   * All inputs are `black_box`'d so the compiler cannot fold the result; the
//     exit is driven from a bit-spread reduction so a wrong high bit cannot
//     collapse mod 256.
//
// Each program is compiled with BOTH backends at BOTH opt levels, run, and the
// trust-cg exit code must equal the LLVM exit code.

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
    assert!(status.success(), "cargo build failed; cannot run split/first/last test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_sfl_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: &str,
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
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
        opt,
    ])
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

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
    match try_compile(dir, name, src, backend, opt) {
        Ok(bin) => bin,
        Err(stderr) => panic!(
            "compile of `{name}` failed ({} backend, {opt}). stderr: <<<{stderr}>>>",
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

#[test]
fn split_first_last_runs_and_matches_llvm() {
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

    // Each program reduces a wide computed value to a single byte via XOR-folding
    // all four bytes of (value as u32) so a wrong high byte cannot be masked away.
    // (name, source)
    let shapes: &[(&str, &str)] = &[
        // 1. `split_at(2)` over `[10,20,30,40]` -> ({10,20}, {30,40}). Left summed
        //    positive (30), right summed negated (-70); total = -40. A wrong split
        //    index or wrong data pointer changes the partition sum.
        (
            "split_at_sum",
            "use std::hint::black_box; \
             #[inline(never)] fn split_sum(a: &[i64], n: usize) -> i64 { \
                 let (l, r) = a.split_at(n); \
                 let mut s = 0i64; \
                 let mut i = 0usize; while i < l.len() { s += l[i]; i += 1; } \
                 let mut j = 0usize; while j < r.len() { s -= r[j]; j += 1; } \
                 s } \
             fn main(){ \
                 let arr = black_box([10i64, 20, 30, 40]); \
                 let n = black_box(2usize); \
                 let v = split_sum(&arr[..], n); \
                 let u = (v as u32); \
                 let b = (u ^ (u >> 8) ^ (u >> 16) ^ (u >> 24)) & 0xff; \
                 std::process::exit(b as i32); }",
        ),
        // 2. `split_at(3)` over `[1,2,3,4,5,6]` (an UNEVEN split): left {1,2,3} sum
        //    6, right {4,5,6} sum 15 -> left - right = -9. The right half's data
        //    pointer is base + 3*8 and length 3.
        (
            "split_at_uneven",
            "use std::hint::black_box; \
             #[inline(never)] fn split_sum(a: &[i64], n: usize) -> i64 { \
                 let (l, r) = a.split_at(n); \
                 let mut s = 0i64; \
                 let mut i = 0usize; while i < l.len() { s += l[i]; i += 1; } \
                 let mut j = 0usize; while j < r.len() { s -= r[j]; j += 1; } \
                 s } \
             fn main(){ \
                 let arr = black_box([1i64, 2, 3, 4, 5, 6]); \
                 let n = black_box(3usize); \
                 let v = split_sum(&arr[..], n); \
                 let u = (v as u32); \
                 let b = (u ^ (u >> 8) ^ (u >> 16) ^ (u >> 24)) & 0xff; \
                 std::process::exit(b as i32); }",
        ),
        // 3. `first()` over a NON-EMPTY slice -> Some(&first). first of
        //    [0x1122334455667788, ...] driven through a bit-spread so a wrong byte
        //    of the loaded value is observed.
        (
            "first_some",
            "use std::hint::black_box; \
             #[inline(never)] fn first_val(a: &[i64]) -> i64 { \
                 match a.first() { Some(v) => *v, None => -1 } } \
             fn main(){ \
                 let arr = black_box([0x1122_3344_5566_7788i64, 99, 7]); \
                 let v = first_val(&arr[..]); \
                 let u = v as u64; \
                 let b = (u ^ (u >> 8) ^ (u >> 16) ^ (u >> 24) \
                            ^ (u >> 32) ^ (u >> 40) ^ (u >> 48) ^ (u >> 56)) & 0xff; \
                 std::process::exit(b as i32); }",
        ),
        // 4. `last()` over a NON-EMPTY slice -> Some(&last). last is the WIDE value.
        (
            "last_some",
            "use std::hint::black_box; \
             #[inline(never)] fn last_val(a: &[i64]) -> i64 { \
                 match a.last() { Some(v) => *v, None => -2 } } \
             fn main(){ \
                 let arr = black_box([7i64, 99, 0x0102_0304_0506_0708i64]); \
                 let v = last_val(&arr[..]); \
                 let u = v as u64; \
                 let b = (u ^ (u >> 8) ^ (u >> 16) ^ (u >> 24) \
                            ^ (u >> 32) ^ (u >> 40) ^ (u >> 48) ^ (u >> 56)) & 0xff; \
                 std::process::exit(b as i32); }",
        ),
        // 5. `first()` over an EMPTY slice -> None. The match returns the None arm
        //    sentinel; if the niche None were mis-encoded as Some, a garbage deref
        //    would diverge from LLVM. -1 as u8 = 255.
        (
            "first_none",
            "use std::hint::black_box; \
             #[inline(never)] fn first_val(a: &[i64]) -> i64 { \
                 match a.first() { Some(v) => *v, None => -1 } } \
             fn main(){ \
                 let e: [i64; 0] = black_box([]); \
                 let v = first_val(&e[..]); \
                 std::process::exit(((v as u32) & 0xff) as i32); }",
        ),
        // 6. `last()` over an EMPTY slice -> None. -2 as u8 = 254.
        (
            "last_none",
            "use std::hint::black_box; \
             #[inline(never)] fn last_val(a: &[i64]) -> i64 { \
                 match a.last() { Some(v) => *v, None => -2 } } \
             fn main(){ \
                 let e: [i64; 0] = black_box([]); \
                 let v = last_val(&e[..]); \
                 std::process::exit(((v as u32) & 0xff) as i32); }",
        ),
        // 7. `split_at(0)` (degenerate): left empty, right whole. left sum 0, right
        //    sum -(1+2+3+4)=-10. Exercises the n=0 boundary (right data == base).
        (
            "split_at_zero",
            "use std::hint::black_box; \
             #[inline(never)] fn split_sum(a: &[i64], n: usize) -> i64 { \
                 let (l, r) = a.split_at(n); \
                 let mut s = 0i64; \
                 let mut i = 0usize; while i < l.len() { s += l[i]; i += 1; } \
                 let mut j = 0usize; while j < r.len() { s -= r[j]; j += 1; } \
                 s } \
             fn main(){ \
                 let arr = black_box([1i64, 2, 3, 4]); \
                 let n = black_box(0usize); \
                 let v = split_sum(&arr[..], n); \
                 let u = (v as u32); \
                 let b = (u ^ (u >> 8) ^ (u >> 16) ^ (u >> 24)) & 0xff; \
                 std::process::exit(b as i32); }",
        ),
        // 8. `split_at(len)` (degenerate): left whole, right empty.
        (
            "split_at_full",
            "use std::hint::black_box; \
             #[inline(never)] fn split_sum(a: &[i64], n: usize) -> i64 { \
                 let (l, r) = a.split_at(n); \
                 let mut s = 0i64; \
                 let mut i = 0usize; while i < l.len() { s += l[i]; i += 1; } \
                 let mut j = 0usize; while j < r.len() { s -= r[j]; j += 1; } \
                 s } \
             fn main(){ \
                 let arr = black_box([1i64, 2, 3, 4]); \
                 let n = black_box(4usize); \
                 let v = split_sum(&arr[..], n); \
                 let u = (v as u32); \
                 let b = (u ^ (u >> 8) ^ (u >> 16) ^ (u >> 24)) & 0xff; \
                 std::process::exit(b as i32); }",
        ),
    ];

    for opt in ["-Copt-level=0", "-Copt-level=3"] {
        for (name, src) in shapes {
            let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{name}` ({opt}) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
