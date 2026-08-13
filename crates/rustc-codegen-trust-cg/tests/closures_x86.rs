// Integration test: CAPTURING (non-ZST) CLOSURES — closures that capture an
// environment — compiled for x86_64 via the rustc_codegen_trust_cg bridge,
// COMPILED, LINKED, and RUN, with exit codes checked against the default LLVM
// backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: a closure that captures environment carries upvars, so calling it
// must pass the closure ENVIRONMENT — for `Fn`/`FnMut` the body's first param is
// `&self` / `&mut self` (a pointer to the closure struct), for `FnOnce` it is
// `self` by value — followed by the (untupled) call args. The bridge:
//
//   * memory-backs a capturing closure local in a real env slot, materializes its
//     upvars there, and passes `&env` (Fn/FnMut) / the env by value (FnOnce) as
//     the receiver of the closure body call, then the untupled args;
//   * gives a scalar local whose address is captured by reference (`&k` / `&mut
//     c`) a memory "cell" so the reference is a stable runtime address — making a
//     `&mut`-captured `FnMut` counter observe writes across calls and a
//     `&`-captured value read the live value;
//   * passes a capturing closure BY VALUE into a generic `fn apply<F: Fn(..)>` as
//     its env aggregate across the SysV boundary, then calls it through `&env`;
//   * stores a capturing adapter closure's upvars in the iterator-chain slot and
//     calls the closure with `&env` while driving `.map`/`.filter`.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A miscompiled closure
// (reading the wrong captured value, a lost `FnMut` mutation, a dropped upvar)
// would diverge from LLVM, so equal exit codes are the differential we assert.

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
    assert!(status.success(), "cargo build failed; cannot run closures test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_clos_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);

    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort"])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend). stderr: <<<{}>>>",
        if backend.is_some() { "trust-cg" } else { "llvm" },
        String::from_utf8_lossy(&output.stderr)
    );
    bin
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The full differential: each capturing-closure program is compiled by trust-cg
/// AND LLVM, run, and the exit codes must match each other and the expected
/// value. A divergence is a miscompiled capture / call.
#[test]
fn capturing_closure_programs_run_and_match_llvm() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("run");

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        // A closure capturing ONE value by reference: `k + x`. f(5) with k=3 -> 8.
        (
            "capture_one_by_ref",
            "fn main() { let k: i64 = 3; let f = |x: i64| x + k; \
             std::process::exit(f(5) as i32); }",
            8,
        ),
        // A closure capturing one value by VALUE (`move`): same result, 8.
        (
            "capture_one_by_move",
            "fn main() { let k: i64 = 3; let f = move |x: i64| x + k; \
             std::process::exit(f(5) as i32); }",
            8,
        ),
        // A closure capturing TWO values: a + b + x. f(5) with a=7,b=20 -> 32.
        (
            "capture_two",
            "fn main() { let a: i64 = 7; let b: i64 = 20; let f = |x: i64| x + a + b; \
             std::process::exit(f(5) as i32); }",
            32,
        ),
        // An `FnMut` counter: each call mutates the captured `c` through `&mut c`,
        // and the mutation must persist across calls. f();f();f() -> 3.
        (
            "fnmut_counter",
            "fn main() { let mut c: i64 = 0; let mut f = || { c += 1; c }; \
             f(); f(); std::process::exit(f() as i32); }",
            3,
        ),
        // An `FnMut` accumulator returning the running sum: 1, then 1+2, then
        // 1+2+3 = 6 (proves the captured state threads correctly across calls).
        (
            "fnmut_accumulate",
            "fn main() { let mut acc: i64 = 0; let mut f = |n: i64| { acc += n; acc }; \
             f(1); f(2); std::process::exit(f(3) as i32); }",
            6,
        ),
        // A capturing closure passed to a generic `fn apply<F: Fn(i64)->i64>`: the
        // closure crosses the by-value ABI boundary as its env and is called
        // through `&env` inside `apply`. k=10, x=5 -> 15.
        (
            "generic_apply",
            "fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 { f(x) } \
             fn main() { let k: i64 = 10; \
             std::process::exit(apply(|x| x + k, 5) as i32); }",
            15,
        ),
        // A two-capture closure passed by value into a generic `apply`: 7+20+5=32.
        (
            "generic_apply_two_captures",
            "fn apply<F: Fn(i64) -> i64>(f: F, x: i64) -> i64 { f(x) } \
             fn main() { let a: i64 = 7; let b: i64 = 20; \
             std::process::exit(apply(|x| x + a + b, 5) as i32); }",
            32,
        ),
        // A CAPTURING closure in a `.map` adapter: `(0..n).map(|x| x*k).sum()`
        // with captured k. n=5, k=3 -> 3*(0+1+2+3+4) = 30.
        (
            "map_capture_sum",
            "fn main() { let n: i64 = 5; let k: i64 = 3; \
             let s: i64 = (0..n).map(|x| x * k).sum(); std::process::exit(s as i32); }",
            30,
        ),
        // A CAPTURING closure in a `.filter` adapter: `(0..10).filter(|x| *x >
        // threshold).sum()` with captured threshold=5 -> 6+7+8+9 = 30.
        (
            "filter_capture_sum",
            "fn main() { let threshold: i64 = 5; \
             let s: i64 = (0..10i64).filter(|x| *x > threshold).sum(); \
             std::process::exit(s as i32); }",
            30,
        ),
        // A capturing `map` followed by a capturing `filter`: multiply by `k`,
        // keep those `>= lo`. (0..6)*2 = {0,2,4,6,8,10}; keep >= 5 -> {6,8,10} =
        // 24. Exercises two distinct capturing closures in one chain.
        (
            "map_then_filter_captures",
            "fn main() { let k: i64 = 2; let lo: i64 = 5; \
             let s: i64 = (0..6i64).map(|x| x * k).filter(|y| *y >= lo).sum(); \
             std::process::exit(s as i32); }",
            24,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib));
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM backend exit code for `{name}` is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for `{name}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
