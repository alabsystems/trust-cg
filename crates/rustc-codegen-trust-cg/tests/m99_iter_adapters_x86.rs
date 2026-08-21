#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: EXTENDED ITERATOR ADAPTERS — `.copied()` / `.cloned()` /
// `.rev()` / `.take(n)` / `.skip(n)` / `.step_by(k)` / `.enumerate()` — composed
// with the existing `.map` / `.filter` / `.sum` / `.fold` / `.count` / `.collect`
// consumers over `Range` and slices, compiled for x86_64 via the
// rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status (the broad matrix is at default -O0. `StepBy` is supported only with
// default O0 MIR settings (MIR inlining disabled); at -O1/-O2/-O3 or when MIR
// inlining is enabled explicitly, the bridge rejects its constructor before
// optimized std methods can read an unmodeled representation. Other optimized
// shapes may inline std generics past the bridge's interception and fail closed
// — a safe coverage gap, not a miscompile):
//   * `.copied()` / `.cloned()` over `&T` integer iters  — yield the deref'd value;
//   * `.rev()` over a bounded Range / slice source         — iterate end -> start;
//   * `.take(n)` / `.skip(n)` (n may be runtime `black_box`) — bound the loop;
//   * `.step_by(k)` (k a compile-time constant >= 1)        — yield every k-th;
//   * `.enumerate()` consumed by `.count()`                 — running index.
//
// The bridge intercepts each adapter constructor and synthesizes its state in a
// memory-backed chain slot, then the terminal consumer drives the chain via the
// SAME `emit_chain_next` header -> cont -> body loop the existing `.map`/`.filter`
// adapters use. A miscompiled adapter (wrong element order, bad bound, dropped /
// duplicated item) would diverge from LLVM, so equal exit codes are the
// differential we assert.
//
// FAIL-CLOSED (asserted to produce NO binary — never a miscompile):
//   * `.enumerate()` / `.zip()` consumed by a `.map(|(i, x)| ..)` — the
//     tuple-pattern closure body is not independently codegen'd by rustc;
//   * `.zip(other)` in any modelable-downstream shape (its tuple item likewise
//     cannot reach a scalar terminal through a codegen'd closure);
//   * `.rev()` over a `.take()` / `.skip()` / `.step_by()` chain (a naive backward
//     source walk cannot reproduce the forward-bounded sequence);
//   * `.step_by(k)` with a RUNTIME (non-constant) step.

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
    assert!(status.success(), "cargo build failed; cannot run iter-adapter test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m99_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src`; returns `Some(bin)` on success, `None` if the (trust-cg)
/// compile failed (the fail-closed case — used by the negative pins).
fn try_compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> Option<PathBuf> {
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
    if output.status.success() && bin.exists() {
        Some(bin)
    } else {
        None
    }
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> PathBuf {
    try_compile(dir, name, src, backend).unwrap_or_else(|| {
        panic!(
            "compile of `{name}` failed ({} backend)",
            if backend.is_some() { "trust-cg" } else { "llvm" }
        )
    })
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The differential: each program is compiled by trust-cg AND LLVM, run, and the
/// exit codes must match each other and the expected value. A divergence is a
/// miscompiled adapter.
#[test]
fn extended_iter_adapters_run_and_match_llvm() {
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

    // (name, source, expected exit code) — every adapter alone + composed.
    let shapes: &[(&str, &str, i32)] = &[
        // .copied() / .cloned() over a slice.
        (
            "copied_sum",
            "fn main() { let a = [1i64, 2, 3, 4]; let s: i64 = a.iter().copied().sum(); \
             std::process::exit(s as i32); }",
            10,
        ),
        (
            "cloned_sum",
            "fn main() { let a = [5i64, 6, 7]; let s: i64 = a.iter().cloned().sum(); \
             std::process::exit(s as i32); }",
            18,
        ),
        (
            "copied_map_sum",
            "fn main() { let a = [1i64, 2, 3]; \
             let s: i64 = a.iter().copied().map(|x| x * 2).sum(); std::process::exit(s as i32); }",
            12,
        ),
        // dot-product-shaped (copied + filter + map) — a common slice idiom.
        (
            "copied_filter_map_sum",
            "fn main() { let a = [1i64, 2, 3, 4, 5, 6, 7, 8, 9, 10]; \
             let s: i64 = a.iter().copied().filter(|x| x % 2 == 1).map(|x| x * x).sum(); \
             std::process::exit(s as i32); }",
            165,
        ),
        // .rev() over a Range / slice (end -> start).
        (
            "rev_range_sum",
            "fn main() { let s: i64 = (0..10i64).rev().sum(); std::process::exit(s as i32); }",
            45,
        ),
        (
            "rev_range_first",
            "fn main() { let v: Vec<i64> = (0..5i64).rev().collect(); \
             std::process::exit(v[0] as i32); }",
            4,
        ),
        (
            "rev_map_sum",
            "fn main() { let s: i64 = (0..5i64).rev().map(|x| x * 2).sum(); \
             std::process::exit(s as i32); }",
            20,
        ),
        (
            "rev_slice_copied_sum",
            "fn main() { let a = [10i64, 20, 30]; \
             let s: i64 = a.iter().rev().copied().sum(); std::process::exit(s as i32); }",
            60,
        ),
        (
            "rev_filter_sum",
            "fn main() { let s: i64 = (0..6i64).rev().filter(|x| x % 2 == 0).sum(); \
             std::process::exit(s as i32); }",
            6,
        ),
        // .take(n) — n const + runtime (black_box) + n > len.
        (
            "take_const_sum",
            "fn main() { let s: i64 = (0..10i64).take(3).sum(); std::process::exit(s as i32); }",
            3,
        ),
        (
            "take_runtime_sum",
            "fn main() { let k = std::hint::black_box(4usize); \
             let s: i64 = (0..10i64).take(k).sum(); std::process::exit(s as i32); }",
            6,
        ),
        (
            "take_over_len_sum",
            "fn main() { let s: i64 = (0..3i64).take(100).sum(); std::process::exit(s as i32); }",
            3,
        ),
        (
            "take_filter_sum",
            "fn main() { let s: i64 = (0..20i64).filter(|x| x % 2 == 0).take(3).sum(); \
             std::process::exit(s as i32); }",
            6,
        ),
        // .skip(n) — n const + runtime + n > len + composed.
        (
            "skip_const_sum",
            "fn main() { let s: i64 = (0..10i64).skip(7).sum(); std::process::exit(s as i32); }",
            24,
        ),
        (
            "skip_runtime_sum",
            "fn main() { let k = std::hint::black_box(8usize); \
             let s: i64 = (0..10i64).skip(k).sum(); std::process::exit(s as i32); }",
            17,
        ),
        (
            "skip_over_len_sum",
            "fn main() { let s: i64 = (0..3i64).skip(100).sum(); std::process::exit(s as i32); }",
            0,
        ),
        (
            "skip_take_sum",
            "fn main() { let s: i64 = (0..100i64).skip(10).take(5).sum(); \
             std::process::exit(s as i32); }",
            60,
        ),
        // .step_by(k) — alone + composed (the stateful adapter that stressed the
        // nested-offset shift the most: step_by inner, take outer).
        (
            "step_sum",
            "fn main() { let s: i64 = (0..10i64).step_by(2).sum(); std::process::exit(s as i32); }",
            20,
        ),
        (
            "step3_sum",
            "fn main() { let s: i64 = (0..10i64).step_by(3).sum(); std::process::exit(s as i32); }",
            18,
        ),
        (
            "step_take_sum",
            "fn main() { let s: i64 = (0..30i64).step_by(3).take(4).sum(); \
             std::process::exit(s as i32); }",
            18,
        ),
        (
            "step_filter_sum",
            "fn main() { let s: i64 = (0..20i64).step_by(2).filter(|x| x % 4 == 0).sum(); \
             std::process::exit(s as i32); }",
            40,
        ),
        (
            "step_count",
            "fn main() { let c: usize = (0..10i64).step_by(2).count(); \
             std::process::exit(c as i32); }",
            5,
        ),
        // .enumerate() consumed by .count() (the item is ignored).
        (
            "enumerate_count",
            "fn main() { let c: usize = (0..7i64).enumerate().count(); \
             std::process::exit(c as i32); }",
            7,
        ),
        (
            "enumerate_take_count",
            "fn main() { let c: usize = (0..100i64).enumerate().take(7).count(); \
             std::process::exit(c as i32); }",
            7,
        ),
        // Big composed chains.
        (
            "rev_filter_half_sum",
            "fn main() { let s: i64 = (0..20i64).rev().filter(|x| x % 2 == 0).map(|x| x / 2).sum(); \
             std::process::exit(s as i32); }",
            45,
        ),
        (
            "skip_take_step_sum",
            "fn main() { let s: i64 = (0..50i64).skip(5).take(10).step_by(2).sum(); \
             std::process::exit(s as i32); }",
            45,
        ),
        // Empty sources through the new adapters yield the identity (0).
        (
            "rev_empty",
            "fn main() { let s: i64 = (5..5i64).rev().take(3).sum(); std::process::exit(s as i32); }",
            0,
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

/// `StepBy` is supported through the bridge's modeled `next` lowering at default
/// O0, where MIR inlining is disabled. At O1+ or O0 with explicitly enabled MIR
/// inlining, std methods may inline and read a different internal representation,
/// so reject the iterator at construction before that state can escape. Exercise
/// both source families at every optimization level: default O0 must compile and
/// preserve the complete sequence; O1/O2/O3 must emit the dedicated compile-time
/// diagnostic and no binary. The optimized-only unsigned
/// `size_hint` case pins the original representation escape; its O0 rejection is
/// covered separately by `unmodeled_iter_adapters_fail_closed`.
#[test]
fn step_by_is_supported_only_at_default_o0() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("stepby_std_layout");
    let shapes: &[(&str, &str, bool)] = &[
        (
            "signed_range",
            "fn main() { \
             let got: Vec<i64> = (1..30i64).step_by(3).collect(); \
             let want = vec![1i64, 4, 7, 10, 13, 16, 19, 22, 25, 28]; \
             std::process::exit(if got == want { 0 } else { 101 }); }",
            true,
        ),
        (
            "slice",
            "fn main() { \
             let input = [2i64, 3, 5, 7, 11, 13, 17, 19, 23, 29]; \
             let got: Vec<i64> = input.iter().step_by(3).copied().collect(); \
             let want = vec![2i64, 7, 17, 29]; \
             std::process::exit(if got == want { 0 } else { 102 }); }",
            true,
        ),
        (
            "direct_next",
            "fn main() { let mut it = (1i64..10).step_by(3); \
             let got = it.next().unwrap() + it.next().unwrap() + it.next().unwrap(); \
             std::process::exit(if got == 12 { 0 } else { 105 }); }",
            true,
        ),
        (
            "unsigned_size_hint",
            "fn main() { let it = (0u64..10u64).step_by(3); \
             let (lo, hi) = it.size_hint(); \
             std::process::exit(if lo == 4 && hi == Some(4) { 0 } else { 103 }); }",
            false,
        ),
        (
            "captured_stepby",
            "fn main() { let it = (0i64..30).step_by(3); \
             let count = move || it.count(); \
             std::process::exit(if count() == 10 { 0 } else { 104 }); }",
            false,
        ),
    ];

    let compile_at_opt = |name: &str, src: &str, backend: Option<&Path>, opt: &str| {
        let src_path = dir.join(format!("{name}.rs"));
        std::fs::write(&src_path, src).expect("write source");
        let bin = dir.join(name);
        let mut cmd = Command::new("rustup");
        cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
            .args(["--crate-type", "bin"]);
        if let Some(dylib) = backend {
            cmd.arg(backend_arg(dylib));
            cmd.env("TCG_NO_PROOF_CERTS", "1");
        }
        let output = cmd
            .args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
            .arg(format!("-Copt-level={opt}"))
            .arg("-o")
            .arg(&bin)
            .arg(&src_path)
            .output()
            .expect("spawn rustc");
        assert!(
            output.status.success() && bin.exists(),
            "compile of `{name}` failed ({} backend) at -O{opt}; stderr:\n{}",
            if backend.is_some() { "trust-cg" } else { "LLVM" },
            String::from_utf8_lossy(&output.stderr),
        );
        bin
    };

    let bridge_compile_at_opt = |name: &str, src: &str, opt: &str, extra_args: &[&str]| {
        let src_path = dir.join(format!("{name}.rs"));
        std::fs::write(&src_path, src).expect("write source");
        let bin = dir.join(name);
        let mut cmd = Command::new("rustup");
        cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
            .args(["--crate-type", "bin"])
            .arg(backend_arg(&dylib))
            .args(["--target", TARGET, "-Cpanic=abort", "-Coverflow-checks=off"])
            .arg(format!("-Copt-level={opt}"))
            .args(extra_args)
            .arg("-o")
            .arg(&bin)
            .arg(&src_path);
        cmd.env("TCG_NO_PROOF_CERTS", "1");
        let output = cmd.output().expect("spawn rustc");
        (
            output.status.success() && bin.exists(),
            String::from_utf8_lossy(&output.stderr).into_owned(),
        )
    };

    for (shape, src, supports_o0) in shapes {
        if *supports_o0 {
            let llvm = compile_at_opt(&format!("{shape}_llvm_o0"), src, None, "0");
            let tcg = compile_at_opt(&format!("{shape}_tcg_o0"), src, Some(&dylib), "0");
            assert_eq!(run_exit_code(&llvm), 0, "LLVM `{shape}` failed at -O0");
            assert_eq!(
                run_exit_code(&tcg),
                0,
                "trust-cg `{shape}` diverged from the complete expected sequence at -O0",
            );
        }

        for opt in ["1", "2", "3"] {
            let llvm = compile_at_opt(&format!("{shape}_llvm_o{opt}"), src, None, opt);
            assert_eq!(run_exit_code(&llvm), 0, "LLVM `{shape}` failed at -O{opt}");
            let (produced, stderr) =
                bridge_compile_at_opt(&format!("{shape}_tcg_o{opt}"), src, opt, &[]);
            assert!(
                !produced,
                "trust-cg `{shape}` at -O{opt} must reject StepBy construction, but a binary was produced"
            );
            assert!(
                stderr.contains("TCG-STEPBY-OPT-LEVEL"),
                "trust-cg `{shape}` at -O{opt} must report the StepBy optimization-level guard; \
                 stderr:\n{stderr}"
            );
        }
    }

    // `-Copt-level=0` normally retains the modeled call-level path, but an
    // explicit MIR-opt level enables the pinned compiler's inliner. Treat that
    // session as optimized too; otherwise unsigned StepBy's historical
    // `size_hint` representation escape can bypass the default-O0 contract.
    let unsigned_src = shapes
        .iter()
        .find(|(name, _, _)| *name == "unsigned_size_hint")
        .map(|(_, src, _)| *src)
        .expect("unsigned StepBy regression source");
    let (produced, stderr) = bridge_compile_at_opt(
        "unsigned_size_hint_tcg_o0_mir3",
        unsigned_src,
        "0",
        &["-Zmir-opt-level=3"],
    );
    assert!(
        !produced,
        "unsigned StepBy at -O0 -Zmir-opt-level=3 must reject construction, but a binary was produced"
    );
    assert!(
        stderr.contains("TCG-STEPBY-OPT-LEVEL"),
        "unsigned StepBy at -O0 -Zmir-opt-level=3 must report the optimization-level guard; \
         stderr:\n{stderr}"
    );

    let (produced, stderr) = bridge_compile_at_opt(
        "unsigned_size_hint_tcg_o0_inline",
        unsigned_src,
        "0",
        &["-Zmir-enable-passes=+Inline"],
    );
    assert!(
        !produced,
        "unsigned StepBy at -O0 -Zmir-enable-passes=+Inline must reject construction, but a binary was produced"
    );
    assert!(
        stderr.contains("TCG-STEPBY-OPT-LEVEL"),
        "unsigned StepBy at -O0 -Zmir-enable-passes=+Inline must report the optimization-level guard; \
         stderr:\n{stderr}"
    );

    let (produced, stderr) = bridge_compile_at_opt(
        "unsigned_size_hint_tcg_o0_inline_mir",
        unsigned_src,
        "0",
        &["-Zinline-mir=yes"],
    );
    assert!(
        !produced,
        "unsigned StepBy at -O0 -Zinline-mir=yes must reject construction, but a binary was produced"
    );
    assert!(
        stderr.contains("TCG-STEPBY-OPT-LEVEL"),
        "unsigned StepBy at -O0 -Zinline-mir=yes must report the optimization-level guard; \
         stderr:\n{stderr}"
    );

    // An optimized body need not retain a bare `StepBy` local: a user struct's
    // field can be the only remaining owner. Pin the nested-field scan against
    // the exact unsigned `size_hint` escape shape.
    let holder_src = "#[repr(C)] struct Holder { it: std::iter::StepBy<std::ops::Range<u64>> } \
        #[no_mangle] pub fn observe(h: Holder) -> usize { h.it.size_hint().0 }";
    let src_path = dir.join("holder_stepby_o3.rs");
    std::fs::write(&src_path, holder_src).expect("write holder source");
    let holder_bin = dir.join("holder_stepby_o3");
    let holder_out = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "lib"])
        .arg(backend_arg(&dylib))
        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=3"])
        .arg("-o")
        .arg(&holder_bin)
        .arg(&src_path)
        .env("TCG_NO_PROOF_CERTS", "1")
        .output()
        .expect("spawn rustc");
    assert!(
        !holder_out.status.success() && !holder_bin.exists(),
        "nested-field StepBy at -O3 must reject construction, but a library was produced"
    );
    let holder_stderr = String::from_utf8_lossy(&holder_out.stderr);
    assert!(
        holder_stderr.contains("TCG-STEPBY-OPT-LEVEL"),
        "nested-field StepBy at -O3 must report the optimization-level guard; \
         stderr:\n{holder_stderr}"
    );

    // Rust permits recursively generic ADTs whose substitutions grow at each
    // field expansion. The StepBy admission scan must bound that graph and fail
    // closed instead of visiting `Foo<u8>`, `Foo<(u8,u8)>`, ... forever.
    let expanding_src = "enum Foo<T> { \
        Next(Box<Foo<(T, T)>>), \
        Marker(std::marker::PhantomData<T>), \
    } \
    #[no_mangle] pub fn observe_expanding_type(_: &Foo<u8>) -> usize { 0 }";
    let expanding_src_path = dir.join("expanding_recursive_type.rs");
    std::fs::write(&expanding_src_path, expanding_src).expect("write expanding type source");
    for opt in ["1", "3"] {
        let output_path = dir.join(format!("expanding_recursive_type_o{opt}"));
        let output = Command::new("rustup")
            .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
            .args(["--crate-type", "lib"])
            .arg(backend_arg(&dylib))
            .args(["--target", TARGET, "-Cpanic=abort"])
            .arg(format!("-Copt-level={opt}"))
            .arg("-o")
            .arg(&output_path)
            .arg(&expanding_src_path)
            .env("TCG_NO_PROOF_CERTS", "1")
            .output()
            .expect("spawn rustc");
        assert!(
            !output.status.success() && !output_path.exists(),
            "expanding recursive type at -O{opt} must fail closed instead of hanging"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("TCG-STEPBY-TYPE-SCAN"),
            "expanding recursive type at -O{opt} must report the bounded StepBy type-scan \
             diagnostic; stderr:\n{stderr}"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// Negative pins: shapes the bridge MUST fail closed on (produce no binary) —
/// never silently miscompile. Each LLVM build succeeds (valid Rust), each trust-cg
/// build is asserted to FAIL.
#[test]
fn unmodeled_iter_adapters_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("closed");

    // NOTE: `(0..5).enumerate().map(|(i,x)| i*x).sum()` was previously pinned here
    // as unmodeled, but the iterator-adapter un-gate commits (zip/step_by/filter +
    // the RangeInclusive spec_try_fold interception) now lower it CORRECTLY -- it
    // compiles and matches LLVM (=30) at O0/O2/O3. It has been REMOVED from the
    // fail-closed list and is covered as a positive case in
    // `enumerate_map_sum_now_modeled` below. The remaining shapes still fail closed.
    let closed: &[(&str, &str)] = &[
        // zip + map (the dot-product idiom): zip's tuple item is unmodeled.
        (
            "zip_map_dot",
            "fn main() { let a = [1i64, 2, 3]; let b = [4i64, 5, 6]; \
             let s: i64 = a.iter().copied().zip(b.iter().copied()).map(|(x, y)| x * y).sum::<i64>(); \
             std::process::exit(s as i32); }",
        ),
        // rev() over a take chain (forward-bounded sequence not reproducible by a
        // backward source walk). A SLICE source so `Take<slice::Iter>` is a valid
        // `DoubleEndedIterator` (LLVM accepts the program; the bridge fails closed).
        (
            "rev_over_take",
            "fn main() { let a = [1i64, 2, 3, 4, 5]; \
             let s: i64 = a.iter().copied().take(3).rev().sum(); std::process::exit(s as i32); }",
        ),
        // step_by with a RUNTIME step.
        (
            "step_by_runtime",
            "fn main() { let k = std::hint::black_box(2usize); \
             let s: i64 = (0..10i64).step_by(k).sum(); std::process::exit(s as i32); }",
        ),
        // The bridge's StepBy constructor uses synthetic state (a packed word
        // for unsigned Range sources). A real core method that is not explicitly
        // intercepted must never read that slot: before the method guard this
        // compiled and `(0u64..10).step_by(3).size_hint()` returned
        // `(0, Some(0))`, while LLVM returned `(4, Some(4))`.
        (
            "step_by_size_hint",
            "fn main() { let it = (0u64..10u64).step_by(3); \
             let (lo, hi) = it.size_hint(); \
             std::process::exit(if lo == 4 && hi == Some(4) { 0 } else { 100 }); }",
        ),
    ];

    for (name, src) in closed {
        // LLVM accepts it (valid Rust).
        let _ = compile(&dir, &format!("{name}_llvm"), src, None);
        // trust-cg must fail closed: NO binary produced.
        let tcg = try_compile(&dir, &format!("{name}_tcg"), src, Some(&dylib));
        assert!(
            tcg.is_none(),
            "`{name}` must FAIL CLOSED under trust-cg (unmodeled adapter), but a binary was produced"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// A `TakeWhile` terminal routed through the bridge's chain driver must not escape
/// its elided persistent `flag`. `Iterator::any(&mut self, ..)` may exhaust the
/// take-while prefix and then leave the iterator available to its caller. The old
/// lowering stopped at the first false predicate without setting `flag`, so a
/// later `.sum()` resumed past that boundary and admitted a later true item. The
/// tuple-item relaxation made the enumerate shape below newly reachable.
///
/// Pin the sound behavior (compile-time fail-close) and a narrowness control:
/// ordinary direct `Range::next()` remains supported and matches LLVM.
#[test]
fn takewhile_borrowed_terminal_fails_closed_but_range_next_remains_supported() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("takewhile_terminal_flag");

    let reuse = "fn main() { let a = [1i64, 0, 2]; \
        let mut it = a.iter().enumerate() \
            .take_while(|(_, x)| **x != 0).map(|(_, x)| *x); \
        let found = it.any(|x| x == 99); let rest: i64 = it.sum(); \
        std::process::exit(if found { 100 } else { rest as i32 }); }";
    // Valid Rust: LLVM preserves TakeWhile's done flag and exits 0.
    let llvm = compile(&dir, "takewhile_reuse_llvm", reuse, None);
    assert_eq!(run_exit_code(&llvm), 0);
    // trust-cg must reject the borrowed terminal for the intended persistent-flag
    // reason rather than produce the old wrong-code binary (which exited 2 by
    // resuming after the false item).
    let src_path = dir.join("takewhile_reuse_tcg.rs");
    std::fs::write(&src_path, reuse).expect("write source");
    let bin = dir.join("takewhile_reuse_tcg");
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"])
        .arg(backend_arg(&dylib))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc");
    assert!(
        !output.status.success() && !bin.exists(),
        "TakeWhile + borrowed terminal reuse must fail closed, but a binary was produced"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("persistent done flag"),
        "TakeWhile + borrowed terminal must reject for the persistent-flag guard; \
         stderr:\n{stderr}"
    );

    // A by-value exhaustive terminal consumes the iterator, so the elided flag
    // cannot escape. Preserve that supported path, including the tuple-item
    // TakeWhile relaxation that made the borrowed misuse newly reachable.
    let product = "fn main() { let a = [2i64, 3, 0, 5]; \
        let p: i64 = a.iter().enumerate() \
            .take_while(|(_, x)| **x != 0).map(|(_, x)| *x).product(); \
        std::process::exit(p as i32); }";
    let llvm = compile(&dir, "takewhile_product_llvm", product, None);
    let tcg = compile(&dir, "takewhile_product_tcg", product, Some(&dylib));
    assert_eq!(run_exit_code(&llvm), 6);
    assert_eq!(
        run_exit_code(&tcg),
        6,
        "by-value exhaustive TakeWhile::product must remain supported"
    );

    let direct_next = "fn main() { let mut it = 10i64..13; \
        let a = it.next().unwrap(); let b = it.next().unwrap(); \
        std::process::exit((a + b) as i32); }";
    let llvm = compile(&dir, "range_next_llvm", direct_next, None);
    let tcg = compile(&dir, "range_next_tcg", direct_next, Some(&dylib));
    assert_eq!(run_exit_code(&llvm), 21);
    assert_eq!(
        run_exit_code(&tcg),
        21,
        "the TakeWhile terminal guard must not over-reject ordinary direct Range::next"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// Positive counterpart: `(0..5).enumerate().map(|(i,x)| i*x).sum()` was formerly
/// pinned as an unmodeled fail-closed shape, but the iterator-adapter un-gate
/// commits now lower it correctly. It must COMPILE under trust-cg AND match LLVM.
#[test]
fn enumerate_map_sum_now_modeled() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("enum_modeled");
    let src = "fn main() { let s: i64 = (0..5i64).enumerate().map(|(i, x)| i as i64 * x).sum(); \
               std::process::exit(s as i32); }";
    let llvm = compile(&dir, "enum_modeled_llvm", src, None);
    let tcg = compile(&dir, "enum_modeled_tcg", src, Some(&dylib));
    let (le, te) = (run_exit_code(&llvm), run_exit_code(&tcg));
    assert_eq!(
        le, te,
        "(0..5).enumerate().map(|(i,x)| i*x).sum() must match LLVM (now a modeled adapter)"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// Pinned regression (COMPLETE-12 follow-on): a `usize`/`isize`-element
/// `.step_by(k)` REDUCTION (`.sum()` / `.fold()`) at rustc -O2/-O3 must fail
/// closed with a CLEAN `[TCG-MIR-UNSUPPORTED]` compile-time reject — NOT an
/// undefined-symbol LINK error.
///
/// At -O2/-O3 the terminal specializes to `<StepBy<Range<T>> as StepByImpl>::
/// spec_fold`. The `u64` sibling already fail-closed on the reachable
/// `<StepBy<Range<u64>> as SpecRangeSetup>::setup` (a `usize`->`u64`
/// `Rvalue::Cast` the backend cannot lower), but a `usize`/`isize` element makes
/// that setup cast-free — so the bridge USED to emit a real `spec_fold` call
/// whose body dragged in an unemitted `unchecked_add::precondition_check`, giving
/// `ld: undefined symbol` instead of a clean reject. Both are SOUND (no binary =>
/// no miscompile), but the link fail is an uglier failure mode; the fix makes the
/// `spec_fold`-over-`StepBy` routing fail closed uniformly for every element type.
///
/// A bare "no binary produced" assertion would NOT catch a regression here (the
/// old link fail ALSO produced no binary), so this pin asserts BOTH that the
/// reject carries `[TCG-MIR-UNSUPPORTED]` AND that stderr shows no undefined
/// symbol / link error.
#[test]
fn usize_step_by_reduction_fails_closed_cleanly_at_o2_o3() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("stepby_usize_clean");

    // Compile `src` at `opt` through the bridge; return (produced_binary, stderr).
    let bridge_compile = |name: &str, src: &str, opt: &str| -> (bool, String) {
        let src_path = dir.join(format!("{name}.rs"));
        std::fs::write(&src_path, src).expect("write source");
        let bin = dir.join(name);
        let out = Command::new("rustup")
            .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
            .args(["--crate-type", "bin"])
            .arg(backend_arg(&dylib))
            .args(["--target", TARGET, "-Cpanic=abort"])
            .arg(format!("-Copt-level={opt}"))
            .arg("-o")
            .arg(&bin)
            .arg(&src_path)
            .output()
            .expect("spawn rustc");
        let produced = out.status.success() && bin.exists();
        (produced, String::from_utf8_lossy(&out.stderr).into_owned())
    };

    let reductions: &[(&str, &str)] = &[
        (
            "usize_stepby_sum",
            "fn main() { let s: usize = (0..40usize).step_by(6).sum(); \
             std::process::exit((s % 126) as i32); }",
        ),
        (
            "usize_stepby_fold",
            "fn main() { let s: usize = (0..40usize).step_by(6).fold(0usize, |a, x| a + x); \
             std::process::exit((s % 126) as i32); }",
        ),
    ];
    for (name, src) in reductions {
        for opt in ["2", "3"] {
            let (produced, stderr) = bridge_compile(&format!("{name}_o{opt}"), src, opt);
            assert!(
                !produced,
                "`{name}` at -O{opt} must FAIL CLOSED (no binary), but one was produced"
            );
            assert!(
                stderr.contains("TCG-MIR-UNSUPPORTED"),
                "`{name}` at -O{opt} must fail closed with a clean [TCG-MIR-UNSUPPORTED] reject; \
                 stderr:\n{stderr}"
            );
            assert!(
                !stderr.contains("undefined symbol") && !stderr.contains("symbol(s) not found"),
                "`{name}` at -O{opt} must NOT link-fail on an unemitted `spec_fold` symbol; it must \
                 reject at compile time. stderr:\n{stderr}"
            );
        }
    }

    // NARROWNESS CONTROLS — the O2/O3 guard is `spec_fold`-over-`StepBy` specific
    // and must not over-reject:
    //  (a) the SAME step_by reduction still COMPILES+RUNS+MATCHES at -O0 (the O0
    //      terminal driver is step-correct; the guard is opt-level-specific), and
    //  (b) a plain (non-step_by) `usize` range sum still COMPILES+RUNS+MATCHES.
    let controls: &[(&str, &str)] = &[
        (
            "usize_stepby_sum_o0",
            "fn main() { let s: usize = (0..40usize).step_by(6).sum(); \
             std::process::exit((s % 126) as i32); }",
        ),
        (
            "usize_plain_sum_o0",
            "fn main() { let s: usize = (0..40usize).sum(); \
             std::process::exit((s % 126) as i32); }",
        ),
    ];
    for (name, src) in controls {
        let llvm = compile(&dir, &format!("{name}_llvm"), src, None);
        let tcg = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib));
        let (le, te) = (run_exit_code(&llvm), run_exit_code(&tcg));
        assert_eq!(
            te, le,
            "`{name}` (O0 non-over-rejection control): trust-cg exit {te} != LLVM {le}"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
