#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: BOUNDED `.flat_map(f)` — `(0..n).flat_map(|x| a..x).sum()` /
// `.count()` / `.fold(init, g)` over a `Range<T>` outer AND a `Range<T>` inner
// (same scalar `T`, non-capturing `f`) — compiled for x86_64 via the
// rustc_codegen_trust_cg bridge, COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// See `lower_flatmap_bounded_ctor` / `lower_flatmap_bounded_consumer` in
// `src/lib.rs` for the driver this exercises: a DEDICATED two-level nested loop
// that bypasses `emit_chain_next`/`AdapterKind` entirely (their "≤1 item out
// per ≤1 item pulled" contract cannot express flat_map's "0..N items out per 1
// outer pull"). The ctor writes a PRIVATE `{start,end}` encoding into the real
// (rustc-sized) `FlatMap` slot; this is sound ONLY because the real
// `FlattenCompat::next`/`try_fold` body is UNCONDITIONALLY unlowerable by this
// backend today — `flatmap_bare_for_loop_still_fails_closed_after_backend_load`
// below is the PERMANENT regression guard for that standing invariant (see the
// ctor's doc comment): if it ever starts compiling, this whole driver's private
// encoding needs an `iter_chain_wraps_flatmap`-style guard before it can keep
// shipping.

use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};

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

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let dylib_name = dylib_name();
    let candidates = [
        target_dir.join("release").join(&dylib_name),
        target_dir.join("debug").join(&dylib_name),
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
    assert!(status.success(), "cargo build failed; cannot run flat_map test");
    let built = target_dir.join("debug").join(&dylib_name);
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
    let dir = std::env::temp_dir().join(format!("rcl2_flatmap_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

fn compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    panic: &str,
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
    cmd.args(["--target", TARGET])
        .arg(format!("-Cpanic={panic}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    if !output.status.success() {
        return Err(String::from_utf8_lossy(&output.stderr).into_owned());
    }
    Ok(bin)
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The positive-shape differential: BOUNDED `.flat_map(f)` programs (`Range<T>`
/// outer AND inner, non-capturing `f`) compiled by trust-cg AND LLVM, run, and
/// the exit codes must match each other and the expected value.
#[test]
fn flatmap_bounded_programs_run_and_match_llvm() {
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
        // `(0..3).flat_map(|x| 0..x).sum()`: x=0 -> {} ; x=1 -> {0} ; x=2 -> {0,1}.
        // Sum = 0 + 0 + (0+1) = 1.
        (
            "sum_basic",
            "fn main() { let s: i64 = (0..std::hint::black_box(3i64)).flat_map(|x| 0..x).sum(); \
             std::process::exit(s as i32); }",
            1,
        ),
        // EMPTY-only: every inner range is empty (`0..0`) regardless of `x` — must
        // never touch the accumulate step.
        (
            "sum_empty_inner",
            "fn main() { let s: i64 = (0..std::hint::black_box(1i64)).flat_map(|x| 0..x).sum(); \
             std::process::exit(s as i32); }",
            0,
        ),
        // EMPTY outer: zero outer pulls at all — `outer_header`'s condition is
        // false on the very first evaluation.
        (
            "sum_empty_outer",
            "fn main() { let s: i64 = (0..std::hint::black_box(0i64)).flat_map(|x| 0..x).sum(); \
             std::process::exit(s as i32); }",
            0,
        ),
        // COUNT: total items across all inner ranges (0 + 1 + 2 = 3) — exercises
        // the item-independent accumulate path.
        (
            "count_basic",
            "fn main() { let c: usize = (0..std::hint::black_box(3i64)).flat_map(|x| 0..x).count(); \
             std::process::exit(c as i32); }",
            3,
        ),
        // ORDER-SENSITIVE fold: `(1..4).flat_map(|x| x*10..x*10+2)` yields, in
        // order, [10,11, 20,21, 30,31]. `fold(0, |a,y| a*7+y)` is order-sensitive —
        // any nested-order bug (outer-reversed, inner-before-full-drain, or
        // acc/outer_next swapped) changes the result. Masked to a byte so the exit
        // code is representable; the differential (vs a genuine LLVM run of the
        // SAME source) is what actually catches a wrong order, not this constant.
        (
            "fold_order_sensitive",
            "fn main() { let r: i64 = (1..std::hint::black_box(4i64)).flat_map(|x| x * 10..x * 10 + 2) \
             .fold(0i64, |a, y| a * 7 + y); std::process::exit(((((r % 256) + 256) % 256) as i32)); }",
            115,
        ),
        // A single outer element with a non-trivial (3-item) inner range: the
        // minimal case that actually enters `inner_body` more than once. Outer
        // `5..6` = {5}; inner `0..(5-2)` = {0,1,2}; sum = 0+1+2 = 3.
        (
            "sum_single_outer_multi_inner",
            "fn main() { let s: i64 = (5..std::hint::black_box(6i64)).flat_map(|x| 0..(x - 2)) \
             .sum(); std::process::exit(s as i32); }",
            3,
        ),
    ];

    for (name, src, expected) in shapes {
        for panic in ["abort", "unwind"] {
            let llvm_bin = compile(&dir, &format!("{name}_{panic}_llvm"), src, None, panic)
                .unwrap_or_else(|e| panic!("LLVM compile of `{name}` ({panic}) failed: {e}"));
            let tcg_bin = compile(&dir, &format!("{name}_{panic}_tcg"), src, Some(&dylib), panic)
                .unwrap_or_else(|e| panic!("trust-cg compile of `{name}` ({panic}) failed: {e}"));
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM backend exit code for `{name}` ({panic}) is {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{name}` ({panic}) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

fn write_temp_source(stem: &str, contents: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("rcl2_flatmap_neg_{}_{}.rs", stem, std::process::id()));
    std::fs::write(&path, contents).expect("failed to write temp source file");
    path
}

struct BackendRun {
    status: ExitStatus,
    stderr: String,
}

fn run_backend_on_source(stem: &str, src: &str) -> BackendRun {
    let src_path = write_temp_source(stem, src);
    let out_bin = std::env::temp_dir().join(format!("rcl2_flatmap_neg_out_{stem}_{}", std::process::id()));
    let dylib = ensure_dylib_built();

    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg(backend_arg(&dylib))
        .arg("-o")
        .arg(&out_bin)
        .arg(&src_path)
        .output()
        .expect("failed to spawn rustc via rustup");

    let _ = std::fs::remove_file(&src_path);
    let _ = std::fs::remove_file(&out_bin);

    BackendRun {
        status: output.status,
        stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
    }
}

fn assert_no_backend_load_failure(stderr: &str) {
    let load_failure_markers = [
        "failed to load",
        "could not load",
        "couldn't load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !stderr.contains(marker),
            "rustc failed to load our backend dylib (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }
}

/// ⚠️ THE STANDING-INVARIANT CANARY (see `lower_flatmap_bounded_ctor`'s doc
/// comment). The private `{start,end}` ctor encoding this driver writes into a
/// real `FlatMap` slot is sound ONLY because `<FlattenCompat<Map<Range,F>,Range>
/// as Iterator>::next`/`try_fold` is UNCONDITIONALLY unlowerable by this
/// backend's general call path today — so a bare `for` loop over a `flat_map`
/// (which reaches that real body directly, with NO `.sum()`/`.fold()`/`.count()`
/// terminal to intercept) MUST keep failing to compile. If this test ever starts
/// observing a successful compile, that invariant has silently broken and this
/// whole driver needs an `iter_chain_wraps_flatmap`-style guard (mirroring
/// `iter_chain_wraps_stepby`) before it can keep shipping — treat it as
/// equivalent in severity to a live miscompile, not a green light.
#[test]
fn flatmap_bare_for_loop_still_fails_closed_after_backend_load() {
    let src = r#"
fn main() {
    let mut acc: i64 = 0;
    for y in (0..std::hint::black_box(3i64)).flat_map(|x| 0..x) {
        acc += y;
    }
    std::process::exit(acc as i32);
}
"#;
    let output = run_backend_on_source("bare_for_loop", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "STANDING INVARIANT BROKEN: a bare `for` loop over `.flat_map(..)` (no \
         sum/fold/count terminal) unexpectedly COMPILED. `lower_flatmap_bounded_ctor`'s \
         private {{start,end}} encoding depends on `FlattenCompat::next`/`try_fold` \
         staying unconditionally unlowerable by the general call path — this now needs \
         an `iter_chain_wraps_flatmap`-style guard before this driver can keep shipping. \
         stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

/// Composed-adapter canary: `.flat_map(..)` UNDER an outer `.map(..)` — the
/// terminal's self type is `Map<FlatMap<...>, G>`, not itself a bare `FlatMap`,
/// so `resolve_flatmap_bounded` cannot see it — must fail closed (never a wrong
/// sum), whichever stage (the `.map()` ctor embedding the private encoding into
/// a real `Map<FlatMap,G>` value, or the terminal finding no modeled chain)
/// actually rejects it first.
#[test]
fn flatmap_under_map_fails_closed_after_backend_load() {
    let src = r#"
fn main() {
    let s: i64 = (0..std::hint::black_box(3i64)).flat_map(|x| 0..x).map(|y| y * 2).sum();
    std::process::exit(s as i32);
}
"#;
    let output = run_backend_on_source("flatmap_under_map", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "`.flat_map(..).map(..).sum()` unexpectedly compiled — this composed shape is \
         outside `resolve_flatmap_bounded`'s scope and must fail closed, not silently \
         drop the outer `.map()`. stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

/// `.rev()` composed over a bounded flat_map: the terminal's self type is
/// `Rev<FlatMap<...>>`, not itself a bare `FlatMap` — must fail closed, never
/// silently ignore the `.rev()`.
#[test]
fn flatmap_then_rev_fails_closed_after_backend_load() {
    let src = r#"
fn main() {
    let s: i64 = (0..std::hint::black_box(3i64)).flat_map(|x| 0..x).rev().sum();
    std::process::exit(s as i32);
}
"#;
    let output = run_backend_on_source("flatmap_then_rev", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "`.flat_map(..).rev().sum()` unexpectedly compiled — must fail closed, never \
         silently ignore the `.rev()`. stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

/// A CAPTURING closure (`f` closes over a runtime local `k`): `resolve_flatmap_
/// bounded`'s `is_zero_sized_ty(F)` gate must reject it — must fail closed, never
/// silently compute over garbage upvar bytes.
#[test]
fn flatmap_capturing_closure_fails_closed_after_backend_load() {
    let src = r#"
fn main() {
    let k: i64 = std::hint::black_box(1i64);
    let s: i64 = (0..std::hint::black_box(3i64)).flat_map(move |x| k..x).sum();
    std::process::exit(s as i32);
}
"#;
    let output = run_backend_on_source("flatmap_capturing", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "a CAPTURING flat_map closure unexpectedly compiled — must fail closed. \
         stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}

/// A non-Range inner (`Vec<T>` via `vec![x, x]`): `range_index_ty(U)` must
/// reject it — must fail closed.
#[test]
fn flatmap_non_range_inner_fails_closed_after_backend_load() {
    let src = r#"
fn main() {
    let s: i64 = (0..std::hint::black_box(3i64)).flat_map(|x| vec![x, x]).sum();
    std::process::exit(s as i32);
}
"#;
    let output = run_backend_on_source("flatmap_non_range_inner", src);
    let stderr = output.stderr.as_str();
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc exit: {:?}", output.status);
    assert!(
        !output.status.success(),
        "a non-Range flat_map inner (`Vec`) unexpectedly compiled — must fail closed. \
         stderr: <<<{stderr}>>>"
    );
    assert_no_backend_load_failure(stderr);
}
