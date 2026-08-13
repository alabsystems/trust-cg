// Integration test: idiomatic `for` loops (`Range` + slice iterators) compiled
// for x86_64 via the rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN,
// with exit codes checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: bare `for` loops over `Range<T>` and `core::slice::Iter<T>` RUN on
// x86_64 via trust-cg.
//
// A `for pat in iterable { body }` desugars (in MIR) to roughly
//
//     let mut it = IntoIterator::into_iter(iterable);
//     loop { match Iterator::next(&mut it) { Some(pat) => body, None => break } }
//
// The real std `next` bodies descend into machinery the backend cannot lower
// (`RangeIteratorImpl::spec_next` / the `cold_path` intrinsic / a `NonNull` +
// `end_or_len` union representation). So — exactly as `Box::new` and the
// `Vec<T>` methods are intercepted — the bridge intercepts the iterator calls a
// bare `for` loop needs (`IntoIterator::into_iter`, `Iterator::next` for these
// two concrete iterators) and synthesizes them directly against a memory-backed
// iterator-state slot:
//
//   * a `Range<T>` is `{ start, end }`; `into_iter` is the identity, and `next`
//     yields `Some(start)` and advances `start` while `start < end`, else `None`;
//   * a `slice::Iter<T>` is `{ ptr, end }`; `into_iter` over a `&[T]` / `&[T; N]`
//     builds `{ data, data + len*size }`, and `next` yields `Some(&*ptr)` and
//     advances `ptr` while `ptr != end`, else `None`.
//
// The synthesized `next` is branchless (loads + arithmetic + `Select`s + stores)
// and writes the `Option<…>` result into the destination's memory slot, so the
// downstream `discriminant` / `switchInt` / payload-read flow through the
// bridge's existing memory-enum machinery unchanged.
//
// Each program is compiled with BOTH backends and run; the trust-cg exit code
// must equal the LLVM exit code (and the expected value). A wrong loop bound or
// element (a miscompiled iterator) would diverge from LLVM, so equal exit codes
// are the differential we assert.

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
    assert!(status.success(), "cargo build failed; cannot run for-loop test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_for_{stem}_{}", std::process::id()));
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

/// The full differential: each `for`-loop program is compiled by trust-cg AND
/// LLVM, run, and the exit codes must match each other and the expected value. A
/// divergence is a miscompile (a wrong loop bound or iterated element).
#[test]
fn for_loop_programs_run_and_match_llvm() {
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
        // `for i in 0..10 { sum += i }` -> 0+..+9 = 45 (the canonical Range loop).
        (
            "range_sum_0_10",
            "fn main() { let mut sum = 0i64; for i in 0..10i64 { sum += i; } \
             std::process::exit(sum as i32); }",
            45,
        ),
        // A non-trivial `usize` Range computation (the index is `usize`, an
        // UNSIGNED `start < end`): sum of squares of 0..7 = 0+1+4+9+16+25+36 = 91.
        (
            "range_usize_squares",
            "fn main() { let n: usize = 7; let mut sum = 0i64; \
             for i in 0..n { sum += (i * i) as i64; } std::process::exit(sum as i32); }",
            91,
        ),
        // A Range over a non-zero start, with a `break` (early exit): 3+4+..+9 vs
        // 0..100 stopping at 10 -> here sum of 3..=9 = 42.
        (
            "range_nonzero_start",
            "fn main() { let mut sum = 0i64; for i in 3i64..10 { sum += i; } \
             std::process::exit(sum as i32); }",
            42,
        ),
        // `for x in &arr { sum += *x }` over a STACK array -> 10+20+30+40+50 = 150.
        (
            "slice_sum_stack_array",
            "fn main() { let arr: [i64; 5] = [10, 20, 30, 40, 50]; let mut sum = 0i64; \
             for x in &arr { sum += *x; } std::process::exit(sum as i32); }",
            150,
        ),
        // `for x in &arr { if *x > k { count += 1 } }` -> elements > 5 in
        // [3,8,1,9,4,7] are {8,9,7} = 3.
        (
            "slice_conditional_count",
            "fn main() { let arr: [i64; 6] = [3, 8, 1, 9, 4, 7]; let k = 5i64; \
             let mut count = 0i32; for x in &arr { if *x > k { count += 1; } } \
             std::process::exit(count); }",
            3,
        ),
        // A `for x in slice` over a `&[T]` FAT POINTER (the array is unsized to a
        // slice when passed to `sum_slice`): 11+22+33+44 = 110.
        (
            "slice_fat_pointer_sum",
            "fn sum_slice(s: &[i64]) -> i64 { let mut sum = 0i64; for x in s { sum += *x; } sum } \
             fn main() { let arr: [i64; 4] = [11, 22, 33, 44]; \
             std::process::exit(sum_slice(&arr) as i32); }",
            110,
        ),
        // A NESTED for-loop (Range inside Range): sum over 0<=j<i<5 of i*j.
        // i=2: 2*0+2*1=2; i=3: 0+3+6=9; i=4: 0+4+8+12=24 -> 2+9+24 = 35.
        (
            "nested_range_loops",
            "fn main() { let mut sum = 0i64; for i in 0..5i64 { for j in 0..i { sum += i * j; } } \
             std::process::exit(sum as i32); }",
            35,
        ),
        // An empty Range (start == end) iterates zero times, then a real range.
        (
            "range_empty_then_real",
            "fn main() { let mut sum = 0i64; for i in 5i64..5 { sum += i; } \
             for i in 1i64..5 { sum += i; } std::process::exit(sum as i32); }",
            10,
        ),
        // Iterating the SAME array twice (the iterator state is rebuilt each time):
        // 10+20+30 twice = 120.
        (
            "slice_iterated_twice",
            "fn main() { let arr: [i64; 3] = [10, 20, 30]; let mut sum = 0i64; \
             for x in &arr { sum += *x; } for x in &arr { sum += *x; } \
             std::process::exit(sum as i32); }",
            120,
        ),
        // The EXPLICIT `.iter()` form (`for x in arr.iter()`): `<[T]>::iter` builds
        // the `slice::Iter`, then `IntoIterator::into_iter` is the identity on it.
        // Product 1*2*3*4 = 24.
        (
            "slice_explicit_iter_product",
            "fn main() { let arr: [i64; 4] = [1, 2, 3, 4]; let mut product = 1i64; \
             for x in arr.iter() { product *= *x; } std::process::exit(product as i32); }",
            24,
        ),
        // A signed Range crossing zero (negative `start`): -3..4 sums to 0, then
        // -5..-2 sums to -12; offset by 100 keeps the exit byte non-negative.
        (
            "range_negative_start",
            "fn main() { let mut sum = 0i64; for i in -3i64..4 { sum += i; } \
             for i in -5i64..-2 { sum += i; } std::process::exit((sum + 100) as i32); }",
            88,
        ),
        // [TCG-SSA-071] regression pins: a loop bound computed by a PRE-LOOP CALL
        // (`.min()`/`.max()`/`.clamp()`/`.len()`) whose value is consumed AFTER the
        // first loop (to build a SECOND loop) must thread through the first loop's
        // header phi. Before the fix these fail-closed at -O0 ("value used ... never
        // defined") because the pre-loop call-result was excluded from loop-header
        // params; a stmt-defined bound (`if..{}else{}`) already worked. See
        // `compute_loop_header_params::call_assigned_preloop_numeric`.
        (
            // `.min()` bound: write v in loop-1, sum v in loop-2.
            "min_bound_two_loop_sum",
            "#[inline(never)] fn go(xs: &[i64]) -> i64 { let m = xs.len().min(4); \
             let mut v = [0i64; 4]; for i in 0..m { v[i] = xs[i] * 2; } \
             let mut acc = 0i64; for i in 0..m { acc += v[i]; } acc } \
             fn main() { let xs=[10i64,20,30,40,50]; std::process::exit(go(&xs) as i32); }",
            200,
        ),
        (
            // `.len()` bound across two loops.
            "len_bound_two_loop",
            "#[inline(never)] fn go(xs: &[i64]) -> i64 { let m = xs.len(); \
             let mut v = [0i64; 3]; for i in 0..m { v[i] = xs[i] + 1; } \
             let mut acc = 0i64; for i in 0..m { acc += v[i]; } acc } \
             fn main() { let xs=[5i64,6,7]; std::process::exit(go(&xs) as i32); }",
            21,
        ),
        (
            // `.clamp()` bound + square-sum in loop-2.
            "clamp_bound_two_loop",
            "#[inline(never)] fn go(xs: &[i64]) -> i64 { let m = xs.len().clamp(1, 4); \
             let mut v = [0i64; 4]; for i in 0..m { v[i] = xs[i]; } \
             let mut acc = 0i64; for i in 0..m { acc += v[i] * v[i]; } acc } \
             fn main() { let xs=[1i64,2,3,4,5]; std::process::exit(go(&xs) as i32); }",
            30,
        ),
        (
            // `.max(.min())` bound + product in loop-2.
            "max_bound_two_loop_product",
            "#[inline(never)] fn go(xs: &[i64]) -> i64 { let m = 2usize.max(xs.len().min(4)); \
             let mut v = [0i64; 4]; for i in 0..m { v[i] = xs[i]; } \
             let mut acc = 1i64; for i in 0..m { acc *= v[i]; } acc } \
             fn main() { let xs=[2i64,3,4,5,6]; std::process::exit(go(&xs) as i32); }",
            120,
        ),
        (
            // NESTED loop-2 under a `.min()` bound (bound threaded through loop-1 and
            // live into the nested loop's Range construction). sum_{i,j} v[i]*v[j].
            "min_bound_nested_loop",
            "#[inline(never)] fn go(xs: &[i64]) -> i64 { let m = xs.len().min(3); \
             let mut v = [0i64; 3]; for i in 0..m { v[i] = xs[i]; } let mut acc = 0i64; \
             for i in 0..m { for j in 0..m { acc += v[i] * v[j]; } } acc } \
             fn main() { let xs=[1i64,2,3,4]; std::process::exit(go(&xs) as i32); }",
            36,
        ),
        (
            // `.min()` bound value used AFTER the loop directly (m live-out): a
            // single loop, so the bound must survive to the post-loop `+ m`.
            "min_bound_used_after_loop",
            "#[inline(never)] fn go(xs: &[i64]) -> i64 { let m = xs.len().min(4); \
             let mut acc = 0i64; for i in 0..m { acc += xs[i]; } acc + m as i64 } \
             fn main() { let xs=[10i64,20,30,40,50]; std::process::exit(go(&xs) as i32); }",
            104,
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
