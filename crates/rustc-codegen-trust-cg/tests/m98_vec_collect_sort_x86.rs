// Integration test: std Rust using `Vec<T>` (integer elements) `collect` and
// in-place `sort` compiled for x86_64 via the rustc_codegen_trust_cg bridge —
// COMPILED, LINKED, and RUN, with exit codes checked against the default LLVM
// backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS — `iter.collect::<Vec<T>>()` and `v.sort()` / `v.sort_unstable()`.
//
// COLLECT: at -O0 rustc emits an explicit
// `<Iter as Iterator>::collect::<Vec<T>>(move iter)` call whose destination is a
// `Vec<T>`. The bridge intercepts it (by the `Vec` destination), resolves the
// source iterator chain (Range / slice::Iter / Map / Filter, possibly nested),
// and DRIVES it to exhaustion — running the SAME element-wise chain loop the
// `.sum()`/`.fold()` consumers use — pushing each yielded element into a fresh
// `{ ptr, cap, len }` Vec slot. So `(0..n).collect()`, `.map(..).collect()`,
// `.filter(..).collect()`, `.map().filter().collect()`, and a slice-iter collect
// all materialize the correct Vec at -O0.
//
// At -O3 rustc INLINES `collect` down to a `SpecFromIterNested::from_iter` real
// call into the RawVec allocator machinery this backend does not lower, so it
// FAILS CLOSED (no binary) rather than miscompiling — asserted below.
//
// SORT: at -O0 `v.sort()` / `v.sort_unstable()` lowers to
// `<Vec<T> as DerefMut>::deref_mut(&mut v)` (yielding `&mut [T]`) then
// `<[T]>::sort(&mut [T])`. The bridge intercepts the `deref_mut` (binding the
// slice's `{ data, len }` to the Vec's buffer) and the `sort` call (reading the
// slice's data+len and calling the hand-authored `__trustcg_vec_sort_T` in-place
// insertion-sort helper, with a signed/unsigned per-element compare). A custom
// comparator (`sort_by`/`sort_by_key`) or a non-integer element fails closed.
//
// Each program is compiled with BOTH backends at the indicated opt level(s) and
// run; the trust-cg exit code must equal the LLVM exit code (and the expected
// value). A wrong collected element or sort order is a miscompile, so equal exit
// codes are the differential we assert. Signed-vs-unsigned sort order and
// duplicate keys are covered explicitly.

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
    assert!(status.success(), "cargo build failed; cannot run collect/sort test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m98_{stem}_{}", std::process::id()));
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
) -> (std::process::Output, PathBuf) {
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
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path);
    let output = cmd.output().expect("spawn rustc");
    (output, bin)
}

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
    let (output, bin) = try_compile(dir, name, src, backend, opt);
    assert!(
        output.status.success(),
        "compile of `{name}` failed ({} backend, -Copt-level={opt}). stderr: <<<{}>>>",
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

/// The full differential for the matched (`-O0`) `collect` / `sort` shapes: each
/// program is compiled by trust-cg AND LLVM at -O0, run, and the exit codes must
/// match each other and the expected value. A divergence is a miscompile (a wrong
/// collected element or sort order).
#[test]
fn collect_and_sort_programs_run_and_match_llvm_o0() {
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

    // Helper that sums a Vec by index (the `.iter().sum()` deref path is exercised
    // separately) and exits with `s % 251` so the value fits an exit code.
    let sum_idx = "let mut s = 0i64; let mut j = 0usize; \
                   while j < v.len() { s += v[j] as i64; j += 1; } \
                   std::process::exit((s % 251) as i32);";

    // (name, source, expected exit code).
    let shapes: &[(&str, &str, i32)] = &[
        // (0..n).collect(): 0+1+..+9 = 45.
        (
            "range_collect",
            &format!("fn main() {{ let v: Vec<i64> = (0..10i64).collect(); {sum_idx} }}"),
            45 % 251,
        ),
        // .map(|x| x*2).collect(): (0+1+..+9)*2 = 90.
        (
            "map_collect",
            &format!(
                "fn main() {{ let v: Vec<i64> = (0..10i64).map(|x| x*2).collect(); {sum_idx} }}"
            ),
            90 % 251,
        ),
        // .filter(|x| x%3==0).collect() over 0..20: 0+3+6+9+12+15+18 = 63.
        (
            "filter_collect",
            &format!(
                "fn main() {{ let v: Vec<i64> = (0..20i64).filter(|x| x % 3 == 0).collect(); {sum_idx} }}"
            ),
            63 % 251,
        ),
        // .map().filter().collect(): map x->x*x over 0..10, keep even -> sum.
        (
            "map_filter_collect",
            &format!(
                "fn main() {{ let v: Vec<i64> = (0..10i64).map(|x| x*x).filter(|y| y % 2 == 0).collect(); {sum_idx} }}"
            ),
            ((0i64..10).map(|x| x * x).filter(|y| y % 2 == 0).sum::<i64>() % 251) as i32,
        ),
        // Collect length used (not sum): count of kept elements.
        (
            "filter_collect_len",
            "fn main() { let v: Vec<i64> = (0..20i64).filter(|x| x % 3 == 0).collect(); \
             std::process::exit(v.len() as i32); }",
            7,
        ),
        // i32 element collect.
        (
            "i32_collect",
            &format!("fn main() {{ let v: Vec<i32> = (0..12i32).map(|x| x + 1).collect(); {sum_idx} }}"),
            ((1i64..=12).sum::<i64>() % 251) as i32,
        ),
        // Empty collect.
        (
            "empty_collect",
            "fn main() { let v: Vec<i64> = (0..0i64).collect(); \
             std::process::exit((v.len() as i32) + 9); }",
            9,
        ),
        // sort: ascending; read v[0] + v[7].
        (
            "i64_sort",
            "fn main() { let mut v: Vec<i64> = Vec::new(); \
             let d = [3i64,1,4,1,5,9,2,6]; let mut i = 0usize; \
             while i < 8 { v.push(d[i]); i += 1; } v.sort(); \
             std::process::exit((v[0] + v[7]) as i32); }",
            1 + 9,
        ),
        // sort_unstable: same data, full sorted sum-of-prefix property: v[0]==1.
        (
            "i64_sort_unstable",
            "fn main() { let mut v: Vec<i64> = Vec::new(); \
             let d = [30i64,10,40,10,50,90,20,60,15]; let mut i = 0usize; \
             while i < 9 { v.push(d[i]); i += 1; } v.sort_unstable(); \
             std::process::exit((v[0] + v[8]) as i32); }",
            10 + 90,
        ),
        // SIGNED sort order: negatives must sort BEFORE positives.
        (
            "i64_sort_signed",
            "fn main() { let mut v: Vec<i64> = Vec::new(); \
             let d = [3i64,-7,0,-1,8,-100,42]; let mut i = 0usize; \
             while i < 7 { v.push(d[i]); i += 1; } v.sort(); \
             std::process::exit((v[0] + 200) as i32); }",
            -100 + 200,
        ),
        // UNSIGNED sort order on u8: 200 must sort AFTER 5 (not before, as a
        // signed-i8 interpretation of 200 = -56 would). v[last] == 200.
        (
            "u8_sort_unsigned",
            "fn main() { let mut v: Vec<u8> = Vec::new(); \
             let d = [200u8,5,255,1,128,0]; let mut i = 0usize; \
             while i < 6 { v.push(d[i]); i += 1; } v.sort(); \
             std::process::exit(v[5] as i32); }",
            255,
        ),
        // u32 sort, duplicate keys preserved, fully sorted: check v[0] and v[len-1].
        (
            "u32_sort_dups",
            "fn main() { let mut v: Vec<u32> = Vec::new(); \
             let d = [7u32,7,3,9,3,1,9,7]; let mut i = 0usize; \
             while i < 8 { v.push(d[i]); i += 1; } v.sort(); \
             std::process::exit((v[0] + v[7]) as i32); }",
            1 + 9,
        ),
        // Already-sorted input stays sorted (insertion-sort no-op path).
        (
            "i64_sort_presorted",
            "fn main() { let mut v: Vec<i64> = Vec::new(); \
             let mut i = 0i64; while i < 10 { v.push(i); i += 1; } v.sort(); \
             let mut ok = true; let mut k = 1usize; \
             while k < v.len() { if v[k] < v[k-1] { ok = false; } k += 1; } \
             std::process::exit(if ok { 42 } else { 1 }); }",
            42,
        ),
        // Empty sort + single-element sort (boundary lengths).
        (
            "sort_empty_single",
            "fn main() { let mut v: Vec<i64> = Vec::new(); v.sort(); \
             v.push(7); v.sort(); \
             std::process::exit((v.len() as i32) + v[0] as i32); }",
            1 + 7,
        ),
        // collect THEN sort (composition): collect a shuffled-by-map range, sort it.
        (
            "collect_then_sort",
            "fn main() { let mut v: Vec<i64> = (0..8i64).map(|x| (x * 5) % 7).collect(); \
             v.sort(); std::process::exit((v[0] + v[7]) as i32); }",
            {
                let mut a: Vec<i64> = (0i64..8).map(|x| (x * 5) % 7).collect();
                a.sort();
                (a[0] + a[7]) as i32
            },
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_o0_llvm"), src, None, "0");
        let tcg_bin = compile(&dir, &format!("{name}_o0_tcg"), src, Some(&dylib), "0");
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            llvm_exit, *expected,
            "LLVM backend exit code for `{name}` (-O0) is {llvm_exit}, expected {expected}"
        );
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for `{name}` (-O0) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// `collect` at -O3 used to fail closed on the `SpecFromIterNested::from_iter`
/// RawVec path; the conditional-grow Vec::push restructure (9329b93) made the
/// inlined O3 collect lowerable, so this test is PROMOTED into the matched set:
/// trust-cg must now produce a binary whose exit matches LLVM (45). If it ever
/// fails closed again, that is a completeness REGRESSION this test catches.
#[test]
fn collect_o3_matches() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("o3fc");

    let src = "fn main() { let v: Vec<i64> = (0..10i64).collect(); \
               let mut s = 0i64; let mut j = 0usize; \
               while j < v.len() { s += v[j]; j += 1; } \
               std::process::exit((s % 251) as i32); }";

    // -O0: trust-cg matches LLVM (= 45).
    let llvm0 = compile(&dir, "collect_o0_llvm", src, None, "0");
    let tcg0 = compile(&dir, "collect_o0_tcg", src, Some(&dylib), "0");
    assert_eq!(run_exit_code(&llvm0), 45, "LLVM collect -O0 should be 45");
    assert_eq!(run_exit_code(&tcg0), 45, "trust-cg collect -O0 should match LLVM (45)");

    // -O3: PROMOTED (post-9329b93): trust-cg must compile AND match LLVM.
    let llvm3 = compile(&dir, "collect_o3_llvm", src, None, "3");
    assert_eq!(run_exit_code(&llvm3), 45, "LLVM collect -O3 should be 45");
    let tcg3 = compile(&dir, "collect_o3_tcg", src, Some(&dylib), "3");
    assert_eq!(
        run_exit_code(&tcg3),
        45,
        "trust-cg collect -O3 must match LLVM (45); a fail-closed or wrong exit \
         here is a regression of the 9329b93 conditional-grow promotion"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// A `sort_by` / `sort_by_key` custom comparator cannot be proven ascending by
/// the bridge, so it FAILS CLOSED (no binary) rather than risk a wrong order.
/// LLVM runs it; trust-cg must not produce a binary at -O0.
#[test]
fn sort_by_custom_comparator_fails_closed_o0() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("sortby");

    // sort_by with a DESCENDING comparator — definitely not the default ascending.
    let src = "fn main() { let mut v: Vec<i64> = Vec::new(); \
               let d = [3i64,1,4,1,5]; let mut i = 0usize; \
               while i < 5 { v.push(d[i]); i += 1; } \
               v.sort_by(|a, b| b.cmp(a)); \
               std::process::exit(v[0] as i32); }";

    // LLVM: descending sort -> v[0] == 5.
    let llvm0 = compile(&dir, "sortby_o0_llvm", src, None, "0");
    assert_eq!(run_exit_code(&llvm0), 5, "LLVM sort_by descending -O0 should be 5");

    // trust-cg: must fail CLOSED (cannot prove the comparator's order).
    let (output, bin) = try_compile(&dir, "sortby_o0_tcg", src, Some(&dylib), "0");
    assert!(
        !output.status.success() && !bin.exists(),
        "trust-cg unexpectedly compiled a custom-comparator sort_by at -O0; a \
         comparator whose order cannot be proven ascending must fail closed"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
