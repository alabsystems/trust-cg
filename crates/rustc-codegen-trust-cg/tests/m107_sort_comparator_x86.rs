// Integration test: CLOSURE-COMPARATOR SLICE SORTS —
// `<[T]>::sort_by_key(f)` / `sort_unstable_by_key(f)` / `sort_by_cached_key(f)`
// over integer slices/`Vec`s with a ZST integer-key closure, compiled for
// x86_64 via the rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with
// the sorted-buffer exit code checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The bridge lowers `v.sort_by_key(f)` (after the `deref_mut` -> `&mut [T]`) to an
// in-place, closure-driven STABLE INSERTION SORT over the slice buffer: the same
// algorithm as the proven `__trustcg_vec_sort_T` helper, but each comparison is
// `keyfn(a[j]) > keyfn(insertee)` over a scalar integer key. A key-based sort is
// ALWAYS a valid total order (keys compared by `<` on an integer), so unlike a raw
// `sort_by(|a,b| ..)` comparator there is no invalid-comparator hazard and the
// resulting permutation is uniquely determined — the bridge's insertion sort is
// observably identical to std's sort for the same key. The strict `>` shift makes
// the sort stable (equal keys keep input order), matching `slice::sort_by_key`;
// `sort_unstable_by_key` / `sort_by_cached_key` observe the SAME order on this
// total order. A wrong sort order would diverge from LLVM, so equal exit codes are
// the differential we assert.
//
// FAIL-CLOSED (asserted to produce NO binary — never a miscompile):
//   * `sort_by(|a,b| ..)` / `sort_unstable_by(|a,b| ..)` — a raw
//     `Fn(&T,&T) -> Ordering` may not be a valid total order, so its result is
//     algorithm-dependent (driftsort/timsort vs our insertion sort); fail closed.
//   * `retain(|x| ..)` — a length-mutating Vec compaction, not modeled.
//   * a CAPTURING (non-ZST) key closure.
//   * a non-integer key.

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
    assert!(status.success(), "cargo build failed; cannot run sort-comparator test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m107_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src`; returns `Some(bin)` on success, `None` if the (trust-cg) compile
/// failed (the fail-closed case — used by the negative pins).
fn try_compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> Option<PathBuf> {
    let src_path = dir.join(format!("{name}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(name);
    let mut cmd = Command::new("rustup");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin"]);
    if let Some(dylib) = backend {
        cmd.arg(backend_arg(dylib));
    }
    cmd.args(["--target", TARGET, "-Cpanic=abort", opt])
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

fn compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>, opt: &str) -> PathBuf {
    try_compile(dir, name, src, backend, opt).unwrap_or_else(|| {
        panic!(
            "compile of `{name}` failed ({} backend, {opt})",
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

const BB: &str = "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }";

/// The differential: each sort program is compiled by trust-cg AND LLVM at -O0 and
/// -O3, run, and the exit codes must match. At -O3 the bridge often fails closed
/// (std generics inline past the interception); that is a safe coverage gap, so we
/// only assert the bridge MATCHES when it produces a binary.
#[test]
fn sort_by_key_run_and_match_llvm() {
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

    // Build a Vec from a literal data array (the `push` loop keeps the data runtime,
    // defeating const-folding), sort it, and exit with a checksum of the sorted vec.
    // `chk` = sum of v[i]*(i+1) — sensitive to BOTH order and content, so any wrong
    // permutation diverges. `INIT` writes the data into `v`.
    fn prog(decl_ty: &str, data: &[i64], sort_call: &str) -> String {
        let pushes = data
            .iter()
            .map(|d| format!("v.push(bb({d}{decl_ty}));"))
            .collect::<Vec<_>>()
            .join(" ");
        format!(
            "{BB}\nfn main() {{ \
               let mut v: Vec<{decl_ty}> = Vec::new(); {pushes} \
               {sort_call}; \
               let mut chk: i64 = 0; let mut i = 0usize; \
               while i < v.len() {{ chk += (v[i] as i64) * ((i as i64) + 1); i += 1; }} \
               std::process::exit((chk & 0xff) as i32); \
             }}\n"
        )
    }

    // (name, source) — each is differential-checked at O0 and O3.
    let shapes: Vec<(String, String)> = vec![
        // ascending key = identity
        ("i64_key_id".into(), prog("i64", &[5, 2, 9, 1, 7, 3], "v.sort_by_key(|&x| x)")),
        // descending key = -x
        ("i64_key_neg".into(), prog("i64", &[5, 2, 9, 1, 7, 3], "v.sort_by_key(|&x| -x)")),
        // key = x % 5 (ties preserve input order — stability)
        ("i64_key_mod".into(), prog("i64", &[10, 2, 7, 5, 12, 1, 6], "v.sort_by_key(|&x| x % 5)")),
        // unstable_by_key, identity
        ("i64_unstable_id".into(), prog("i64", &[8, 3, 8, 1, 4, 1], "v.sort_unstable_by_key(|&x| x)")),
        // cached_key, identity (observably same order)
        ("i64_cached_id".into(), prog("i64", &[6, 6, 2, 9, 2, 0], "v.sort_by_cached_key(|&x| x)")),
        // signed: negatives sort before positives
        ("i64_signed".into(), prog("i64", &[-3, 5, -8, 2, -1, 0], "v.sort_by_key(|&x| x)")),
        // u32 unsigned key: 250 sorts AFTER 5 (not before, as a signed -6 would)
        ("u32_key_id".into(), prog("u32", &[5, 200, 9, 1, 250, 30], "v.sort_by_key(|&x| x)")),
        // u8: full unsigned ordering
        ("u8_key_id".into(), prog("u8", &[5, 200, 9, 1, 250, 30, 128], "v.sort_by_key(|&x| x)")),
        // i32 with a wider (i64) key projection
        ("i32_key_wide".into(), prog("i32", &[4, 1, 3, 2, 5], "v.sort_by_key(|&x| (x as i64) * 7)")),
        // empty vec — built without a zero-length array literal (which is a SEPARATE
        // pre-existing fail-closed gap); the `n=0` loop pushes nothing.
        (
            "empty".into(),
            format!(
                "{BB}\nfn main() {{ \
                   let mut v: Vec<i64> = Vec::new(); \
                   let n = bb(0i64); let mut i = 0i64; while i < n {{ v.push(bb(i)); i += 1; }} \
                   v.sort_by_key(|&x| x); \
                   let mut chk: i64 = 0; let mut k = 0usize; \
                   while k < v.len() {{ chk += v[k] * ((k as i64) + 1); k += 1; }} \
                   std::process::exit((chk & 0xff) as i32); \
                 }}\n"
            ),
        ),
        // single element
        ("single".into(), prog("i64", &[42], "v.sort_by_key(|&x| x)")),
        // already sorted (ascending)
        ("already_sorted".into(), prog("i64", &[1, 2, 3, 4, 5], "v.sort_by_key(|&x| x)")),
        // reverse sorted
        ("reverse_sorted".into(), prog("i64", &[5, 4, 3, 2, 1], "v.sort_by_key(|&x| x)")),
        // all duplicates
        ("all_dups".into(), prog("i64", &[7, 7, 7, 7], "v.sort_by_key(|&x| x)")),
        // many duplicates with key
        ("dups_key".into(), prog("i64", &[3, 1, 3, 1, 3, 1, 2], "v.sort_by_key(|&x| x)")),
        // a slice (array) sort_by_key directly (no Vec)
        (
            "array_slice".into(),
            format!(
                "{BB}\nfn main() {{ \
                   let mut a = [bb(5i64), bb(2), bb(9), bb(1), bb(7)]; \
                   a.sort_by_key(|&x| x); \
                   let mut chk: i64 = 0; let mut i = 0usize; \
                   while i < a.len() {{ chk += a[i] * ((i as i64) + 1); i += 1; }} \
                   std::process::exit((chk & 0xff) as i32); \
                 }}\n"
            ),
        ),
    ];

    let mut matched = 0u32;
    let mut closed_o3 = 0u32;
    for (name, src) in &shapes {
        for opt in ["-O0", "-O3"] {
            let opt_flag = if opt == "-O0" { "-Copt-level=0" } else { "-Copt-level=3" };
            let suffix = if opt == "-O0" { "o0" } else { "o3" };
            let llvm_bin = compile(&dir, &format!("{name}_{suffix}_llvm"), src, None, opt_flag);
            let llvm_exit = run_exit_code(&llvm_bin);
            match try_compile(&dir, &format!("{name}_{suffix}_tcg"), src, Some(&dylib), opt_flag) {
                Some(tcg_bin) => {
                    let tcg_exit = run_exit_code(&tcg_bin);
                    assert_eq!(
                        tcg_exit, llvm_exit,
                        "trust-cg exit code for `{name}` ({opt}) is {tcg_exit}, LLVM is {llvm_exit} (must match)"
                    );
                    matched += 1;
                }
                None => {
                    // Fail-closed is acceptable (a safe coverage gap), but we want at
                    // least the -O0 cases to compile (the bridge intercepts there).
                    if opt == "-O3" {
                        closed_o3 += 1;
                    } else {
                        panic!("`{name}` failed closed at -O0 (expected the bridge to lower sort_by_key)");
                    }
                }
            }
        }
    }
    eprintln!("sort_by_key: matched={matched} fail_closed_o3={closed_o3}");
    assert!(matched > 0, "no sort_by_key program compiled+matched");

    let _ = std::fs::remove_dir_all(&dir);
}

/// Negative pins: comparator shapes the bridge MUST fail closed on (produce no
/// binary at -O0) — never silently miscompile. Each is valid Rust (LLVM builds it).
#[test]
fn unmodeled_sort_comparators_fail_closed() {
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

    fn prog(sort_call: &str) -> String {
        format!(
            "{BB}\nfn main() {{ \
               let mut v: Vec<i64> = Vec::new(); \
               let mut i = 0i64; while i < 6 {{ v.push(bb(6 - i)); i += 1; }} \
               {sort_call}; \
               std::process::exit((v[0] & 0xff) as i32); \
             }}\n"
        )
    }

    let closed: Vec<(String, String)> = vec![
        // sort_by with a raw comparator — not a provable total order; fail closed.
        ("sort_by_cmp".into(), prog("v.sort_by(|a, b| a.cmp(b))")),
        ("sort_by_rev".into(), prog("v.sort_by(|a, b| b.cmp(a))")),
        ("sort_unstable_by_cmp".into(), prog("v.sort_unstable_by(|a, b| a.cmp(b))")),
        // retain — a length-mutating compaction, not modeled.
        ("retain_even".into(), prog("v.retain(|&x| x % 2 == 0)")),
        // a CAPTURING key closure (captures `k`): must be a ZST; fail closed.
        (
            "key_capturing".into(),
            format!(
                "{BB}\nfn main() {{ \
                   let mut v: Vec<i64> = Vec::new(); \
                   let mut i = 0i64; while i < 6 {{ v.push(bb(6 - i)); i += 1; }} \
                   let k = bb(3i64); \
                   v.sort_by_key(|&x| (x - k).abs()); \
                   std::process::exit((v[0] & 0xff) as i32); \
                 }}\n"
            ),
        ),
    ];

    let mut closed_count = 0u32;
    for (name, src) in &closed {
        // LLVM accepts it (valid Rust).
        let _ = compile(&dir, &format!("{name}_llvm"), src, None, "-Copt-level=0");
        // trust-cg must fail closed: NO binary produced at -O0.
        let tcg = try_compile(&dir, &format!("{name}_tcg"), src, Some(&dylib), "-Copt-level=0");
        assert!(
            tcg.is_none(),
            "`{name}` must FAIL CLOSED under trust-cg (unmodeled comparator), but a binary was produced"
        );
        closed_count += 1;
    }
    eprintln!("unmodeled_sort_comparators: fail_closed={closed_count}");

    let _ = std::fs::remove_dir_all(&dir);
}
