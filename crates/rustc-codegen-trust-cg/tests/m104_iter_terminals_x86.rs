// Integration test: REDUCING / SHORT-CIRCUITING ITERATOR TERMINALS —
// `.find(p)` / `.position(p)` / `.any(p)` / `.all(p)` / `.min()` / `.max()` /
// `.min_by(cmp)` / `.max_by(cmp)` / `.min_by_key(f)` / `.max_by_key(f)` /
// `.product()` / `.last()` / `.nth(k)` and the `.chain(other)` adapter — over
// `Range` and slices (and composed with the
// existing `.map` / `.filter` / `.copied` / `.take` / `.skip` / `.step_by` /
// `.rev` / `.enumerate` adapters), compiled for x86_64 via the
// rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN, with exit codes
// checked against the default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The bridge drives the iterator chain to exhaustion (or, for the short-circuiting
// terminals, until the first match) directly against the memory-backed chain slot,
// using the SAME `emit_chain_next` header -> cont -> body loop the existing
// `.sum`/`.fold`/`.count` consumers use:
//   * `.find`/`.position`/`.any`/`.all`/`.nth` add a found-flag + an early break
//     out of the loop on a hit;
//   * `.min`/`.max`/`.product`/`.last` reduce to exhaustion;
//   * `.chain(b)` concatenates two Range sub-sources (drain `a`, then `b`) by
//     iterating each sub-source's raw Range state within the `Chain` slot.
// The Option-returning terminals materialize their `Some`/`None` result into the
// destination's memory-backed `Option` slot through the existing memory-enum
// machinery. A wrong reduction (bad found value/index/bool/min/max, dropped or
// duplicated element) would diverge from LLVM, so equal exit codes are the
// differential we assert. (All at -O0; -O3 inlines the std generics so the bridge's
// interception often does not trigger and the program fails closed — a safe
// coverage gap, not a miscompile.)
//
// FAIL-CLOSED (asserted to produce NO binary — never a miscompile):
//   * a terminal with a CAPTURING (non-ZST) predicate / key closure;
//   * a nested `.chain().chain()` (a Concat sub-source is not modeled);
//   * a `.chain()` of two SLICE sources (the niche-encoded `Option<slice::Iter>`
//     sub-source has no addressable Direct payload offset).

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
    assert!(status.success(), "cargo build failed; cannot run iter-terminal test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m104_{stem}_{}", std::process::id()));
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
fn try_compile(dir: &Path, name: &str, src: &str, backend: Option<&Path>) -> Option<PathBuf> {
    try_compile_at(dir, name, src, backend, 0)
}

fn try_compile_at(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt_level: u8,
) -> Option<PathBuf> {
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
        .arg(format!("-Copt-level={opt_level}"))
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
    compile_at(dir, name, src, backend, 0)
}

fn compile_at(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt_level: u8,
) -> PathBuf {
    try_compile_at(dir, name, src, backend, opt_level).unwrap_or_else(|| {
        panic!(
            "compile of `{name}` failed ({} backend)",
            if backend.is_some() { "trust-cg" } else { "llvm" }
        )
    })
}

/// The O3 `Iterator::reduce` recognizer may flatten only the exact `Ord::cmp`
/// diagnostic item used by ordinary `.min()` / `.max()`. A user comparator is
/// semantically load-bearing, even when its def path contains `Ord::cmp`.
#[test]
fn ord_minmax_and_custom_comparators_preserve_semantics_at_o3() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("minmax_cmp_identity");
    const BB: &str = "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }";

    for (name, body, expected) in [
        (
            "ord_min_o3",
            "let r = (bb(1i64)..bb(10)).min().unwrap_or(-1); std::process::exit(r as i32);",
            1,
        ),
        (
            "ord_max_o3",
            "let r = (bb(1i64)..bb(10)).max().unwrap_or(-1); std::process::exit(r as i32);",
            9,
        ),
    ] {
        let src = format!("{BB}\nfn main() {{ {body} }}\n");
        let llvm = compile_at(&dir, &format!("{name}_llvm"), &src, None, 3);
        let tcg = compile_at(&dir, &format!("{name}_tcg"), &src, Some(&dylib), 3);
        assert_eq!(run_exit_code(&llvm), expected, "LLVM `{name}` result");
        assert_eq!(run_exit_code(&tcg), expected, "trust-cg `{name}` result");
    }

    let custom: &[(&str, &str, i32)] = &[
        (
            "reverse_min_by_o3",
            "let r = (bb(1i64)..bb(10)).min_by(|a, b| b.cmp(a)).unwrap_or(-1); \
             std::process::exit(r as i32);",
            9,
        ),
        (
            "reverse_max_by_o3",
            "let r = (bb(1i64)..bb(10)).max_by(|a, b| b.cmp(a)).unwrap_or(-1); \
             std::process::exit(r as i32);",
            1,
        ),
        (
            "spoofed_ord_cmp_path_o3",
            "trait MyOrd { fn cmp(a: &Self, b: &Self) -> std::cmp::Ordering; } \
             impl MyOrd for i64 { fn cmp(a: &Self, b: &Self) -> std::cmp::Ordering { b.cmp(a) } } \
             let r = (bb(1i64)..bb(10)).min_by(<i64 as MyOrd>::cmp).unwrap_or(-1); \
             std::process::exit(r as i32);",
            9,
        ),
    ];
    for (name, body, native_expected) in custom {
        let src = format!("{BB}\nfn main() {{ {body} }}\n");
        let llvm = compile_at(&dir, &format!("{name}_llvm"), &src, None, 3);
        assert_eq!(
            run_exit_code(&llvm),
            *native_expected,
            "LLVM `{name}` sanity result"
        );
        // Depending on optimized MIR shape, the comparator-driven reducer may
        // lower this exactly or fail closed. A successful build must preserve the
        // custom comparator rather than flattening it to ordinary min/max.
        if let Some(tcg) =
            try_compile_at(&dir, &format!("{name}_tcg"), &src, Some(&dylib), 3)
        {
            assert_eq!(
                run_exit_code(&tcg),
                *native_expected,
                "trust-cg `{name}` custom-comparator result"
            );
        }
    }

    // Name spoof: a user-defined method whose final segment is `min_by` and whose
    // receiver really is Range must execute its own body, not the std interceptor.
    let spoof = format!(
        "{BB}\n\
         trait Evil {{ fn min_by<F>(self, f: F) -> Option<i64> \
             where F: FnMut(&i64, &i64) -> std::cmp::Ordering; }}\n\
         impl Evil for std::ops::Range<i64> {{\n\
             #[inline(never)] fn min_by<F>(self, _f: F) -> Option<i64> \
                 where F: FnMut(&i64, &i64) -> std::cmp::Ordering {{ Some(77) }}\n\
         }}\n\
         fn main() {{ let r = Evil::min_by(bb(1i64)..bb(10), |a,b| a.cmp(b))\n\
             .unwrap_or(-1); std::process::exit(r as i32); }}\n"
    );
    let llvm = compile(&dir, "evil_min_by_llvm", &spoof, None);
    let tcg = compile(&dir, "evil_min_by_tcg", &spoof, Some(&dylib));
    assert_eq!(run_exit_code(&llvm), 77, "LLVM name-spoof sanity");
    assert_eq!(run_exit_code(&tcg), 77, "trust-cg must retain user method body");

    let _ = std::fs::remove_dir_all(&dir);
}

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

/// The differential: each terminal program is compiled by trust-cg AND LLVM, run,
/// and the exit codes must match each other and the expected value. A divergence
/// is a miscompiled reduction (wrong found value/index/bool/min/max/product).
#[test]
fn iter_terminals_run_and_match_llvm() {
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

    const BB: &str = "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }";

    // (name, body-of-main, expected exit code). `bb` defeats const-folding so the
    // synthesized loop actually runs.
    let shapes: &[(&str, &str, i32)] = &[
        // --- find / position (short-circuit, Option result) ---
        // first x with x*x > 20 over 0..10 -> 5.
        (
            "find_sq_gt_20",
            "let n = bb(10i64); let r = (0..n).find(|&x| x * x > bb(20)).unwrap_or(-1); \
             std::process::exit(r as i32);",
            5,
        ),
        // find no match -> None -> -1 (255 as exit byte).
        (
            "find_none",
            "let n = bb(10i64); let r = (0..n).find(|&x| x > bb(100)).unwrap_or(-1); \
             std::process::exit(r as i32);",
            255,
        ),
        // map then find: ((0..6)+10) first > 13 -> 14.
        (
            "map_find",
            "let n = bb(6i64); let r = (0..n).map(|x| x + 10).find(|&x| x > bb(13)).unwrap_or(-1); \
             std::process::exit(r as i32);",
            14,
        ),
        // position of first x == 7 over 0..10 -> 7.
        (
            "position_eq_7",
            "let n = bb(10i64); \
             let r = match (0..n).position(|x| x == bb(7)) { Some(p) => p as i64, None => -1 }; \
             std::process::exit(r as i32);",
            7,
        ),
        // position no match -> None -> -1.
        (
            "position_none",
            "let n = bb(10i64); \
             let r = match (0..n).position(|x| x == bb(77)) { Some(p) => p as i64, None => -1 }; \
             std::process::exit(r as i32);",
            255,
        ),
        // --- any / all (short-circuit, bool result) ---
        (
            "any_div5",
            "let n = bb(10i64); let r = (1..n).any(|x| x % 5 == 0); std::process::exit(r as i32);",
            1,
        ),
        (
            "any_false",
            "let n = bb(10i64); let r = (0..n).any(|x| x > bb(100)); std::process::exit(r as i32);",
            0,
        ),
        (
            "all_true",
            "let n = bb(10i64); let r = (0..n).all(|x| x < bb(100)); std::process::exit(r as i32);",
            1,
        ),
        (
            "all_false",
            "let n = bb(10i64); let r = (0..n).all(|x| x < bb(5)); std::process::exit(r as i32);",
            0,
        ),
        // `all` over an EMPTY iterator is vacuously true.
        (
            "all_empty_vacuous",
            "let n = bb(0i64); let r = (0..n).all(|x| x > bb(100)); std::process::exit(r as i32);",
            1,
        ),
        // --- min / max (reduce, Option result) ---
        // max of (0..10).map(|x| (x*3)%7) -> 6.
        (
            "map_max",
            "let n = bb(10i64); let r = (0..n).map(|x| (x * 3) % 7).max().unwrap_or(-1); \
             std::process::exit(r as i32);",
            6,
        ),
        // min of the same -> 0.
        (
            "map_min",
            "let n = bb(10i64); let r = (0..n).map(|x| (x * 3) % 7).min().unwrap_or(-1); \
             std::process::exit(r as i32);",
            0,
        ),
        // min over an empty range -> None -> -1.
        (
            "min_empty",
            "let n = bb(0i64); let r = (0..n).min().unwrap_or(-1); std::process::exit(r as i32);",
            255,
        ),
        // First-element paths must establish state before reading payload/key.
        (
            "min_singleton_i128",
            "let r = (bb(7i128)..bb(8i128)).min().unwrap_or(-1); std::process::exit(r as i32);",
            7,
        ),
        // min_by/max_by call the comparator exactly N-1 times (never for the first
        // item). The side-effect count makes an eager first call observable.
        (
            "min_by_empty_no_cmp",
            "static mut CALLS: i32 = 0; let n = bb(0i64); \
             let r = (0..n).min_by(|a,b| { unsafe { CALLS += 1; } a.cmp(b) }); \
             let c = unsafe { CALLS }; std::process::exit((r.unwrap_or(-1)+1+c*10) as i32);",
            0,
        ),
        (
            "min_by_singleton_no_cmp",
            "static mut CALLS: i32 = 0; let n = bb(1i64); \
             let r = (0..n).min_by(|a,b| { unsafe { CALLS += 1; } a.cmp(b) }).unwrap(); \
             let c = unsafe { CALLS }; std::process::exit((r+c*10) as i32);",
            0,
        ),
        (
            "max_by_n_minus_one_calls",
            "static mut CALLS: i32 = 0; let n = bb(5i64); \
             let r = (0..n).max_by(|a,b| { unsafe { CALLS += 1; } a.cmp(b) }).unwrap(); \
             let c = unsafe { CALLS }; std::process::exit((r+c*10) as i32);",
            44,
        ),
        // Exact scratch types: narrow items and 128-bit items/keys must not be
        // stored through a shared I64 alloca.
        (
            "min_by_u8_exact_slot",
            "let r = (bb(1u8)..bb(5u8)).min_by(|a,b| b.cmp(a)).unwrap(); \
             std::process::exit(r as i32);",
            4,
        ),
        (
            "max_by_i128_exact_slot",
            "let r = (bb(0i128)..bb(5i128)).max_by(|a,b| a.cmp(b)).unwrap(); \
             std::process::exit(r as i32);",
            4,
        ),
        // by_key calls its key function exactly N times, including the first; an
        // i128 key also pins the key-slot width.
        (
            "max_by_key_i128_exact_calls",
            "static mut CALLS: i32 = 0; let n = bb(5i64); \
             let r = (0..n).max_by_key(|x| { unsafe { CALLS += 1; } (*x as i128)*2 }).unwrap(); \
             let c = unsafe { CALLS }; std::process::exit((r+c*10) as i32);",
            54,
        ),
        (
            "min_by_key_empty_no_calls",
            "static mut CALLS: i32 = 0; let n = bb(0i64); \
             let r = (0..n).min_by_key(|x| { unsafe { CALLS += 1; } *x }); \
             let c = unsafe { CALLS }; std::process::exit((r.unwrap_or(-1)+1+c*10) as i32);",
            0,
        ),
        // slice max / min (reference item, signed) via `match` (Option<&i64>).
        (
            "slice_max",
            "let a = [5i64, 2, 9, 1, 7]; \
             let r = match a.iter().max() { Some(v) => *v, None => -1 }; std::process::exit(r as i32);",
            9,
        ),
        (
            "slice_min",
            "let a = [5i64, 2, 9, 1, 7]; \
             let r = match a.iter().min() { Some(v) => *v, None => -1 }; std::process::exit(r as i32);",
            1,
        ),
        // Equal maxima return the LAST reference; equal minima return the FIRST.
        // Pointer identity makes the tie rule observable even though values match.
        (
            "slice_max_equal_last_ptr",
            "let a = [9i64,1,9]; let r = a.iter().max().unwrap(); \
             std::process::exit(std::ptr::eq(r, &a[2]) as i32);",
            1,
        ),
        (
            "slice_min_equal_first_ptr",
            "let a = [1i64,9,1]; let r = a.iter().min().unwrap(); \
             std::process::exit(std::ptr::eq(r, &a[0]) as i32);",
            1,
        ),
        // Empty Option exits must not read the uninitialized payload slot. Cover a
        // reference niche, a scalar direct tag, and a raw-pointer direct payload.
        (
            "empty_slice_last_none",
            "let a: [i64;0] = []; std::process::exit(a.iter().last().is_none() as i32);",
            1,
        ),
        (
            "empty_range_find_none",
            "let n=bb(0i64); std::process::exit((0..n).find(|_| true).is_none() as i32);",
            1,
        ),
        (
            "empty_raw_ptr_last_none",
            "let n=bb(0i64); let r=(0..n).map(|_| std::ptr::null::<i64>()).last(); \
             std::process::exit(r.is_none() as i32);",
            1,
        ),
        // UNSIGNED slice max / min (signedness of the compare must be unsigned).
        (
            "slice_u32_max",
            "let a = [5u32, 200, 9, 1, 250]; \
             let r = match a.iter().max() { Some(v) => *v as i64, None => -1 }; \
             std::process::exit(r as i32);",
            250,
        ),
        (
            "slice_u32_min",
            "let a = [5u32, 200, 9, 1, 250]; \
             let r = match a.iter().min() { Some(v) => *v as i64, None => -1 }; \
             std::process::exit(r as i32);",
            1,
        ),
        // max of NEGATIVE values (= -1, the largest) -> +20 -> 19.
        (
            "slice_neg_max",
            "let a = [-5i64, -2, -9, -1, -7]; \
             let r = match a.iter().max() { Some(v) => *v, None => 0 }; \
             std::process::exit((r + 20) as i32);",
            19,
        ),
        // filter then max: max of {3,4,5} (elements > 2) -> 5.
        (
            "filter_max",
            "let a = [3i64, 1, 4, 1, 5]; \
             let r = a.iter().copied().filter(|&x| x > bb(2)).max().unwrap_or(-1); \
             std::process::exit(r as i32);",
            5,
        ),
        // --- product ---
        // (1..6).product() = 120.
        (
            "range_product",
            "let n = bb(6i64); let r: i64 = (1..n).product(); std::process::exit(r as i32);",
            120,
        ),
        // slice product = 2*3*4 = 24.
        (
            "slice_product",
            "let a = [2i64, 3, 4]; let r: i64 = a.iter().product(); std::process::exit(r as i32);",
            24,
        ),
        // --- last / nth ---
        // last of (0..10).map(|x| x*2) -> 18.
        (
            "map_last",
            "let n = bb(10i64); let r = (0..n).map(|x| x * 2).last().unwrap_or(-1); \
             std::process::exit(r as i32);",
            18,
        ),
        // last of filter(even) over 0..8 -> 6.
        (
            "filter_last",
            "let n = bb(8i64); let r = (0..n).filter(|x| x % 2 == 0).last().unwrap_or(-1); \
             std::process::exit(r as i32);",
            6,
        ),
        // nth(3) of 0..10 -> 3.
        (
            "range_nth",
            "let n = bb(10i64); \
             let r = match (0..n).nth(bb(3usize)) { Some(v) => v, None => -1 }; \
             std::process::exit(r as i32);",
            3,
        ),
        // nth out of range -> None -> -1.
        (
            "nth_oob",
            "let n = bb(5i64); \
             let r = match (0..n).nth(bb(20usize)) { Some(v) => v, None => -1 }; \
             std::process::exit(r as i32);",
            255,
        ),
        // map then nth(4) -> 12.
        (
            "map_nth",
            "let n = bb(20i64); \
             let r = match (0..n).map(|x| x * 3).nth(bb(4usize)) { Some(v) => v, None => -1 }; \
             std::process::exit(r as i32);",
            12,
        ),
        // --- chain (two Range sub-sources) ---
        // (0..3).chain(10..13).sum() = (0+1+2) + (10+11+12) = 36.
        (
            "chain_sum",
            "let a = bb(3i64); let b = bb(10i64); let c = bb(13i64); \
             let r: i64 = (0..a).chain(b..c).sum(); std::process::exit(r as i32);",
            36,
        ),
        // chain then map then sum: 2*36 = 72.
        (
            "chain_map_sum",
            "let a = bb(3i64); let b = bb(10i64); let c = bb(13i64); \
             let r: i64 = (0..a).chain(b..c).map(|x| x * 2).sum(); std::process::exit(r as i32);",
            72,
        ),
        // chain then count: 3 + 5 = 8.
        (
            "chain_count",
            "let a = bb(3i64); let b = bb(10i64); let c = bb(15i64); \
             let cnt = (0..a).chain(b..c).count(); std::process::exit(cnt as i32);",
            8,
        ),
        // chain with an EMPTY first sub-source: just (5..9) -> 5+6+7+8 = 26.
        (
            "chain_empty_first",
            "let a = bb(0i64); let b = bb(5i64); let c = bb(9i64); \
             let r: i64 = (0..a).chain(b..c).sum(); std::process::exit(r as i32);",
            26,
        ),
        // chain with an EMPTY second sub-source: just (0..4) -> 6.
        (
            "chain_empty_second",
            "let a = bb(4i64); let b = bb(7i64); let c = bb(7i64); \
             let r: i64 = (0..a).chain(b..c).sum(); std::process::exit(r as i32);",
            6,
        ),
        // chain then find (short-circuit crossing the source boundary): first > 11
        // over (0..3) ++ (10..20) -> 12.
        (
            "chain_find",
            "let a = bb(3i64); let b = bb(10i64); let c = bb(20i64); \
             let r = (0..a).chain(b..c).find(|&x| x > bb(11)).unwrap_or(-1); \
             std::process::exit(r as i32);",
            12,
        ),
        // chain then count over filter: even of {0,1,2,3} ++ {10,11,12,13} = {0,2,10,12} = 4.
        (
            "chain_filter_count",
            "let n = bb(4i64); let r = (0..n).chain(10..14).filter(|x| x % 2 == 0).count(); \
             std::process::exit(r as i32);",
            4,
        ),
    ];

    for (name, body, expected) in shapes {
        let src = format!("{BB}\nfn main() {{ {body} }}\n");
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), &src, None);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), &src, Some(&dylib));
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

/// Negative pins: terminal/chain shapes the bridge MUST fail closed on (produce no
/// binary) — never silently miscompile. Each is valid Rust (LLVM builds it).
#[test]
fn unmodeled_iter_terminals_fail_closed() {
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

    const BB: &str = "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }";

    let closed: &[(&str, &str)] = &[
        // A CAPTURING predicate closure (`|x| x < n` captures `n`): the terminal's
        // closure must be a ZST (consistent with `.fold`); fail closed.
        (
            "all_capturing",
            "let n = bb(10i64); let r = (0..n).all(|x| x < n); std::process::exit(r as i32);",
        ),
        (
            "find_capturing",
            "let n = bb(10i64); let t = bb(4i64); \
             let r = (0..n).find(|&x| x > t).unwrap_or(-1); std::process::exit(r as i32);",
        ),
        // A nested `.chain().chain()` — the outer chain's sub-source is a Concat,
        // which is not modeled (only bare Range sub-sources).
        (
            "nested_chain",
            "let r: i64 = (0..3i64).chain(5..8).chain(10..12).sum(); std::process::exit(r as i32);",
        ),
        // A `.chain()` of two SLICE sources — the `Option<slice::Iter>` sub-source
        // is niche-encoded (no addressable Direct payload offset); fail closed.
        (
            "chain_slices",
            "let a = [1i64, 2, 3]; let b = [4i64, 5, 6]; \
             let r: i64 = a.iter().copied().chain(b.iter().copied()).sum(); \
             std::process::exit(r as i32);",
        ),
    ];

    for (name, body) in closed {
        let src = format!("{BB}\nfn main() {{ {body} }}\n");
        // LLVM accepts it (valid Rust).
        let _ = compile(&dir, &format!("{name}_llvm"), &src, None);
        // trust-cg must fail closed: NO binary produced.
        let tcg = try_compile(&dir, &format!("{name}_tcg"), &src, Some(&dylib));
        assert!(
            tcg.is_none(),
            "`{name}` must FAIL CLOSED under trust-cg (unmodeled terminal/chain), but a binary was produced"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
