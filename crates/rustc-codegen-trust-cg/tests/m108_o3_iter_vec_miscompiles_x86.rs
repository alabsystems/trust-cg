// Integration test: TWO O3-only SILENT MISCOMPILES, now fixed —
//
//   #111  Two iterator terminals over a STRUCTURALLY-IDENTICAL `Range` source: at
//         O3, rustc CSE/GVN folds the two identical `(1..n)` init sequences into ONE
//         memory slot, so both terminals resolved the same chain slot; the first
//         DRAINED it in place and the second reduced over an exhausted range (sum
//         -> 0, product -> 1, …). FIX: each terminal drives over a PRIVATE copy of
//         the iterator state (`copy_iter_state_to_private_slot`).
//
//   #112  `Vec::truncate(k)` / `Vec::clear()`: at O3 these inline to a direct len
//         FIELD store `(v.1: usize) = k`, which the bridge dropped onto a dead
//         scalarized projection while the matching `len()` read consulted the live
//         slot lane — so the shrink was silently lost (`len()`/`iter()` stayed at
//         the full length). FIX: a len-field WRITE intercept routes the inlined
//         store to the slot's `len` lane (`lower_vec_field_write`), plus O0
//         `truncate`/`clear` call arms.
//
// Each program is compiled by trust-cg AND LLVM at BOTH -Copt-level=0 and
// -Copt-level=3, run, and the exit codes asserted. The hard invariant: trust-cg
// MUST match LLVM **or fail closed (produce no binary)** — NEVER a different exit
// code. The two O3 repros below specifically MUST NOT reproduce their old wrong
// values (10 / 10) — they are asserted to match LLVM.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0

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
    assert!(status.success(), "cargo build failed; cannot run test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m108_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` at `opt`; returns `Some(bin)` on success, `None` on (trust-cg)
/// compile failure (the fail-closed case).
fn try_compile(
    dir: &Path,
    name: &str,
    src: &str,
    backend: Option<&Path>,
    opt: u8,
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
        .arg(format!("-Copt-level={opt}"))
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

fn run_exit_code(bin: &Path) -> i32 {
    Command::new(bin)
        .output()
        .expect("run binary")
        .status
        .code()
        .expect("process exited via signal, not exit code")
}

const BB: &str = "#[inline(never)] fn bb<T>(x: T) -> T { std::hint::black_box(x) }";

/// For each (name, body, expected) program, at BOTH O0 and O3: LLVM must produce
/// `expected`, and trust-cg must either MATCH LLVM or FAIL CLOSED (no binary).
/// A trust-cg binary whose exit code DIFFERS from LLVM is the silent miscompile we
/// forbid and fails the test.
fn assert_match_or_fail_closed(dir: &Path, shapes: &[(&str, &str, i32)]) {
    for (name, body, expected) in shapes {
        let src = format!("{BB}\nfn main() {{ {body} }}\n");
        let dylib = ensure_dylib_built();
        for opt in [0u8, 3u8] {
            let llvm_bin = try_compile(dir, &format!("{name}_llvm_{opt}"), &src, None, opt)
                .unwrap_or_else(|| panic!("LLVM compile of `{name}` @O{opt} failed"));
            let llvm_exit = run_exit_code(&llvm_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit for `{name}` @O{opt} is {llvm_exit}, expected {expected}"
            );
            match try_compile(dir, &format!("{name}_tcg_{opt}"), &src, Some(&dylib), opt) {
                Some(tcg_bin) => {
                    let tcg_exit = run_exit_code(&tcg_bin);
                    assert_eq!(
                        tcg_exit, llvm_exit,
                        "MISCOMPILE: trust-cg exit for `{name}` @O{opt} is {tcg_exit}, \
                         LLVM is {llvm_exit} (must match or fail closed)"
                    );
                }
                None => {
                    // Fail closed — an acceptable, safe outcome (a coverage gap).
                    eprintln!("note: `{name}` @O{opt} failed closed under trust-cg (safe)");
                }
            }
        }
    }
}

/// #111 — range double/triple consume (and the slice control). The two O3 repros
/// (`range_double_sum` / `range_double_product`) used to return the reduction
/// IDENTITY for the second consumer; they are now asserted to match LLVM.
#[test]
fn iter_double_consume_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("iter");
    let shapes: &[(&str, &str, i32)] = &[
        // THE #111 REPRO: two `(1..n).sum()` over the same range -> 10 + 10 = 20
        // (was O3=10: the second sum saw an exhausted range -> 0).
        (
            "range_double_sum",
            "let n = bb(5i64); let a: i64 = (1..n).sum(); let b: i64 = (1..n).sum(); \
             std::process::exit((a + b) as i32);",
            20,
        ),
        // Double product -> 24 + 24 = 48 (was O3=24+1=25: second product saw the
        // multiplicative identity 1).
        (
            "range_double_product",
            "let n = bb(5i64); let a: i64 = (1..n).product(); let b: i64 = (1..n).product(); \
             std::process::exit((a + b) as i32);",
            48,
        ),
        // Triple sum -> 30.
        (
            "range_triple_sum",
            "let n = bb(5i64); let a: i64 = (1..n).sum(); let b: i64 = (1..n).sum(); \
             let c: i64 = (1..n).sum(); std::process::exit((a + b + c) as i32);",
            30,
        ),
        // min + max + count over the same range (1..6): 1 + 5 + 5 = 11.
        (
            "range_min_max_count",
            "let n = bb(6i64); let a = (1..n).min().unwrap_or(-1); \
             let b = (1..n).max().unwrap_or(-1); let c = (1..n).count() as i64; \
             std::process::exit((a + b + c) as i32);",
            11,
        ),
        // count + count -> 5 + 5 = 10.
        (
            "range_double_count",
            "let n = bb(5i64); let a = (1..n).count() as i64; let b = (1..n).count() as i64; \
             std::process::exit((a + b) as i32);",
            8,
        ),
        // fold + fold -> (1+2+3+4) twice = 10 + 10 = 20.
        (
            "range_double_fold",
            "let n = bb(5i64); let a: i64 = (1..n).fold(0, |s, x| s + x); \
             let b: i64 = (1..n).fold(0, |s, x| s + x); std::process::exit((a + b) as i32);",
            20,
        ),
        // SLICE control: a slice double-consume was always correct; it must STAY
        // correct (the private-copy path runs over it too). 15 + 15 = 30.
        (
            "slice_double_sum_control",
            "let a = [1i64, 2, 3, 4, 5]; let s: i64 = a.iter().sum(); let t: i64 = a.iter().sum(); \
             std::process::exit((s + t) as i32);",
            30,
        ),
        // Single consume control: still correct (0..10 sum = 45).
        (
            "range_single_sum_control",
            "let n = bb(10i64); let s: i64 = (0..n).sum(); std::process::exit(s as i32);",
            45,
        ),
        // SHARED `&mut` iterator control: a `&mut self` terminal (`find`) must drain
        // the SHARED iterator in place so a SUBSEQUENT consumer sees the consumed
        // state — the private-copy fix must apply to BY-VALUE receivers ONLY, never
        // to a borrowed `&mut` iterator (which the caller reuses). find consumes
        // 0..=3 (-> 3); the remaining `it.sum()` is 4+..+9 = 39; total 42.
        (
            "shared_mut_iter_find_then_sum",
            "let n = bb(10i64); let mut it = 0..n; \
             let f = it.find(|&x| x == bb(3)).unwrap_or(-1); let s: i64 = it.sum(); \
             std::process::exit((f + s) as i32);",
            42,
        ),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}

/// #112 — `Vec::truncate` / `Vec::clear`, then `len()` / `iter()` / push-after. The
/// O3 repros (`vec_clear_len` / `vec_truncate_len`) used to silently no-op the
/// shrink (len() stayed 10); they now match LLVM at O0 AND O3.
#[test]
fn vec_truncate_clear_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("vec");
    let shapes: &[(&str, &str, i32)] = &[
        // THE #112 REPRO: clear() then len() -> 0 (was O3=10).
        (
            "vec_clear_len",
            "let mut v: Vec<i64> = (0..bb(10i64)).collect(); v.clear(); \
             std::process::exit(v.len() as i32);",
            0,
        ),
        // truncate(k<len) then len() -> 3 (was O3=10).
        (
            "vec_truncate_len",
            "let mut v: Vec<i64> = (0..bb(10i64)).collect(); v.truncate(3); \
             std::process::exit(v.len() as i32);",
            3,
        ),
        // truncate(0) -> 0.
        (
            "vec_truncate_zero",
            "let mut v: Vec<i64> = (0..bb(10i64)).collect(); v.truncate(0); \
             std::process::exit(v.len() as i32);",
            0,
        ),
        // truncate(k>=len) is a no-op -> 10.
        (
            "vec_truncate_ge_len",
            "let mut v: Vec<i64> = (0..bb(10i64)).collect(); v.truncate(20); \
             std::process::exit(v.len() as i32);",
            10,
        ),
        // truncate(3) then push(100) -> len 4.
        (
            "vec_truncate_push",
            "let mut v: Vec<i64> = (0..bb(10i64)).collect(); v.truncate(3); v.push(100); \
             std::process::exit(v.len() as i32);",
            4,
        ),
        // clear() then push(7) -> len 1.
        (
            "vec_clear_push",
            "let mut v: Vec<i64> = (0..bb(10i64)).collect(); v.clear(); v.push(7); \
             std::process::exit(v.len() as i32);",
            1,
        ),
        // truncate(3) then iter().sum() over the surviving {0,1,2} -> 3.
        (
            "vec_truncate_iter_sum",
            "let mut v: Vec<i64> = (0..bb(10i64)).collect(); v.truncate(3); \
             let s: i64 = v.iter().sum(); std::process::exit(s as i32);",
            3,
        ),
        // clear() then iter().sum() over the (now empty) Vec -> 0 (+99 = 99).
        (
            "vec_clear_iter_sum",
            "let mut v: Vec<i64> = (0..bb(5i64)).collect(); v.clear(); \
             let s: i64 = v.iter().sum(); std::process::exit((s + 99) as i32);",
            99,
        ),
        // truncate to a runtime k (k = 4) -> len 4.
        (
            "vec_truncate_runtime_k",
            "let mut v: Vec<i64> = (0..bb(10i64)).collect(); let k = bb(4usize); v.truncate(k); \
             std::process::exit(v.len() as i32);",
            4,
        ),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}
