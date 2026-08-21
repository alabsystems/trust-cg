#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: the `Vec<T>` `collect` element-type guard.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS — soundness guard for `iter.collect::<Vec<T>>()`.
//
// The bridge's `<Iterator>::collect::<Vec<T>>()` interception drives the source
// iterator chain to exhaustion, pushing each yielded element into a fresh
// `{ ptr, cap, len }` Vec slot as ONE fixed-width INTEGER LANE per element. That
// model is correct ONLY when the element type `T` is a single fixed-width
// integer scalar. The recognizer (`vec_element_ty`) admits any leaf with a known
// `bit_width`, which (mis)includes:
//   - a `Vec<i32>` element (i.e. the OUTER `Vec` of a `Vec<Vec<i32>>`) — mapped
//     to the IR type `Ptr` (width 64),
//   - a `String` element (also a `Ptr`),
//   - a `(i32, i32)` tuple / a struct element,
//   - a `&T` reference element (a `Ref`, width 64),
//   - a `bool` element (floats f32/f64 ARE now supported — see below),
//   - an `i128` / `u128` element (a 128-bit lane the 64-bit push/index path
//     cannot store without truncation).
// For any of those, the collect loop would push a single corrupt scalar per
// element (a dangling pointer, a truncated payload) and build a structurally
// WRONG outer `Vec` — a SILENT miscompile. The canonical repro:
//
//     let grid: Vec<Vec<i32>> = (0..5).map(|i| (0..5).map(|j| i*5+j).collect()).collect();
//     std::process::exit(grid[2][3]);   // LLVM = 13; the corrupt build returned 0.
//
// The guard restricts the collect interception to a single fixed-width INTEGER
// element (the SAME predicate the push/index/extend/sort interceptions require,
// `is_integer`, plus a `size <= 8` lane bound) — checking BOTH the destination
// Vec's element type AND the lane the source chain actually pushes — and FAILS
// CLOSED (no binary) for every non-integer-scalar element. A SINGLE-LEVEL integer
// collect (`(0..n).collect::<Vec<i64>>()`, `.map(..).collect()`,
// `.filter(..).collect()`, slice `.iter().copied().collect()`) is unaffected and
// still matches LLVM byte-for-byte.
//
// This test pins both directions: nested / non-integer-scalar collect fails
// CLOSED at -O0 AND -O3 (NEVER a wrong value), and single-level integer collect
// still runs and matches LLVM at -O0.

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
    assert!(status.success(), "cargo build failed; cannot run nested-collect test");
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
    let dir = std::env::temp_dir().join(format!("rcl2_m103_{stem}_{}", std::process::id()));
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

/// Every non-integer-scalar `collect::<Vec<T>>()` shape — `Vec<Vec<_>>`,
/// `Vec<String>`, `Vec<(_,_)>`, `Vec<bool>`, `Vec<i128>`, `Vec<&T>` (floats are
/// supported and checked separately) —
/// must FAIL CLOSED (no binary) at BOTH -O0 and -O3. LLVM compiles and runs the
/// canonical nested-collect repro (= 13); trust-cg must refuse to produce a binary
/// rather than emit the structurally-corrupt outer Vec (which previously returned
/// the wrong value 0 at -O0).
#[test]
fn non_integer_scalar_collect_fails_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("fc");

    // The canonical repro: a `Vec<Vec<i32>>` nested collect. LLVM runs it and
    // grid[2][3] == 2*5+3 == 13. trust-cg previously built a corrupt outer Vec and
    // returned 0 at -O0 — now it must fail closed.
    let nested = "fn main() { \
        let grid: Vec<Vec<i32>> = (0..5).map(|i| (0..5).map(|j| i * 5 + j).collect()).collect(); \
        std::process::exit(grid[2][3]); }";
    let llvm0 = compile(&dir, "nested_o0_llvm", nested, None, "0");
    assert_eq!(
        run_exit_code(&llvm0),
        13,
        "LLVM nested-collect repro -O0 should be 13"
    );

    // (name, source) — each must fail closed at -O0 AND -O3 on trust-cg.
    let non_scalar: &[(&str, &str)] = &[
        ("nested_vec", nested),
        (
            "vec_string",
            "fn main() { let v: Vec<String> = (0..3).map(|i| i.to_string()).collect(); \
             std::process::exit(v.len() as i32); }",
        ),
        (
            "vec_tuple",
            "fn main() { let v: Vec<(i32, i32)> = (0..3).map(|i| (i, i + 1)).collect(); \
             std::process::exit(v.len() as i32); }",
        ),
        (
            "vec_bool",
            "fn main() { let v: Vec<bool> = (0..3).map(|i| i % 2 == 0).collect(); \
             std::process::exit(v.len() as i32); }",
        ),
        (
            "vec_i128",
            "fn main() { let v: Vec<i128> = (0..3i128).map(|i| i + 1).collect(); \
             let mut s = 0i128; let mut j = 0usize; \
             while j < v.len() { s += v[j]; j += 1; } std::process::exit(s as i32); }",
        ),
        (
            "vec_ref",
            "fn main() { let a = [1i32, 2, 3]; let v: Vec<&i32> = a.iter().collect(); \
             std::process::exit(v.len() as i32); }",
        ),
    ];

    for (name, src) in non_scalar {
        for opt in ["0", "3"] {
            let (output, bin) =
                try_compile(&dir, &format!("{name}_o{opt}_tcg"), src, Some(&dylib), opt);
            assert!(
                !output.status.success() && !bin.exists(),
                "trust-cg unexpectedly produced a binary for non-integer-scalar collect \
                 `{name}` (-O{opt}); a `Vec<Vec<_>>`/`Vec<String>`/`Vec<(_,_)>`/\
                 `Vec<bool>`/`Vec<i128>`/`Vec<&T>` collect must FAIL CLOSED, never build a \
                 corrupt Vec. stderr: <<<{}>>>",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }

    // FLOAT elements ARE soundly supported: `f32`/`f64` are single fixed-width
    // scalar lanes the collect/index path stores via a typed 8-/4-byte `Store`
    // (verified byte-exact against LLVM). So a `Vec<f64>`/`Vec<f32>` collect
    // COMPILES and MATCHES — it is NOT in the fail-closed set above.
    let float_ok: &[(&str, &str, i32)] = &[
        (
            "vec_f64",
            "fn main() { let v: Vec<f64> = (0..20).map(|i| (i as f64) * 1.5 + 0.25).collect(); \
             let mut a = 0.0f64; for &x in v.iter() { a += x; } \
             std::process::exit(((a * 4.0) as i64 % 251) as i32); }",
            156,
        ),
        (
            "vec_f32",
            "fn main() { let v: Vec<f32> = (0..16).map(|i| (i as f32) * 0.5).collect(); \
             let mut a = 0.0f32; for &x in v.iter() { a += x; } \
             std::process::exit((a as i64 % 251) as i32); }",
            60,
        ),
    ];
    for (name, src, expected) in float_ok {
        let llvm = compile(&dir, &format!("{name}_llvm"), src, None, "3");
        assert_eq!(run_exit_code(&llvm), *expected, "LLVM `{name}` should be {expected}");
        for opt in ["0", "3"] {
            let tcg = compile(&dir, &format!("{name}_o{opt}_tcg"), src, Some(&dylib), opt);
            assert_eq!(
                run_exit_code(&tcg),
                *expected,
                "trust-cg float collect `{name}` (-O{opt}) must compile + match LLVM ({expected})"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}

/// SINGLE-LEVEL integer collect is unaffected by the guard: it still compiles and
/// matches LLVM byte-for-byte at -O0. This is the regression pin for the matched
/// `collect` set (a guard that was too broad would fail-close these too).
#[test]
fn single_level_integer_collect_still_matches_llvm_o0() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("match");

    // Sum a Vec by index, exit with `s % 251` so the value fits an exit code.
    let sum_idx = "let mut s = 0i64; let mut j = 0usize; \
                   while j < v.len() { s += v[j] as i64; j += 1; } \
                   std::process::exit((s % 251) as i32);";

    let shapes: &[(&str, String)] = &[
        (
            "range_i64",
            format!("fn main() {{ let v: Vec<i64> = (0..10i64).collect(); {sum_idx} }}"),
        ),
        (
            "map_i64",
            format!("fn main() {{ let v: Vec<i64> = (0..10i64).map(|x| x * 2).collect(); {sum_idx} }}"),
        ),
        (
            "filter_i64",
            format!(
                "fn main() {{ let v: Vec<i64> = (0..20i64).filter(|x| x % 3 == 0).collect(); {sum_idx} }}"
            ),
        ),
        (
            "i32_collect",
            format!("fn main() {{ let v: Vec<i32> = (0..12i32).map(|x| x + 1).collect(); {sum_idx} }}"),
        ),
        (
            "u32_collect",
            format!("fn main() {{ let v: Vec<u32> = (0..12u32).map(|x| x + 1).collect(); {sum_idx} }}"),
        ),
        (
            "u8_collect",
            format!("fn main() {{ let v: Vec<u8> = (0..10u8).map(|x| x + 1).collect(); {sum_idx} }}"),
        ),
        (
            "copied_slice",
            format!(
                "fn main() {{ let a = [3i64, 1, 4, 1, 5, 9]; \
                 let v: Vec<i64> = a.iter().copied().collect(); {sum_idx} }}"
            ),
        ),
        (
            "map_filter",
            format!(
                "fn main() {{ let v: Vec<i64> = (0..10i64).map(|x| x * x).filter(|y| y % 2 == 0).collect(); {sum_idx} }}"
            ),
        ),
    ];

    for (name, src) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_o0_llvm"), src, None, "0");
        let tcg_bin = compile(&dir, &format!("{name}_o0_tcg"), src, Some(&dylib), "0");
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            tcg_exit, llvm_exit,
            "trust-cg exit code for single-level integer collect `{name}` (-O0) is {tcg_exit}, \
             LLVM is {llvm_exit} (must match — the guard must not fail-close a valid integer collect)"
        );
    }

    let _ = std::fs::remove_dir_all(&dir);
}
