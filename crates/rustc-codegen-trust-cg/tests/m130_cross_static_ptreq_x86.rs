#[path = "support/target_dir.rs"]
mod target_dir_support;

// Integration test: CROSS-STATIC `ptr::eq` via canonical weak-linked statics
// [WEAKLINK-1 Part 2] — compiled for x86_64 through the rustc_codegen_trust_cg
// bridge at -O0/-O2/-O3, LINKED, RUN, and the exit codes checked against the
// default LLVM backend.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// THE HAZARD (STAT-1): `static A: i64 = 11; static R: &i64 = &A;` — a static
// whose value is a reference to ANOTHER immutable static. Before this fix every
// function-body `&A` reader got a PRIVATE per-object inlined copy of A's bytes,
// so `&A` had a DIFFERENT address in every object, and a static cross-referencing
// A (`R = &A`) FAILED CLOSED entirely (splicing A's Internal symbol would not
// link). `ptr::eq(R, &A)` would have been tcg=0 vs llvm=1 — a silent wrong value
// — so the whole compile was fail-closed pending weak linkage.
//
// THE FIX: A's canonical symbol is emitted ONCE as an EXPORTED, coalescable
// LINK-ONCE (ODR) definition (Part 1's `N_WEAK_DEF` weak linkage), EVERY
// address-taking `&A` reader IMPORTS that one symbol, and a cross-referencing
// static splices the SAME symbol into its slot. So R's stored pointer and every
// `&A` share ONE program-wide address: `ptr::eq(R, &A) == 1`, `*R == 7`, and two
// functions taking `&A` compare equal. Duplicate promotions of A COALESCE
// (weak) instead of a duplicate-strong link error.
//
// Every program is compiled by trust-cg AND LLVM at -O0, -O2 and -O3, run, and
// the exit codes asserted equal. The exit code folds in BOTH the identity
// (`ptr::eq`) AND the content (`*R`), so a wrong address OR wrong bytes diverges.
// The hard invariant: trust-cg MUST match LLVM (a wrong `ptr::eq`, wrong content,
// or duplicate-symbol link error is a P0 STOP).

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
    let dir = std::env::temp_dir().join(format!("rcl2_m130_{stem}_{}", std::process::id()));
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
        "compile of `{name}` failed ({} backend, opt={opt}). stderr: <<<{}>>>",
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

/// The cross-static `ptr::eq` shapes: each must COMPILE, LINK (no
/// duplicate-strong-symbol error), and match LLVM's exit code at every opt level.
#[test]
fn cross_static_ptr_eq_matches_llvm_across_opt_levels() {
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

    // (name, source, expected exit code). All values are in 0..=255.
    let shapes: &[(&str, &str, i32)] = &[
        // THE STAT-1 HAZARD: `ptr::eq(R, &A)` — R's stored pointer and a direct
        // `&A` must be the SAME address (was tcg=0 vs llvm=1). Fold in `*R` too:
        // identity(1)*100 + content(11) = 111.
        (
            "ptr_eq_R_and_refA_with_content",
            "static A: i64 = 11; static R: &i64 = &A; \
             fn main(){ std::process::exit(std::ptr::eq(R, &A) as i32 * 100 + *R as i32); }",
            111,
        ),
        // Plain deref through the cross-static reference: `*R == 7`.
        (
            "deref_cross_static",
            "static A: i64 = 7; static R: &i64 = &A; \
             fn main(){ std::process::exit(*R as i32); }",
            7,
        ),
        // TWO functions each take `&A`: as-ptr identity must hold (both import the
        // ONE canonical symbol). Private per-object copies would give 0.
        (
            "two_fns_same_addr",
            "static A: i64 = 11; \
             #[inline(never)] fn a1() -> *const i64 { &A } \
             #[inline(never)] fn a2() -> *const i64 { &A } \
             fn main(){ std::process::exit(std::ptr::eq(a1(), a2()) as i32); }",
            1,
        ),
        // A CHAIN: `static R2: &i64 = &A` alongside `R = &A`. R, R2 and a direct
        // `&A` are all one address: eq(R,R2)*100 + eq(R,&A)*10 + *R = 100+10+5=115.
        (
            "chain_two_refs_to_A",
            "static A: i64 = 5; static R: &i64 = &A; static R2: &i64 = &A; \
             fn main(){ std::process::exit( \
                 std::ptr::eq(R, R2) as i32 * 100 \
                 + std::ptr::eq(R, &A) as i32 * 10 \
                 + *R as i32); }",
            115,
        ),
        // An ARRAY of references to distinct immutable statics: read the 3rd.
        (
            "static_ref_table",
            "static A: i64 = 11; static B: i64 = 22; static C: i64 = 33; \
             static T: [&i64; 3] = [&A, &B, &C]; \
             fn main(){ let s: &[&i64] = &T; std::process::exit(*s[2] as i32); }",
            33,
        ),
        // A struct static with a `&'static i64` field pointing at another static.
        (
            "struct_static_with_ptr",
            "struct P { v: i64, p: &'static i64 } \
             static Y: i64 = 7; static S: P = P { v: 100, p: &Y }; \
             fn main(){ std::process::exit((S.v + *S.p) as i32); }",
            107,
        ),
    ];

    for opt in ["0", "2", "3"] {
        for (name, src, expected) in shapes {
            let case = format!("{name}_O{opt}");
            let llvm_bin = compile(&dir, &format!("{case}_llvm"), src, None, opt);
            let tcg_bin = compile(&dir, &format!("{case}_tcg"), src, Some(&dylib), opt);
            let llvm_exit = run_exit_code(&llvm_bin);
            let tcg_exit = run_exit_code(&tcg_bin);
            assert_eq!(
                llvm_exit, *expected,
                "LLVM exit code for `{case}` is {llvm_exit}, expected {expected}"
            );
            assert_eq!(
                tcg_exit, llvm_exit,
                "trust-cg exit code for `{case}` is {tcg_exit}, LLVM is {llvm_exit} (must match)"
            );
        }
    }

    let _ = std::fs::remove_dir_all(&dir);
}
