// Interaction pin: #108 (RangeInclusive `a..=b`, 3-field {start,end,exhausted})
// × #111 (per-consumer PRIVATE COPY of iterator state, layout-sized).
//
// #108 made `(1..=n).sum()` twice COMPILE (previously fail-closed). #111's
// private-copy is layout-derived (`iter_state_slot_size` = tcx.layout_of().size),
// so it MUST size the 3-field RangeInclusive correctly and protect a double-consume
// at O3 the same way it protects an exclusive Range. This test forbids a wrong O3
// value for inclusive-range double/triple-consume (the would-be new miscompile if
// the copy path didn't cover RangeInclusive).
//
// trust-cg MUST match LLVM or fail closed (no binary) at BOTH O0 and O3.
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
    let dir = std::env::temp_dir().join(format!("rcl2_m108b_{stem}_{}", std::process::id()));
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
                    eprintln!("note: `{name}` @O{opt} failed closed under trust-cg (safe)");
                }
            }
        }
    }
}

#[test]
fn inclusive_range_double_consume_match_or_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dir = workdir("incl");
    let shapes: &[(&str, &str, i32)] = &[
        // Inclusive double sum: (1+2+3+4+5)=15 twice -> 30. The would-be NEW O3
        // miscompile if #111's private copy doesn't cover the 3-field RangeInclusive
        // (second sum would see exhausted -> 0 -> total 15).
        (
            "incl_double_sum",
            "let n = bb(5i64); let a: i64 = (1..=n).sum(); let b: i64 = (1..=n).sum(); \
             std::process::exit((a + b) as i32);",
            30,
        ),
        // Inclusive double product: 120 twice -> 240.
        (
            "incl_double_product",
            "let n = bb(5i64); let a: i64 = (1..=n).product(); let b: i64 = (1..=n).product(); \
             std::process::exit((a + b) as i32);",
            240,
        ),
        // Inclusive triple sum -> 45.
        (
            "incl_triple_sum",
            "let n = bb(5i64); let a: i64 = (1..=n).sum(); let b: i64 = (1..=n).sum(); \
             let c: i64 = (1..=n).sum(); std::process::exit((a + b + c) as i32);",
            45,
        ),
        // Inclusive min + max + count over (1..=6): 1 + 6 + 6 = 13.
        (
            "incl_min_max_count",
            "let n = bb(6i64); let a = (1..=n).min().unwrap_or(-1); \
             let b = (1..=n).max().unwrap_or(-1); let c = (1..=n).count() as i64; \
             std::process::exit((a + b + c) as i32);",
            13,
        ),
        // Inclusive double fold -> (1+2+3+4+5) twice = 30.
        (
            "incl_double_fold",
            "let n = bb(5i64); let a: i64 = (1..=n).fold(0, |s, x| s + x); \
             let b: i64 = (1..=n).fold(0, |s, x| s + x); std::process::exit((a + b) as i32);",
            30,
        ),
        // Inclusive single consume control -> 15.
        (
            "incl_single_sum_control",
            "let n = bb(5i64); let s: i64 = (1..=n).sum(); std::process::exit(s as i32);",
            15,
        ),
        // Mixed exclusive + inclusive over similar bounds (must NOT alias each other).
        // (1..n=5) sum = 1+2+3+4 = 10 ; (1..=n) sum = 15 ; total 25.
        (
            "mixed_excl_incl_sum",
            "let n = bb(5i64); let a: i64 = (1..n).sum(); let b: i64 = (1..=n).sum(); \
             std::process::exit((a + b) as i32);",
            25,
        ),
    ];
    assert_match_or_fail_closed(&dir, shapes);
    let _ = std::fs::remove_dir_all(&dir);
}
