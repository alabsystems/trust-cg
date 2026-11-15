#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: `print!`/`println!`/`eprint!`/`eprintln!` through the
// bridge — compiled + RUN for x86_64 and DIFFERENTIALLY compared against
// rustc's default LLVM backend on STDOUT BYTES, STDERR BYTES, and exit code.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: task m140 — the `std::io::_print`/`_eprint` interception (the
// hello-world unblock). The interception decodes the `fmt::Arguments` shape
// statically (the same four MIR shapes `format!` already decodes), synthesizes
// the bytes in the caller's frame, and hands them to the same std entry as a
// string-literal `fmt::Arguments` (std's own buffered sink; see
// `print_order_differential.rs`). SOUND-PARTIAL: only the bounded
// `{}` subset of int/&str/char/bool is modeled; `{:?}`, padding/alignment,
// named args, and u128/i128 FAIL CLOSED (pinned below — never a wrong byte).
//
// LEVEL SCOPE: the modeled shapes must compile+match at EVERY opt level
// (O0/O1/O2/O3 — the fuzz-lesson gate; rustc reshapes `Arguments` per level).

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = host_target_support::X86_64_TARGET;
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m140_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

#[derive(Debug, PartialEq, Eq)]
struct RunResult {
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    code: i32,
}

fn run_bin(bin: &Path) -> RunResult {
    let out = Command::new(bin).output().expect("run binary");
    RunResult {
        stdout: out.stdout,
        stderr: out.stderr,
        code: out.status.code().expect("exit code"),
    }
}

/// Ground truth: compile+run under rustc's default LLVM backend at `-O`.
fn run_llvm(dir: &Path, stem: &str, src: &str) -> RunResult {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("{stem}_llvm"));
    let status = toolchain_support::rustc_command()
        .args(["--crate-type", "bin", "-Cpanic=abort", "-O"])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .status()
        .expect("spawn rustc (LLVM)");
    assert!(
        status.success(),
        "LLVM reference failed to compile: <<<{src}>>>"
    );
    run_bin(&bin)
}

/// Bridge lane: `Some(result)` when it compiled+ran, `None` on fail-closed.
fn run_bridge(dir: &Path, dylib: &Path, stem: &str, src: &str, opt: &str) -> Option<RunResult> {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("{stem}_t{opt}"));
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "bin"])
        .arg(backend_arg)
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc (bridge)");
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("failing closed") || stderr.contains("unsupported"),
            "bridge compile failed NOT fail-closed at -O{opt}: <<<{stderr}>>>"
        );
        return None;
    }
    Some(run_bin(&bin))
}

/// The modeled print shapes: every case must compile AND byte-match LLVM's
/// stdout/stderr/exit at EVERY opt level.
#[test]
fn println_shapes_match_llvm_bytes_at_all_opt_levels() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("shapes");

    let cases: &[(&str, &str)] = &[
        ("hello", r#"fn main(){ println!("Hello, world!"); }"#),
        (
            "int",
            r#"fn main(){ let x=std::hint::black_box(42i64); println!("x={}", x); }"#,
        ),
        ("conststr", r#"fn main(){ println!("s={}", "abc"); }"#),
        (
            "noline",
            r#"fn main(){ print!("no-newline"); print!("+more"); }"#,
        ),
        (
            "eprint",
            r#"fn main(){ eprintln!("to-stderr {}", std::hint::black_box(7i32)); }"#,
        ),
        (
            "order",
            r#"fn main(){ println!("first {}", std::hint::black_box(1i32)); println!("second {}", std::hint::black_box(2i32)); }"#,
        ),
        (
            "mixed",
            r#"fn main(){ let a=std::hint::black_box(5u32); let b=std::hint::black_box(-3i64); println!("a={} b={} c={}", a, b, std::hint::black_box(true)); }"#,
        ),
        (
            "in_loop",
            r#"fn main(){ let mut i=0i32; while i<3 { println!("i={}", std::hint::black_box(i)); i+=1; } }"#,
        ),
    ];

    for (stem, src) in cases {
        let want = run_llvm(&dir, stem, src);
        for opt in OPT_LEVELS {
            match run_bridge(&dir, &dylib, stem, src, opt) {
                Some(got) => assert_eq!(
                    got, want,
                    "`{stem}` at -O{opt}: stdout/stderr/exit mismatch vs LLVM"
                ),
                None => panic!(
                    "`{stem}` unexpectedly FAILED CLOSED at -O{opt} — the print \
                     interception regressed"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// FAIL-CLOSED pins: shapes outside the bounded `{}` subset must refuse (or —
/// if a future model admits them — byte-match; NEVER wrong output). These pin
/// the deferred-GC-drop hazard class: the unlowerable `_print` body must never
/// ship a garbage formatter.
#[test]
fn unmodeled_println_shapes_fail_closed_or_match() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("canaries");

    let cases: &[(&str, &str)] = &[
        (
            "dbg",
            r#"fn main(){ println!("{:?}", std::hint::black_box(3i32)); }"#,
        ),
        (
            "pad",
            r#"fn main(){ println!("{:>5}", std::hint::black_box(3i32)); }"#,
        ),
        (
            "u128p",
            r#"fn main(){ println!("{}", std::hint::black_box(3u128)); }"#,
        ),
        (
            "named",
            r#"fn main(){ let v=std::hint::black_box(9i32); println!("{v}"); }"#,
        ),
        (
            "hexfmt",
            r#"fn main(){ println!("{:x}", std::hint::black_box(255u32)); }"#,
        ),
    ];

    for (stem, src) in cases {
        let want = run_llvm(&dir, stem, src);
        for opt in OPT_LEVELS {
            if let Some(got) = run_bridge(&dir, &dylib, stem, src, opt) {
                assert_eq!(
                    got, want,
                    "`{stem}` at -O{opt} compiled but output is WRONG (silent \
                     print miscompile)"
                );
            }
            // None (fail-closed) is the expected, accepted outcome.
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}
