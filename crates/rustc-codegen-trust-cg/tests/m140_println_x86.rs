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
// the bytes in the caller's frame, and sinks them to fd 1/2 via the
// `__trustcg_write_all` full-write helper. SOUND-PARTIAL: only the bounded
// `{}` subset of int/&str/char/bool is modeled; `{:?}`, padding/alignment,
// named args, and u128/i128 FAIL CLOSED (pinned below — never a wrong byte).
//
// LEVEL SCOPE: the modeled shapes must compile+match at EVERY opt level
// (O0/O1/O2/O3 — the fuzz-lesson gate; rustc reshapes `Arguments` per level).

use std::path::{Path, PathBuf};
use std::process::Command;

const TARGET: &str = "x86_64-apple-darwin";
const OPT_LEVELS: [&str; 4] = ["0", "1", "2", "3"];

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
        .args(["build", "--release"])
        .current_dir(crate_dir)
        .status()
        .expect("failed to invoke `cargo build`");
    assert!(status.success(), "cargo build failed; cannot run m140 test");
    let built = target_dir
        .join("release")
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
    let status = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .args(["--crate-type", "bin", "-Cpanic=abort", "-O"])
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .status()
        .expect("spawn rustc (LLVM)");
    assert!(status.success(), "LLVM reference failed to compile: <<<{src}>>>");
    run_bin(&bin)
}

/// Bridge lane: `Some(result)` when it compiled+ran, `None` on fail-closed.
fn run_bridge(dir: &Path, dylib: &Path, stem: &str, src: &str, opt: &str) -> Option<RunResult> {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("{stem}_t{opt}"));
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    let output = Command::new("rustup")
        .args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
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
        ("dbg", r#"fn main(){ println!("{:?}", std::hint::black_box(3i32)); }"#),
        ("pad", r#"fn main(){ println!("{:>5}", std::hint::black_box(3i32)); }"#),
        ("u128p", r#"fn main(){ println!("{}", std::hint::black_box(3u128)); }"#),
        ("named", r#"fn main(){ let v=std::hint::black_box(9i32); println!("{v}"); }"#),
        ("hexfmt", r#"fn main(){ println!("{:x}", std::hint::black_box(255u32)); }"#),
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
