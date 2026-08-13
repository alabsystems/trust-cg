// Integration test: integer `ToString::to_string` / `SpecToString::spec_to_string`
// (`42i32.to_string()`, `n.to_string()` for a primitive integer `n`) compiled
// for x86_64 via the rustc_codegen_trust_cg bridge — COMPILED, LINKED, and RUN,
// with exit codes checked against the default LLVM backend (X1: the SpecToString
// integer-to-String gap; the real std body builds the decimal ASCII in a stack
// `itoa::Buffer` and returns an OWNING `String`, which the collection
// return-escape guard rejects — was fail-closed).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// The bridge lowers the CALL to `to_string`/`spec_to_string` as a call-site
// materialization (never the real, String-returning std body): a fresh
// `{ptr,cap,len}` String slot sized to the width's worst-case decimal length,
// the branchless `format!` itoa emitter (`emit_itoa`) writing the value's
// decimal ASCII, `len = digit count` — `lower_int_to_string`, reusing the
// `format!` String-slot machinery. The receiver's integer value is read through
// its `&self` reference (a `(*_r)` deref place at -O0, or the pointee of a
// promoted-const `&i32` at -O2/-O3).
//
// The differential pins CONTENT, not just lengths: byte reads through
// `as_bytes`, a leading `'-'` for negatives, `0`, the width extremes
// (`i32::MIN`, `i64::MIN`, `u64::MAX` — full 64-bit magnitude), and multiple
// widths (i16/i32/i64/u8/u64). The negative test pins that i128/u128 (the
// I64-carried itoa cannot represent a >64-bit magnitude), a user fn RETURNING an
// integer-`to_string` `String` by value (the collection return-escape guard),
// and a `Display` struct `.to_string()` (self is not a primitive integer — must
// NOT be misrouted into the integer path) all stay FAIL-CLOSED — never a silent
// wrong value.

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
    let dir = std::env::temp_dir().join(format!("rcl2_m123_{stem}_{}", std::process::id()));
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

/// The O0 differential: each program is compiled by trust-cg AND LLVM, run, and
/// the exit codes must match each other and the expected value. Content (byte
/// reads through `as_bytes`, a leading `'-'`, the width extremes) is part of
/// every exit code, so a wrong decimal byte, wrong length, or wrong sign
/// diverges.
#[test]
fn int_to_string_matches_llvm_at_o0() {
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

    // (name, source, expected exit code). Every exit encodes both the length and
    // specific decimal bytes (`as_bytes()[i]`), so content is verified — not just
    // the String length.
    let shapes: &[(&str, &str, i32)] = &[
        // `42i32` -> "42": len 2, bytes '4','2'.
        (
            "pos_i32_42",
            "fn main() { let s = 42i32.to_string(); \
             std::process::exit((s.len() as i32) * 10 \
             + (s.as_bytes()[0] as i32 - 48) + (s.as_bytes()[1] as i32 - 48)); }",
            26,
        ),
        // `-5i32` -> "-5": leading '-' (45), '5'.
        (
            "neg_i32_m5",
            "fn main() { let s = (-5i32).to_string(); \
             std::process::exit((s.len() as i32) * 10 \
             + (s.as_bytes()[0] as i32) + (s.as_bytes()[1] as i32 - 48)); }",
            70,
        ),
        // A RUNTIME (black_box) i32 -> "12345": len 5, bytes '1','5'.
        (
            "runtime_i32_12345",
            "fn main() { let n = std::hint::black_box(12345i32); let s = n.to_string(); \
             std::process::exit((s.len() as i32) * 10 \
             + (s.as_bytes()[0] as i32 - 48) + (s.as_bytes()[4] as i32 - 48)); }",
            56,
        ),
        // `0i32` -> "0" (leading-zero suppression: prints "0", not "").
        (
            "zero_i32",
            "fn main() { let n = std::hint::black_box(0i32); let s = n.to_string(); \
             std::process::exit((s.len() as i32) * 10 + (s.as_bytes()[0] as i32 - 48)); }",
            10,
        ),
        // `i32::MIN` -> "-2147483648": len 11, leading '-' (45), last '8'.
        (
            "i32_min",
            "fn main() { let n = std::hint::black_box(i32::MIN); let s = n.to_string(); \
             std::process::exit((s.len() as i32) * 10 \
             + (s.as_bytes()[0] as i32) + (s.as_bytes()[10] as i32 - 48)); }",
            163,
        ),
        // `-32768i16` -> "-32768": len 6, leading '-' (45), last '8'.
        (
            "i16_min",
            "fn main() { let n = std::hint::black_box(-32768i16); let s = n.to_string(); \
             std::process::exit((s.len() as i32) * 10 \
             + (s.as_bytes()[0] as i32) + (s.as_bytes()[5] as i32 - 48)); }",
            113,
        ),
        // `255u8` -> "255": len 3, bytes '2','5'.
        (
            "u8_255",
            "fn main() { let n = std::hint::black_box(255u8); let s = n.to_string(); \
             std::process::exit((s.len() as i32) * 10 \
             + (s.as_bytes()[0] as i32 - 48) + (s.as_bytes()[2] as i32 - 48)); }",
            37,
        ),
        // `u64::MAX` -> "18446744073709551615": len 20, full unsigned range,
        // bytes '1','5'.
        (
            "u64_max",
            "fn main() { let n = std::hint::black_box(u64::MAX); let s = n.to_string(); \
             std::process::exit((s.len() as i32) * 5 \
             + (s.as_bytes()[0] as i32 - 48) + (s.as_bytes()[19] as i32 - 48)); }",
            106,
        ),
        // `i64::MIN` -> "-9223372036854775808": len 20, `0 - MIN == MIN` unsigned
        // magnitude, leading '-' (45), last '8'.
        (
            "i64_min",
            "fn main() { let n = std::hint::black_box(i64::MIN); let s = n.to_string(); \
             std::process::exit((s.len() as i32) * 5 \
             + (s.as_bytes()[0] as i32) + (s.as_bytes()[19] as i32 - 48)); }",
            153,
        ),
    ];

    for (name, src, expected) in shapes {
        let llvm_bin = compile(&dir, &format!("{name}_llvm"), src, None, "0");
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_bin = compile(&dir, &format!("{name}_tcg"), src, Some(&dylib), "0");
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            tcg_exit, llvm_exit,
            "`{name}`: trust-cg exit {tcg_exit} != LLVM exit {llvm_exit} (MISCOMPILE)"
        );
        assert_eq!(
            tcg_exit, *expected,
            "`{name}`: exit {tcg_exit} != expected {expected}"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// A runtime `i32.to_string()` (whose `spec_to_string` stays a CALL — the bridge
/// intercepts it — at every opt level, unlike the small unsigned widths rustc
/// fully inlines) matches LLVM at O0/O2/O3, content included. The -O2/-O3 form
/// passes a promoted-const / inlined `String::len`/`as_bytes` consumer over the
/// synthesized slot.
#[test]
fn i32_to_string_matches_llvm_across_opt_levels() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("opt");
    // `6789` -> "6789": len 4, bytes '6','9'.
    let src = "fn main() { let n = std::hint::black_box(6789i32); let s = n.to_string(); \
               std::process::exit((s.len() as i32) * 10 \
               + (s.as_bytes()[0] as i32 - 48) + (s.as_bytes()[3] as i32 - 48)); }";
    for opt in ["0", "2", "3"] {
        let llvm_bin = compile(&dir, &format!("i32ts_o{opt}_llvm"), src, None, opt);
        let llvm_exit = run_exit_code(&llvm_bin);
        let tcg_bin = compile(&dir, &format!("i32ts_o{opt}_tcg"), src, Some(&dylib), opt);
        let tcg_exit = run_exit_code(&tcg_bin);
        assert_eq!(
            tcg_exit, llvm_exit,
            "i32.to_string (opt={opt}): trust-cg exit {tcg_exit} != LLVM {llvm_exit}"
        );
        assert_eq!(tcg_exit, 55, "i32.to_string (opt={opt}): exit != 55");
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// Unsupported shapes stay FAIL-CLOSED (a loud [TCG-MIR-UNSUPPORTED], never a
/// wrong value): an i128 receiver (the I64-carried itoa cannot represent a
/// >64-bit magnitude — must not truncate), a user fn RETURNING an integer
/// `to_string` `String` by value (the collection return-escape guard — its
/// `{ptr,cap,len}` slot would die with the callee frame), and a `Display` struct
/// `.to_string()` (self is not a primitive integer — the integer path must NOT
/// be misrouted onto it).
#[test]
fn unsupported_int_to_string_shapes_stay_fail_closed() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("neg");

    let negatives: &[(&str, &str, &str)] = &[
        (
            "i128_not_truncated",
            "fn main() { let n = std::hint::black_box(5i128); let s = n.to_string(); \
             std::process::exit(s.len() as i32); }",
            "TCG-MIR-UNSUPPORTED",
        ),
        (
            "int_to_string_return_escape_guard",
            "#[inline(never)] fn f(n: i32) -> String { n.to_string() } \
             fn main() { let s = f(std::hint::black_box(3i32)); \
             std::process::exit(s.len() as i32); }",
            "escape its frame-local",
        ),
        (
            "display_struct_not_misrouted",
            "use std::fmt; struct S(i32); \
             impl fmt::Display for S { \
             fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, \"{}\", self.0) } } \
             fn main() { let s = S(std::hint::black_box(7i32)).to_string(); \
             std::process::exit(s.len() as i32); }",
            "TCG-MIR-UNSUPPORTED",
        ),
    ];

    for (name, src, needle) in negatives {
        let (output, _bin) = try_compile(&dir, name, src, Some(&dylib), "0");
        assert!(
            !output.status.success(),
            "`{name}`: expected trust-cg to FAIL CLOSED but it compiled"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains(needle),
            "`{name}`: fail-closed message does not contain {needle:?}: <<<{stderr}>>>"
        );
    }
    let _ = std::fs::remove_dir_all(&dir);
}
