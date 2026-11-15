#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/host_target.rs"]
mod host_target_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test: DEFENSIVE HARDENING of the runtime-integer `format!` feature
// against a LATENT silent-truncation class (X1).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// BACKGROUND. The bridge synthesizes `format!("{}", n)` for a primitive integer
// `n` with a branchless itoa (`emit_itoa`) over an I64 magnitude carrier. The
// placeholder emitter (`emit_format_one_placeholder`) widens the value to that
// carrier via `coerce_to_i64` — a SAME-WIDTH `I64` Copy. For an i128/u128 that
// Copy would TRUNCATE the magnitude to its low 64 bits and print a WRONG decimal
// string. `classify_fmt_value` used to CLASSIFY 128-bit ints as formattable
// (`Some(128) => I128 / U128`), so the only thing preventing a wrong binary was
// ISel/regalloc INCIDENTALLY dying downstream on the 128-bit op (a signed i128
// died at `Icmp SignedLessThan lhs=I128`; a u128 at regalloc "value not defined
// before use"). A future ISel that grew 128-bit support would have SILENTLY
// TRUNCATED instead.
//
// THE FIX (soundness, non-regressing). `classify_fmt_value` now REFUSES 128-bit
// ints at the FRONT END (returns `None`), so the whole `format!` fails closed
// with a principled "format! placeholder of unsupported type i128/u128"
// diagnostic BEFORE any IR is emitted — the truncating `coerce_to_i64` is never
// reached. A defense-in-depth guard in the placeholder emitter (`[TCG-FMT-INT128]`,
// `bits > 64` => fail closed) makes the no-truncation invariant explicit at the
// truncation site itself. i128/u128 `format!` ALREADY failed closed (incidentally)
// before this change, so the differential is UNCHANGED — only WHERE the refusal
// happens moved (front end, robust), not WHETHER.
//
// THIS TEST pins BOTH directions:
//   (1) the supported integer feature still MATCHES LLVM — byte LENGTH at O0/O2/O3
//       and byte CONTENT at O3 — over VARYING `black_box` values (so a hardcoded
//       or truncated result cannot pass), including an adversarial sign+width+order
//       probe (`"v={} w={}"` with `i32::MIN` and a `u32`);
//   (2) i128/u128 `format!` now COMPILES and MATCHES LLVM (byte length AND
//       content) at O0/O2/O3, via the 128-bit `emit_itoa_i128` digit loop that
//       replaced the old truncating I64 carrier. High-bit-set magnitudes and
//       i128::MIN/MAX are the sentinels a low-64-bit truncation could not pass.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const TARGET: &str = host_target_support::X86_64_TARGET;

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn x86_64_std_available() -> bool {
    toolchain_support::target_std_available(TARGET)
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_m126_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

fn backend_arg(dylib: &Path) -> std::ffi::OsString {
    let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
    s.push(dylib);
    s
}

/// Compile `src` with rustc's default LLVM backend at `-O` and return the run's
/// exit code (the GROUND TRUTH).
fn run_llvm(dir: &Path, src: &str) -> i32 {
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join("llvm_out");
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
    Command::new(&bin)
        .status()
        .expect("run LLVM binary")
        .code()
        .expect("LLVM binary exit code")
}

/// Compile `src` via the trust-cg bridge at `opt_level` WITHOUT running it. Returns
/// the raw compiler `Output` and the intended binary path.
fn compile_bridge(dir: &Path, dylib: &Path, src: &str, opt_level: &str) -> (Output, PathBuf) {
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join(format!("bridge_out_{opt_level}"));
    let _ = std::fs::remove_file(&bin);
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "bin"])
        .arg(backend_arg(dylib))
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt_level}"))
        .arg("-o")
        .arg(&bin)
        .arg(&src_path)
        .output()
        .expect("spawn rustc (bridge)");
    (output, bin)
}

/// Compile via the bridge at `opt_level` and RUN it. `Some(exit)` when it compiled
/// + ran; `None` when the bridge FAILED CLOSED (a safe coverage gap). A
/// link/run/non-fail-closed error `panic!`s.
fn run_bridge(dir: &Path, dylib: &Path, src: &str, opt_level: &str) -> Option<i32> {
    let (output, bin) = compile_bridge(dir, dylib, src, opt_level);
    let stderr = String::from_utf8_lossy(&output.stderr);
    if !output.status.success() {
        if stderr.contains("failing closed") || stderr.contains("unsupported") {
            return None;
        }
        panic!("bridge compile failed (not fail-closed) at -O{opt_level}: <<<{stderr}>>>");
    }
    assert!(
        !stderr.contains("Undefined symbols"),
        "bridge link has an undefined symbol at -O{opt_level}: <<<{stderr}>>>"
    );
    let code = Command::new(&bin)
        .status()
        .expect("run bridge binary")
        .code()
        .expect("bridge binary exit code");
    Some(code)
}

/// A program exiting with the byte LENGTH of the formatted String.
fn len_program(fmt_expr: &str) -> String {
    format!("fn main() {{\n    let s = {fmt_expr};\n    std::process::exit(s.len() as i32);\n}}\n")
}

/// A program exiting with a 31-rolling-hash of the formatted BYTES (catches a wrong
/// digit/sign/byte a length-only check would miss). Mirrors m90's content harness.
fn content_program(fmt_expr: &str) -> String {
    format!(
        "fn main() {{\n    let s = {fmt_expr};\n    let b = s.as_bytes();\n    \
         let mut acc: i32 = 0;\n    let mut i = 0usize;\n    \
         while i < b.len() {{ acc = (acc.wrapping_mul(31).wrapping_add(b[i] as i32)) % 1000; i += 1; }}\n    \
         std::process::exit(((acc % 250) + 250) % 250);\n}}\n"
    )
}

/// (1a) The supported integer `format!` feature MATCHES LLVM by byte LENGTH at
/// O0/O2/O3 over VARYING `black_box` values — a hardcoded or truncated result
/// cannot pass. Includes the adversarial `"v={} w={}"` (sign + width + arg order).
#[test]
fn integer_format_length_matches_llvm_o0_o2_o3() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("len");

    let cases: &[(&str, &str)] = &[
        ("format!(\"{}\", std::hint::black_box(42i32))", "int 42"),
        (
            "format!(\"x={}\", std::hint::black_box(7i32))",
            "prefix + 7",
        ),
        (
            "format!(\"{} {}\", std::hint::black_box(1i32), std::hint::black_box(23i32))",
            "two ints",
        ),
        (
            "format!(\"{}\", std::hint::black_box(-2147483648i32))",
            "i32::MIN",
        ),
        (
            "format!(\"{}\", std::hint::black_box(9999999999u64))",
            "wide u64",
        ),
        (
            "format!(\"{}\", std::hint::black_box(-9223372036854775808i64))",
            "i64::MIN",
        ),
        (
            "format!(\"v={} w={}\", std::hint::black_box(i32::MIN), std::hint::black_box(70000u32))",
            "adversarial sign+width+order",
        ),
    ];

    for (fmt_expr, label) in cases {
        let src = len_program(fmt_expr);
        let llvm = run_llvm(&dir, &src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, &src, opt) {
                Some(code) => assert_eq!(
                    code, llvm,
                    "LEN MISMATCH `{label}` at -O{opt}: bridge={code} llvm={llvm}\nsrc: {src}"
                ),
                None => panic!(
                    "`{label}` unexpectedly FAILED CLOSED at -O{opt} (should be intercepted)"
                ),
            }
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// (1b) The supported integer `format!` feature MATCHES LLVM by byte CONTENT at O3
/// over VARYING values — a wrong digit/sign/byte (e.g. a low-64-bit truncation)
/// surfaces here, not just a length change. Includes the adversarial probe.
#[test]
fn integer_format_content_matches_llvm_o3() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("content");

    let cases: &[(&str, &str)] = &[
        ("format!(\"{}\", std::hint::black_box(42i32))", "int 42"),
        (
            "format!(\"x={}\", std::hint::black_box(7i32))",
            "prefix + 7",
        ),
        (
            "format!(\"{} {}\", std::hint::black_box(1i32), std::hint::black_box(23i32))",
            "two ints",
        ),
        (
            "format!(\"{}\", std::hint::black_box(u64::MAX))",
            "u64::MAX full magnitude",
        ),
        (
            "format!(\"{}\", std::hint::black_box(-9223372036854775808i64))",
            "i64::MIN",
        ),
        (
            "format!(\"v={} w={}\", std::hint::black_box(i32::MIN), std::hint::black_box(70000u32))",
            "adversarial sign+width+order",
        ),
    ];

    for (fmt_expr, label) in cases {
        let src = content_program(fmt_expr);
        let llvm = run_llvm(&dir, &src);
        match run_bridge(&dir, &dylib, &src, "3") {
            Some(code) => assert_eq!(
                code, llvm,
                "CONTENT MISMATCH `{label}` at -O3: bridge={code} llvm={llvm}\nsrc: {src}"
            ),
            None => panic!("`{label}` unexpectedly FAILED CLOSED at -O3 (content check)"),
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}

/// (2) i128/u128 `format!` COMPILES and MATCHES LLVM at O0/O2/O3 — the full
/// 128-bit `emit_itoa_i128` digit loop (128-bit magnitude, sign, and
/// `mag / 10^k % 10` divisions) replaces the old truncating I64 carrier that
/// forced this to fail closed. Checks BOTH byte LENGTH (digit count + sign) and
/// byte CONTENT (a wrong digit — e.g. a low-64-bit truncation — changes the
/// content sum, so it cannot pass): a magnitude whose HIGH bits are set
/// (`u128_high_bits_set`, `i128::MIN`) would print a different number than a
/// truncation and is the direct regression sentinel for the old bug.
#[test]
fn wide_int_format_matches_llvm_o0_o2_o3() {
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let dylib = ensure_dylib_built();
    let dir = workdir("wide");

    let cases: &[(&str, &str)] = &[
        ("format!(\"{}\", std::hint::black_box(0u128))", "u128 0"),
        (
            "format!(\"{}\", std::hint::black_box(12345678901234567890u128))",
            "u128 > u64 range",
        ),
        (
            "format!(\"{}\", std::hint::black_box(340282366920938463463374607431768211455u128))",
            "u128::MAX (39 digits)",
        ),
        // HIGH bits set: a low-64-bit truncation would print a different value —
        // the direct sentinel for the pre-fix truncation bug.
        (
            "format!(\"{}\", std::hint::black_box(0xFFFF_FFFF_FFFF_FFFF_0000_0000_0000_0001u128))",
            "u128 high-bits-set",
        ),
        ("format!(\"{}\", std::hint::black_box(-5i128))", "i128 -5"),
        ("format!(\"{}\", std::hint::black_box(0i128))", "i128 0"),
        (
            "format!(\"{}\", std::hint::black_box(-170141183460469231731687303715884105728i128))",
            "i128::MIN (40 bytes)",
        ),
        (
            "format!(\"{}\", std::hint::black_box(170141183460469231731687303715884105727i128))",
            "i128::MAX (39 digits)",
        ),
        (
            "format!(\"v={} w={}\", std::hint::black_box(-1i128), std::hint::black_box(999u128))",
            "adversarial sign + two 128-bit args + order",
        ),
    ];

    // Byte LENGTH match (digit count + sign) at every opt level.
    for (fmt_expr, label) in cases {
        let src = len_program(fmt_expr);
        let llvm = run_llvm(&dir, &src);
        for opt in ["0", "2", "3"] {
            match run_bridge(&dir, &dylib, &src, opt) {
                Some(code) => assert_eq!(
                    code, llvm,
                    "128-bit LEN MISMATCH `{label}` at -O{opt}: bridge={code} llvm={llvm}\nsrc: {src}"
                ),
                None => panic!(
                    "`{label}` at -O{opt} FAILED CLOSED — i128/u128 format! must now compile \
                     via emit_itoa_i128\nsrc: {src}"
                ),
            }
        }
    }
    // Byte CONTENT match at O3 (a wrong digit / low-64 truncation surfaces here).
    for (fmt_expr, label) in cases {
        let src = content_program(fmt_expr);
        let llvm = run_llvm(&dir, &src);
        match run_bridge(&dir, &dylib, &src, "3") {
            Some(code) => assert_eq!(
                code, llvm,
                "128-bit CONTENT MISMATCH `{label}` at -O3: bridge={code} llvm={llvm}\nsrc: {src}"
            ),
            None => panic!("`{label}` content check FAILED CLOSED at -O3\nsrc: {src}"),
        }
    }
    let _ = std::fs::remove_dir_all(&dir);
}
