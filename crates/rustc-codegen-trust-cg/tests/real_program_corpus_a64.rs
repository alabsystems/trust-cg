// Compiled only on an aarch64-apple-darwin host, whose Trust package ships the
// target's rust-std: another host builds this target with no test in it, never
// one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// crates/rustc-codegen-trust-cg/tests/real_program_corpus_a64.rs
//
// A64-ROW — REAL-PROGRAM CORPUS CROSS-COMPILE VERDICT GATE.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHAT THIS IS
// ------------
// The FIRST end-to-end aarch64 coverage number in the repo: every guest in
// the shared real-program corpus (the exact same 13 programs the x86 gate
// runs — `include!`d from one source so the sets can never drift) is
// compiled through the bridge for `aarch64-apple-darwin` at O0 and O3 with
// `--emit=obj` (the full backend pipeline: lowering, mid-end, regalloc,
// encode, object emission — everything except ld64 and execution).
//
// WHY VERDICT-ONLY: the row was written on an x86 Mac that could not run
// aarch64 code. It now runs only on an aarch64-apple-darwin host, which could
// link and run every guest, but converting it to compile-and-run rows is open
// work (docs/darwin-aarch64-completion.md, "Darwin bridge coverage"). Until
// then it is compile-verdict evidence only: a fail-closed guest is an honest
// INCOMPLETE, a rustc ICE/panic is a hard failure, and a coverage regression
// (previously-compiling guest newly refusing) reds the ratchet floor. Every
// refused row, a proof-promotion refusal (`[TCG-PROOF-465]`) included, counts
// against the floor; no refusal suspends it.
//
// THE GATE (mirror of the x86 row's intent-to-treat doctrine):
//   * rustc ICE / non-fail-closed crash  -> HARD FAIL.
//   * trust-cg fail-closed               -> INCOMPLETE row (stays in the
//     denominator), listed with its named TCG diagnostic.
//   * coverage% = COMPILED rows / all rows; the test passes only if
//     coverage >= the committed floor in
//     tests/real_program_corpus/A64_COMPILE_FLOOR.txt. NEVER lower the
//     floor to make the gate pass.
//
// Run (requires rust-std for aarch64-apple-darwin on the pinned toolchain; the
// required runner is scripts/check_darwin_aarch64_bridge.py):
//     cd crates/rustc-codegen-trust-cg
//     ../../scripts/trust_cargo.sh test --release --locked --test real_program_corpus_a64 -- --nocapture

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

const TARGET: &str = "aarch64-apple-darwin";
const OPT_LEVELS: [&str; 2] = ["0", "3"];

fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

fn workdir(stem: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("rcl2_a64corpus_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Pull the `[TCG-...]` / `TCG-...` diagnostic codes out of a stderr blob so
/// INCOMPLETE rows report the exact named blocker.
fn extract_tcg_codes(stderr: &str) -> Vec<String> {
    let mut codes: Vec<String> = Vec::new();
    let bytes = stderr.as_bytes();
    let mut i = 0;
    while let Some(pos) = stderr[i..].find("TCG-") {
        let start = i + pos;
        let mut end = start;
        while end < bytes.len()
            && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'-' || bytes[end] == b'_')
        {
            end += 1;
        }
        let code = stderr[start..end].to_string();
        if !codes.contains(&code) {
            codes.push(code);
        }
        i = end;
    }
    codes
}

fn a64_compile_floor_percent() -> f64 {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/real_program_corpus/A64_COMPILE_FLOOR.txt");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("failed to read {}: {e}", path.display()));
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("a64_compile_floor_percent") {
            let value = rest.trim_start().trim_start_matches('=').trim();
            return value
                .parse::<f64>()
                .expect("a64_compile_floor_percent must parse as f64");
        }
    }
    panic!(
        "no `a64_compile_floor_percent = <value>` line in {}",
        path.display()
    );
}

#[derive(Debug)]
enum A64Verdict {
    Compiled,
    FailClosed {
        tcg_codes: Vec<String>,
        stderr_tail: String,
    },
    HardError {
        stderr_tail: String,
    },
}

/// Cross-compile one guest for aarch64 through the bridge, object-emission
/// only (`--emit=obj` — the full backend pipeline minus ld64/execution).
///
/// The verdict is the rustc EXIT STATUS: a bridge compile emits MULTIPLE
/// objects (main CGU + allocator shim + lazy helpers), so rustc ignores `-o`
/// for `--emit=obj` and writes the objects under out-dir names — an
/// output-FILE existence check would misclassify every successful multi-object
/// compile as a refusal (the first measurement's 0/26 artifact).
fn compile_a64_obj(dir: &Path, dylib: &Path, stem: &str, src: &str, opt: &str) -> A64Verdict {
    let src_path = dir.join(format!("{stem}.rs"));
    std::fs::write(&src_path, src).expect("write source");
    let out_dir = dir.join(format!("{stem}_o{opt}_out"));
    let _ = std::fs::create_dir_all(&out_dir);
    let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
    backend_arg.push(dylib);
    let output = toolchain_support::rustc_command()
        .args(["--crate-type", "bin", "--emit=obj"])
        .arg(backend_arg)
        .args(["--target", TARGET, "-Cpanic=abort"])
        .arg(format!("-Copt-level={opt}"))
        .arg("--out-dir")
        .arg(&out_dir)
        .arg(&src_path)
        .output()
        .expect("spawn rustc (bridge, a64)");
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    if output.status.success() {
        return A64Verdict::Compiled;
    }
    let tail: String = stderr
        .lines()
        .rev()
        .take(6)
        .collect::<Vec<_>>()
        .into_iter()
        .rev()
        .collect::<Vec<_>>()
        .join("\n");
    let codes = extract_tcg_codes(&stderr);
    // An ICE ("internal compiler error" / rustc panic) is never fail-closed.
    if stderr.contains("internal compiler error") || stderr.contains("thread 'rustc' panicked") {
        return A64Verdict::HardError { stderr_tail: tail };
    }
    if !codes.is_empty() || stderr.contains("failing closed") || stderr.contains("unsupported") {
        return A64Verdict::FailClosed {
            tcg_codes: codes,
            stderr_tail: tail,
        };
    }
    A64Verdict::HardError { stderr_tail: tail }
}

include!("real_program_corpus/corpus_guests.rs");

#[test]
fn real_program_corpus_a64_compile_gate() {
    // The backend knob option and Darwin rust-std are required here; a missing
    // one fails the test by name instead of returning early.
    darwin_native::require("real_program_corpus_a64", &[]);
    let dylib = ensure_dylib_built();
    let dir = workdir("verdicts");

    let mut compiled = 0usize;
    let mut incomplete: Vec<(String, Vec<String>)> = Vec::new();
    let mut hard_errors: Vec<(String, String)> = Vec::new();
    let mut gap_tags: BTreeMap<String, usize> = BTreeMap::new();
    let guests = corpus();
    let total_rows = guests.len() * OPT_LEVELS.len();

    for guest in &guests {
        for opt in OPT_LEVELS {
            let row = format!("{}@O{opt}", guest.name);
            match compile_a64_obj(&dir, &dylib, guest.name, guest.src, opt) {
                A64Verdict::Compiled => {
                    compiled += 1;
                    eprintln!("  [a64] {row}: COMPILED");
                }
                A64Verdict::FailClosed {
                    tcg_codes,
                    stderr_tail,
                } => {
                    for code in &tcg_codes {
                        *gap_tags.entry(code.clone()).or_default() += 1;
                    }
                    if tcg_codes.is_empty() {
                        *gap_tags
                            .entry("<untagged fail-closed>".to_string())
                            .or_default() += 1;
                    }
                    eprintln!("  [a64] {row}: INCOMPLETE ({tcg_codes:?})\n{stderr_tail}");
                    incomplete.push((row, tcg_codes));
                }
                A64Verdict::HardError { stderr_tail } => {
                    eprintln!("  [a64] {row}: HARD ERROR\n{stderr_tail}");
                    hard_errors.push((row, stderr_tail));
                }
            }
        }
    }

    let coverage = 100.0 * compiled as f64 / total_rows as f64;
    eprintln!(
        "\n[a64 corpus row] {compiled}/{total_rows} rows COMPILED ({coverage:.1}%), \
         {} incomplete, {} hard errors",
        incomplete.len(),
        hard_errors.len()
    );
    eprintln!("[a64 corpus row] ranked gap tags: {gap_tags:?}");

    assert!(
        hard_errors.is_empty(),
        "aarch64 bridge compiles must fail CLOSED, never crash: {hard_errors:?}"
    );
    // Every refused row counts against the floor, whatever refused it; the
    // proof-promotion refusal (`[TCG-PROOF-465]`) used to suspend the floor
    // here, which let this test pass without measuring coverage (L06-P10).
    let floor = a64_compile_floor_percent();
    assert!(
        coverage >= floor,
        "a64 compile coverage {coverage:.1}% fell below the ratchet floor {floor:.1}% \
         (a previously-compiling guest regressed to fail-closed); rows: {incomplete:?}"
    );
    let _ = std::fs::remove_dir_all(&dir);
    positive_evidence::record(
        positive_evidence::Evidence::CompileVerdict,
        positive_evidence::Certs::On,
    );
}
