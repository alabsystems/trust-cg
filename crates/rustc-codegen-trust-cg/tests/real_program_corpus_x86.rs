#[path = "support/target_dir.rs"]
mod target_dir_support;

// crates/rustc-codegen-trust-cg/tests/real_program_corpus_x86.rs
//
// COMPLETE-5 — REAL-PROGRAM CORPUS ACCEPTANCE GATE (the G5/M6 measuring stick).
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// WHAT THIS IS
// ------------
// A committed corpus of REAL-PROGRAM-shaped guests (bigger than the perf
// benchmarks: interpreter loop, sorting over Vec, tokenizer over &[u8],
// fixed-size matrix ops, state machine, recursive descent over a byte slice,
// hashmap-free word count, Box'd tree, Vec-as-stack, struct-heavy business
// logic — all inside today's envelope: no println, exit-code checksums,
// panic=abort). Every program is compiled through BOTH lanes (stock
// rustc/LLVM oracle and the trust-cg backend) at O0 and O3, run, and diffed.
//
// THE GATE (intent-to-treat, per roadmap §1 G5):
//   * exit-code MISMATCH between lanes  -> HARD FAIL (P0 stop-the-line
//     soundness event; fuzzer-finding doctrine applies).
//   * trust-cg fail-closed              -> INCOMPLETE row, listed in the
//     report with its named TCG diagnostic (these rows stay in the
//     DENOMINATOR — fail-closed programs are not dropped from coverage).
//   * coverage% = MATCH rows / all rows, and the test passes only if
//     coverage >= the committed RATCHET FLOOR *and* mismatches == 0.
//
// The floor lives in tests/real_program_corpus/COVERAGE_FLOOR.txt (committed;
// seeded at the initially measured value). Raise it when completeness fixes
// land; NEVER lower it to make the gate pass (soundness doctrine: a gate is
// never weakened in-run).
//
// NONDET-FAILCLOSED (BENCH-8 doctrine): a trust-cg compile failure is retried
// once; if the retry succeeds the row is labeled NONDET-FAILCLOSED and still
// counted INCOMPLETE (never silently upgraded to MATCH), but flagged loudly —
// it is evidence of the load-sensitive solver-deadline flap, not of a
// completeness gap.
//
// Run (requires target-bridge toolchain + x86_64-apple-darwin std, x86 host):
//     cd crates/rustc-codegen-trust-cg
//     cargo test --release --test real_program_corpus_x86 -- --nocapture
//
// (Plumbing below mirrors tests/bridge_differential_x86.rs — each bridge test
// target is its own crate, so the minimal outcome model is re-derived inline
// exactly like that harness does; the authoritative unit-tested versions live
// in crates/trust-cg-fuzz/src/bridge_diff.rs.)

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

const TARGET: &str = "x86_64-apple-darwin";
const MACOS_DEPLOYMENT_TARGET: &str = "13.0";
const OPT_LEVELS: [&str; 2] = ["0", "3"];
const RUN_TIMEOUT: Duration = Duration::from_secs(60);

// ---------------------------------------------------------------------------
// Outcome model (mirror of trust_cg_fuzz::bridge_diff, reduced to this gate)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum RunOutcome {
    Exited { code: i32 },
    Signalled { signal: i32 },
    /// rustc (compile+link in one invocation) failed — for the trust-cg lane
    /// this is the fail-closed shape (compile rejection OR an unemitted-symbol
    /// link error; both mean the program never runs, so it cannot miscompile).
    CompileError { stderr_tail: String, tcg_codes: Vec<String> },
    Timeout,
}

#[derive(Debug, Clone)]
enum RowVerdict {
    Match { exit_code: i32 },
    Mismatch { detail: String },
    Incomplete { reason: String },
    NondetFailClosed { first_reason: String },
}

// ---------------------------------------------------------------------------
// Toolchain / dylib plumbing (mirror of bridge_differential_x86.rs)
// ---------------------------------------------------------------------------

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

fn dylib_name() -> String {
    format!(
        "{}rustc_codegen_trust_cg{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    )
}

fn ensure_dylib_built() -> PathBuf {
    let crate_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let target_dir = target_dir_support::cargo_target_dir(crate_dir);
    let name = dylib_name();
    let candidates = [
        target_dir.join("release").join(&name),
        target_dir.join("debug").join(&name),
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
    assert!(
        status.success(),
        "cargo build failed; cannot run the corpus gate"
    );
    let built = target_dir.join("release").join(&name);
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
    let dir = std::env::temp_dir().join(format!("rcl2_corpus_{stem}_{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create workdir");
    dir
}

/// Extract named `[TCG-*]`-style diagnostic codes from a trust-cg stderr, so
/// INCOMPLETE rows carry the typed reason (the ranked-gap-table input).
fn extract_tcg_codes(stderr: &str) -> Vec<String> {
    let mut codes: Vec<String> = Vec::new();
    let bytes = stderr.as_bytes();
    let mut i = 0;
    while let Some(pos) = stderr[i..].find("TCG-") {
        let start = i + pos;
        let mut end = start + 4;
        while end < bytes.len()
            && (bytes[end].is_ascii_alphanumeric() || bytes[end] == b'-' || bytes[end] == b'_')
        {
            end += 1;
        }
        let code = stderr[start..end].trim_end_matches(['-', '_']).to_string();
        if code.len() > 4 && !codes.contains(&code) {
            codes.push(code);
        }
        i = end;
    }
    codes
}

fn run_with_timeout(bin: &Path, timeout: Duration) -> RunOutcome {
    let mut child = Command::new(bin).spawn().expect("spawn compiled binary");
    let start = Instant::now();
    loop {
        match child.try_wait().expect("try_wait") {
            Some(status) => {
                if let Some(code) = status.code() {
                    return RunOutcome::Exited { code };
                }
                return RunOutcome::Signalled {
                    signal: signal_of(&status),
                };
            }
            None => {
                if start.elapsed() > timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    return RunOutcome::Timeout;
                }
                std::thread::sleep(Duration::from_millis(20));
            }
        }
    }
}

/// Compile+link `src` with `dylib` (Some=trust-cg, None=LLVM oracle) via the
/// FULL rustc link (`-o bin`, the heap_canary_x86.rs recipe — supports
/// Vec/Box/std::process::exit shaped guests on both lanes), run with a
/// timeout, classify. A rustc failure on the trust-cg lane (compile rejection
/// or unemitted-symbol link error) is the fail-closed shape: the program
/// never runs, so it cannot silently miscompile.
fn compile_link_run(stem: &str, src: &str, opt: &str, dylib: Option<&Path>) -> RunOutcome {
    let dir = workdir(&format!(
        "{stem}_o{opt}_{}",
        if dylib.is_some() { "tcg" } else { "llvm" }
    ));
    let src_path = dir.join("prog.rs");
    std::fs::write(&src_path, src).expect("write source");
    let bin = dir.join("bin");

    let mut cmd = Command::new("rustup");
    cmd.env("MACOSX_DEPLOYMENT_TARGET", MACOS_DEPLOYMENT_TARGET);
    // Typed diagnostics for the gap table (harmless if the bridge ignores it).
    cmd.env("TCG_DIAG_JSON", "1");
    cmd.args(["run", pinned_toolchain().as_str(), "rustc", "--edition=2021"])
        .arg("--crate-type")
        .arg("bin");
    if let Some(dylib) = dylib {
        let mut backend_arg = std::ffi::OsString::from("-Zcodegen-backend=");
        backend_arg.push(dylib);
        cmd.arg(&backend_arg);
    }
    cmd.args([
        "--target",
        TARGET,
        "-Cpanic=abort",
        "-Coverflow-checks=off",
        "-Ccodegen-units=1",
    ])
    .arg(format!("-Copt-level={opt}"))
    .arg("-o")
    .arg(&bin)
    .arg(&src_path);
    let output = cmd.output().expect("failed to spawn rustc via rustup");
    if !output.status.success() {
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        let _ = std::fs::remove_dir_all(&dir);
        return RunOutcome::CompileError {
            stderr_tail: stderr
                .lines()
                .rev()
                .take(6)
                .collect::<Vec<_>>()
                .join(" | "),
            tcg_codes: extract_tcg_codes(&stderr),
        };
    }

    let outcome = run_with_timeout(&bin, RUN_TIMEOUT);
    let _ = std::fs::remove_dir_all(&dir);
    outcome
}

#[cfg(unix)]
fn signal_of(status: &std::process::ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    status.signal().unwrap_or(-1)
}

#[cfg(not(unix))]
fn signal_of(_status: &std::process::ExitStatus) -> i32 {
    -1
}

// ---------------------------------------------------------------------------
// Ratchet floor (committed file; intent-to-treat coverage %)
// ---------------------------------------------------------------------------

fn coverage_floor_percent() -> f64 {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/real_program_corpus/COVERAGE_FLOOR.txt");
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "COMPLETE-5 ratchet floor file missing/unreadable at {}: {e}\n\
             The corpus gate is fail-closed: commit the floor file (seed it at \
             the currently measured coverage).",
            path.display()
        )
    });
    for line in text.lines() {
        let line = line.trim();
        if let Some(rest) = line.strip_prefix("coverage_floor_percent") {
            let Some((_, v)) = rest.split_once('=') else { continue };
            return v
                .trim()
                .parse::<f64>()
                .expect("coverage_floor_percent must parse as f64");
        }
    }
    panic!(
        "no `coverage_floor_percent = <value>` line in {}",
        path.display()
    );
}

// ---------------------------------------------------------------------------
// THE CORPUS — real-program-shaped guests, exit-code checksums (mod 251),
// no println, panic=abort-safe (inputs chosen so no panic path fires).
// ---------------------------------------------------------------------------

include!("real_program_corpus/corpus_guests.rs");

#[test]
fn real_program_corpus_acceptance_gate() {
    if !host_is_x86_64() {
        eprintln!("skipping: x86_64 run requires an x86_64 host");
        return;
    }
    if !x86_64_std_available() {
        eprintln!("skipping: rust-std for {TARGET} not installed for pinned toolchain");
        return;
    }
    let floor = coverage_floor_percent(); // fail-closed if the file is missing
    let dylib = ensure_dylib_built();

    let mut rows: Vec<(String, RowVerdict)> = Vec::new();
    let mut mismatches: Vec<String> = Vec::new();

    for guest in corpus() {
        eprintln!("corpus guest {} — {}", guest.name, guest.what);
        for opt in OPT_LEVELS {
            let row_id = format!("{} (O{opt})", guest.name);
            let reference = compile_link_run(guest.name, guest.src, opt, None);
            if let RunOutcome::CompileError { stderr_tail, .. } = &reference {
                panic!(
                    "FIXTURE BROKEN: LLVM could not compile `{}` (opt={opt}): {stderr_tail}",
                    guest.name
                );
            }

            let mut test = compile_link_run(guest.name, guest.src, opt, Some(&dylib));
            let mut nondet_first_reason: Option<String> = None;
            if matches!(test, RunOutcome::CompileError { .. }) {
                // BENCH-8 NONDET-FAILCLOSED doctrine: retry ONCE. If the retry
                // succeeds, the row is labeled NONDET (still INCOMPLETE, never
                // upgraded to MATCH), because the first verdict flapped.
                let first_reason = match &test {
                    RunOutcome::CompileError { stderr_tail, tcg_codes } => {
                        if tcg_codes.is_empty() {
                            stderr_tail.clone()
                        } else {
                            tcg_codes.join(",")
                        }
                    }
                    _ => unreachable!(),
                };
                let retry = compile_link_run(guest.name, guest.src, opt, Some(&dylib));
                if !matches!(retry, RunOutcome::CompileError { .. }) {
                    nondet_first_reason = Some(first_reason);
                    test = retry;
                }
            }

            let verdict = if let Some(first_reason) = nondet_first_reason {
                // The retry compiled; STILL verify the retry outcome against
                // the oracle so a flapping-then-wrong compile cannot hide.
                match (&reference, &test) {
                    (RunOutcome::Exited { code: rc }, RunOutcome::Exited { code: tc })
                        if rc != tc =>
                    {
                        mismatches.push(format!(
                            "{row_id}: NONDET retry MISMATCH llvm_exit={rc} trust_cg_exit={tc}"
                        ));
                        RowVerdict::Mismatch {
                            detail: format!("llvm_exit={rc} trust_cg_exit={tc} (nondet retry)"),
                        }
                    }
                    _ => RowVerdict::NondetFailClosed { first_reason },
                }
            } else {
                match (&reference, &test) {
                    (_, RunOutcome::CompileError { stderr_tail, tcg_codes }) => {
                        RowVerdict::Incomplete {
                            reason: if tcg_codes.is_empty() {
                                format!("fail-closed: {stderr_tail}")
                            } else {
                                tcg_codes.join(",")
                            },
                        }
                    }
                    (RunOutcome::Exited { code: rc }, RunOutcome::Exited { code: tc }) => {
                        if rc == tc {
                            RowVerdict::Match { exit_code: *rc }
                        } else {
                            let d = format!("llvm_exit={rc} trust_cg_exit={tc}");
                            mismatches.push(format!("{row_id}: {d}"));
                            RowVerdict::Mismatch { detail: d }
                        }
                    }
                    (RunOutcome::Signalled { signal: rs }, RunOutcome::Signalled { .. }) => {
                        // Both trapped — corpus programs should never trap;
                        // treat agreement-in-trap as MATCH (mirrors the
                        // differential harness) but note it.
                        eprintln!("note: {row_id}: both lanes trapped (sig={rs})");
                        RowVerdict::Match { exit_code: -1 }
                    }
                    (r, t) => {
                        let d = format!("outcome-shape mismatch: llvm={r:?} trust_cg={t:?}");
                        mismatches.push(format!("{row_id}: {d}"));
                        RowVerdict::Mismatch { detail: d }
                    }
                }
            };
            eprintln!(
                "corpus row {row_id:<28} -> {}",
                match &verdict {
                    RowVerdict::Match { exit_code } => format!("MATCH (exit={exit_code})"),
                    RowVerdict::Mismatch { detail } => format!("MISMATCH ({detail})"),
                    RowVerdict::Incomplete { reason } => format!("INCOMPLETE ({reason})"),
                    RowVerdict::NondetFailClosed { first_reason } =>
                        format!("NONDET-FAILCLOSED (first: {first_reason})"),
                }
            );
            rows.push((row_id, verdict));
        }
    }

    // ---- Report ----
    let total = rows.len();
    let matched = rows
        .iter()
        .filter(|(_, v)| matches!(v, RowVerdict::Match { .. }))
        .count();
    let coverage = 100.0 * matched as f64 / total as f64;

    let mut gap_table: BTreeMap<String, u32> = BTreeMap::new();
    let mut incomplete_rows: Vec<String> = Vec::new();
    let mut nondet_count = 0u32;
    for (id, v) in &rows {
        match v {
            RowVerdict::Incomplete { reason } => {
                let key = reason
                    .split(&[':', '|'][..])
                    .next()
                    .unwrap_or(reason)
                    .trim()
                    .to_string();
                *gap_table.entry(key).or_insert(0) += 1;
                incomplete_rows.push(format!("  INCOMPLETE {id}: {reason}"));
            }
            RowVerdict::NondetFailClosed { first_reason } => {
                nondet_count += 1;
                incomplete_rows.push(format!(
                    "  NONDET-FAILCLOSED {id}: first verdict was '{first_reason}' \
                     (retry compiled; counted INCOMPLETE, flagged — solver-deadline flap)"
                ));
            }
            _ => {}
        }
    }

    eprintln!("\n==================== COMPLETE-5 CORPUS REPORT ====================");
    eprintln!(
        "rows: {total} (programs x O0/O3) | MATCH: {matched} | INCOMPLETE: {} | \
         NONDET-FAILCLOSED: {nondet_count} | MISMATCH: {}",
        incomplete_rows.len() as u32 - nondet_count,
        mismatches.len()
    );
    eprintln!(
        "compile-and-match coverage: {coverage:.1}% (ratchet floor: {floor:.1}%)"
    );
    if !gap_table.is_empty() {
        eprintln!("ranked gap table (diagnostic -> row count):");
        let mut ranked: Vec<(&String, &u32)> = gap_table.iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(a.1));
        for (reason, count) in ranked {
            eprintln!("  {count:>3}x {reason}");
        }
    }
    if !incomplete_rows.is_empty() {
        eprintln!("incomplete rows:\n{}", incomplete_rows.join("\n"));
    }
    eprintln!("==================================================================\n");

    // ---- The gate ----
    assert!(
        mismatches.is_empty(),
        "COMPLETE-5 P0: exit-code MISMATCH between LLVM and trust-cg — a real-program \
         miscompile (stop-the-line; fuzzer-finding doctrine applies):\n{}",
        mismatches.join("\n")
    );
    assert!(
        coverage >= floor,
        "COMPLETE-5 coverage regression: measured {coverage:.1}% < committed floor {floor:.1}%.\n\
         A previously-compiling corpus row now fails closed. Find the regression; do NOT \
         lower the floor.\n{}",
        incomplete_rows.join("\n")
    );
}
