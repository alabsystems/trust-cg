// Compiled only on an aarch64-apple-darwin host: another host builds this
// target with no test in it, never one that passes without running (L06-P10).
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

// Integration test for the rustc_codegen_trust_cg M1 hello-loop path.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates
// License: Apache-2.0
//
// Status: WS4 milestone M1.
//
// The end-goal of this test is to:
//
//     1. Build the backend library (Cargo builds it for this test).
//     2. Invoke `trustc -Zcodegen-backend=<dylib> --target aarch64-apple-darwin`
//        on a source file containing `fn main() { loop {} }`.
//     3. Run the resulting binary for up to 1s, expect it to block forever
//        (SIGKILL = success; the infinite loop IS the program's semantics).
//
// M1 covers the full end-to-end pipeline: run the compiled binary,
// assert that it infinite-loops, assert that a SIGKILL after 1s
// terminates it, and assert it produced no output.
//
// Running this test:
//
//     cd crates/rustc-codegen-trust-cg
//     targo --unverified test --release -- --nocapture
//
// Prerequisites: the installed Trust package this crate pins
// (`rust-toolchain.toml` `channel = "trust"`; it ships the rustc_private crates
// and llvm-tools).

use std::path::PathBuf;
use std::process::{Command, Stdio};
use std::time::Duration;

/// The backend sibling of this Cargo test executable, not another profile or
/// whichever cached library happens to have the newest modification time.
fn ensure_dylib_built() -> PathBuf {
    backend_artifact_support::current_test_backend()
}

/// Write `contents` to a temp file with the requested filename stem.
/// Returns the full path. We avoid pulling in `tempfile` to keep this
/// crate's M0 dependency set empty.
fn write_temp_source(stem: &str, contents: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    // PID-scoped to avoid collisions between parallel cargo-test
    // invocations. `stem` disambiguates tests inside the same run.
    path.push(format!("rcl2_{}_{}.rs", stem, std::process::id()));
    std::fs::write(&path, contents).expect("failed to write temp source file");
    path
}

#[test]
fn m1_hello_loop_compiles_and_runs_until_killed() {
    // This M0 smoke test drives the host compile (`aarch64-apple-darwin`, the
    // only host this target is built for) against the backend Cargo built for
    // this test. The bridge-notes assertion below needs the backend's
    // `bridge-notes` knob, which only a compiler carrying `-Ztrust-ir-cg-args`
    // can express; a missing prerequisite fails by name.
    darwin_native::require("hello_loop", &[]);
    // The smallest possible Rust program. This is literally the WS4 M0
    // target: when this compiles end-to-end and runs, we are done with
    // M0.
    let src = "fn main() { loop {} }\n";
    let src_path = write_temp_source("hello_loop", src);

    let dylib = ensure_dylib_built();
    assert!(
        dylib.exists(),
        "backend dylib was not produced at {:?}",
        dylib
    );

    let out_bin = std::env::temp_dir().join(format!("rcl2_hello_loop_out_{}", std::process::id()));

    // Invoke nightly rustc with our backend. We do NOT pass
    // --target=aarch64-apple-darwin explicitly; the host triple IS
    // aarch64-apple-darwin for the machines this test is expected to
    // run on (per the WS4 brief). Hard-coding it would cause the test
    // to fail on Linux workstations that don't have an
    // aarch64-apple-darwin target installed.
    let backend_arg = {
        let mut s = std::ffi::OsString::from("-Zcodegen-backend=");
        s.push(&dylib);
        s
    };
    // ASK for the bridge notes; do not hope the environment carries them.
    // The success path below asserts on the "#574 entry wrapper uses lang_start"
    // line, and 13989b40 moved every such note behind `bridge_notes_enabled()`
    // — i.e. behind the `bridge-notes` knob being set — because they fired on every
    // compile into every build log. The assertion therefore only held on a
    // developer shell that happened to export the variable, and could never
    // hold in a clean one. The publication gate runs the anonymous clone with a
    // scrubbed environment (PATH, LANG/LC_*, TZ, RUSTUP_HOME, SSL_CERT_* and
    // nothing else), so it stripped the variable and this test failed there
    // with an EMPTY stderr and a rustc that had exited 0.
    //
    // The staleness was invisible until then: while lowering `lang_start`'s
    // closure was still fail-closed, this test always took an early-return
    // skip branch (since removed), whose diagnostics come from
    // `tcx.dcx().fatal(...)` and are never gated. Lowering landed, the success path ran for the first
    // time, and the latent coupling surfaced as a release-gate failure.
    //
    // Setting it on the child makes the observation hermetic — the test now
    // depends on what the backend DOES, not on what the ambient shell exports.
    //
    // It is passed as a TRACKED compiler option, not an environment variable:
    // trustc refuses every `TCG_*`/`TRUST_CG_*` variable as an untracked
    // semantic/codegen control, so `TCG_BRIDGE_NOTES=1` on the child now makes
    // the compile fail before the backend loads at all.
    let output = toolchain_support::rustc_command()
        .arg(&backend_arg)
        .arg(toolchain_support::backend_knobs_arg(&["bridge-notes"]))
        .arg("-o")
        .arg(&out_bin)
        .arg(&src_path)
        .output()
        .expect("failed to spawn trustc");

    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    eprintln!("rustc stderr:\n{stderr}");
    eprintln!("rustc stdout:\n{stdout}");
    eprintln!("rustc exit: {:?}", output.status);

    let _ = std::fs::remove_file(&src_path);

    // The compile must succeed; no refusal is an accepted early return. The
    // branch that used to treat a failed compile as a skip accepted any
    // refusal naming `lang_start`, a closure and `failing closed`, so on
    // aarch64-apple-darwin it credited the certificates-on proof-promotion
    // refusal of `std::rt::lang_start` and its shims (`[TCG-PROOF-465]`,
    // measured 2026-09-29 on Trust 9192) as a pass (ledger L06-P10). Lowering
    // `lang_start`'s closure landed long ago; a refusal of any kind fails here.
    assert!(
        output.status.success(),
        "hello-loop did not compile through the bridge in the default \
         (certificates-on) lane; a refusal is a failure, never a skip. \
         stderr was: <<<{stderr}>>>"
    );

    assert!(
        stderr.contains("rustc_codegen_trust_cg: #574 entry wrapper uses lang_start"),
        "hello-loop did not report using the lang_start entry wrapper. stderr was: <<<{stderr}>>>"
    );
    assert!(
        !stderr.contains("refusing to fall back to direct Rust main"),
        "hello-loop unexpectedly reached the direct Rust-main fallback diagnostic. stderr was: <<<{stderr}>>>"
    );

    let load_failure_markers = [
        "failed to load",
        "could not load",
        "dlopen",
        "image not found",
        "Library not loaded",
    ];
    for marker in &load_failure_markers {
        assert!(
            !stderr.contains(marker),
            "rustc failed to load our backend dylib \
             (matched marker: {marker:?}). stderr: <<<{stderr}>>>"
        );
    }

    assert!(
        out_bin.exists(),
        "rustc succeeded but did not produce the expected binary at {:?}",
        out_bin
    );

    let mut child = Command::new(&out_bin)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn compiled hello-loop binary");
    std::thread::sleep(Duration::from_secs(1));
    match child
        .try_wait()
        .expect("failed to poll compiled hello-loop binary")
    {
        None => {}
        Some(status) => panic!("hello-loop exited before SIGKILL: {status:?}"),
    }

    child.kill().expect("failed to SIGKILL hello-loop binary");
    let killed = child
        .wait_with_output()
        .expect("failed to collect killed hello-loop output");
    let run_stdout = String::from_utf8_lossy(&killed.stdout);
    let run_stderr = String::from_utf8_lossy(&killed.stderr);
    assert_eq!(run_stdout, "", "hello-loop unexpectedly wrote stdout");
    assert_eq!(run_stderr, "", "hello-loop unexpectedly wrote stderr");

    let _ = std::fs::remove_file(&out_bin);
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::On,
    );
}
