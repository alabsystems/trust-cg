//! Darwin AArch64 host of the `rust-call` / closure-body boundary checks that
//! `aarch64_c_fnabi_aggregate_linux` runs on Linux AArch64: the same two
//! support modules (`support/rust_call_pointer_calls.rs`,
//! `support/inlined_closure_bodies.rs`), the same fixtures and the same
//! LLVM-computed values, compiled for `aarch64-apple-darwin` natively. Every
//! program must compile with the bridge and print LLVM's value in all four
//! library x binary pairings at O0-O3; nothing is refused.
//!
//! Diagnostic native execution under the backend's `no-proof-certs` knob; it
//! does not qualify mandatory machine proof, and a Darwin run does not stand in
//! for the Linux host (the placement rules differ: Darwin packs narrow stack
//! arguments, AAPCS64 does not).

#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/inlined_closure_bodies.rs"]
mod inlined_closure_bodies;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/rust_call_pointer_calls.rs"]
mod rust_call_pointer_calls;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const TARGET: &str = "aarch64-apple-darwin";
const KEEP_ARTIFACTS: &str = "RUST_CALL_BOUNDARY_KEEP_ARTIFACTS";

/// The test's artifacts directory, removed when the test ends, passing or
/// failing; every failure message carries its complete step transcript.
/// `RUST_CALL_BOUNDARY_KEEP_ARTIFACTS=1` retains it.
struct Artifacts(PathBuf);

impl Drop for Artifacts {
    fn drop(&mut self) {
        if std::env::var_os(KEEP_ARTIFACTS).is_some_and(|value| value == "1") {
            eprintln!("retained artifacts: {}", self.0.display());
        } else if let Err(error) = std::fs::remove_dir_all(&self.0) {
            eprintln!("could not remove artifacts {}: {error}", self.0.display());
        }
    }
}

/// The exact build compiler, edition 2024 (the fixtures' edition on Linux too).
fn rustc_command() -> Command {
    toolchain_support::rustc_command_with_edition("2024")
}

/// Run `command` to completion within `seconds`, killing it past that, and
/// retain its complete transcript at `log`. (macOS has no `timeout`.)
fn run_bounded(command: &mut Command, seconds: u32, log: &Path) -> (Output, String) {
    let mut child = command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn bounded step");
    let limit = Duration::from_secs(u64::from(seconds));
    let start = Instant::now();
    let mut killed = false;
    while child.try_wait().expect("poll bounded step").is_none() {
        if start.elapsed() > limit {
            let _ = child.kill();
            killed = true;
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    let output = child.wait_with_output().expect("collect bounded step");
    let transcript = format!(
        "command: {command:?}\nstatus: {}{}\nstdout:\n{}\nstderr:\n{}",
        output.status,
        if killed {
            " (killed: over its time limit)"
        } else {
            ""
        },
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::write(log, &transcript).expect("retain complete step log");
    (output, transcript)
}

fn checked(command: &mut Command, seconds: u32, log: &Path) -> Output {
    let (output, transcript) = run_bounded(command, seconds, log);
    assert!(
        output.status.success(),
        "{transcript}\nartifacts: {}",
        log.display()
    );
    output
}

fn sha256(path: &Path) -> String {
    let output = Command::new("shasum")
        .args(["-a", "256"])
        .arg(path)
        .output()
        .expect("shasum");
    assert!(output.status.success(), "hash {}", path.display());
    let text = String::from_utf8(output.stdout).expect("SHA256 output");
    let hash = text.split_whitespace().next().expect("SHA256 digest");
    assert!(hash.len() == 64 && hash.bytes().all(|b| b.is_ascii_hexdigit()));
    hash.to_owned()
}

/// The backend arguments of every bridge compile in the shared modules:
/// proof certificates off (`no-proof-certs`), a diagnostic lane.
fn cg_knobs() -> String {
    toolchain_support::backend_knobs_arg(&["no-proof-certs"])
}

/// The library Cargo built for this test build (never a nested build).
fn backend(_artifacts: &Path) -> (PathBuf, String) {
    let path = backend_artifact_support::current_test_backend();
    let hash = sha256(&path);
    (path, hash)
}

#[test]
fn rust_call_pointer_calls_match_llvm_aarch64() {
    rust_call_pointer_calls::no_proof_rust_call_pointer_calls_match_llvm();
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn inlined_closure_bodies_match_llvm_aarch64() {
    inlined_closure_bodies::no_proof_inlined_closure_bodies_match_llvm();
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
