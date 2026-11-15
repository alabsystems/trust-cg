// trust-cg-cli/tests/print_ay_identity.rs - `--print-ay-identity`
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Scripts that run an AY themselves (scripts/check_aarch64_aot_arithmetic.py's
// independent replay) obtain admission from this flag. These tests pin that
// the answer is the identity rule's, that a banner-faking script is refused
// and never executed, and that the report's digest is the file's bytes.
//
// This test binary links the same trust-cg-verify build as the CLI, so it
// reads the same compiled-in record. A stock-toolchain build records no AY:
// then every case must be refused TCG-AY-IDENTITY-UNRECORDED, which is
// asserted rather than skipped.

#![cfg(unix)]

use std::ffi::OsStr;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;
use sha2::{Digest, Sha256};
use trust_cg_verify::ay_identity::{ToolchainAyRecord, recorded_toolchain_ay_identity};

fn cli() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

fn run(ay_solver_path: Option<&OsStr>, extra: &[&str]) -> (Value, i32) {
    let mut command = Command::new(cli());
    command.arg("--permit-unlicensed"); // Claim-less fixtures: refused by default since WS7.5 (DG-73).
    command.arg("--print-ay-identity").args(extra);
    command.env_remove("AY_SOLVER_PATH");
    if let Some(value) = ay_solver_path {
        command.env("AY_SOLVER_PATH", value);
    }
    let output = command.output().expect("run trust-cg");
    let stdout = String::from_utf8(output.stdout).expect("utf-8 report");
    let report: Value = serde_json::from_str(stdout.trim())
        .unwrap_or_else(|error| panic!("report is not one JSON object ({error}): {stdout:?}"));
    assert_eq!(report["schema"], "trust-cg.ay-identity.v2");
    assert_toolchain_overlay(&report);
    (report, output.status.code().expect("exit code"))
}

/// `toolchain_overlay` is present in every report: `null` for a build from an
/// installed (or stock) toolchain, else the overlay this build recorded.
fn assert_toolchain_overlay(report: &Value) {
    let overlay = report
        .get("toolchain_overlay")
        .unwrap_or_else(|| panic!("no toolchain_overlay field: {report}"));
    match ToolchainAyRecord::recorded().overlay() {
        None => assert!(overlay.is_null(), "{report}"),
        Some(recorded) => {
            assert_eq!(
                overlay["manifest_sha256"],
                recorded.manifest_sha256(),
                "{report}"
            );
            assert_eq!(overlay["clean_sha256"], recorded.clean_sha256(), "{report}");
            assert_eq!(overlay["clean_commit"], recorded.clean_commit(), "{report}");
            if report["admitted"] == true {
                assert!(
                    report["identity"]
                        .as_str()
                        .is_some_and(|identity| identity.contains(recorded.manifest_sha256())),
                    "{report}"
                );
            }
        }
    }
}

fn sha256_file(path: &Path) -> String {
    format!("{:x}", Sha256::digest(std::fs::read(path).unwrap()))
}

fn executable(path: &Path, bytes: &[u8]) {
    std::fs::write(path, bytes).unwrap();
    std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
}

fn assert_refused(report: &Value, status: i32, recorded_code: &str) {
    assert_eq!(status, 1, "a refusal exits 1: {report}");
    assert_eq!(report["admitted"], false, "{report}");
    let expected = if recorded_toolchain_ay_identity().is_ok() {
        recorded_code
    } else {
        "TCG-AY-IDENTITY-UNRECORDED"
    };
    assert_eq!(report["code"], expected, "{report}");
    assert!(
        report.get("sha256").is_none(),
        "a refusal names no admitted digest: {report}"
    );
}

/// `exec_path` is a `0500` single-link file in a `0700` directory, addressed
/// by the admitted digest, holding exactly the admitted bytes, and it is not
/// the admitted path.
fn assert_private_copy(report: &Value, sha256: &str) {
    use std::os::unix::fs::MetadataExt;
    let exec = PathBuf::from(report["exec_path"].as_str().expect("exec_path"));
    assert_ne!(report["exec_path"], report["path"], "{report}");
    assert_eq!(sha256_file(&exec), sha256, "{report}");
    let file = std::fs::symlink_metadata(&exec).unwrap();
    assert!(file.file_type().is_file(), "{report}");
    assert_eq!(file.mode() & 0o7777, 0o500, "{report}");
    assert_eq!(file.nlink(), 1, "{report}");
    let directory = exec.parent().unwrap();
    assert_eq!(
        directory.file_name().unwrap(),
        OsStr::new(sha256),
        "{report}"
    );
    for directory in [directory, directory.parent().unwrap()] {
        assert_eq!(
            std::fs::symlink_metadata(directory).unwrap().mode() & 0o7777,
            0o700,
            "{}",
            directory.display()
        );
    }
}

#[test]
fn banner_faking_script_is_refused_and_never_executed() {
    let dir = tempfile::tempdir().unwrap();
    let marker = dir.path().join("executed");
    let script = dir.path().join("ay");
    let banner = match recorded_toolchain_ay_identity() {
        Ok(identity) => identity.describe(),
        Err(_) => "ay 0.26.0+build.9624.075a482aec84e441918d935743957876bd24afdb".to_owned(),
    };
    executable(
        &script,
        format!(
            "#!/bin/sh\necho executed >> '{}'\necho '{banner}'\necho unsat\n",
            marker.display()
        )
        .as_bytes(),
    );
    let (report, status) = run(Some(script.as_os_str()), &[]);
    assert_refused(&report, status, "TCG-AY-IDENTITY-MISMATCH");
    if recorded_toolchain_ay_identity().is_ok() {
        assert!(
            report["detail"]
                .as_str()
                .unwrap()
                .contains(&sha256_file(&script)),
            "the mismatch names the candidate's digest: {report}"
        );
    }
    assert!(
        !marker.exists(),
        "deciding admission executed the candidate"
    );
}

#[test]
fn relative_empty_and_missing_overrides_are_refused() {
    let (report, status) = run(Some(OsStr::new("ay")), &[]);
    assert_refused(&report, status, "TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE");
    let (report, status) = run(Some(OsStr::new("")), &[]);
    assert_refused(&report, status, "TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE");
    let dir = tempfile::tempdir().unwrap();
    let (report, status) = run(Some(dir.path().join("absent").as_os_str()), &[]);
    assert_refused(&report, status, "TCG-AY-IDENTITY-OVERRIDE-MISSING");
}

#[test]
fn byte_copy_of_the_recorded_ay_is_admitted_with_its_digest() {
    let recorded = match recorded_toolchain_ay_identity() {
        Ok(identity) => identity,
        Err(refusal) => {
            // Stock build: the toolchain route is refused too, by name.
            let (report, status) = run(None, &[]);
            assert_eq!(status, 1, "{report}");
            assert_eq!(report["code"], refusal.code(), "{report}");
            assert_eq!(report["recorded"]["code"], refusal.code(), "{report}");
            return;
        }
    };
    // The toolchain route, with no override.
    let (report, status) = run(None, &[]);
    assert_eq!(status, 0, "{report}");
    assert_eq!(report["admitted"], true, "{report}");
    assert_eq!(report["route"], "toolchain-pinned-ay", "{report}");
    assert_eq!(report["sha256"], recorded.sha256(), "{report}");
    assert_eq!(report["recorded"]["sha256"], recorded.sha256(), "{report}");
    let toolchain_ay = PathBuf::from(report["path"].as_str().unwrap());
    assert_eq!(sha256_file(&toolchain_ay), recorded.sha256());
    // What a script must start: the private copy of the admitted bytes.
    assert_private_copy(&report, recorded.sha256());

    // A byte copy named by AY_SOLVER_PATH.
    let dir = tempfile::tempdir().unwrap();
    let copy = dir.path().join("ay-copy");
    executable(&copy, &std::fs::read(&toolchain_ay).unwrap());
    let (report, status) = run(Some(copy.as_os_str()), &[]);
    assert_eq!(status, 0, "{report}");
    assert_eq!(report["route"], "override-pinned-ay", "{report}");
    assert_eq!(report["path"], copy.display().to_string(), "{report}");
    assert_eq!(report["sha256"], recorded.sha256(), "{report}");
    assert_private_copy(&report, recorded.sha256());

    // One flipped byte is a different AY.
    let mut bytes = std::fs::read(&toolchain_ay).unwrap();
    *bytes.last_mut().unwrap() ^= 1;
    executable(&copy, &bytes);
    let (report, status) = run(Some(copy.as_os_str()), &[]);
    assert_refused(&report, status, "TCG-AY-IDENTITY-MISMATCH");
}

#[test]
fn inputs_are_refused_alongside_the_report() {
    let output = Command::new(cli())
        .arg("--permit-unlicensed")
        .args(["--print-ay-identity", "input.tmbc"])
        .output()
        .expect("run trust-cg");
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("--print-ay-identity") && stderr.contains("cannot be used"),
        "{stderr}"
    );
}
