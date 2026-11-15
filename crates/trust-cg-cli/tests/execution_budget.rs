// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Invalid resource controls must be diagnosed before any output is replaced.

use std::ffi::OsStr;
use std::fs;
use std::path::Path;
use std::process::Command;

fn assert_rejected_without_publication(value: &OsStr, inputs: &[&str], serial: bool) {
    let directory = tempfile::tempdir().unwrap();
    let output_path = directory.path().join("out");
    let sidecar = directory.path().join("roundtrip.json");
    let sentinel = b"previous successful artifact";
    fs::write(&output_path, sentinel).unwrap();
    fs::write(&sidecar, sentinel).unwrap();
    let scratch = directory.path().join("scratch");
    fs::create_dir(&scratch).unwrap();

    let mut command = Command::new(env!("CARGO_BIN_EXE_trust-cg"));
    command.arg("--permit-unlicensed"); // Claim-less fixtures: refused by default since WS7.5 (DG-73).
    command
        .current_dir(directory.path())
        .env("TRUST_CG_MAX_PARALLELISM", value)
        .env("TMPDIR", &scratch)
        .env("TMP", &scratch)
        .env("TEMP", &scratch)
        .args(["--target", "aarch64", "-o", "out"])
        .args(inputs);
    if serial {
        command.arg("--no-parallel");
    }
    if inputs.len() == 1 {
        command.args(["-c", "--emit-json", "roundtrip.json"]);
    }
    // Intentionally missing inputs prove budget admission happens before
    // input reads, not merely before the eventual linker call.
    let output = command.output().unwrap();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{value:?}: {stderr}");
    assert!(
        stderr.contains("invalid execution resource budget"),
        "{stderr}"
    );
    assert!(stderr.contains("TRUST_CG_MAX_PARALLELISM"), "{stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
    assert_eq!(fs::read(&output_path).unwrap(), sentinel);
    assert_eq!(fs::read(&sidecar).unwrap(), sentinel);
    assert_eq!(fs::read_dir(&scratch).unwrap().count(), 0);
}

#[test]
fn malformed_budgets_fail_before_single_or_multiple_input_publication() {
    for value in ["0", "", "no", "-1", "999999999999999999999999999999"] {
        for inputs in [&["missing.tmbc"][..], &["a.tmbc", "b.tmbc"][..]] {
            for serial in [false, true] {
                assert_rejected_without_publication(OsStr::new(value), inputs, serial);
            }
        }
    }
}

#[cfg(unix)]
#[test]
fn non_unicode_budget_is_a_diagnostic() {
    use std::ffi::OsString;
    use std::os::unix::ffi::OsStringExt;
    assert_rejected_without_publication(&OsString::from_vec(vec![0xff]), &["missing.tmbc"], false);
}

#[test]
fn valid_serial_budget_preserves_normal_compilation() {
    let directory = tempfile::tempdir().unwrap();
    let input = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/return_42.trust_ir");
    let object = directory.path().join("out.o");
    let output = Command::new(env!("CARGO_BIN_EXE_trust-cg"))
        .arg("--permit-unlicensed")
        .env("TRUST_CG_MAX_PARALLELISM", "1")
        .args([
            "--format=text",
            "--target",
            "aarch64-apple-darwin",
            "-O0",
            "-c",
        ])
        .arg(input)
        .arg("-o")
        .arg(&object)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(object.metadata().unwrap().len() > 0);
}
