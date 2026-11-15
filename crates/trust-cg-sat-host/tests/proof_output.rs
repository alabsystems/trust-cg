// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::Path;
use std::process::Command;

const CNF: &[u8] = b"p cnf 1 2\n1 0\n-1 0\n";

fn assert_alias_refused(input: &Path, output: &Path) {
    let result = Command::new(env!("CARGO_BIN_EXE_trust_cg_sat"))
        .arg(input)
        .arg("--proof")
        .arg(output)
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(stderr.contains("aliases CNF input"), "{stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
    assert_eq!(std::fs::read(input).unwrap(), CNF);
}

#[test]
fn proof_cannot_overwrite_its_cnf_input() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("input.cnf");
    std::fs::write(&input, CNF).unwrap();
    assert_alias_refused(&input, &input);
}

#[test]
fn hard_link_proof_alias_preserves_input_bytes() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("input.cnf");
    let output = directory.path().join("proof.drat");
    std::fs::write(&input, CNF).unwrap();
    std::fs::hard_link(&input, &output).unwrap();
    assert_alias_refused(&input, &output);
}

#[cfg(unix)]
#[test]
fn symlink_proof_alias_preserves_input_bytes() {
    let directory = tempfile::tempdir().unwrap();
    let input = directory.path().join("input.cnf");
    let output = directory.path().join("proof.drat");
    std::fs::write(&input, CNF).unwrap();
    std::os::unix::fs::symlink(&input, &output).unwrap();
    assert_alias_refused(&input, &output);
}
