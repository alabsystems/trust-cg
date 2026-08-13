// trust-cg-cli/tests/target_flag.rs - CLI target parsing boundary tests
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use std::path::PathBuf;
use std::process::Command;

/// Path to the compiled `trust-cg` binary for this test run.
fn trust_cg_bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_trust-cg"))
}

#[test]
fn cli_rejects_unsupported_x86_32_targets_before_compilation() {
    for target in [
        "x86",
        "i386",
        "i486",
        "i586",
        "i686",
        "i686-unknown-linux-gnu",
        "i686-pc-windows-msvc",
        "i386-apple-darwin",
    ] {
        let output = Command::new(trust_cg_bin())
            .arg("-c")
            .arg("--target")
            .arg(target)
            .arg("unused.tmbc")
            .output()
            .unwrap_or_else(|error| panic!("run trust-cg for target {target}: {error}"));

        assert!(
            !output.status.success(),
            "unsupported 32-bit x86 target {target} should fail"
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("unsupported 32-bit x86 target"),
            "{target} error should explicitly reject 32-bit x86. stderr:\n{stderr}"
        );
        assert!(
            stderr.contains("x86 support is x86_64 only") && stderr.contains("x86_64 triple"),
            "{target} error should point users at x86_64-only support. stderr:\n{stderr}"
        );
        assert!(
            !stderr.contains("failed to read trust_ir module"),
            "{target} should fail while parsing --target, before input loading. stderr:\n{stderr}"
        );
    }
}

#[test]
fn cli_help_says_x86_support_is_x86_64_only() {
    let output = Command::new(trust_cg_bin())
        .arg("--help")
        .output()
        .expect("run trust-cg --help");

    assert!(output.status.success(), "--help should succeed");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("x86_64 only") && stdout.contains("32-bit x86"),
        "--help should document the x86_64-only boundary. stdout:\n{stdout}"
    );
}
