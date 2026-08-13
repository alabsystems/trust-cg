// Golden help-text snapshot tests for `trust-cg-test`.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The snapshots under `tests/snapshots/` are the stable contract with
// operators + CI — CI fails on any un-committed drift. Regenerate via:
//   INSTA_UPDATE=always cargo test -p trust-cg-test --test cli

use assert_cmd::Command;

fn bin() -> Command {
    Command::cargo_bin("trust-cg-test").expect("binary built")
}

fn help_of(subcmd: &[&str]) -> String {
    let mut c = bin();
    c.args(subcmd).arg("--help");
    let out = c.output().expect("run");
    let raw = String::from_utf8_lossy(&out.stdout);
    let raw = raw.replace("trust-cg-test.exe", "trust-cg-test");
    let mut normalized = raw
        .lines()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n");
    if raw.ends_with('\n') {
        normalized.push('\n');
    }
    normalized
}

#[test]
fn top_level_help() {
    insta::assert_snapshot!("top_help", help_of(&[]));
}

#[test]
fn matrix_help() {
    insta::assert_snapshot!("matrix_help", help_of(&["matrix"]));
}

#[test]
fn suite_help() {
    insta::assert_snapshot!("suite_help", help_of(&["suite"]));
}

#[test]
fn fuzz_help() {
    insta::assert_snapshot!("fuzz_help", help_of(&["fuzz"]));
}

#[test]
fn rustc_help() {
    insta::assert_snapshot!("rustc_help", help_of(&["rustc"]));
}

#[test]
fn rustc_smoke_help() {
    insta::assert_snapshot!("rustc_smoke_help", help_of(&["rustc", "smoke"]));
}

#[test]
fn rustc_ui_help() {
    insta::assert_snapshot!("rustc_ui_help", help_of(&["rustc", "ui"]));
}

#[test]
fn rustc_feature_coverage_help() {
    insta::assert_snapshot!(
        "rustc_feature_coverage_help",
        help_of(&["rustc", "feature-coverage"])
    );
}

#[test]
fn bootstrap_help() {
    insta::assert_snapshot!("bootstrap_help", help_of(&["bootstrap"]));
}

#[test]
fn ecosystem_help() {
    insta::assert_snapshot!("ecosystem_help", help_of(&["ecosystem"]));
}

#[test]
fn prove_help() {
    insta::assert_snapshot!("prove_help", help_of(&["prove"]));
}

#[test]
fn pipeline_help() {
    insta::assert_snapshot!("pipeline_help", help_of(&["pipeline"]));
}

#[test]
fn pipeline_regalloc_help() {
    insta::assert_snapshot!("pipeline_regalloc_help", help_of(&["pipeline", "regalloc"]));
}

#[test]
fn pipeline_schedule_help() {
    insta::assert_snapshot!("pipeline_schedule_help", help_of(&["pipeline", "schedule"]));
}

#[test]
fn pipeline_emit_help() {
    insta::assert_snapshot!("pipeline_emit_help", help_of(&["pipeline", "emit"]));
}

#[test]
fn report_help() {
    insta::assert_snapshot!("report_help", help_of(&["report"]));
}

#[test]
fn ratchet_help() {
    insta::assert_snapshot!("ratchet_help", help_of(&["ratchet"]));
}

#[test]
fn ratchet_tests_help() {
    insta::assert_snapshot!("ratchet_tests_help", help_of(&["ratchet", "tests"]));
}

#[test]
fn ratchet_warnings_help() {
    insta::assert_snapshot!("ratchet_warnings_help", help_of(&["ratchet", "warnings"]));
}

#[test]
fn ratchet_unwrap_help() {
    insta::assert_snapshot!("ratchet_unwrap_help", help_of(&["ratchet", "unwrap"]));
}

#[test]
fn ratchet_panic_clippy_help() {
    insta::assert_snapshot!(
        "ratchet_panic_clippy_help",
        help_of(&["ratchet", "panic-clippy"])
    );
}

#[test]
fn ratchet_shell_isolation_help() {
    insta::assert_snapshot!(
        "ratchet_shell_isolation_help",
        help_of(&["ratchet", "shell-isolation"])
    );
}

#[test]
fn ratchet_schema_help() {
    insta::assert_snapshot!("ratchet_schema_help", help_of(&["ratchet", "schema"]));
}

#[test]
fn ratchet_lint_linux_help() {
    insta::assert_snapshot!(
        "ratchet_lint_linux_help",
        help_of(&["ratchet", "lint-linux"])
    );
}

#[test]
fn doctor_help() {
    insta::assert_snapshot!("doctor_help", help_of(&["doctor"]));
}

#[test]
fn lint_linux_help() {
    insta::assert_snapshot!("lint_linux_help", help_of(&["lint-linux"]));
}

#[test]
fn every_remaining_stub_exits_with_code_2_and_says_not_implemented() {
    let cases: &[&[&str]] = &[
        &["suite"],
        &["fuzz"],
        &["bootstrap"],
        &["ecosystem"],
        &["prove"],
        &["pipeline", "regalloc"],
    ];
    for args in cases {
        let temp = tempfile::tempdir().expect("temporary output directory");
        let artifact = temp.path().join("must-not-exist.json");
        let mut command = bin();
        command
            .arg("--out")
            .arg(&artifact)
            .args(args.iter().copied());
        let output = command.output().expect("run stub");
        assert_eq!(output.status.code(), Some(2), "{args:?} stub must exit 2");
        assert!(output.stdout.is_empty(), "{args:?} stub wrote to stdout");
        assert!(
            !artifact.exists(),
            "{args:?} stub wrote an output artifact at {}",
            artifact.display()
        );
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            stderr.contains("not implemented in trust-cg 0.1.0"),
            "{args:?}: {stderr}"
        );
    }
}

#[test]
fn test_ratchet_requires_an_explicit_baseline() {
    let mut command = bin();
    command.args(["ratchet", "tests"]);
    let output = command.output().expect("run ratchet help validation");
    assert_eq!(output.status.code(), Some(2));
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--baseline <PATH>"), "{stderr}");
}

#[test]
fn matrix_shard_requires_crate_without_running_matrix() {
    let mut c = bin();
    c.args(["matrix", "--shard", "integration-jit-runtime"]);
    let out = c.output().expect("run");
    assert_eq!(out.status.code(), Some(64));
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("--shard requires --crate"), "{stderr}");
}

#[test]
fn doctor_json_format_smoke() {
    let mut c = bin();
    c.args(["--format", "json", "doctor", "--for", "report"]);
    let out = c.output().expect("run");
    // `for=report` has no required tools, so we expect exit 0.
    assert!(
        out.status.code() == Some(0) || out.status.code() == Some(2),
        "unexpected doctor exit: {:?}",
        out.status.code()
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("\"tools\""), "json report missing tools");
}

#[test]
fn rustc_feature_coverage_json_dry_run_reports_inventory() {
    let mut c = bin();
    c.args(["--dry-run", "--format", "json", "rustc", "feature-coverage"]);
    let out = c.output().expect("run");
    assert_eq!(out.status.code(), Some(0));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains("\"mode\": \"feature-coverage\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("\"target\": \"aarch64-unknown-linux-gnu\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("\"target\": \"x86_64-unknown-linux-gnu\""),
        "{stdout}"
    );
    assert!(stdout.contains("\"variant\": \"Intrinsic\""), "{stdout}");
    assert!(!stdout.contains("not yet implemented"), "{stdout}");
}

#[test]
fn rustc_smoke_json_dry_run_invokes_backend_plan() {
    let mut c = bin();
    c.args(["--dry-run", "--format", "json", "rustc", "smoke"]);
    let out = c.output().expect("run");
    assert_eq!(out.status.code(), Some(0));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("\"mode\": \"smoke\""), "{stdout}");
    assert!(stdout.contains("\"invoked\": true"), "{stdout}");
    assert!(stdout.contains("\"name\": \"build-backend\""), "{stdout}");
    assert!(stdout.contains("\"name\": \"smoke-main\""), "{stdout}");
    assert!(stdout.contains("-Zcodegen-backend="), "{stdout}");
    assert!(
        stdout.contains("rustc smoke would build and invoke rustc_codegen_trust_cg on 1 fixture"),
        "{stdout}"
    );
}

#[test]
fn rustc_ui_json_dry_run_invokes_backend_fixtures() {
    let mut c = bin();
    c.args(["--dry-run", "--format", "json", "rustc", "ui"]);
    let out = c.output().expect("run");
    assert_eq!(out.status.code(), Some(0));
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("\"mode\": \"ui\""), "{stdout}");
    assert!(stdout.contains("\"invoked\": true"), "{stdout}");
    assert!(stdout.contains("\"name\": \"build-backend\""), "{stdout}");
    assert!(stdout.contains("\"name\": \"empty-main\""), "{stdout}");
    assert!(
        stdout.contains("\"name\": \"extern-c-bool-and-narrow-integer-direct\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("\"name\": \"extern-c-char-direct-scalar-fail-closed\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("\"name\": \"extern-c-i128-scalar-abi-fail-closed\""),
        "{stdout}"
    );
    assert!(
        stdout.contains("\"name\": \"extern-c-u128-scalar-abi-fail-closed\""),
        "{stdout}"
    );
    assert!(stdout.contains("-Zcodegen-backend="), "{stdout}");
    assert!(!stdout.contains("NotImplemented"), "{stdout}");
}
