// trust-cg-cli/tests/insert_field_store_form.rs - WS7.1 (b) on the CLI
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// The STORE FORM of `insertfield` (a pointer operand whose pointee the
// producer expects to be updated in place) is invalid trust-ir. The CLI must
// refuse it by name rather than compile it with either meaning — since WS7.3
// at ingestion, as trust-ir's `FieldAccessInvalid`; the value form of the same insert still
// compiles. The fixtures are shared with trust-cg-codegen's
// `insert_field_value_semantics` test.

use std::path::PathBuf;
use std::process::Command;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../trust-cg-codegen/tests/fixtures/insert_field")
        .join(name)
}

fn scratch_dir(test_name: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_cli_insert_field_{}_{}",
        test_name,
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

fn compile(input: &PathBuf, output: &PathBuf, extra: &[&str]) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_trust-cg"))
        .arg("--format=text")
        .args(extra)
        .arg("-c")
        .arg("-o")
        .arg(output)
        .arg(input)
        .output()
        .expect("spawn trust-cg")
}

#[test]
fn store_form_insert_field_is_refused_on_the_cli() {
    let dir = scratch_dir("store_form");
    let output = dir.join("store_form.o");
    // The fixture is claim-less (`body_gate` absent), which the CLI refuses
    // by default (WS7.5, DG-73); the disclosed Permit makes the refusal the
    // store form's, never the license's.
    let result = compile(
        &fixture("store_form.trust_ir"),
        &output,
        &["--permit-unlicensed"],
    );
    let stderr = String::from_utf8_lossy(&result.stderr);
    let stdout = String::from_utf8_lossy(&result.stdout);
    assert!(
        !result.status.success(),
        "the store form must be refused; stdout={stdout} stderr={stderr}"
    );
    // WS7.3: the CLI's ingestion admission refuses the store form as the
    // trust-ir finding it is, before the adapter's own named refusal
    // (`AggregateInsertNotValueForm`, still pinned on the raw adapter entry by
    // trust-cg-codegen's `insert_field_value_semantics`).
    assert!(
        stderr.contains("trust-ir validation refused module `ws7_1-store-form`")
            && stderr.contains("FieldAccessInvalid"),
        "must be the named ingestion refusal (FieldAccessInvalid); stderr={stderr}"
    );
    assert!(
        !output.exists(),
        "a refused module must not leave an object"
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// Negative twin: the VALUE form (two insert chains off one seed) compiles.
#[test]
fn value_form_insert_field_compiles_on_the_cli() {
    let dir = scratch_dir("value_form");
    let output = dir.join("shared_seed.o");
    let result = compile(
        &fixture("c13_shared_seed.trust_ir"),
        &output,
        &["--recognize-authority", "c13-repro"],
    );
    assert!(
        result.status.success(),
        "the value form must compile; stderr={}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(output.exists(), "the object must be written");
    let _ = std::fs::remove_dir_all(&dir);
}
