// Integration test: drive `bcp_matrix` against the smoke SAT corpus
// committed under `crates/trust-cg-sat-host/tests/fixtures/sat_corpus/`.
//
// Purpose
// -------
// `bcp_matrix` is the native baseline path through the
// `SolverKernelProvider` ABI. Running it against the same DIMACS files
// that `trust-cg-sat-host`'s integration test feeds to MicroSAT proves
// that:
//
//   1. The DIMACS parser in this crate accepts the same fixture set.
//   2. `bcp_matrix` does not crash on real (50-variable, 218-clause)
//      random 3-SAT inputs.
//   3. The emitted JSON report has the shape downstream tooling expects.
//
// We deliberately do NOT assert SAT vs UNSAT here: `bcp_matrix` is a
// one-shot BCP runner (not a CDCL solver), so its `result_code` reflects
// whether unit-propagation reached a conflict on the pseudo-random
// decision sequence, not the formula's overall satisfiability. The
// solver-level SAT/UNSAT contract is exercised in
// `trust-cg-sat-host/tests/sat_corpus.rs`.

use std::path::{Path, PathBuf};
use std::process::Command;

use serde_json::Value;

fn corpus_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/ parent")
        .join("trust-cg-sat-host")
        .join("tests")
        .join("fixtures")
        .join("sat_corpus")
}

fn run_bcp_matrix(cnf: &Path) -> Value {
    let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
        .arg("--input")
        .arg(cnf)
        .arg("--decisions")
        .arg("64")
        .arg("--seed")
        .arg("12648430")
        .output()
        .expect("bcp_matrix invocation should not fail to spawn");

    assert!(
        output.status.success(),
        "bcp_matrix exit was {:?} on {}; stderr={}",
        output.status.code(),
        cnf.display(),
        String::from_utf8_lossy(&output.stderr)
    );

    serde_json::from_slice(&output.stdout).unwrap_or_else(|err| {
        panic!(
            "bcp_matrix stdout was not valid JSON on {}: {err}\n--- stdout ---\n{}",
            cnf.display(),
            String::from_utf8_lossy(&output.stdout)
        )
    })
}

fn assert_report_shape(cnf: &Path, report: &Value, expected_vars: u64, expected_clauses: u64) {
    assert_eq!(
        report["input"].as_str().expect("input"),
        cnf.display().to_string()
    );
    assert_eq!(
        report["num_vars"].as_u64().expect("num_vars"),
        expected_vars,
        "num_vars mismatch on {}",
        cnf.display()
    );
    assert_eq!(
        report["num_clauses"].as_u64().expect("num_clauses"),
        expected_clauses,
        "num_clauses mismatch on {}",
        cnf.display()
    );
    let code = report["result_code"].as_u64().expect("result_code");
    assert!(
        code == 0 || code == 1,
        "result_code {} not in {{0,1}} on {}",
        code,
        cnf.display()
    );
    let label = report["result_label"].as_str().expect("result_label");
    assert!(
        label == "ok" || label == "conflict",
        "result_label {} not in {{ok, conflict}} on {}",
        label,
        cnf.display()
    );
    assert!(report["propagation_counter"].is_u64());
    assert!(report["elapsed_us"].is_u64());
    assert_eq!(report["jit"], Value::Bool(false));
}

#[test]
fn bcp_matrix_runs_against_uuf50_fixture() {
    let cnf = corpus_dir().join("uuf50-01.cnf");
    if !cnf.exists() {
        // Defensive: if the corpus has been pruned, fail loudly rather
        // than silently passing.
        panic!(
            "expected corpus fixture missing: {} (was the sat_corpus directory removed?)",
            cnf.display()
        );
    }
    let report = run_bcp_matrix(&cnf);
    assert_report_shape(&cnf, &report, 50, 218);
}

#[test]
fn bcp_matrix_runs_against_legacy_aim_named_parity_fixture() {
    let cnf = corpus_dir().join("aim-50-1_6-no-1.cnf");
    if !cnf.exists() {
        panic!(
            "expected corpus fixture missing: {} (was the sat_corpus directory removed?)",
            cnf.display()
        );
    }
    let report = run_bcp_matrix(&cnf);
    assert_report_shape(&cnf, &report, 50, 80);
}
