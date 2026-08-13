use std::process::Command;

use serde_json::Value;

#[test]
fn bcp_matrix_runs_against_tiny_dimacs_and_emits_expected_json() {
    let temp_dir = tempfile::tempdir().expect("tempdir");
    let cnf_path = temp_dir.path().join("tiny.cnf");
    std::fs::write(&cnf_path, "p cnf 3 2\n1 -3 0\n2 3 0\n").expect("write cnf");

    let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
        .arg("--input")
        .arg(&cnf_path)
        .arg("--decisions")
        .arg("32")
        .arg("--seed")
        .arg("42")
        .output()
        .expect("bcp_matrix should run");

    assert!(
        output.status.success(),
        "expected exit code 0, got {:?}; stderr={}",
        output.status.code(),
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value =
        serde_json::from_slice(&output.stdout).expect("stdout should be valid JSON");
    assert_eq!(
        report["input"].as_str().expect("input string"),
        cnf_path.display().to_string()
    );
    assert_eq!(report["num_vars"].as_u64().expect("num_vars"), 3);
    assert_eq!(report["num_clauses"].as_u64().expect("num_clauses"), 2);
    assert_eq!(report["decisions_fed"].as_u64().expect("decisions_fed"), 32);
    let code = report["result_code"].as_u64().expect("result_code");
    assert!(
        code == 0 || code == 1,
        "expected result_code in {{0,1}}, got {code}"
    );
    let label = report["result_label"].as_str().expect("result_label");
    assert!(
        label == "ok" || label == "conflict",
        "expected label ok|conflict, got {label}"
    );
    assert!(report["propagation_counter"].is_u64());
    assert!(report["elapsed_us"].is_u64());
}

#[test]
fn bcp_matrix_defaults_use_one_hundred_decisions() {
    let temp_dir = tempfile::tempdir().expect("tempdir");
    let cnf_path = temp_dir.path().join("default.cnf");
    std::fs::write(&cnf_path, "p cnf 2 1\n1 -2 0\n").expect("write cnf");

    let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
        .arg("--input")
        .arg(&cnf_path)
        .output()
        .expect("bcp_matrix should run");

    assert!(output.status.success());
    let report: Value = serde_json::from_slice(&output.stdout).expect("json");
    assert_eq!(
        report["decisions_fed"].as_u64().expect("decisions_fed"),
        100
    );
}

#[test]
fn bcp_matrix_reports_parse_error_with_exit_code_one() {
    let temp_dir = tempfile::tempdir().expect("tempdir");
    let cnf_path = temp_dir.path().join("malformed.cnf");
    std::fs::write(&cnf_path, "p cnf 3 1\n1 foo -2 0\n").expect("write cnf");

    let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
        .arg("--input")
        .arg(&cnf_path)
        .output()
        .expect("bcp_matrix should run");

    assert_eq!(
        output.status.code(),
        Some(1),
        "expected exit code 1 on malformed CNF; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let report: Value =
        serde_json::from_slice(&output.stdout).expect("stdout should be JSON error");
    assert_eq!(report["error"].as_str().expect("error kind"), "parse_error");
    assert_eq!(
        report["input"].as_str().expect("input"),
        cnf_path.display().to_string()
    );
    assert!(report["message"].is_string());
}

#[test]
fn bcp_matrix_reports_io_error_for_missing_file() {
    let temp_dir = tempfile::tempdir().expect("tempdir");
    let missing = temp_dir.path().join("does-not-exist.cnf");

    let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
        .arg("--input")
        .arg(&missing)
        .output()
        .expect("bcp_matrix should run");

    assert_eq!(output.status.code(), Some(1));
    let report: Value = serde_json::from_slice(&output.stdout).expect("stdout JSON");
    assert_eq!(report["error"].as_str().expect("error kind"), "io_error");
}

#[test]
fn bcp_matrix_native_default_reports_jit_false() {
    let temp_dir = tempfile::tempdir().expect("tempdir");
    let cnf_path = temp_dir.path().join("native.cnf");
    std::fs::write(&cnf_path, "p cnf 3 2\n1 -3 0\n2 3 0\n").expect("write cnf");

    let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
        .arg("--input")
        .arg(&cnf_path)
        .output()
        .expect("bcp_matrix should run");

    assert!(output.status.success());
    let report: Value = serde_json::from_slice(&output.stdout).expect("json");
    assert!(
        !report["jit"].as_bool().expect("jit field present"),
        "native default should report jit=false"
    );
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[test]
fn bcp_matrix_jit_flag_runs_against_tiny_dimacs() {
    let temp_dir = tempfile::tempdir().expect("tempdir");
    let cnf_path = temp_dir.path().join("tiny_jit.cnf");
    std::fs::write(&cnf_path, "p cnf 3 2\n1 -3 0\n2 3 0\n").expect("write cnf");

    let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
        .arg("--input")
        .arg(&cnf_path)
        .arg("--decisions")
        .arg("16")
        .arg("--seed")
        .arg("42")
        .arg("--jit")
        .output()
        .expect("bcp_matrix should run under --jit");

    assert!(
        output.status.success(),
        "expected exit 0 from --jit run; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_slice(&output.stdout).expect("stdout JSON");
    assert!(
        report["jit"].as_bool().expect("jit field present"),
        "--jit flag should set jit=true in the JSON output"
    );
    assert_eq!(report["num_vars"].as_u64().expect("num_vars"), 3);
    assert_eq!(report["num_clauses"].as_u64().expect("num_clauses"), 2);
    let code = report["result_code"].as_u64().expect("result_code");
    assert!(
        code == 0 || code == 1,
        "expected result_code in {{0,1}}, got {code}"
    );
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[test]
fn bcp_matrix_jit_uses_watched_literal_by_default() {
    // Headline-switchover contract: `bcp_matrix --jit` with no
    // `--jit-kernel` flag runs the watched-literal kernel (the
    // 2.5–3.1×-faster default). The JSON output reports
    // `"jit_kernel": "watched-literal"` and the `result_label` is a
    // valid kernel-status string. Use a generated release-corpus fixture path
    // when present, otherwise an in-tempdir fixture.
    let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("..")
        .join("trust-cg-sat-host")
        .join("tests")
        .join("fixtures")
        .join("sat_corpus")
        .join("uf50-01.cnf");
    let tmp = tempfile::tempdir().expect("tempdir");
    let cnf_path = if fixture.exists() {
        fixture
    } else {
        let local = tmp.path().join("default_kernel.cnf");
        std::fs::write(&local, "p cnf 3 2\n1 -3 0\n2 3 0\n").expect("write fallback cnf");
        local
    };

    let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
        .arg("--input")
        .arg(&cnf_path)
        .arg("--jit")
        .output()
        .expect("bcp_matrix should run under --jit");
    assert!(
        output.status.success(),
        "expected exit 0 from --jit run; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let report: Value = serde_json::from_slice(&output.stdout).expect("stdout JSON");
    assert!(
        report["jit"].as_bool().expect("jit field present"),
        "--jit flag should set jit=true"
    );
    assert_eq!(
        report["jit_kernel"]
            .as_str()
            .expect("jit_kernel field present"),
        "watched-literal",
        "bcp_matrix --jit must default to the watched-literal kernel"
    );
    let label = report["result_label"]
        .as_str()
        .expect("result_label field present");
    assert!(
        matches!(label, "ok" | "conflict" | "decode_error"),
        "result_label must be one of ok|conflict|decode_error, got {label}"
    );
}

#[cfg(any(target_arch = "aarch64", target_arch = "x86_64"))]
#[test]
fn bcp_matrix_jit_kernel_flag_selects_older_kernels() {
    // The older kernels stay reachable via `--jit-kernel`. Sanity
    // check that the JSON `jit_kernel` field round-trips each
    // explicitly named choice.
    let tmp = tempfile::tempdir().expect("tempdir");
    let cnf_path = tmp.path().join("kernel_choice.cnf");
    std::fs::write(&cnf_path, "p cnf 3 2\n1 -3 0\n2 3 0\n").expect("write cnf");

    for kernel in ["scan", "with-decisions", "watched-literal"] {
        let output = Command::new(env!("CARGO_BIN_EXE_bcp_matrix"))
            .arg("--input")
            .arg(&cnf_path)
            .arg("--jit")
            .arg("--jit-kernel")
            .arg(kernel)
            .output()
            .expect("bcp_matrix should run under --jit-kernel");
        assert!(
            output.status.success(),
            "expected exit 0 from --jit-kernel {kernel}; stderr={}",
            String::from_utf8_lossy(&output.stderr)
        );
        let report: Value = serde_json::from_slice(&output.stdout).expect("stdout JSON");
        assert_eq!(
            report["jit_kernel"]
                .as_str()
                .expect("jit_kernel field present"),
            kernel,
            "JSON jit_kernel must echo the requested choice"
        );
    }
}
