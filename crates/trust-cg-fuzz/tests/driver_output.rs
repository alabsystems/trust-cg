//! Operator I/O and duration failures must not be reported as fuzz-driver crashes.

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

const DRIVERS: &[(&str, &str)] = &[
    (env!("CARGO_BIN_EXE_csmith-driver"), "csmith-driver"),
    (env!("CARGO_BIN_EXE_yarpgen-driver"), "yarpgen-driver"),
    (env!("CARGO_BIN_EXE_trust-ir-gen"), "trust-ir-gen"),
    (env!("CARGO_BIN_EXE_trust-ir-jit-diff"), "trust-ir-jit-diff"),
];

fn run(binary: &str, out: &Path, duration: &str) -> Output {
    Command::new(binary)
        .args(["--duration", duration, "--out"])
        .arg(out)
        // External tools are intentionally unavailable. The zero-duration
        // tests exercise report publication without starting a compiler run.
        .env("PATH", "")
        .env_remove("TRUST_CG_AUTOFILE")
        .output()
        .expect("start fuzz driver")
}

fn assert_diagnostic(output: &Output, label: &str, expected: &str) {
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert_eq!(output.status.code(), Some(1), "{label}: {stderr}");
    assert!(stderr.contains(expected), "{label}: {stderr}");
    assert!(!stderr.contains("panicked"), "{label}: {stderr}");
}

#[test]
fn output_directory_failure_is_a_diagnostic_and_preserves_the_file() {
    let temp = tempfile::tempdir().unwrap();
    let out = temp.path().join("not-a-directory");
    fs::write(&out, b"preserve this input").unwrap();
    for (binary, name) in DRIVERS {
        assert_diagnostic(
            &run(binary, &out, "0"),
            name,
            "cannot create output directory",
        );
        assert_eq!(fs::read(&out).unwrap(), b"preserve this input");
    }
}

#[test]
fn runlog_write_failure_is_not_a_success_or_panic() {
    let temp = tempfile::tempdir().unwrap();
    for (binary, name) in DRIVERS {
        let out = temp.path().join(name);
        let blocked = out.join(format!("{name}.json"));
        fs::create_dir_all(&blocked).unwrap();
        let sentinel = blocked.join("keep");
        fs::write(&sentinel, b"preserve existing directory").unwrap();
        assert_diagnostic(&run(binary, &out, "0"), name, "cannot write fuzz run log");
        assert_eq!(fs::read(sentinel).unwrap(), b"preserve existing directory");
    }
}

#[test]
fn zero_duration_keeps_the_runlog_schema_and_honest_availability() {
    let temp = tempfile::tempdir().unwrap();
    for (binary, name) in DRIVERS {
        let out = temp.path().join(name);
        let output = run(binary, &out, "0");
        assert!(output.status.success(), "{name}: {output:?}");
        let log: trust_cg_fuzz::runlog::RunLog =
            serde_json::from_slice(&fs::read(out.join(format!("{name}.json"))).unwrap()).unwrap();
        assert_eq!(log.driver, *name);
        assert_eq!(log.runs, 0);
        assert_eq!(log.crashes, 0);
        assert_eq!(log.miscompiles, 0);
        if matches!(*name, "csmith-driver" | "yarpgen-driver") {
            assert_eq!(log.status, "unavailable");
            assert!(log.reason.is_some());
        } else {
            #[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
            assert_eq!(log.status, "ok");
        }
    }
}

#[test]
fn overflowing_duration_is_rejected_before_output_creation() {
    let temp = tempfile::tempdir().unwrap();
    for (binary, name) in DRIVERS {
        let out = temp.path().join(name);
        assert_diagnostic(
            &run(binary, &out, &u64::MAX.to_string()),
            name,
            "--duration exceeds",
        );
        assert!(
            !out.exists(),
            "{name} published output before validating duration"
        );
    }
}

#[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
fn jit_diff_log(out: &Path, extra: &[&str]) -> trust_cg_fuzz::runlog::RunLog {
    let output = Command::new(env!("CARGO_BIN_EXE_trust-ir-jit-diff"))
        .args(["--duration", "600", "--seed-start", "1", "--out"])
        .arg(out)
        .args(extra)
        .output()
        .expect("start trust-ir-jit-diff");
    assert!(output.status.success(), "{output:?}");
    serde_json::from_slice(&fs::read(out.join("trust-ir-jit-diff.json")).unwrap()).unwrap()
}

/// `--runs` walks exactly the fixed seed range and records what it executed,
/// so a lane can require the whole range with every JIT level run.
#[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
#[test]
fn jit_diff_covers_a_fixed_seed_range_and_counts_executed_rows() {
    let temp = tempfile::tempdir().unwrap();
    let log = jit_diff_log(&temp.path().join("range"), &["--runs", "3"]);
    assert_eq!(log.runs, 3);
    assert_eq!(log.seed_start, Some(1));
    assert_eq!(log.requested_runs, Some(3));
    assert_eq!(log.planted_miscompile_seed, None);
    assert_eq!((log.miscompiles, log.crashes, log.timeouts), (0, 0, 0));
    let checked = log.rows_checked.unwrap();
    assert_eq!(log.scalar_rows_per_seed, Some(6));
    // Every seed checks its six scalar rows and the same six rows on its
    // control-shape module; none of seeds 1-3 is a multiple of eight, so no
    // consumer-shape rows are added.
    assert_eq!(checked, 3 * (6 + 6), "{log:?}");
    assert_eq!(log.seeds_incomplete, Some(0), "{log:?}");
    assert_eq!(log.rows_executed, Some(checked), "{log:?}");
    assert_eq!(log.rows_refused, Some(0), "{log:?}");
    let compared = log.rows_oracle_compared.unwrap();
    let cross_only = log.rows_cross_level_only.unwrap();
    assert_eq!(compared + cross_only, checked, "{log:?}");
    assert!(compared > 0, "{log:?}");
    assert_eq!(
        cross_only == 0,
        log.oracle_error_samples.is_empty(),
        "{log:?}"
    );
    assert!(log.repros.is_empty());
}

/// The planted negative control reports exactly its seed as a tagged
/// miscompile; the other seeds of the range stay clean.
#[cfg(all(unix, any(target_arch = "aarch64", target_arch = "x86_64")))]
#[test]
fn jit_diff_planted_miscompile_is_reported_for_its_seed_only() {
    let temp = tempfile::tempdir().unwrap();
    let log = jit_diff_log(
        &temp.path().join("planted"),
        &["--runs", "3", "--plant-miscompile-seed", "2"],
    );
    assert_eq!(log.runs, 3);
    assert_eq!(log.planted_miscompile_seed, Some(2));
    assert_eq!(log.miscompiles, 1, "{log:?}");
    assert_eq!(log.repros.len(), 1, "{log:?}");
    assert_eq!(log.repros[0].seed, 2);
    // The planted seed stops at its first (planted) defect.
    assert_eq!(log.seeds_incomplete, Some(1), "{log:?}");
    assert_eq!(log.incomplete_seed_samples, vec![2], "{log:?}");
    assert!(
        log.repros[0]
            .summary
            .starts_with("miscompile seed=2 planted-negative-control "),
        "{log:?}"
    );
}
