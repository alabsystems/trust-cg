//! Captured allocation cleanup with the audit's independent glibc observer.
//! Every original cell must compile and release the actual allocation once.
#![cfg(all(target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::Path;
use std::process::Command;

#[test]
fn consumed_box_and_direct_drop_both_free_once() {
    let scratch = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-closure-release.XXXXXX"])
        .output()
        .expect("create closure observer capture directory");
    assert!(scratch.status.success());
    let scratch = String::from_utf8(scratch.stdout).expect("UTF-8 temporary path");
    let capture = Path::new(scratch.trim()).join("capture");
    let reporter = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../reports/2026-10-14-bidirectional-completeness-audit/reproduce.py");
    let backend = backend_artifact_support::current_test_backend();
    let compiler = toolchain_support::rustc_driver_command();
    let mut report = Command::new("python3");
    for name in toolchain_support::RUNNER_TEST_ONLY_ENV {
        report.env_remove(name);
    }
    let result = report
        .arg(reporter)
        .arg("--compiler")
        .arg(compiler.get_program())
        .arg("--backend")
        .arg(&backend)
        .arg("--output")
        .arg(&capture)
        .output()
        .expect("run bounded compiler/native observer matrix");
    println!("{}", String::from_utf8_lossy(&result.stdout));
    assert_eq!(
        result.status.code(),
        Some(0),
        "every original observer cell must compile and free once: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    let receipt: serde_json::Value = serde_json::from_slice(
        &std::fs::read(capture.join("result.json")).expect("complete observer receipt"),
    )
    .expect("parse observer receipt");
    assert_eq!(
        receipt["backend_sha256_before"],
        receipt["backend_sha256_after"]
    );
    let cells = receipt["cells"].as_array().expect("observer cells");
    assert_eq!(cells.len(), 16);
    let mut seen = std::collections::BTreeSet::new();
    for cell in cells {
        assert!(cell.get("timeout").is_none(), "{cell}");
        assert_eq!(cell["compile_exit"], 0, "{cell}");
        assert_eq!(cell["native_exit"], 1, "{cell}");
        let case = cell["case"].as_str().expect("case");
        let lane = cell["lane"].as_str().expect("lane");
        let level = cell["optimization"].as_u64().expect("optimization level");
        assert!(["direct_drop", "closure_capture"].contains(&case));
        assert!(["llvm", "cg"].contains(&lane));
        assert!(level < 4);
        assert!(seen.insert((case, lane, level)), "duplicate cell: {cell}");
    }
    assert_eq!(seen.len(), 16);
    println!(
        "CLOSURE_ALLOCATION_CLEANUP native=16 refused=0 opts=0,1,2,3 capture={}",
        capture.display()
    );
}

#[test]
fn destructor_panic_releases_iterator_before_caller_cleanup() {
    let scratch = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-iterator-release.XXXXXX"])
        .output()
        .expect("create iterator observer capture directory");
    assert!(scratch.status.success());
    let scratch = String::from_utf8(scratch.stdout).expect("UTF-8 temporary path");
    let capture = Path::new(scratch.trim()).join("capture");
    let reporter = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../reports/2026-10-17-linux-ownership-cleanup/observe_iterator.py");
    let backend = backend_artifact_support::current_test_backend();
    let compiler = toolchain_support::rustc_driver_command();
    let mut report = Command::new("python3");
    for name in toolchain_support::RUNNER_TEST_ONLY_ENV {
        report.env_remove(name);
    }
    let result = report
        .arg(reporter)
        .arg("--compiler")
        .arg(compiler.get_program())
        .arg("--backend")
        .arg(&backend)
        .arg("--output")
        .arg(&capture)
        .output()
        .expect("run terminal destructor-panic allocation observer");
    println!("{}", String::from_utf8_lossy(&result.stdout));
    assert_eq!(
        result.status.code(),
        Some(0),
        "both terminal families must free their iterator before caller cleanup: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    let receipt: serde_json::Value = serde_json::from_slice(
        &std::fs::read(capture.join("result.json")).expect("complete observer receipt"),
    )
    .expect("parse observer receipt");
    assert_eq!(receipt["pass"], true);
    assert_eq!(receipt["c_compile_exit"], 0);
    assert_eq!(
        receipt["backend_sha256_before"],
        receipt["backend_sha256_after"]
    );
    let cells = receipt["cells"].as_array().expect("observer cells");
    assert_eq!(cells.len(), 16);
    let mut seen = std::collections::BTreeSet::new();
    for cell in cells {
        assert!(cell.get("timeout").is_none(), "{cell}");
        assert_eq!(cell["compile_exit"], 0, "{cell}");
        assert_eq!(cell["caller_exit"], 0, "{cell}");
        assert_eq!(cell["native_exit"], 0, "{cell}");
        let case = cell["case"].as_str().expect("case");
        let lane = cell["lane"].as_str().expect("lane");
        let level = cell["optimization"].as_u64().expect("optimization level");
        assert!(["for_each", "fold"].contains(&case));
        assert!(["llvm", "cg"].contains(&lane));
        assert!(level < 4);
        assert!(seen.insert((case, lane, level)), "duplicate cell: {cell}");
        assert_eq!(
            cell["stdout"],
            format!("case={case} panicked=1 marker=99 heap=1 frees=1 caller=1 before_caller=1\n"),
            "{cell}"
        );
    }
    println!(
        "ITERATOR_DESTRUCTOR_CLEANUP native=16 refused=0 opts=0,1,2,3 capture={}",
        capture.display()
    );
}
