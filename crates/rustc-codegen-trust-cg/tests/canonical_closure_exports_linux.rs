//! A canonical CG closure symbol must be called by LLVM, and a bad argument
//! binding in that body must fail the native oracle.
#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::Path;
use std::process::Command;

#[test]
fn llvm_caller_imports_cg_closure_and_detects_argument_mutation() {
    let scratch = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-canonical-export.XXXXXX"])
        .output()
        .expect("create symbol observer capture directory");
    assert!(scratch.status.success());
    let scratch = String::from_utf8(scratch.stdout).expect("UTF-8 temporary path");
    let capture = Path::new(scratch.trim()).join("capture");
    let reporter = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../reports/2026-10-17-canonical-library-exports/observe_export.py");
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
        .arg(backend)
        .arg("--output")
        .arg(&capture)
        .output()
        .expect("run bounded native symbol and argument-placement control");
    println!("{}", String::from_utf8_lossy(&result.stdout));
    assert_eq!(
        result.status.code(),
        Some(0),
        "the LLVM caller must reach CG code and detect the mutation: {}",
        String::from_utf8_lossy(&result.stderr)
    );
    let receipt: serde_json::Value = serde_json::from_slice(
        &std::fs::read(capture.join("result.json")).expect("complete symbol observer receipt"),
    )
    .expect("parse symbol observer receipt");
    assert_eq!(receipt["pass_result"], true);
    assert_eq!(receipt["symbol_edge"]["undefined_in_llvm_caller"], true);
    assert_eq!(receipt["mutation"]["changed_bytes"], 1);
    assert_eq!(
        receipt["backend_sha256_before"],
        receipt["backend_sha256_after"]
    );
}
