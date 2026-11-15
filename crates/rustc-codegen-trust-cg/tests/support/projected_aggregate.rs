//! Projected aggregate call arguments preserve their complete rustc layout.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-projected-aggregate.XXXXXX"])
        .output()
        .expect("mktemp projected_aggregate artifacts");
    assert!(temp.status.success());
    Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ))
}

fn native_case(
    root: &Path,
    backend: &Path,
    digest: &str,
    rust: &str,
    driver: &str,
    expected: &str,
) {
    std::fs::create_dir(root).unwrap();
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("driver.rs"), driver).unwrap();
    let shared = root.join("libprojected_aggregate_types.rlib");
    std::fs::write(
        root.join("types.rs"),
        include_str!("projected_aggregate/types.rs"),
    )
    .unwrap();
    checked(
        rustc_command()
            .args([
                "--crate-type=rlib",
                "--crate-name=projected_aggregate_types",
                "-Cpanic=abort",
                "--target",
                TARGET,
            ])
            .arg(root.join("types.rs"))
            .arg("-o")
            .arg(&shared),
        180,
        &root.join("types-compile.log"),
    );
    for opt in 0..=3 {
        for lane in ["llvm", "cg"] {
            let stem = format!("{lane}-O{opt}");
            let dir = root.join(&stem);
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            command.arg(format!(
                "--extern=projected_aggregate_types={}",
                shared.display()
            ));
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            command
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            checked(&mut command, 180, &dir.join("compile.log"));
            let mut objects: Vec<_> = std::fs::read_dir(&dir)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty(), "no objects from {stem}");
            checked(
                Command::new("ar")
                    .arg("crs")
                    .arg(dir.join("libprojected_aggregate.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET, "-Cpanic=abort"])
                    .arg(root.join("driver.rs"))
                    .arg(format!(
                        "--extern=projected_aggregate_types={}",
                        shared.display()
                    ))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=projected_aggregate")
                    .arg("-o")
                    .arg(&executable),
                180,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            assert_eq!(output.stdout, expected.as_bytes());
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
}

#[test]
fn no_proof_projected_aggregate_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("projected_aggregate/corpus.rs"),
        include_str!("projected_aggregate/driver.rs"),
        "PASS projected_aggregate checks=99588\n",
    );
    println!(
        "TCG_PROJECTED_AGGREGATE_DIAGNOSTIC executions=8 checks=796704 backend_sha256={digest}"
    );
}

/// A `&mut` borrow of a by-value repr(Rust) aggregate with interleaved
/// zero-sized fields, passed to a callback and then moved whole. This shape
/// was the `[TCG-ZST-LANE-INDEX]` known refusal; it is now a required native
/// positive, checked against a local-copy oracle and the LLVM twin.
#[test]
fn no_proof_projected_aggregate_zst_borrow_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("zst-borrow"),
        &backend,
        &digest,
        include_str!("projected_aggregate/zst_borrow.rs"),
        include_str!("projected_aggregate/zst_borrow_driver.rs"),
        "PASS zst_borrow checks=12288\n",
    );
    println!(
        "TCG_PROJECTED_AGGREGATE_ZST_BORROW executions=8 checks=98304 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_projected_aggregate_known_refusals_remain_named() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    // `zst_borrow` ([TCG-ZST-LANE-INDEX]) left this list once the bridge
    // lowered it; it is the native positive
    // `no_proof_projected_aggregate_zst_borrow_matches_llvm` below.
    for (name, source, reason) in [
        (
            "indirect_return",
            include_str!("projected_aggregate/negative_indirect_return.rs"),
            "TCG-SRET-ABI",
        ),
        (
            "float_return",
            include_str!("projected_aggregate/negative_float_return.rs"),
            "TCG-RET-ABI",
        ),
    ] {
        let source_path = artifacts.0.join(format!("{name}.rs"));
        std::fs::write(&source_path, source).unwrap();
        for lane in ["llvm", "cg"] {
            let dir = artifacts.0.join(format!("{name}-{lane}"));
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command
                .args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Cpanic=abort",
                    "-Copt-level=0",
                    "-Ccodegen-units=1",
                    "--target",
                    TARGET,
                ])
                .arg(&source_path)
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let (result, log) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(result.status.code(), Some(1), "{name}: {log}");
                assert!(log.contains(reason), "{name}: {log}");
            } else {
                checked(&mut command, 180, &dir.join("compile.log"));
            }
        }
        assert_eq!(sha256(&backend), digest);
    }
    println!("TCG_PROJECTED_AGGREGATE_NEGATIVE cases=2 backend_sha256={digest}");
}

#[test]
fn no_proof_projected_aggregate_union_tuple_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("union-tuple"),
        &backend,
        &digest,
        include_str!("projected_aggregate/union_tuple.rs"),
        include_str!("projected_aggregate/union_tuple_driver.rs"),
        "PASS projected_union_tuple checks=65536\n",
    );
    println!(
        "TCG_PROJECTED_UNION_TUPLE_DIAGNOSTIC executions=8 checks=524288 backend_sha256={digest}"
    );
}
