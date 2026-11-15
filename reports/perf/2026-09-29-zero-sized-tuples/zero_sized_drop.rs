//! Native ZST Drop regression: real destructor effects, identity and unwind.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-zero-sized-drop.XXXXXX"])
        .output()
        .expect("mktemp zero-sized Drop artifacts");
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
    for opt in 0..=3 {
        for lane in ["llvm", "cg"] {
            let stem = format!("{lane}-O{opt}");
            let dir = root.join(&stem);
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=unwind",
                "-Cforce-unwind-tables=yes",
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            checked(
                command
                    .arg(root.join("corpus.rs"))
                    .arg("--out-dir")
                    .arg(&dir),
                180,
                &dir.join("compile.log"),
            );
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
                    .arg(dir.join("libtryfold.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET, "-Cpanic=unwind"])
                    .arg(root.join("driver.rs"))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=tryfold")
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
fn no_proof_zero_sized_drop_matches_llvm() {
    let artifacts = artifacts();
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    native_case(
        &root.join("original"),
        &backend,
        &digest,
        include_str!("zero_sized_drop/original.rs"),
        include_str!("zero_sized_drop/original_driver.rs"),
        "PASS try_fold_unwind checks=12\n",
    );
    native_case(
        &root.join("expanded"),
        &backend,
        &digest,
        include_str!("zero_sized_drop/corpus.rs"),
        include_str!("zero_sized_drop/driver.rs"),
        "PASS zero_sized_drop checks=147\n",
    );
    println!("TCG_ZERO_SIZED_DROP_DIAGNOSTIC executions=16 checks=1272 backend_sha256={digest}");
}

#[test]
fn zero_sized_drop_requires_supported_alignment() {
    let artifacts = artifacts();
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("zero_sized_drop/overaligned.rs"),
    )
    .unwrap();
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
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            command
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
            if lane == "llvm" {
                assert!(output.status.success(), "{transcript}");
                assert!(std::fs::read_dir(&dir).unwrap().any(|entry| {
                    entry
                        .unwrap()
                        .path()
                        .extension()
                        .is_some_and(|ext| ext == "o")
                }));
            } else {
                assert_eq!(output.status.code(), Some(1), "{transcript}");
                let stderr = String::from_utf8(output.stderr).unwrap();
                let diagnostics: Vec<serde_json::Value> = stderr
                    .lines()
                    .filter_map(|line| serde_json::from_str(line).ok())
                    .filter(|row: &serde_json::Value| row["code"] == "TCG-MIR-UNSUPPORTED")
                    .collect();
                assert_eq!(diagnostics.len(), 1, "{transcript}");
                let failures = diagnostics[0]["fields"]["failed_roots"].as_str().unwrap();
                assert!(
                    failures.contains("zst_overaligned")
                        && failures.contains("zst_tuple_overaligned")
                        && failures.contains("64-byte")
                        && failures.contains("16-byte stack alignment"),
                    "{transcript}"
                );
            }
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
    println!("TCG_ZERO_SIZED_DROP_REFUSAL llvm_accepted=4 cg_refused=4 backend_sha256={digest}");
}
