//! f16 pointer images preserve addresses, element stride and caller-owned bits.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-f16-pointee.XXXXXX"])
        .output()
        .expect("mktemp f16 pointer artifacts");
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
    value_refusal: bool,
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
            command
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" && value_refusal {
                let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(output.status.code(), Some(1), "{transcript}");
                let diagnostics: Vec<serde_json::Value> = String::from_utf8(output.stderr)
                    .unwrap()
                    .lines()
                    .filter_map(|line| serde_json::from_str(line).ok())
                    .filter(|row: &serde_json::Value| row["code"] == "TCG-MIR-UNSUPPORTED")
                    .collect();
                assert_eq!(diagnostics.len(), 1, "{transcript}");
                let fields = &diagnostics[0]["fields"];
                assert_eq!(fields["failed_root_count"], "2", "{transcript}");
                let failures: Vec<_> = fields["failed_roots"]
                    .as_str()
                    .unwrap()
                    .split("\n  - ")
                    .collect();
                assert_eq!(failures.len(), 2, "{transcript}");
                assert!(
                    failures.iter().all(|v| v.contains("Ty::Float(f16)")),
                    "{transcript}"
                );
                let mut names: Vec<_> = failures
                    .iter()
                    .map(|v| v.split(": ").next().unwrap())
                    .collect();
                names.sort();
                assert_eq!(names, ["f16_value_add", "f16_value_load"], "{transcript}");
                assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
                continue;
            }
            checked(&mut command, 180, &dir.join("compile.log"));
            if value_refusal {
                assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
                continue;
            }
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
                    .arg(dir.join("libpointee.a"))
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
                    .arg("-lstatic=pointee")
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
fn no_proof_f16_pointee_images_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("positive"),
        &backend,
        &digest,
        include_str!("f16_pointee_images/corpus.rs"),
        include_str!("f16_pointee_images/driver.rs"),
        "PASS f16_pointee_shell checks=11776\n",
        false,
    );
    println!("TCG_F16_POINTEE_DIAGNOSTIC executions=8 checks=94208 backend_sha256={digest}");
}

#[test]
fn f16_values_retain_refusal() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("refusal"),
        &backend,
        &digest,
        include_str!("f16_pointee_images/value_refusal.rs"),
        "",
        "",
        true,
    );
    println!("TCG_F16_VALUE_REFUSAL llvm_accepted=4 cg_refused=4 backend_sha256={digest}");
}
