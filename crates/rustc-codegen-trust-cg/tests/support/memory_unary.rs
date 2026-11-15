//! Unary field writes retain aggregate storage, offsets and callback mutations.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-memory-unary.XXXXXX"])
        .output()
        .expect("mktemp memory_unary artifacts");
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
    checked_negation: bool,
) {
    std::fs::create_dir(root).unwrap();
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("types.rs"), include_str!("memory_unary/types.rs")).unwrap();
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
                "-Cpanic=abort",
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            command.arg(if checked_negation {
                "-Coverflow-checks=on"
            } else {
                "-Coverflow-checks=off"
            });
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
                    .arg(dir.join("libmemory_unary.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET, "-Cpanic=abort"])
                    .arg(root.join("driver.rs"))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=memory_unary")
                    .arg("-o")
                    .arg(&executable),
                180,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            assert_eq!(output.stdout, expected.as_bytes());
            assert!(output.stderr.is_empty());
            if checked_negation {
                for width in [8, 16, 32, 64, 128] {
                    for field in ["hi", "lo"] {
                        let mode = format!("i{width}-{field}");
                        let (output, transcript) = run_bounded(
                            Command::new(&executable).arg(&mode),
                            10,
                            &dir.join(format!("{mode}.log")),
                        );
                        assert_eq!(output.status.signal(), Some(6), "{transcript}");
                        if lane == "llvm" {
                            assert!(
                                String::from_utf8_lossy(&output.stderr)
                                    .contains("attempt to negate with overflow"),
                                "{transcript}"
                            );
                        }
                    }
                }
            }
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
}

#[test]
fn no_proof_memory_unary_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("memory_unary/corpus.rs"),
        include_str!("memory_unary/driver.rs"),
        "PASS memory_unary checks=18102272\n",
        false,
    );
    println!("TCG_MEMORY_UNARY_DIAGNOSTIC executions=8 checks=144818176 backend_sha256={digest}");
}

#[test]
fn no_proof_memory_unary_retains_checked_negation() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("checked"),
        &backend,
        &digest,
        include_str!("memory_unary/checked.rs"),
        include_str!("memory_unary/checked_driver.rs"),
        "PASS memory_unary_checked checks=100\n",
        true,
    );
    println!(
        "TCG_MEMORY_UNARY_CHECKED executions=8 checks=800 overflow_aborts=80 backend_sha256={digest}"
    );
}
