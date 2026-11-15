//! Captured aggregate references retain stable storage and observe writes.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-borrowed-aggregate-captures.XXXXXX"])
        .output()
        .expect("mktemp borrowed_aggregate_captures artifacts");
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
                    .arg(dir.join("libborrowed_aggregate_captures.a"))
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
                    .arg("-lstatic=borrowed_aggregate_captures")
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
fn no_proof_borrowed_aggregate_captures_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("borrowed_aggregate_captures/corpus.rs"),
        include_str!("borrowed_aggregate_captures/driver.rs"),
        "PASS borrowed_aggregate_captures checks=40960\n",
    );
    println!(
        "TCG_BORROWED_AGGREGATE_CAPTURES_DIAGNOSTIC executions=8 checks=327680 backend_sha256={digest}"
    );
}
