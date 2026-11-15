//! Whole transparent wide-pointer reads preserve data and length.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-wide-newtype-read.XXXXXX"])
        .output()
        .expect("mktemp wide-pointer read artifacts");
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
fn no_proof_wide_newtype_reads_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("positive"),
        &backend,
        &digest,
        include_str!("wide_newtype_reads/corpus.rs"),
        include_str!("wide_newtype_reads/driver.rs"),
        "PASS wide_newtype_read checks=6105\n",
    );
    println!("TCG_WIDE_NEWTYPE_READ_DIAGNOSTIC executions=8 checks=48840 backend_sha256={digest}");
}

/// The store through a `NonNull<[u32]>` place was refused ("Place deref store
/// of a transparent wide-slice newtype pointee") when this source was added;
/// the bridge lowered it by d0d0e4caf. It is now a required native positive:
/// the driver checks the stored pointer, length and both neighbouring words
/// against the LLVM twin at O0-O3.
#[test]
fn no_proof_wide_newtype_store_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("cleanup"),
        &backend,
        &digest,
        include_str!("wide_newtype_reads/unwind.rs"),
        include_str!("wide_newtype_reads/unwind_driver.rs"),
        "PASS wide_newtype_store checks=68\n",
    );
    println!("TCG_WIDE_NEWTYPE_STORE executions=8 checks=544 backend_sha256={digest}");
}
