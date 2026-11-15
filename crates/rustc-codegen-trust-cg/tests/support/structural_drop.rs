//! Structural drops use actual layout and preserve destructor order and addresses.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-structural-drop.XXXXXX"])
        .output()
        .expect("mktemp structural_drop artifacts");
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
    panic_mode: &str,
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
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            command.arg(format!("-Cpanic={panic_mode}"));
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
                    .arg(dir.join("libstructural_drop.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET])
                    .arg(format!("-Cpanic={panic_mode}"))
                    .arg(root.join("driver.rs"))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=structural_drop")
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
fn no_proof_structural_drop_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("structural_drop/corpus.rs"),
        include_str!("structural_drop/driver.rs"),
        "PASS structural_drop checks=16384\n",
        "abort",
    );
    println!("TCG_STRUCTURAL_DROP_DIAGNOSTIC executions=8 checks=131072 backend_sha256={digest}");
}

#[test]
fn no_proof_structural_drop_unwind_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("unwind"),
        &backend,
        &digest,
        include_str!("structural_drop/unwind.rs"),
        include_str!("structural_drop/unwind_driver.rs"),
        "PASS structural_drop_unwind checks=768\n",
        "unwind",
    );
    println!("TCG_STRUCTURAL_DROP_UNWIND executions=8 checks=6144 backend_sha256={digest}");
}
#[test]
fn no_proof_structural_drop_known_refusals_remain_named() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for (name, source, reason) in [
        (
            "zst_tuple",
            include_str!("structural_drop/negative_zst_tuple.rs"),
            "TCG-ZST-LANE-INDEX",
        ),
        (
            "collection",
            include_str!("structural_drop/negative_collection.rs"),
            "TCG-COLLECTION-IMAGE",
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
    println!("TCG_STRUCTURAL_DROP_NEGATIVE cases=2 backend_sha256={digest}");
}
