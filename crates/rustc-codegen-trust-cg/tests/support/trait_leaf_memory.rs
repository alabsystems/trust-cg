//! Trait-object aggregate leaves: return-slot and projected-pair sources.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-trait-leaf-memory.XXXXXX"])
        .output()
        .expect("mktemp trait-object leaf artifacts");
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
fn no_proof_trait_leaf_memory_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("positive"),
        &backend,
        &digest,
        include_str!("trait_leaf_memory/corpus.rs"),
        include_str!("trait_leaf_memory/driver.rs"),
        "PASS trait_leaf_memory checks=696\n",
    );
    println!("TCG_TRAIT_LEAF_MEMORY_DIAGNOSTIC executions=8 checks=5568 backend_sha256={digest}");
}

/// The closure-call cleanup this source carries was a `[TCG-EH-CALL-EDGE]`
/// refusal until d0d0e4caf lowered closure calls with an unwind cleanup edge.
/// It is now a required native positive: the driver panics through the bridge
/// frames and checks every cleanup effect, against the LLVM twin at O0-O3.
#[test]
fn no_proof_trait_leaf_memory_cleanup_unwind_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("cleanup"),
        &backend,
        &digest,
        include_str!("trait_leaf_memory/unwind.rs"),
        include_str!("trait_leaf_memory/unwind_driver.rs"),
        "PASS trait_leaf_unwind checks=12\n",
    );
    println!("TCG_TRAIT_LEAF_CLEANUP_UNWIND executions=8 checks=96 backend_sha256={digest}");
}
