//! Returning a scalar cell reads its current value through the ordinary load path.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-scalar-cell-returns.XXXXXX"])
        .output()
        .expect("mktemp scalar_cell_returns artifacts");
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
                "-Cdebug-assertions=yes",
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
                    .arg(dir.join("libscalar_cell_returns.a"))
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
                    .arg("-lstatic=scalar_cell_returns")
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
fn no_proof_scalar_cell_returns_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("scalar_cell_returns/corpus.rs"),
        include_str!("scalar_cell_returns/driver.rs"),
        "PASS scalar_cell_returns checks=73728\n",
    );
    println!(
        "TCG_SCALAR_CELL_RETURNS_DIAGNOSTIC executions=8 checks=589824 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_borrowed_scalar_cell_returns_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for (name, source, driver, expected) in [
        (
            "tagged_owner",
            include_str!("scalar_cell_returns/original.rs"),
            include_str!("scalar_cell_returns/original_driver.rs"),
            "PASS tagged_owner_return checks=8192\n",
        ),
        (
            "mutable_alias",
            include_str!("scalar_cell_returns/alias.rs"),
            include_str!("scalar_cell_returns/alias_driver.rs"),
            "PASS scalar_cell_return_alias checks=16384\n",
        ),
        (
            "interior_mutable",
            include_str!("scalar_cell_returns/interior.rs"),
            include_str!("scalar_cell_returns/interior_driver.rs"),
            "PASS scalar_cell_return_interior_values checks=14336\n",
        ),
    ] {
        native_case(
            &artifacts.0.join(name),
            &backend,
            &digest,
            source,
            driver,
            expected,
        );
    }
    println!(
        "TCG_BORROWED_SCALAR_CELL_RETURNS_DIAGNOSTIC executions=24 checks=311296 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_interior_pointer_returns_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    // The historical snapshot refusal is superseded on this target by stable
    // storage for call-reference arguments. Check the admitted pointer values
    // and their actual aliasing behavior against independently compiled LLVM.
    native_case(
        &artifacts.0.join("interior_pointer"),
        &backend,
        &digest,
        include_str!("scalar_cell_returns/interior_pointer.rs"),
        include_str!("scalar_cell_returns/interior_pointer_driver.rs"),
        "PASS scalar_cell_return_interior_pointer checks=16384\n",
    );
    println!(
        "TCG_INTERIOR_POINTER_RETURNS_DIAGNOSTIC executions=8 checks=131072 backend_sha256={digest}"
    );
}
