//! Assertion operands retain reference identity, bytes, mutation, and cleanup.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_assert_pointer_matches_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-assert-pointer.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("assert_pointer/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.rs"),
        include_str!("assert_pointer/driver.rs"),
    )
    .unwrap();
    let mut checks = 0;
    for panic in ["unwind", "abort"] {
        for opt in 0..=3 {
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("{panic}-{lane}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                // The std crate-name fixture preserves real assert_failed calls
                // under the existing sysroot interception boundary.
                command.args([
                    "--crate-name=std",
                    "--crate-type=lib",
                    "--emit=obj,mir",
                    "-Ccodegen-units=1",
                    "-Cforce-unwind-tables=yes",
                    "-Cmetadata=assert_pointer_fixture",
                    "--target",
                    TARGET,
                ]);
                command
                    .arg(format!("-Cpanic={panic}"))
                    .arg(format!("-Copt-level={opt}"));
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
                    .map(|e| e.unwrap().path())
                    .filter(|p| p.extension().is_some_and(|e| e == "o"))
                    .collect();
                objects.sort();
                assert!(!objects.is_empty());
                checked(
                    Command::new("ar")
                        .arg("crs")
                        .arg(dir.join("libassert_pointer.a"))
                        .args(&objects),
                    60,
                    &dir.join("archive.log"),
                );
                checked(
                    rustc_command()
                        .args(["--target", TARGET, "-Copt-level=2"])
                        .arg(format!("-Cpanic={panic}"))
                        .arg(root.join("driver.rs"))
                        .arg(format!("-Lnative={}", dir.display()))
                        .arg("-lstatic=assert_pointer")
                        .arg("-o")
                        .arg(dir.join("native.elf")),
                    180,
                    &dir.join("link.log"),
                );
                let output = checked(
                    &mut Command::new(dir.join("native.elf")),
                    60,
                    &dir.join("native.log"),
                );
                let count = if panic == "unwind" { 11008 } else { 10624 };
                assert_eq!(
                    output.stdout,
                    format!("PASS assert_pointer checks={count}\n").as_bytes()
                );
                assert!(output.stderr.is_empty());
                checks += count;
                if panic == "abort" {
                    let (output, transcript) = run_bounded(
                        Command::new("sh")
                            .args(["-c", "ulimit -c 0; exec \"$@\"", "assert-pointer"])
                            .arg(dir.join("native.elf"))
                            .arg("abort"),
                        60,
                        &dir.join("abort.log"),
                    );
                    assert_eq!(output.status.signal(), Some(6), "{transcript}");
                    assert!(output.stdout.is_empty(), "{transcript}");
                    assert!(String::from_utf8_lossy(&output.stderr).contains(
                        "assertion `left == right` failed\n  left: [1, 2, 3, 4]\n right: [1, 2, 4, 3]"),"{transcript}");
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    assert_eq!(checks, 173056);
    println!("TCG_ASSERT_POINTER executions=16 checks={checks} aborts=8 backend_sha256={digest}");
}
