//! Pointer values must be loaded after an alias can replace their storage.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_live_pointer_reads_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-live-pointer.XXXXXX"])
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
        include_str!("live_pointer/corpus.rs"),
    )
    .unwrap();
    std::fs::write(root.join("driver.c"), include_str!("live_pointer/driver.c")).unwrap();
    let mut checks = 0;
    let mut executions = 0;
    for panic in ["abort", "unwind"] {
        for opt in 0..=3 {
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("{panic}-{lane}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--emit=obj,mir",
                    "-Ccodegen-units=1",
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
                    .map(|f| f.unwrap().path())
                    .filter(|f| f.extension().is_some_and(|s| s == "o"))
                    .collect();
                objects.sort();
                assert!(!objects.is_empty());
                checked(
                    Command::new("cc")
                        .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                        .arg(root.join("driver.c"))
                        .args(&objects)
                        .arg("-o")
                        .arg(dir.join("native.elf")),
                    60,
                    &dir.join("link.log"),
                );
                let result = checked(
                    &mut Command::new(dir.join("native.elf")),
                    60,
                    &dir.join("native.log"),
                );
                assert_eq!(result.stdout, b"PASS live_pointer checks=81920\n");
                assert!(result.stderr.is_empty());
                checks += 81920;
                executions += 1;
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    assert_eq!((checks, executions), (1310720, 16));
    println!("TCG_LIVE_POINTER executions={executions} checks={checks} backend_sha256={digest}");
}
