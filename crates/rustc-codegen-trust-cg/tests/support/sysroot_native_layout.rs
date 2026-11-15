//! Standard-library builds preserve upstream iterator layouts and real methods.
//! This diagnostic matrix does not qualify mandatory machine proof or self-hosting.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_sysroot_native_layout_matches_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-sysroot-native-layout.XXXXXX"])
        .output()
        .expect("mktemp sysroot native layout artifacts");
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("sysroot_native_layout/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.rs"),
        include_str!("sysroot_native_layout/driver.rs"),
    )
    .unwrap();
    for name in ["core", "alloc", "std", "hashbrown"] {
        for opt in 0..=3 {
            for lane in ["llvm", "cg"] {
                let stem = format!("{name}-{lane}-O{opt}");
                let dir = root.join(&stem);
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Ccodegen-units=1",
                    "-Cpanic=abort",
                    "-Cmetadata=sysroot_native_layout_fixture",
                    "--target",
                    TARGET,
                ]);
                command.arg(format!("--crate-name={name}"));
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
                        .arg(dir.join("libsysroot_native_layout.a"))
                        .args(&objects),
                    60,
                    &dir.join("archive.log"),
                );
                let executable = dir.join("native.elf");
                checked(
                    rustc_command()
                        .args(["--target", TARGET, "-Cpanic=abort", "-Copt-level=2"])
                        .arg(root.join("driver.rs"))
                        .arg("-L")
                        .arg(&dir)
                        .arg("-lstatic=sysroot_native_layout")
                        .arg("-o")
                        .arg(&executable),
                    180,
                    &dir.join("link.log"),
                );
                let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
                assert_eq!(output.stdout, b"PASS native_iterators checks=99840\n");
                assert!(output.stderr.is_empty());
                assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
            }
        }
    }
    println!("TCG_SYSROOT_NATIVE_LAYOUT executions=32 checks=3194880 backend_sha256={digest}");
}
