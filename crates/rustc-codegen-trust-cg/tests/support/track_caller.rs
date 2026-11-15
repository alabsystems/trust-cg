//! Caller-location ABI and inlining boundaries, including both LLVM link directions.
//! Diagnostic codegen: the mandatory machine-proof gate is a separate test.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_track_caller_matches_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-track-caller.XXXXXX"])
        .output()
        .expect("mktemp caller-location artifacts");
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    for (name, source) in [
        ("corpus.rs", include_str!("track_caller/corpus.rs")),
        ("driver.rs", include_str!("track_caller/driver.rs")),
        ("companion.rs", include_str!("track_caller/companion.rs")),
    ] {
        std::fs::write(root.join(name), source).unwrap();
    }
    let dependency = root.join("libcompanion.rlib");
    checked(
        rustc_command()
            .args([
                "--crate-type=rlib",
                "--crate-name=companion",
                "-Cpanic=unwind",
                "--target",
                TARGET,
            ])
            .arg(root.join("companion.rs"))
            .arg("-o")
            .arg(&dependency),
        180,
        &root.join("companion.log"),
    );
    for opt in 0..=3 {
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("{lane}-O{opt}"));
            std::fs::create_dir(&dir).unwrap();
            let library = dir.join("libtracked.rlib");
            let mut command = rustc_command();
            command
                .args([
                    "--crate-type=rlib",
                    "--crate-name=tracked",
                    "-Cpanic=unwind",
                    "-Ccodegen-units=1",
                    "--target",
                    TARGET,
                ])
                .arg(format!("-Copt-level={opt}"))
                .arg("--extern")
                .arg(format!("companion={}", dependency.display()))
                .arg(root.join("corpus.rs"))
                .arg("-o")
                .arg(&library);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            checked(&mut command, 180, &dir.join("compile.log"));
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["-Cpanic=unwind", "--target", TARGET])
                    .env("CORPUS_DIR", root)
                    .arg(root.join("driver.rs"))
                    .arg("--extern")
                    .arg(format!("tracked={}", library.display()))
                    .arg("-L")
                    .arg(format!("dependency={}", root.display()))
                    .arg("-o")
                    .arg(&executable),
                180,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            assert_eq!(output.stdout, b"PASS track_caller checks=1288\n");
            assert!(output.stderr.is_empty());
            assert_eq!(
                sha256(&backend),
                digest,
                "backend changed during {lane}-O{opt}"
            );
        }
    }
    println!("TCG_TRACK_CALLER_DIAGNOSTIC executions=8 checks=10304 backend_sha256={digest}");
}
