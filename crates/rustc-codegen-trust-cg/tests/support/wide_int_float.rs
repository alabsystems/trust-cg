//! Full-width casts use the runtime ABI and round once to the destination.
//! The C oracle computes IEEE bits using integer arithmetic only.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_wide_int_float_matches_integer_oracle() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-wide-int-float.XXXXXX"])
        .output()
        .expect("mktemp wide_int_float artifacts");
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("wide_int_float/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.c"),
        include_str!("wide_int_float/driver.c"),
    )
    .unwrap();
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
            let symbols = checked(
                Command::new("nm").arg("-u").args(&objects),
                30,
                &dir.join("undefined.log"),
            );
            if lane == "cg" {
                let symbols = String::from_utf8_lossy(&symbols.stdout);
                for helper in [
                    "__floattisf",
                    "__floattidf",
                    "__floatuntisf",
                    "__floatuntidf",
                ] {
                    assert!(
                        symbols
                            .lines()
                            .any(|line| line.split_whitespace().last() == Some(helper)),
                        "missing conversion runtime call {helper} in {stem}"
                    );
                }
            }
            let executable = dir.join("native.elf");
            // Under -Cpanic=abort the bridge raises the real `core` panic entry
            // for a failed overflow `Assert` (here the never-taken `>> 64`
            // check at O0) rather than an inline trap; the C driver links no
            // `libcore`, so those helpers get aborting stubs.
            checked(
                Command::new("cc")
                    .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                    .arg(root.join("driver.c"))
                    .args(&objects)
                    .arg(super::toolchain_support::write_abort_stubs(&dir, &objects))
                    .arg("-o")
                    .arg(&executable),
                60,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 30, &dir.join("native.log"));
            assert_eq!(
                output.stdout,
                b"PASS wide_int_float values=152912 checks=2293681\n"
            );
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
    println!("TCG_WIDE_INT_FLOAT_DIAGNOSTIC executions=8 checks=18349448 backend_sha256={digest}");
}
