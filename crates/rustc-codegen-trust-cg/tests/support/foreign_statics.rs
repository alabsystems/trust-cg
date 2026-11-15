//! Foreign data and weak imports preserve linker binding and pointer identity.
//! Diagnostic native execution does not qualify mandatory machine proof.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_foreign_statics_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-foreign-statics.XXXXXX"])
        .output()
        .expect("mktemp foreign static artifacts");
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("foreign_statics/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.c"),
        include_str!("foreign_statics/driver.c"),
    )
    .unwrap();
    for opt in 0..=3 {
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("{lane}-O{opt}"));
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--crate-name=foreign_static_probe",
                "--emit=obj",
                "-Ccodegen-units=1",
                "-Cpanic=abort",
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
                .map(|e| e.unwrap().path())
                .filter(|p| p.extension().is_some_and(|e| e == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty());
            checked(
                Command::new("ar")
                    .arg("crs")
                    .arg(dir.join("libprobe.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            if lane == "cg" {
                let symbols = checked(
                    Command::new("readelf")
                        .args(["--symbols", "--wide"])
                        .args(&objects),
                    60,
                    &dir.join("symbols.log"),
                );
                let symbols = String::from_utf8(symbols.stdout).unwrap();
                for name in ["optional_function", "optional_data", "optional_mutable"] {
                    let rows: Vec<_> = symbols
                        .lines()
                        .map(|line| line.split_whitespace().collect::<Vec<_>>())
                        .filter(|r| r.len() == 8 && r[7] == name)
                        .collect();
                    assert!(!rows.is_empty(), "missing weak import {name}");
                    assert!(
                        rows.iter().all(|r| r[4] == "WEAK" && r[6] == "UND"),
                        "wrong binding for {name}: {rows:?}"
                    );
                }
            }
            for present in [0, 1] {
                for pie in ["pie", "no-pie"] {
                    let stem = format!("{present}-{pie}");
                    let exe = dir.join(format!("native-{stem}.elf"));
                    checked(
                        Command::new("cc")
                            .arg("-O2")
                            .arg(format!("-DPRESENT={present}"))
                            .arg(format!("-{pie}"))
                            .arg(root.join("driver.c"))
                            .arg(dir.join("libprobe.a"))
                            .arg("-o")
                            .arg(&exe),
                        60,
                        &dir.join(format!("link-{stem}.log")),
                    );
                    let result = checked(
                        &mut Command::new(&exe),
                        20,
                        &dir.join(format!("native-{stem}.log")),
                    );
                    assert_eq!(result.stdout, b"PASS foreign_statics checks=16387\n");
                    assert!(result.stderr.is_empty());
                }
            }
            assert_eq!(
                sha256(&backend),
                digest,
                "backend changed during {lane}-O{opt}"
            );
        }
    }
    println!("TCG_FOREIGN_STATICS executions=32 checks=524384 backend_sha256={digest}");
}
