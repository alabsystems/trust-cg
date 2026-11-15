//! Exact initialized CTFE scalar images and relocated aggregate constants.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_union_constants_images_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-union-constants.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let runtime = super::scalar_cell_runtime::Runtime::build(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("union_constants/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.c"),
        include_str!("union_constants/driver.c"),
    )
    .unwrap();
    std::fs::write(
        root.join("refused.rs"),
        include_str!("union_constants/refused.rs"),
    )
    .unwrap();
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
                let mut linker = Command::new("cc");
                linker
                    .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror"])
                    .arg(root.join("driver.c"))
                    .args(&objects);
                runtime.link_into(&mut linker);
                checked(
                    linker.arg("-o").arg(dir.join("native.elf")),
                    60,
                    &dir.join("link.log"),
                );
                let result = checked(
                    &mut Command::new(dir.join("native.elf")),
                    60,
                    &dir.join("native.log"),
                );
                assert_eq!(result.stdout, b"PASS union_constant checks=24638\n");
                assert!(result.stderr.is_empty());
                checks += 24638;
                executions += 1;
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    assert_eq!((checks, executions), (394208, 16));
    let mut refusals = 0;
    for case in ["boolean", "reference", "partial"] {
        for opt in [0, 2] {
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("refused-{case}-{lane}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command
                    .args([
                        "--crate-type=lib",
                        "--emit=obj,mir",
                        "-Cpanic=abort",
                        "-Ccodegen-units=1",
                        "--target",
                        TARGET,
                        "--cfg",
                    ])
                    .arg(format!("case=\"{case}\""))
                    .arg(format!("-Copt-level={opt}"));
                if lane == "cg" {
                    command
                        .arg(format!("-Zcodegen-backend={}", backend.display()))
                        .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                }
                command
                    .arg(root.join("refused.rs"))
                    .arg("--out-dir")
                    .arg(&dir);
                if lane == "llvm" {
                    checked(&mut command, 180, &dir.join("compile.log"));
                } else {
                    let (result, _) =
                        super::run_bounded(&mut command, 180, &dir.join("compile.log"));
                    assert!(!result.status.success());
                    let stderr = String::from_utf8_lossy(&result.stderr);
                    assert!(stderr.contains("ConstValue::Indirect"), "{stderr}");
                    assert!(
                        !stderr.contains("internal compiler error")
                            && !stderr.contains("panicked at")
                    );
                    assert!(
                        !std::fs::read_dir(&dir).unwrap().any(|f| f
                            .unwrap()
                            .path()
                            .extension()
                            .is_some_and(|s| s == "o"))
                    );
                    refusals += 1;
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    assert_eq!(refusals, 6);
    println!(
        "TCG_UNION_CONSTANTS executions={executions} checks={checks} refusals={refusals} backend_sha256={digest}"
    );
}
