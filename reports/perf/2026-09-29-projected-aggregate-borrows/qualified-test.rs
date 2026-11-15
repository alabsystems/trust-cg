//! A borrowed aggregate field keeps its mutations when its parent is moved.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_projected_aggregate_borrows_images_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-projected-aggregate-borrows.XXXXXX"])
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
        include_str!("projected_aggregate_borrows/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.c"),
        include_str!("projected_aggregate_borrows/driver.c"),
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
                assert_eq!(
                    result.stdout,
                    b"PASS projected_aggregate_borrows checks=524288\n"
                );
                assert!(result.stderr.is_empty());
                checks += 524288;
                executions += 1;
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    assert_eq!((checks, executions), (8388608, 16));
    // A padded nested copy is still outside the admitted field-copy layout.
    std::fs::write(
        root.join("refused.rs"),
        include_str!("projected_aggregate_borrows/refused.rs"),
    )
    .unwrap();
    for opt in [0, 2] {
        let dir = root.join(format!("refused-O{opt}"));
        std::fs::create_dir(&dir).unwrap();
        let mut command = rustc_command();
        command
            .args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ])
            .arg(format!("-Copt-level={opt}"))
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs")
            .arg(root.join("refused.rs"))
            .arg("--out-dir")
            .arg(&dir);
        let (result, transcript) = super::run_bounded(&mut command, 180, &dir.join("compile.log"));
        assert!(!result.status.success(), "{transcript}");
        let stderr = String::from_utf8_lossy(&result.stderr);
        assert!(
            stderr.contains("field-copy faithfulness") && stderr.contains("partial copy"),
            "{transcript}"
        );
        assert!(
            !stderr.contains("internal compiler error") && !stderr.contains("panicked at"),
            "{transcript}"
        );
    }
    println!(
        "TCG_PROJECTED_AGGREGATE_BORROWS executions={executions} checks={checks} refusals=2 backend_sha256={digest}"
    );
}
