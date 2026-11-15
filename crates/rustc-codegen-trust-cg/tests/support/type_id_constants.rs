//! Native regression for TypeId hash constants and mixed pointer globals.
//! This explicitly disables codegen proof certificates to isolate MIR lowering;
//! the separate proof-required ABI test remains required.

use super::{Artifacts, TARGET, backend, checked, rustc_command, scalar_cell_runtime, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_type_id_constants_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-type-id.XXXXXX"])
        .output()
        .expect("mktemp type-id artifacts");
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let runtime = scalar_cell_runtime::Runtime::build(root);
    let rust = include_str!("type_id_constants/corpus.rs");
    let c = include_str!("type_id_constants/driver.c");
    let checks = 164;
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("driver.c"), c).unwrap();
    let mut oracle: Option<Vec<u8>> = None;
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
            checked(
                command
                    .arg(root.join("corpus.rs"))
                    .arg("--out-dir")
                    .arg(&dir),
                180,
                &dir.join("compile.log"),
            );
            let mut objects: Vec<_> = std::fs::read_dir(&dir)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty(), "no objects from {stem}");
            let executable = dir.join("native.elf");
            let mut linker = Command::new("cc");
            linker
                .args(["-std=c11", "-O2"])
                .arg(root.join("driver.c"))
                .args(&objects);
            runtime.link_into(&mut linker);
            checked(linker.arg("-o").arg(&executable), 60, &dir.join("link.log"));
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            let text = std::str::from_utf8(&output.stdout).unwrap();
            assert!(text.ends_with(&format!("PASS type_id checks={checks}\n")));
            assert_eq!(text.lines().count(), 9);
            if let Some(expected) = &oracle {
                assert_eq!(
                    &output.stdout, expected,
                    "TypeId hash bits differ in {stem}"
                );
            } else {
                assert_eq!(stem, "llvm-O0");
                oracle = Some(output.stdout.clone());
            }
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
    println!(
        "TCG_TYPE_ID_DIAGNOSTIC executions=8 types=8 checks={} backend_sha256={digest}",
        checks * 8
    );
}
