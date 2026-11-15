//! Native regression for scalar wrappers of closure environments.
//! This explicitly disables codegen proof certificates to isolate MIR lowering;
//! the separate proof-required ABI test remains required.

use super::{Artifacts, TARGET, backend, checked, rustc_command, scalar_cell_runtime, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_closure_wrappers_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-closure-wrapper.XXXXXX"])
        .output()
        .expect("mktemp closure-wrapper artifacts");
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    let runtime = scalar_cell_runtime::Runtime::build(root);
    let rust = include_str!("closure_wrappers/corpus.rs");
    let c = include_str!("closure_wrappers/driver.c");
    let checks = 3682;
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("driver.c"), c).unwrap();
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
            assert_eq!(text, format!("PASS closure_wrappers checks={checks}\n"));
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
    mixed_wrapper_calls(root, &runtime);
    assert_eq!(
        sha256(&backend),
        digest,
        "backend changed during mixed calls"
    );
    println!(
        "TCG_CLOSURE_WRAPPER_DIAGNOSTIC executions=10 functions=6 mixed=2 checks={} backend_sha256={digest}",
        checks * 10
    );
}

fn mixed_wrapper_calls(root: &std::path::Path, runtime: &scalar_cell_runtime::Runtime) {
    use std::collections::BTreeSet;
    let objects = |lane: &str| -> Vec<PathBuf> {
        let mut paths: Vec<_> = std::fs::read_dir(root.join(format!("{lane}-O0")))
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
            .collect();
        paths.sort();
        assert!(!paths.is_empty());
        paths
    };
    let llvm = objects("llvm");
    let cg = objects("cg");
    let symbols = |lane: &str, paths: &[PathBuf]| -> BTreeSet<String> {
        let output = checked(
            Command::new("nm")
                .args(["-g", "--defined-only"])
                .args(paths),
            20,
            &root.join(format!("{lane}-symbols.log")),
        );
        String::from_utf8(output.stdout)
            .unwrap()
            .lines()
            .filter_map(|line| {
                let parts: Vec<_> = line.split_whitespace().collect();
                (parts.len() == 3 && matches!(parts[1], "T" | "W")).then(|| parts[2].to_owned())
            })
            .collect()
    };
    let llvm_symbols = symbols("llvm", &llvm);
    let cg_symbols = symbols("cg", &cg);
    let common: BTreeSet<_> = llvm_symbols.intersection(&cg_symbols).cloned().collect();
    let wrappers: BTreeSet<_> = common
        .iter()
        .filter(|name| name.contains("_6corpus4wrap"))
        .cloned()
        .collect();
    assert_eq!(wrappers.len(), 8, "missing wrapper monomorphizations");
    for (lane, paths) in [("llvm", &llvm), ("cg", &cg)] {
        let output = checked(
            Command::new("readelf").arg("-rW").args(paths),
            20,
            &root.join(format!("{lane}-relocations.log")),
        );
        let relocations = String::from_utf8(output.stdout).unwrap();
        for name in &wrappers {
            assert!(
                relocations
                    .lines()
                    .any(|line| line.contains("R_AARCH64_CALL26") && line.contains(name)),
                "no real {lane} call to {name}"
            );
        }
    }
    // Symbol binding selects each implementation without changing its code.
    // Both objects retain their real call relocations and closure environments.
    for caller in ["llvm", "cg"] {
        let dir = root.join(format!("mixed-{caller}-caller"));
        std::fs::create_dir(&dir).unwrap();
        let mut mixed = Vec::new();
        for (lane, paths) in [("llvm", &llvm), ("cg", &cg)] {
            let weaken: Vec<_> = common
                .iter()
                .filter(|name| wrappers.contains(*name) == (lane == caller))
                .collect();
            for (index, original) in paths.iter().enumerate() {
                let object = dir.join(format!("{lane}-{index}.o"));
                let mut command = Command::new("objcopy");
                for name in &weaken {
                    command.arg(format!("--weaken-symbol={name}"));
                }
                checked(
                    command.arg(original).arg(&object),
                    20,
                    &dir.join(format!("{lane}-{index}.log")),
                );
                mixed.push(object);
            }
        }
        let executable = dir.join("native.elf");
        let mut linker = Command::new("cc");
        linker
            .args(["-std=c11", "-O2"])
            .arg(root.join("driver.c"))
            .args(&mixed)
            .arg(format!("-Wl,-Map={}", dir.join("link.map").display()));
        runtime.link_into(&mut linker);
        checked(linker.arg("-o").arg(&executable), 60, &dir.join("link.log"));
        let output = checked(&mut Command::new(executable), 20, &dir.join("native.log"));
        assert_eq!(output.stdout, b"PASS closure_wrappers checks=3682\n");
        assert!(output.stderr.is_empty());
    }
}
