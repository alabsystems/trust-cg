//! Monomorphized constant branches and no-op drop calls match rustc collection.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-mono-cfg.XXXXXX"])
        .output()
        .expect("mktemp mono_cfg artifacts");
    assert!(temp.status.success());
    Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ))
}

fn native_case(
    root: &Path,
    backend: &Path,
    digest: &str,
    rust: &str,
    driver: &str,
    expected: &str,
) {
    std::fs::create_dir(root).unwrap();
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
    std::fs::write(root.join("driver.rs"), driver).unwrap();
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
            checked(
                Command::new("ar")
                    .arg("crs")
                    .arg(dir.join("libmono_cfg.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET, "-Cpanic=abort"])
                    .arg(root.join("driver.rs"))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=mono_cfg")
                    .arg("-o")
                    .arg(&executable),
                180,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 20, &dir.join("native.log"));
            assert_eq!(output.stdout, expected.as_bytes());
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
}

#[test]
fn no_proof_mono_cfg_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("mono_cfg/corpus.rs"),
        include_str!("mono_cfg/driver.rs"),
        "PASS mono_cfg checks=90112\n",
    );
    println!("TCG_MONO_CFG_DIAGNOSTIC executions=8 checks=720896 backend_sha256={digest}");
}

#[test]
fn mono_cfg_retains_live_and_dynamic_calls() {
    use super::run_bounded;
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let source = artifacts.0.join("refusals.rs");
    std::fs::write(&source, include_str!("mono_cfg/refusals.rs")).unwrap();
    for opt in 0..=3 {
        for config in ["dead", "live", "dynamic_branch"] {
            for lane in ["llvm", "cg"] {
                let dir = artifacts.0.join(format!("{lane}-{config}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Cpanic=abort",
                    "-Ccodegen-units=1",
                    "--target",
                    TARGET,
                    "--cfg",
                    config,
                ]);
                command.arg(format!("-Copt-level={opt}"));
                if lane == "cg" {
                    command
                        .arg(format!("-Zcodegen-backend={}", backend.display()))
                        .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                }
                command.arg(&source).arg("--out-dir").arg(&dir);
                let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                if lane == "llvm" || config == "dead" {
                    assert!(output.status.success(), "{transcript}");
                } else {
                    // The live `assembly::<true>` instance (v0 `Kb1_`) is the
                    // only failed root, and its inline asm is refused by the
                    // bounded AArch64 FP-asm lowering (`aarch64_fp_asm::lower`):
                    // this `nop` lacks the required `pure` option.
                    assert_eq!(output.status.code(), Some(1), "{transcript}");
                    let diagnostics: Vec<serde_json::Value> = transcript
                        .lines()
                        .filter_map(|line| serde_json::from_str(line).ok())
                        .filter(|row: &serde_json::Value| row["code"] == "TCG-MIR-UNSUPPORTED")
                        .collect();
                    assert_eq!(diagnostics.len(), 1, "{transcript}");
                    let fields = &diagnostics[0]["fields"];
                    assert_eq!(fields["failed_root_count"], "1", "{transcript}");
                    let root = fields["failed_roots"].as_str().unwrap();
                    assert!(
                        root.contains("8assemblyKb1_")
                            && root.contains(
                                "AArch64 FP asm requires Linux or Darwin, pure/nomem/nostack \
                                 and one non-unwinding successor"
                            ),
                        "{transcript}"
                    );
                }
                if config == "dead" {
                    let objects: Vec<_> = std::fs::read_dir(&dir)
                        .unwrap()
                        .map(|x| x.unwrap().path())
                        .filter(|p| p.extension().is_some_and(|x| x == "o"))
                        .collect();
                    assert!(!objects.is_empty());
                    let symbols = checked(
                        Command::new("nm").arg("-u").args(&objects),
                        30,
                        &dir.join("undefined.log"),
                    );
                    assert!(
                        !String::from_utf8_lossy(&symbols.stdout).contains("assembly"),
                        "dead helper referenced"
                    );
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    println!(
        "TCG_MONO_CFG_BOUNDARIES llvm_accepted=12 cg_accepted_dead=4 cg_refused_live=8 backend_sha256={digest}"
    );
}
