//! Overflowing loop updates and conditional exits retain their back-edge values.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-wide-loop-threading.XXXXXX"])
        .output()
        .expect("mktemp wide_loop_threading artifacts");
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
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs refine-trace");
            }
            command
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            let compile = checked(&mut command, 180, &dir.join("compile.log"));
            if lane == "cg" && opt == 0 {
                let log = String::from_utf8_lossy(&compile.stderr);
                // Since the wasm32 bridge port merged with main (991b0f996),
                // pow_loop and pow_break_loop no longer leave a structurally
                // misthreaded back-edge at O0, so no VC proof is due for them;
                // the driver's oracle still checks their results.
                for function in [
                    "triangle_loop",
                    "overflow_rotate",
                    "signed_rotate",
                    "signed_multiply",
                    "wide_switch",
                    "wide_wrapping",
                ] {
                    assert!(
                        log.lines().any(|line| line
                            .starts_with(&format!("TCG_REFINE_TRACE {function}: "))
                            && line.contains("back-edge threading PROVEN")),
                        "missing semantic threading check for {function}: {log}"
                    );
                }
                // No loop here may be admitted by storage instead: a VC that
                // stops proving one of them must fail this test, not hand the
                // loop to the SSA-071 cell retry.
                assert!(!log.contains("SSA-071 cell retry admitted"), "{log}");
            }
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
                    .arg(dir.join("libwide_loop_threading.a"))
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
                    .arg("-lstatic=wide_loop_threading")
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
fn no_proof_wide_loop_threading_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("wide_loop_threading/corpus.rs"),
        include_str!("wide_loop_threading/driver.rs"),
        "PASS wide_loop_threading checks=43008\n",
    );
    println!(
        "TCG_WIDE_LOOP_THREADING_DIAGNOSTIC executions=8 checks=344064 backend_sha256={digest}"
    );
}
