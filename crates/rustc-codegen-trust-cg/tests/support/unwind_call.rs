//! Normal call continuations preserve result stores, reloads and panic cleanup.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_unwind_call_continuations_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-unwind-call.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("unwind_call/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.rs"),
        include_str!("unwind_call/driver.rs"),
    )
    .unwrap();
    for panic in ["unwind", "abort"] {
        for opt in 0..=3 {
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("{panic}-{lane}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-name=unwind_call",
                    "--crate-type=lib",
                    "--emit=obj,mir",
                    "-Cforce-unwind-tables=yes",
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
                    .map(|e| e.unwrap().path())
                    .filter(|p| p.extension().is_some_and(|e| e == "o"))
                    .collect();
                objects.sort();
                assert!(!objects.is_empty());
                checked(
                    Command::new("ar")
                        .arg("crs")
                        .arg(dir.join("libunwind_call.a"))
                        .args(&objects),
                    60,
                    &dir.join("archive.log"),
                );
                checked(
                    rustc_command()
                        .args(["-Copt-level=2", "-Cpanic=unwind", "--target", TARGET])
                        .arg(root.join("driver.rs"))
                        .arg(format!("-Lnative={}", dir.display()))
                        .arg("-lstatic=unwind_call")
                        .arg("-o")
                        .arg(dir.join("native.elf")),
                    180,
                    &dir.join("link.log"),
                );
                let output = checked(
                    Command::new(dir.join("native.elf")).arg(panic),
                    60,
                    &dir.join("native.log"),
                );
                let count = if panic == "unwind" { 6400 } else { 2816 };
                assert_eq!(
                    output.stdout,
                    format!("PASS unwind_call checks={count}\n").as_bytes()
                );
                assert!(output.stderr.is_empty());
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    // The opt-out must keep refusing real cleanup, rather than accepting a
    // plain call that loses the driver's observable destructor events.
    for opt in [0, 2] {
        let dir = root.join(format!("disabled-O{opt}"));
        std::fs::create_dir(&dir).unwrap();
        let mut command = rustc_command();
        command
            .args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=unwind",
                "--target",
                TARGET,
            ])
            .arg(format!("-Copt-level={opt}"))
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs disable-unwind")
            .arg(root.join("corpus.rs"))
            .arg("--out-dir")
            .arg(&dir);
        let (output, transcript) = run_bounded(&mut command, 120, &dir.join("compile.log"));
        assert_eq!(output.status.code(), Some(1), "{transcript}");
        assert!(
            String::from_utf8_lossy(&output.stderr)
                .contains("TerminatorKind::Call with cleanup unwind"),
            "{transcript}"
        );
    }
    assert_eq!(sha256(&backend), digest);
    println!(
        "TCG_UNWIND_CALL executions=16 checks=73728 cleanup_refusals=2 backend_sha256={digest}"
    );
}
