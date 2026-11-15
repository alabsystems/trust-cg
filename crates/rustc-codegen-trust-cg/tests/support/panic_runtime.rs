//! Sysroot panic calls preserve payloads, locations, unwinding and termination.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_panic_runtime_matches_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-panic-runtime.XXXXXX"])
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
        include_str!("panic_runtime/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.rs"),
        include_str!("panic_runtime/driver.rs"),
    )
    .unwrap();
    let mut checks = 0;
    let mut aborts = 0;
    // These crate-name fixtures exercise the existing sysroot interception
    // boundary; separate library-build probes qualify the actual core artifact.
    for name in ["core", "alloc", "std"] {
        for panic in ["unwind", "abort"] {
            for opt in 0..=3 {
                for lane in ["llvm", "cg"] {
                    let dir = root.join(format!("{name}-{panic}-{lane}-O{opt}"));
                    std::fs::create_dir(&dir).unwrap();
                    let mut command = rustc_command();
                    command.args([
                        "--crate-type=lib",
                        "--emit=obj,mir",
                        "-Ccodegen-units=1",
                        "-Cforce-unwind-tables=yes",
                        "-Cmetadata=panic_runtime_fixture",
                        "--target",
                        TARGET,
                    ]);
                    command
                        .arg(format!("--crate-name={name}"))
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
                            .arg(dir.join("libpanic_runtime.a"))
                            .args(&objects),
                        60,
                        &dir.join("archive.log"),
                    );
                    checked(
                        rustc_command()
                            .args(["--target", TARGET, "-Copt-level=2"])
                            .arg(format!("-Cpanic={panic}"))
                            .arg(root.join("driver.rs"))
                            .arg(format!("-Lnative={}", dir.display()))
                            .arg("-lstatic=panic_runtime")
                            .arg("-o")
                            .arg(dir.join("native.elf")),
                        180,
                        &dir.join("link.log"),
                    );
                    if panic == "unwind" {
                        let output = checked(
                            &mut Command::new(dir.join("native.elf")),
                            60,
                            &dir.join("native.log"),
                        );
                        assert_eq!(output.stdout, b"PASS panic_runtime checks=768\n");
                        assert!(output.stderr.is_empty());
                        checks += 768;
                    }
                    let cases = if panic == "unwind" {
                        vec![("nounwind", "runtime cannot unwind")]
                    } else {
                        vec![
                            ("literal", "runtime abort literal"),
                            ("formatted", "value=18446744073709551615"),
                            ("arguments", "runtime argument=37"),
                        ]
                    };
                    for (case, message) in cases {
                        let mut command = Command::new("sh");
                        command
                            .args(["-c", "ulimit -c 0; exec \"$@\"", "panic-runtime"])
                            .arg(dir.join("native.elf"))
                            .arg(case);
                        let (output, transcript) =
                            run_bounded(&mut command, 60, &dir.join(format!("{case}.log")));
                        assert_eq!(output.status.signal(), Some(6), "{transcript}");
                        assert!(output.stdout.is_empty(), "{transcript}");
                        let stderr = String::from_utf8_lossy(&output.stderr);
                        assert!(stderr.contains(message), "{transcript}");
                        if case == "nounwind" {
                            assert!(
                                stderr.contains("thread caused non-unwinding panic. aborting."),
                                "{transcript}"
                            );
                        }
                        aborts += 1;
                    }
                    assert_eq!(sha256(&backend), digest);
                }
            }
        }
    }
    assert_eq!(checks, 18432);
    assert_eq!(aborts, 96);
    println!(
        "TCG_PANIC_RUNTIME executions=24 checks={checks} aborts={aborts} backend_sha256={digest}"
    );
}
