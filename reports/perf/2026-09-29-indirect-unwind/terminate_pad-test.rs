//! Terminate edges abort at C boundaries, including bodies without MIR cleanup.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::os::unix::process::ExitStatusExt;
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_terminate_pads_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-terminate-pad.XXXXXX"])
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
        include_str!("terminate_pad/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.rs"),
        include_str!("terminate_pad/driver.rs"),
    )
    .unwrap();
    let mut aborts = 0;
    for panic in ["unwind", "abort"] {
        for opt in 0..=3 {
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("{panic}-{lane}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-name=terminate_pad",
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
                        .arg(dir.join("libterminate_pad.a"))
                        .args(&objects),
                    60,
                    &dir.join("archive.log"),
                );
                checked(
                    rustc_command()
                        .args(["-Copt-level=2", "-Cpanic=unwind", "--target", TARGET])
                        .arg(root.join("driver.rs"))
                        .arg(format!("-Lnative={}", dir.display()))
                        .arg("-lstatic=terminate_pad")
                        .arg("-o")
                        .arg(dir.join("native.elf")),
                    180,
                    &dir.join("link.log"),
                );
                let output = checked(
                    &mut Command::new(dir.join("native.elf")),
                    60,
                    &dir.join("native.log"),
                );
                assert_eq!(output.stdout, b"PASS terminate_pad checks=7168\n");
                assert!(output.stderr.is_empty());
                if panic == "unwind" {
                    for case in 0..14 {
                        // Limit only the child process's core dumps. Arguments are
                        // positional parameters, never interpolated into shell code.
                        let mut command = Command::new("sh");
                        command
                            .args(["-c", "ulimit -c 0; exec \"$@\"", "terminate-pad"])
                            .arg(dir.join("native.elf"))
                            .arg(case.to_string());
                        let (output, transcript) =
                            run_bounded(&mut command, 60, &dir.join(format!("panic-{case}.log")));
                        assert_eq!(output.status.signal(), Some(6), "{transcript}");
                        let expected = if case == 9 || case == 13 {
                            b"CALL 42\nCALL 43\n".as_slice()
                        } else {
                            b"CALL 42\n".as_slice()
                        };
                        assert_eq!(output.stdout, expected, "{transcript}");
                        let reason = if case == 9 || case == 13 {
                            "panic in a destructor during cleanup"
                        } else {
                            "panic in a function that cannot unwind"
                        };
                        assert!(
                            String::from_utf8_lossy(&output.stderr).contains(reason),
                            "{transcript}"
                        );
                        assert!(
                            String::from_utf8_lossy(&output.stderr)
                                .contains("thread caused non-unwinding panic. aborting."),
                            "{transcript}"
                        );
                        aborts += 1;
                    }
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    for opt in [0, 2] {
        for (name, source, knobs, diagnostic) in [(
            "disabled",
            "corpus.rs",
            "diag-json no-proof-certs disable-unwind",
            "terminate unwind while EH is inactive",
        )] {
            let dir = root.join(format!("{name}-O{opt}"));
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
                .arg(format!("-Ztrust-ir-cg-args={knobs}"))
                .arg(root.join(source))
                .arg("--out-dir")
                .arg(&dir);
            let (output, transcript) = run_bounded(&mut command, 120, &dir.join("compile.log"));
            assert_eq!(output.status.code(), Some(1), "{transcript}");
            assert!(
                String::from_utf8_lossy(&output.stderr).contains(diagnostic),
                "{transcript}"
            );
        }
    }
    assert_eq!(aborts, 112);
    assert_eq!(sha256(&backend), digest);
    println!(
        "TCG_TERMINATE_PAD executions=16 checks=114688 aborts=112 refusals=2 backend_sha256={digest}"
    );
}
