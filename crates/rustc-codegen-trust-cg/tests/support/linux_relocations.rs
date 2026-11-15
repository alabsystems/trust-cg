//! Session relocation policy, shared symbols, self addresses, and thread-local storage.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_linux_relocations_match_llvm() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-linux-relocations.XXXXXX"])
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
        include_str!("linux_relocations/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.c"),
        include_str!("linux_relocations/driver.c"),
    )
    .unwrap();
    for override_symbols in [false, true] {
        let name = if override_symbols {
            "override"
        } else {
            "normal"
        };
        let mut cc = Command::new("cc");
        cc.args([
            "-std=c11",
            "-O2",
            "-Wall",
            "-Wextra",
            "-Werror",
            "-rdynamic",
        ])
        .arg(root.join("driver.c"))
        .args(["-ldl", "-pthread"])
        .arg("-o")
        .arg(root.join(format!("driver-{name}.elf")));
        if override_symbols {
            cc.arg("-DOVERRIDE");
        }
        checked(&mut cc, 60, &root.join(format!("driver-{name}.log")));
    }
    let mut checks = 0;
    let mut executions = 0;
    for model in ["default", "pic", "pie", "static"] {
        let shared = matches!(model, "default" | "pic");
        for opt in 0..=3 {
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("{model}-{lane}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command.args([
                    "--crate-type=lib",
                    "--emit=obj,mir",
                    "-Ccodegen-units=1",
                    "-Cpanic=abort",
                    "--target",
                    TARGET,
                ]);
                command.arg(format!("-Copt-level={opt}"));
                if model != "default" {
                    command.arg(format!("-Crelocation-model={model}"));
                }
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
                // Under -Cpanic=abort the bridge raises the real `core` panic
                // entry for a failed non-bounds `Assert` (the never-taken
                // remainder check in `rotate_left`'s fallback body) rather than
                // an inline trap. The C link has no `libcore`, so those helpers
                // get aborting stubs (position-independent, for the shared lane).
                let stubs = super::toolchain_support::write_abort_stubs(&dir, &objects);
                let relocations = checked(
                    Command::new("readelf").arg("-Wr").args(&objects),
                    60,
                    &dir.join("relocations.log"),
                );
                let relocations = String::from_utf8(relocations.stdout).unwrap();
                let references: Vec<_> = relocations
                    .lines()
                    .filter(|l| l.contains("exported_function"))
                    .collect();
                assert!(!references.is_empty(), "{relocations}");
                if shared {
                    assert!(
                        references
                            .iter()
                            .any(|l| l.contains("R_AARCH64_ADR_GOT_PAGE")),
                        "{relocations}"
                    );
                    assert!(
                        !references
                            .iter()
                            .any(|l| l.contains("R_AARCH64_ADR_PREL_PG_HI21")),
                        "{relocations}"
                    );
                    checked(
                        Command::new("cc")
                            .args(["-shared", "-fPIC", "-Wl,-z,defs"])
                            .args(&objects)
                            .arg(&stubs)
                            .arg("-o")
                            .arg(dir.join("libfixture.so")),
                        60,
                        &dir.join("link.log"),
                    );
                    let dynamic = checked(
                        Command::new("readelf")
                            .arg("-Wd")
                            .arg(dir.join("libfixture.so")),
                        60,
                        &dir.join("dynamic.log"),
                    );
                    assert!(!String::from_utf8_lossy(&dynamic.stdout).contains("TEXTREL"));
                    for name in ["normal", "override"] {
                        let result = checked(
                            Command::new(root.join(format!("driver-{name}.elf")))
                                .arg(dir.join("libfixture.so")),
                            60,
                            &dir.join(format!("native-{name}.log")),
                        );
                        assert_eq!(result.stdout, b"PASS linux_pic checks=7187\n");
                        assert!(result.stderr.is_empty());
                        checks += 7187;
                        executions += 1;
                    }
                } else {
                    assert!(
                        references
                            .iter()
                            .any(|l| l.contains("R_AARCH64_ADR_PREL_PG_HI21")),
                        "{relocations}"
                    );
                    checked(
                        Command::new("cc")
                            .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-DDIRECT"])
                            .arg(if model == "pie" { "-pie" } else { "-no-pie" })
                            .arg(root.join("driver.c"))
                            .args(&objects)
                            .arg(&stubs)
                            .args(["-ldl", "-pthread"])
                            .arg("-o")
                            .arg(dir.join("native.elf")),
                        60,
                        &dir.join("link.log"),
                    );
                    let result = checked(
                        &mut Command::new(dir.join("native.elf")),
                        60,
                        &dir.join("native.log"),
                    );
                    assert_eq!(result.stdout, b"PASS linux_pic checks=7184\n");
                    assert!(result.stderr.is_empty());
                    checks += 7184;
                    executions += 1;
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    assert_eq!((checks, executions), (344928, 48));
    for model in ["dynamic-no-pic", "ropi", "rwpi", "ropi-rwpi"] {
        let dir = root.join(format!("refuse-{model}"));
        std::fs::create_dir(&dir).unwrap();
        let mut command = rustc_command();
        command
            .args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "--target",
                TARGET,
            ])
            .arg(format!("-Crelocation-model={model}"))
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs")
            .arg(root.join("corpus.rs"))
            .arg("--out-dir")
            .arg(&dir);
        let (result, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
        assert!(!result.status.success(), "{transcript}");
        assert!(
            transcript.contains("unsupported AArch64 Linux relocation model"),
            "{transcript}"
        );
        assert!(
            !transcript.contains("internal compiler error"),
            "{transcript}"
        );
    }
    assert_eq!(sha256(&backend), digest);
    println!(
        "TCG_LINUX_RELOCATIONS executions={executions} checks={checks} refusals=4 backend_sha256={digest}"
    );
}
