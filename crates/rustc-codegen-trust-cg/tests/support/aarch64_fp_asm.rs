//! Scalar FP asm preserves hardware result bits and FPSR across FPCR modes.
//! The independent C driver uses GCC inline asm as the native oracle.
use super::{Artifacts, TARGET, backend, checked, rustc_command, sha256};
use std::path::PathBuf;
use std::process::Command;

#[test]
fn no_proof_aarch64_fp_asm_matches_hardware() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-aarch64-fp-asm.XXXXXX"])
        .output()
        .expect("mktemp aarch64_fp_asm artifacts");
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let root = &artifacts.0;
    let (backend, digest) = backend(root);
    std::fs::write(
        root.join("corpus.rs"),
        include_str!("aarch64_fp_asm/corpus.rs"),
    )
    .unwrap();
    std::fs::write(
        root.join("driver.c"),
        include_str!("aarch64_fp_asm/driver.c"),
    )
    .unwrap();
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
            let executable = dir.join("native.elf");
            checked(
                Command::new("cc")
                    .args([
                        "-std=c11",
                        "-O2",
                        "-Wall",
                        "-Wextra",
                        "-Werror",
                        "-frounding-math",
                        "-ffp-contract=off",
                    ])
                    .arg(root.join("driver.c"))
                    .args(&objects)
                    .arg("-o")
                    .arg(&executable),
                60,
                &dir.join("link.log"),
            );
            let output = checked(&mut Command::new(&executable), 30, &dir.join("native.log"));
            assert_eq!(output.stdout, b"PASS aarch64_fp_asm checks=2359296\n");
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
    println!("TCG_AARCH64_FP_ASM_DIAGNOSTIC executions=8 checks=18874368 backend_sha256={digest}");
}

#[test]
fn no_proof_aarch64_fp_asm_refusals() {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-aarch64-fp-asm-refusal.XXXXXX"])
        .output()
        .unwrap();
    assert!(temp.status.success());
    let artifacts = Artifacts(PathBuf::from(
        String::from_utf8(temp.stdout).unwrap().trim(),
    ));
    let (backend, digest) = backend(&artifacts.0);
    let cases = [
        (
            "current_rounding",
            "f64",
            "frinti {x:d}, {x:d}",
            "pure,nomem,nostack",
            "",
            "unsupported AArch64 FP asm instruction",
        ),
        (
            "multiple",
            "f64",
            "fsqrt {x:d}, {x:d}; fsqrt {x:d}, {x:d}",
            "pure,nomem,nostack",
            "",
            "one exact scalar instruction",
        ),
        (
            "opaque",
            "f64",
            "fsqrt {x:d}, {x:d}",
            "nomem,nostack",
            "",
            "pure/nomem/nostack",
        ),
        (
            "integer_bits",
            "u64",
            "fsqrt {x:d}, {x:d}",
            "pure,nomem,nostack",
            "",
            "input type/use disagrees",
        ),
        (
            "clobber",
            "f64",
            "fsqrt {x:d}, {x:d}",
            "pure,nomem,nostack",
            "out(\"x0\") _,",
            "operand/clobber is unsupported",
        ),
    ];
    for (name, ty, template, options, extra, reason) in cases {
        let dir = artifacts.0.join(name);
        std::fs::create_dir(&dir).unwrap();
        let source = dir.join("input.rs");
        std::fs::write(&source, format!(
            "#![no_std]\n#[unsafe(no_mangle)]pub fn probe(mut x:{ty})->{ty}{{unsafe{{core::arch::asm!({template:?},x=inout(vreg)x,{extra}options({options}));}}x}}\n"
        )).unwrap();
        for lane in ["llvm", "cg"] {
            let mut command = rustc_command();
            command.args([
                "--crate-type=lib",
                "--emit=obj",
                "-Cpanic=abort",
                "--target",
                TARGET,
            ]);
            command
                .arg(&source)
                .arg("-o")
                .arg(dir.join(format!("{lane}.o")));
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let (output, transcript) =
                    super::run_bounded(&mut command, 60, &dir.join("cg.log"));
                assert_eq!(output.status.code(), Some(1), "{transcript}");
                assert!(
                    transcript.contains("TCG-MIR-UNSUPPORTED") && transcript.contains(reason),
                    "{transcript}"
                );
            } else {
                checked(&mut command, 60, &dir.join("llvm.log"));
            }
        }
        assert_eq!(sha256(&backend), digest);
    }
    println!("TCG_AARCH64_FP_ASM_REFUSALS cases=5 backend_sha256={digest}");
}
