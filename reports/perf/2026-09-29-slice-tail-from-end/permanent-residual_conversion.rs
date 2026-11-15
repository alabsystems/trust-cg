//! Non-identity Result residuals execute their real From implementation.
//! Diagnostic codegen only; proof-required admission remains a separate gate.
use super::{Artifacts, TARGET, backend, checked, run_bounded, rustc_command, sha256};
use std::path::{Path, PathBuf};
use std::process::Command;

fn artifacts() -> Artifacts {
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-residual-conversion.XXXXXX"])
        .output()
        .expect("mktemp residual_conversion artifacts");
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
    panic_mode: &str,
) {
    native_case_with_flags(
        root,
        backend,
        digest,
        rust,
        driver,
        expected,
        panic_mode,
        &[],
        &[],
    );
}

fn native_case_with_flags(
    root: &Path,
    backend: &Path,
    digest: &str,
    rust: &str,
    driver: &str,
    expected: &str,
    panic_mode: &str,
    compiler_flags: &[&str],
    driver_flags: &[&str],
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
                "-Ccodegen-units=1",
                "--target",
                TARGET,
            ]);
            command.arg(format!("-Copt-level={opt}"));
            command.arg(format!("-Cpanic={panic_mode}"));
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
            }
            command
                .args(compiler_flags)
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
                    .arg(dir.join("libresidual_conversion.a"))
                    .args(&objects),
                60,
                &dir.join("archive.log"),
            );
            let executable = dir.join("native.elf");
            checked(
                rustc_command()
                    .args(["--target", TARGET])
                    .args(driver_flags)
                    .arg(format!("-Cpanic={panic_mode}"))
                    .arg(root.join("driver.rs"))
                    .arg("-L")
                    .arg(&dir)
                    .arg("-lstatic=residual_conversion")
                    .arg("-o")
                    .arg(&executable),
                180,
                &dir.join("link.log"),
            );
            let output = checked(
                Command::new("sh")
                    .args(["-c", "ulimit -c 0; exec \"$@\"", "residual-conversion"])
                    .arg(&executable),
                20,
                &dir.join("native.log"),
            );
            assert_eq!(output.stdout, expected.as_bytes());
            assert!(output.stderr.is_empty());
            assert_eq!(sha256(&backend), digest, "backend changed during {stem}");
        }
    }
}

#[test]
fn no_proof_residual_conversion_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("native"),
        &backend,
        &digest,
        include_str!("residual_conversion/corpus.rs"),
        include_str!("residual_conversion/driver.rs"),
        "PASS residual_conversion checks=20480\n",
        "abort",
    );
    println!(
        "TCG_RESIDUAL_CONVERSION_DIAGNOSTIC executions=8 checks=163840 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_residual_conversion_known_refusals_remain_named() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for (name, source, reason) in [(
        "collection",
        include_str!("residual_conversion/negative_collection.rs"),
        "TCG-COLLECTION-IMAGE",
    )] {
        let source_path = artifacts.0.join(format!("{name}.rs"));
        std::fs::write(&source_path, source).unwrap();
        for lane in ["llvm", "cg"] {
            let dir = artifacts.0.join(format!("{name}-{lane}"));
            std::fs::create_dir(&dir).unwrap();
            let mut command = rustc_command();
            command
                .args([
                    "--crate-type=lib",
                    "--emit=obj",
                    "-Cpanic=abort",
                    "-Copt-level=0",
                    "-Ccodegen-units=1",
                    "--target",
                    TARGET,
                ])
                .arg(&source_path)
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let (result, log) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(result.status.code(), Some(1), "{name}: {log}");
                assert!(log.contains(reason), "{name}: {log}");
            } else {
                checked(&mut command, 180, &dir.join("compile.log"));
            }
        }
        assert_eq!(sha256(&backend), digest);
    }
    println!("TCG_RESIDUAL_CONVERSION_NEGATIVE cases=1 backend_sha256={digest}");
}
#[test]
fn no_proof_residual_conversion_unwind_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("unwind"),
        &backend,
        &digest,
        include_str!("residual_conversion/unwind.rs"),
        include_str!("residual_conversion/unwind_driver.rs"),
        "PASS residual_conversion_unwind checks=1024\n",
        "unwind",
    );
    println!("TCG_RESIDUAL_CONVERSION_UNWIND executions=8 checks=8192 backend_sha256={digest}");
}

#[test]
fn no_proof_aggregate_return_unwind_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("aggregate-unwind"),
        &backend,
        &digest,
        include_str!("residual_conversion/aggregate_unwind.rs"),
        include_str!("residual_conversion/aggregate_unwind_driver.rs"),
        "PASS aggregate_unwind checks=2560\n",
        "unwind",
    );
    println!("TCG_AGGREGATE_RETURN_UNWIND executions=8 checks=20480 backend_sha256={digest}");
}

#[test]
fn no_proof_indirect_return_unwind_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("indirect-unwind"),
        &backend,
        &digest,
        include_str!("residual_conversion/indirect_unwind.rs"),
        include_str!("residual_conversion/indirect_unwind_driver.rs"),
        "PASS indirect_aggregate_unwind checks=3584\n",
        "unwind",
    );
    println!("TCG_INDIRECT_RETURN_UNWIND executions=8 checks=28672 backend_sha256={digest}");
}

#[test]
fn no_proof_dyn_drop_unwind_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    native_case(
        &artifacts.0.join("dyn-drop-unwind"),
        &backend,
        &digest,
        include_str!("residual_conversion/dyn_drop_unwind.rs"),
        include_str!("residual_conversion/dyn_drop_unwind_driver.rs"),
        "PASS indirect_dyn_drop checks=1024\n",
        "unwind",
    );
    println!("TCG_DYN_DROP_UNWIND executions=8 checks=8192 backend_sha256={digest}");
}

#[test]
fn no_proof_slice_tail_from_end_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic_mode in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(panic_mode),
            &backend,
            &digest,
            include_str!("residual_conversion/slice_tail_from_end.rs"),
            include_str!("residual_conversion/slice_tail_from_end_driver.rs"),
            "PASS slice_from_end checks=512\nPASS slice_from_end_wrapped checks=16\nPASS slice_tail_from_end checks=23936\n",
            panic_mode,
        );
    }
    println!("TCG_SLICE_TAIL_FROM_END executions=16 checks=391424 backend_sha256={digest}");
}

#[test]
fn no_proof_slice_tail_from_end_keeps_projected_field_refusal() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let source = artifacts.0.join("projected_field.rs");
    std::fs::write(
        &source,
        include_str!("residual_conversion/negative_slice_tail_from_end_field.rs"),
    )
    .unwrap();
    for panic_mode in ["abort", "unwind"] {
        for opt in [2, 3] {
            for lane in ["llvm", "cg"] {
                let dir = artifacts.0.join(format!("{panic_mode}-{lane}-O{opt}"));
                std::fs::create_dir(&dir).unwrap();
                let mut command = rustc_command();
                command
                    .args(["--crate-type=lib", "--emit=obj", "--target", TARGET])
                    .arg(format!("-Cpanic={panic_mode}"))
                    .arg(format!("-Copt-level={opt}"))
                    .arg(&source)
                    .arg("--out-dir")
                    .arg(&dir);
                if lane == "cg" {
                    command
                        .arg(format!("-Zcodegen-backend={}", backend.display()))
                        .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                    let (result, log) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                    assert_eq!(result.status.code(), Some(1), "{log}");
                    assert!(log.contains("from-end ConstantIndex"), "{log}");
                    assert!(log.contains("needs the runtime slice length"), "{log}");
                } else {
                    checked(&mut command, 180, &dir.join("compile.log"));
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    println!("TCG_SLICE_TAIL_FROM_END_NEGATIVE refusals=4 backend_sha256={digest}");
}

#[test]
fn no_proof_fat_fn_arguments_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic_mode in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(panic_mode),
            &backend,
            &digest,
            include_str!("residual_conversion/fat_fn_arguments.rs"),
            include_str!("residual_conversion/fat_fn_arguments_driver.rs"),
            if panic_mode == "abort" {
                "PASS fat_fn_arguments checks=2567 panics=0\n"
            } else {
                "PASS fat_fn_arguments checks=5127 panics=1152\n"
            },
            panic_mode,
        );
    }
    println!("TCG_FAT_FN_ARGUMENTS executions=16 checks=61552 panics=9216 backend_sha256={digest}");
}

#[test]
fn no_proof_fat_fn_box_arguments_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic_mode in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(panic_mode),
            &backend,
            &digest,
            include_str!("residual_conversion/fat_fn_box_arguments.rs"),
            include_str!("residual_conversion/fat_fn_box_arguments_driver.rs"),
            "PASS fat_fn_box checks=384\n",
            panic_mode,
        );
    }
    println!("TCG_FAT_FN_BOX_ARGUMENTS executions=16 checks=6144 backend_sha256={digest}");
}

#[test]
fn no_proof_fat_fn_arguments_keep_callee_refusal() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let source = artifacts.0.join("callee.rs");
    std::fs::write(
        &source,
        include_str!("residual_conversion/negative_fat_fn_callee.rs"),
    )
    .unwrap();
    for opt in [0, 2] {
        for lane in ["llvm", "cg"] {
            let dir = artifacts.0.join(format!("{lane}-O{opt}"));
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
                .arg(&source)
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let (result, log) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(result.status.code(), Some(1), "{log}");
                assert!(log.contains("TCG-ARG-ABI"), "{log}");
                assert!(log.contains("takes the address of"), "{log}");
                assert!(log.contains("UNTUPLED arguments"), "{log}");
            } else {
                checked(&mut command, 180, &dir.join("compile.log"));
            }
            assert_eq!(sha256(&backend), digest);
        }
    }
    println!("TCG_FAT_FN_CALLEE_NEGATIVE refusals=2 backend_sha256={digest}");
}

#[test]
fn no_proof_virtual_unwind_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic_mode in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(panic_mode),
            &backend,
            &digest,
            include_str!("residual_conversion/virtual_unwind.rs"),
            include_str!("residual_conversion/virtual_unwind_driver.rs"),
            if panic_mode == "abort" {
                "PASS virtual_unwind checks=2048 panics=0 aborts=1\n"
            } else {
                "PASS virtual_unwind checks=4096 panics=896 aborts=1\n"
            },
            panic_mode,
        );
    }
    println!(
        "TCG_VIRTUAL_UNWIND executions=16 checks=49152 panics=7168 aborts=16 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_virtual_termination_skips_forced_unwind() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let source = artifacts.0.join("forced.c");
    let object = artifacts.0.join("forced.o");
    std::fs::write(
        &source,
        include_str!("residual_conversion/virtual_forced.c"),
    )
    .unwrap();
    checked(
        Command::new("cc")
            .args(["-O2", "-fexceptions", "-Werror", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&object),
        60,
        &artifacts.0.join("forced-compile.log"),
    );
    native_case_with_flags(
        &artifacts.0.join("forced"),
        &backend,
        &digest,
        include_str!("residual_conversion/virtual_unwind.rs"),
        include_str!("residual_conversion/virtual_forced_driver.rs"),
        "PASS forced filter\n",
        "unwind",
        &[],
        &[&format!("-Clink-arg={}", object.display())],
    );
    println!("TCG_VIRTUAL_FORCED_UNWIND executions=8 backend_sha256={digest}");
}

#[test]
fn no_proof_virtual_unwind_keeps_refusals() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for (name, source, knobs, diagnostic) in [
        (
            "sret",
            include_str!("residual_conversion/negative_virtual_sret.rs"),
            "diag-json no-proof-certs",
            "TCG-SRET-ABI",
        ),
        (
            "disabled",
            include_str!("residual_conversion/virtual_unwind.rs"),
            "diag-json no-proof-certs disable-unwind",
            "EH is inactive",
        ),
    ] {
        let input = artifacts.0.join(format!("{name}.rs"));
        std::fs::write(&input, source).unwrap();
        for opt in [0, 2] {
            for lane in ["llvm", "cg"] {
                let dir = artifacts.0.join(format!("{name}-{lane}-O{opt}"));
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
                    .arg(&input)
                    .arg("--out-dir")
                    .arg(&dir);
                if lane == "cg" {
                    command
                        .arg(format!("-Zcodegen-backend={}", backend.display()))
                        .arg(format!("-Ztrust-ir-cg-args={knobs}"));
                    let (result, transcript) =
                        run_bounded(&mut command, 180, &dir.join("compile.log"));
                    assert_eq!(result.status.code(), Some(1), "{transcript}");
                    assert!(transcript.contains(diagnostic), "{transcript}");
                } else {
                    checked(&mut command, 180, &dir.join("compile.log"));
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    println!("TCG_VIRTUAL_UNWIND_NEGATIVE refusals=4 llvm_controls=4 backend_sha256={digest}");
}

#[test]
fn no_proof_indirect_unwind_keeps_sret_refusal() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let source = artifacts.0.join("indirect_sret.rs");
    std::fs::write(
        &source,
        include_str!("residual_conversion/negative_indirect_sret.rs"),
    )
    .unwrap();
    for opt in [0, 2] {
        for lane in ["llvm", "cg"] {
            let dir = artifacts.0.join(format!("{lane}-O{opt}"));
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
                .arg(&source)
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let (result, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(result.status.code(), Some(1), "{transcript}");
                assert!(transcript.contains("TCG-SRET-ABI"), "{transcript}");
            } else {
                checked(&mut command, 180, &dir.join("compile.log"));
            }
            assert_eq!(sha256(&backend), digest);
        }
    }
    println!("TCG_INDIRECT_UNWIND_NEGATIVE refusals=2 llvm_controls=2 backend_sha256={digest}");
}

#[test]
fn no_proof_projected_reference_types_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(format!("projected-reference-{panic}")),
            &backend,
            &digest,
            include_str!("residual_conversion/projected_reference_types.rs"),
            include_str!("residual_conversion/projected_reference_types_driver.rs"),
            "PASS projected_reference_types checks=77824\n",
            panic,
        );
    }
    println!("TCG_PROJECTED_REFERENCE_TYPES executions=16 checks=1245184 backend_sha256={digest}");
}

#[test]
fn no_proof_projected_aggregate_reference_types_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(format!("aggregate-reference-{panic}")),
            &backend,
            &digest,
            include_str!("residual_conversion/projected_aggregate_reference_types.rs"),
            include_str!("residual_conversion/projected_aggregate_reference_types_driver.rs"),
            "PASS aggregate_reference_types checks=57344\n",
            panic,
        );
    }
    println!(
        "TCG_PROJECTED_AGGREGATE_REFERENCE_TYPES executions=16 checks=917504 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_intrinsic_validity_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic in ["abort", "unwind"] {
        for strict in [false, true] {
            native_case_with_flags(
                &artifacts.0.join(format!("validity-{panic}-strict{strict}")),
                &backend,
                &digest,
                include_str!("residual_conversion/intrinsic_validity.rs"),
                include_str!("residual_conversion/intrinsic_validity_driver.rs"),
                if strict {
                    "PASS intrinsic_validity checks=20480 aborts=7\n"
                } else {
                    "PASS intrinsic_validity checks=20480 aborts=6\n"
                },
                panic,
                if strict {
                    &["-Zstrict-init-checks=yes"]
                } else {
                    &[]
                },
                if strict { &["--cfg=strict_init"] } else { &[] },
            );
        }
    }
    println!(
        "TCG_INTRINSIC_VALIDITY executions=32 checks=655360 aborts=208 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_union_array_transmute_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(format!("union-array-transmute-{panic}")),
            &backend,
            &digest,
            include_str!("residual_conversion/union_array_transmute.rs"),
            include_str!("residual_conversion/union_array_transmute_driver.rs"),
            "PASS union_array_transmute checks=36864\n",
            panic,
        );
    }
    println!("TCG_UNION_ARRAY_TRANSMUTE executions=16 checks=589824 backend_sha256={digest}");
}

#[test]
fn no_proof_zero_sized_tuples_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(format!("zero-sized-tuples-{panic}")),
            &backend,
            &digest,
            include_str!("residual_conversion/zero_sized_tuples.rs"),
            include_str!("residual_conversion/zero_sized_tuples_driver.rs"),
            "PASS zero_sized_tuples checks=36864\n",
            panic,
        );
    }
    println!("TCG_ZERO_SIZED_TUPLES executions=16 checks=589824 backend_sha256={digest}");
}
