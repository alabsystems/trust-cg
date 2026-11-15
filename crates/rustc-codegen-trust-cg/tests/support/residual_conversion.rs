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
    native_case_with_objects(
        root,
        backend,
        digest,
        rust,
        driver,
        expected,
        panic_mode,
        compiler_flags,
        driver_flags,
        &[],
    );
}

fn native_case_with_objects(
    root: &Path,
    backend: &Path,
    digest: &str,
    rust: &str,
    driver: &str,
    expected: &str,
    panic_mode: &str,
    compiler_flags: &[&str],
    driver_flags: &[&str],
    native_objects: &[PathBuf],
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
                    .args(&objects)
                    .args(native_objects),
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

/// A `C-unwind` fixture whose live foreign unwind edge (a cleanup for a local
/// with drop glue around a can-unwind callee) is compiled under
/// `-Cpanic=abort`. LLVM must emit the object (valid-Rust control) at O0-O3.
/// The bridge must refuse `function` with `[TCG-EH-FOREIGN-ABORT]`: the
/// foreign-exception abort adapter is implemented for Mach-O only
/// (`foreign_abort_eh::supported`), and lowering the call as a plain call
/// would let a foreign exception skip the cleanup instead of running it.
fn foreign_abort_refusal(root: &Path, backend: &Path, digest: &str, rust: &str, function: &str) {
    single_root_refusal(
        root,
        backend,
        digest,
        rust,
        "abort",
        &format!("{function}: [TCG-EH-FOREIGN-ABORT] `{function}`"),
    );
}

/// Compile `rust` under `panic_mode` at O0-O3: LLVM must emit the object
/// (valid-Rust control), and the bridge must exit 1 with exactly one
/// `[TCG-MIR-UNSUPPORTED]` diagnostic naming exactly one failed root whose text
/// starts with `root_prefix` (the refused function's name and its named code).
fn single_root_refusal(
    root: &Path,
    backend: &Path,
    digest: &str,
    rust: &str,
    panic_mode: &str,
    root_prefix: &str,
) {
    std::fs::create_dir(root).unwrap();
    std::fs::write(root.join("corpus.rs"), rust).unwrap();
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
                .arg(root.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&dir);
            if lane == "llvm" {
                checked(&mut command, 180, &dir.join("compile.log"));
            } else {
                let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(output.status.code(), Some(1), "{transcript}");
                let diagnostics: Vec<serde_json::Value> = transcript
                    .lines()
                    .filter_map(|line| serde_json::from_str(line).ok())
                    .filter(|row: &serde_json::Value| row["code"] == "TCG-MIR-UNSUPPORTED")
                    .collect();
                assert_eq!(diagnostics.len(), 1, "{transcript}");
                let fields = &diagnostics[0]["fields"];
                assert_eq!(fields["failed_root_count"], "1", "{transcript}");
                let root_text = fields["failed_roots"].as_str().unwrap();
                assert!(root_text.starts_with(root_prefix), "{transcript}");
            }
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

/// A closure body this crate compiles, whose address escapes through a `&dyn
/// Fn` vtable to a caller another crate compiles. It used to be refused
/// ([TCG-ARG-ABI] "UNTUPLED arguments"): the bridge declared the body TUPLED.
/// OD-RUST-CALL-ONE-RULE-20261008 declares every closure body as rustc's
/// `FnAbi` lists it and makes each program those refusals pinned a row that
/// must compile and match LLVM, so the bridge object is linked with an LLVM
/// `invoke_dynamic` and both lanes must agree, panics included.
#[test]
fn no_proof_fat_fn_callee_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for panic_mode in ["abort", "unwind"] {
        native_case(
            &artifacts.0.join(panic_mode),
            &backend,
            &digest,
            include_str!("residual_conversion/fat_fn_callee.rs"),
            include_str!("residual_conversion/fat_fn_callee_driver.rs"),
            if panic_mode == "abort" {
                "PASS fat_fn_callee checks=480 panics=0\n"
            } else {
                "PASS fat_fn_callee checks=480 panics=40\n"
            },
            panic_mode,
        );
    }
    println!("TCG_FAT_FN_CALLEE executions=16 checks=7680 panics=320 backend_sha256={digest}");
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

#[test]
fn no_proof_variadic_calls_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for (name, c, rust, driver) in [
        (
            "scalar",
            include_str!("residual_conversion/variadic_call.c"),
            include_str!("residual_conversion/variadic_call.rs"),
            include_str!("residual_conversion/variadic_call_driver.rs"),
        ),
        (
            "unwind",
            include_str!("residual_conversion/variadic_unwind.c"),
            include_str!("residual_conversion/variadic_unwind.rs"),
            include_str!("residual_conversion/variadic_unwind_driver.rs"),
        ),
    ] {
        let c_source = artifacts.0.join(format!("{name}.c"));
        let object = artifacts.0.join(format!("{name}.o"));
        std::fs::write(&c_source, c).unwrap();
        checked(
            Command::new("cc")
                .args([
                    "-std=c11",
                    "-O2",
                    "-fexceptions",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    "-c",
                ])
                .arg(&c_source)
                .arg("-o")
                .arg(&object),
            60,
            &artifacts.0.join(format!("{name}-cc.log")),
        );
        for panic_mode in ["unwind", "abort"] {
            let expected = match (name, panic_mode) {
                ("scalar", _) => "PASS variadic_call checks=40961\n",
                ("unwind", "unwind") => "PASS variadic_unwind checks=2048 panics=128\n",
                _ => {
                    // `invoke_variadic` keeps a live foreign unwind edge (its
                    // guard's cleanup around a C-unwind callee) under abort.
                    foreign_abort_refusal(
                        &artifacts.0.join(format!("{name}-{panic_mode}")),
                        &backend,
                        &digest,
                        rust,
                        "invoke_variadic",
                    );
                    continue;
                }
            };
            native_case_with_objects(
                &artifacts.0.join(format!("{name}-{panic_mode}")),
                &backend,
                &digest,
                rust,
                driver,
                expected,
                panic_mode,
                &[],
                &[],
                std::slice::from_ref(&object),
            );
        }
    }
    // `call_constant_empty` calls `variadic_words` through a pointer reified
    // from the declaration itself. The bridge emits that call as a
    // non-variadic `CallIndirect` (`functy.2 = (u32) -> (u64)`) of a FnDef
    // whose own signature is variadic (`functy.1 = (u32, ...) -> (u64)`).
    // OD-56 made the adapter refuse such an edge by name wherever the pointer
    // visibly names a variadic declaration
    // (`refuse_indirect_call_to_variadic_declaration`), on every target and
    // convention, base AAPCS64 included. Since WS7.3 (3c2356c70) trust-ir's
    // own validator, which every ingestion entry runs BEFORE the adapter,
    // refuses the same edge first: its `CallEdgeSignatureMismatch` names the
    // non-variadic call signature, the variadic FnDef and `variadic_words`
    // (LD-51). Before OD-56 it ran here and matched LLVM; it is now required
    // as exactly that one refused root at O0-O3 under both strategies, so the
    // rest of the scalar corpus keeps its LLVM comparison.
    // `call_pointer_empty` (a pointer the caller passes in, which neither walk
    // traces) still runs natively above.
    for panic_mode in ["unwind", "abort"] {
        single_root_refusal(
            &artifacts.0.join(format!("constant-pointer-{panic_mode}")),
            &backend,
            &digest,
            include_str!("residual_conversion/variadic_constant_pointer.rs"),
            panic_mode,
            "call_constant_empty: [TCG-IR-LOWER] rustc_codegen_trust_cg: Trust Codegen object \
             emission failed: trust-ir validation refused module `call_constant_empty` \
             (received): 1 finding(s): CallEdgeSignatureMismatch: bb0: indirect call declares \
             signature call functy.2 ((u32)) -> ((u64)); FnDef declares functy.1 but resolves \
             to `variadic_words` whose signature is target functy.1 ((u32)) -> ((u64))",
        );
    }
    println!(
        "TCG_VARIADIC executions=24 checks=671760 caught_panics=1024 foreign_abort_refusals=4 \
         call_edge_signature_refusals=8 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_variadic_calls_keep_refusals() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for (name, source, diagnostic) in [
        (
            "indirect",
            include_str!("residual_conversion/negative_variadic_indirect.rs"),
            "TerminatorKind::Call argument count 3 does not match callee input count 1",
        ),
        (
            "aggregate",
            include_str!("residual_conversion/negative_variadic_aggregate.rs"),
            "TCG-VARARG-ABI",
        ),
        (
            "i128",
            include_str!("residual_conversion/negative_variadic_i128.rs"),
            "TCG-VARARG-ABI",
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
                        .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                    let (output, transcript) =
                        run_bounded(&mut command, 180, &dir.join("compile.log"));
                    assert_eq!(output.status.code(), Some(1), "{transcript}");
                    assert!(transcript.contains(diagnostic), "{transcript}");
                } else {
                    checked(&mut command, 180, &dir.join("compile.log"));
                }
                assert_eq!(sha256(&backend), digest);
            }
        }
    }
    println!("TCG_VARIADIC_NEGATIVE refusals=6 llvm_controls=6 backend_sha256={digest}");
}

#[test]
fn no_proof_variadic_pointer_mutation_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let source = artifacts.0.join("mutation.c");
    let object = artifacts.0.join("mutation.o");
    std::fs::write(
        &source,
        include_str!("residual_conversion/variadic_mutation.c"),
    )
    .unwrap();
    checked(
        Command::new("cc")
            .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(&source)
            .arg("-o")
            .arg(&object),
        60,
        &artifacts.0.join("mutation-cc.log"),
    );
    for panic_mode in ["unwind", "abort"] {
        native_case_with_objects(
            &artifacts.0.join(panic_mode),
            &backend,
            &digest,
            include_str!("residual_conversion/variadic_mutation.rs"),
            include_str!("residual_conversion/variadic_call_driver.rs"),
            "PASS variadic_mutation checks=12288\n",
            panic_mode,
            &[],
            &[],
            std::slice::from_ref(&object),
        );
    }
    println!("TCG_VARIADIC_MUTATION executions=16 checks=196608 backend_sha256={digest}");
}

#[test]
fn no_proof_variadic_references_match_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    for (name, c, rust, driver) in [
        (
            "scalar",
            include_str!("residual_conversion/variadic_references.c"),
            include_str!("residual_conversion/variadic_references.rs"),
            include_str!("residual_conversion/variadic_call_driver.rs"),
        ),
        (
            "unwind",
            include_str!("residual_conversion/variadic_reference_unwind.c"),
            include_str!("residual_conversion/variadic_reference_unwind.rs"),
            include_str!("residual_conversion/variadic_reference_unwind_driver.rs"),
        ),
    ] {
        let c_source = artifacts.0.join(format!("{name}.c"));
        let object = artifacts.0.join(format!("{name}.o"));
        std::fs::write(&c_source, c).unwrap();
        checked(
            Command::new("cc")
                .args([
                    "-std=c11",
                    "-O2",
                    "-fexceptions",
                    "-Wall",
                    "-Wextra",
                    "-Werror",
                    "-c",
                ])
                .arg(&c_source)
                .arg("-o")
                .arg(&object),
            60,
            &artifacts.0.join(format!("{name}-cc.log")),
        );
        for panic_mode in ["unwind", "abort"] {
            let expected = match (name, panic_mode) {
                ("scalar", _) => "PASS variadic_reference checks=61440\n",
                ("unwind", "unwind") => "PASS variadic_reference_unwind checks=3072 panics=128\n",
                _ => {
                    // `write_then_unwind` keeps a live foreign unwind edge (the
                    // `Record` drop around a C-unwind callee) under abort.
                    foreign_abort_refusal(
                        &artifacts.0.join(format!("{name}-{panic_mode}")),
                        &backend,
                        &digest,
                        rust,
                        "write_then_unwind",
                    );
                    continue;
                }
            };
            native_case_with_objects(
                &artifacts.0.join(format!("{name}-{panic_mode}")),
                &backend,
                &digest,
                rust,
                driver,
                expected,
                panic_mode,
                &[],
                &[],
                std::slice::from_ref(&object),
            );
        }
    }
    println!(
        "TCG_VARIADIC_REFERENCES executions=24 checks=1007616 caught_panics=1024 foreign_abort_refusals=4 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_variadic_references_keep_wide_refusals() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let input = artifacts.0.join("wide.rs");
    std::fs::write(
        &input,
        include_str!("residual_conversion/negative_variadic_wide_references.rs"),
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
                .arg(&input)
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(output.status.code(), Some(1), "{transcript}");
                for name in [
                    "rejected_slice",
                    "rejected_str",
                    "rejected_dyn",
                    "rejected_raw_slice",
                ] {
                    assert!(
                        transcript.contains(&format!("{name}: [TCG-VARARG-ABI]")),
                        "{transcript}"
                    );
                }
                assert!(
                    transcript.contains("\"failed_root_count\":\"4\""),
                    "{transcript}"
                );
            } else {
                checked(&mut command, 180, &dir.join("compile.log"));
            }
            assert_eq!(sha256(&backend), digest);
        }
    }
    println!(
        "TCG_VARIADIC_WIDE_REF_NEGATIVE failing_roots=8 compiler_refusals=2 llvm_controls=2 backend_sha256={digest}"
    );
}

#[test]
fn no_proof_reference_identity_matches_llvm() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let c_source = artifacts.0.join("identity.c");
    let object = artifacts.0.join("identity.o");
    std::fs::write(
        &c_source,
        include_str!("residual_conversion/reference_identity.c"),
    )
    .unwrap();
    checked(
        Command::new("cc")
            .args(["-std=c11", "-O2", "-Wall", "-Wextra", "-Werror", "-c"])
            .arg(&c_source)
            .arg("-o")
            .arg(&object),
        60,
        &artifacts.0.join("identity-cc.log"),
    );
    for panic_mode in ["unwind", "abort"] {
        native_case_with_objects(
            &artifacts.0.join(panic_mode),
            &backend,
            &digest,
            include_str!("residual_conversion/reference_identity.rs"),
            include_str!("residual_conversion/reference_identity_driver.rs"),
            "PASS reference_identity checks=102400 failing_cases=0\n",
            panic_mode,
            &[],
            &[],
            std::slice::from_ref(&object),
        );
    }
    println!("TCG_REFERENCE_IDENTITY executions=16 checks=1638400 backend_sha256={digest}");
}

#[test]
fn no_proof_reference_identity_refuses_unresolved_storage() {
    let artifacts = artifacts();
    let (backend, digest) = backend(&artifacts.0);
    let input = artifacts.0.join("unresolved.rs");
    std::fs::write(
        &input,
        include_str!("residual_conversion/negative_reference_storage.rs"),
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
                .arg(&input)
                .arg("--out-dir")
                .arg(&dir);
            if lane == "cg" {
                command
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg("-Ztrust-ir-cg-args=diag-json no-proof-certs");
                let (output, transcript) = run_bounded(&mut command, 180, &dir.join("compile.log"));
                assert_eq!(output.status.code(), Some(1), "{transcript}");
                assert!(
                    transcript.contains("unsupported_drop_referent: [TCG-REF-ARG-STORAGE]"),
                    "{transcript}"
                );
                assert!(
                    transcript.contains("\"failed_root_count\":\"1\""),
                    "{transcript}"
                );
            } else {
                checked(&mut command, 180, &dir.join("compile.log"));
            }
            assert_eq!(sha256(&backend), digest);
        }
    }
    println!("TCG_REFERENCE_STORAGE_NEGATIVE refusals=2 llvm_controls=2 backend_sha256={digest}");
}
