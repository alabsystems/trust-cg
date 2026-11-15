// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
#![cfg(all(target_os = "linux", target_arch = "aarch64", target_env = "gnu"))]
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const EXPECTED: &str = "SCALAR_ZST_FIELD checks=57 layouts=16 callback_checks=10 address_observations=40 offsets=0,8,64 refs=shared,mut raw=const,mut aliases=integer,pointer\n";

fn sha256(path: &Path) -> String {
    let output = Command::new("sha256sum")
        .arg(path)
        .output()
        .expect("hash exact artifact");
    assert!(output.status.success(), "artifact hash failed");
    let text = String::from_utf8(output.stdout).expect("ASCII SHA-256");
    let digest = text.split_whitespace().next().expect("artifact SHA-256");
    assert!(digest.len() == 64 && digest.bytes().all(|b| b.is_ascii_hexdigit()));
    digest.to_owned()
}

fn record_command(mut command: Command, directory: &Path, name: &str, limit: Duration) -> Output {
    let command_path = directory.join(format!("{name}.command.txt"));
    std::fs::write(&command_path, format!("{command:?}\n"))
        .expect("record compiler or native command");
    let stdout_path = directory.join(format!("{name}.stdout.log"));
    let stderr_path = directory.join(format!("{name}.stderr.log"));
    command
        .stdout(Stdio::from(
            std::fs::File::create(&stdout_path).expect("retain stdout"),
        ))
        .stderr(Stdio::from(
            std::fs::File::create(&stderr_path).expect("retain stderr"),
        ));
    for (key, _) in std::env::vars_os() {
        let name = key.to_string_lossy();
        if name.starts_with("TCG_") || name.starts_with("AY_") || name.starts_with("TRUST_IR_CG_") {
            command.env_remove(key);
        }
    }
    command.env_remove("CARGO_MAKEFLAGS");
    let mut child = command.spawn().expect("run compiler or native caller");
    let started = Instant::now();
    let status = loop {
        match child.try_wait().expect("poll scalar ZST field command") {
            Some(status) => break status,
            None if started.elapsed() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                std::fs::write(
                    directory.join(format!("{name}.timeout.txt")),
                    format!("timed out after {limit:?}\n"),
                )
                .expect("record timeout");
                panic!("{name} timed out; retained {directory:?}");
            }
            None => std::thread::sleep(Duration::from_millis(5)),
        }
    };
    std::fs::write(
        directory.join(format!("{name}.status.txt")),
        format!("status={status:?} elapsed={:?}\n", started.elapsed()),
    )
    .expect("record scalar ZST field status");
    let output = Output {
        status,
        stdout: std::fs::read(stdout_path).expect("read retained stdout"),
        stderr: std::fs::read(stderr_path).expect("read retained stderr"),
    };
    assert!(
        output.status.success(),
        "{name} failed ({:?}); retained {directory:?}\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn compile_and_run(directory: &Path, opt: &str, panic: &str, backend: Option<&Path>) -> Output {
    std::fs::create_dir_all(directory).expect("create isolated differential output");
    let library_source = directory.join("library.rs");
    let caller_source = directory.join("caller.rs");
    std::fs::write(
        &library_source,
        include_str!("support/scalar_zst_field/library.rs"),
    )
    .expect("write exact library fixture");
    std::fs::write(
        &caller_source,
        include_str!("support/scalar_zst_field/caller.rs"),
    )
    .expect("write exact LLVM caller fixture");
    let library = directory.join("libscalar_zst_field_fixture.rlib");
    let mut compiler = toolchain_support::rustc_command_with_edition("2024");
    compiler
        .args([
            "--crate-name=scalar_zst_field_fixture",
            "--crate-type=rlib",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Cpanic={panic}"));
    if let Some(backend) = backend {
        let mut option = std::ffi::OsString::from("-Zcodegen-backend=");
        option.push(backend);
        compiler
            .arg(option)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    compiler.arg(&library_source).arg("-o").arg(&library);
    record_command(
        compiler,
        directory,
        "compile-library",
        Duration::from_secs(240),
    );

    // The caller uses LLVM on both lanes. Crate metadata supplies exactly the
    // same Rust ABI/types, so passing pointers and scalars also checks the
    // compiled library boundary independently of its own caller lowering.
    let binary = directory.join("caller");
    let mut caller = toolchain_support::rustc_command_with_edition("2024");
    caller
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("-Cpanic={panic}"))
        .arg("--extern")
        .arg(format!("scalar_zst_field_fixture={}", library.display()))
        .arg(&caller_source)
        .arg("-o")
        .arg(&binary);
    record_command(
        caller,
        directory,
        "compile-llvm-caller",
        Duration::from_secs(240),
    );
    record_command(
        Command::new(binary),
        directory,
        "native",
        Duration::from_secs(30),
    )
}

#[test]
fn scalar_zst_field_matches_llvm() {
    // The producer's correction is scoped to Linux AArch64. This mandatory
    // native target has no skip path and makes no proof/sysroot qualification.
    assert_eq!(
        usize::BITS,
        64,
        "this native layout witness requires 64-bit pointers"
    );
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = sha256(&backend);
    let compiler = PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let compiler_before = sha256(&compiler);
    let root: PathBuf =
        std::env::temp_dir().join(format!("trust-cg-scalar-zst-field-{}", std::process::id()));
    assert!(
        !root.exists(),
        "refuse to overwrite retained differential output {root:?}"
    );
    let mut comparisons = 0;
    let mut lanes = Vec::new();
    for panic in ["abort", "unwind"] {
        for opt in ["0", "1", "2", "3"] {
            let row = root.join(format!("{panic}-O{opt}"));
            let oracle = compile_and_run(&row.join("llvm"), opt, panic, None);
            assert_eq!(
                String::from_utf8_lossy(&oracle.stdout),
                EXPECTED,
                "LLVM control must execute all checks"
            );
            let actual = compile_and_run(&row.join("cg"), opt, panic, Some(&backend));
            assert_eq!(
                actual.stdout, oracle.stdout,
                "{panic}/O{opt}: LLVM caller observed different library behavior"
            );
            assert_eq!(
                actual.status.code(),
                oracle.status.code(),
                "{panic}/O{opt}: native exit differs"
            );
            assert_eq!(
                sha256(&backend),
                backend_before,
                "backend changed during scalar ZST field comparison"
            );
            assert_eq!(
                sha256(&compiler),
                compiler_before,
                "compiler changed during scalar ZST field comparison"
            );
            for lane in ["llvm", "cg"] {
                let directory = row.join(lane);
                assert_eq!(
                    std::fs::read_to_string(directory.join("library.rs"))
                        .expect("reread library fixture"),
                    include_str!("support/scalar_zst_field/library.rs"),
                    "library fixture changed"
                );
                assert_eq!(
                    std::fs::read_to_string(directory.join("caller.rs"))
                        .expect("reread caller fixture"),
                    include_str!("support/scalar_zst_field/caller.rs"),
                    "caller fixture changed"
                );
                lanes.push(serde_json::json!({
                    "compiler": lane, "panic": panic, "opt_level": opt.parse::<u8>().unwrap(),
                    "executions": 1, "driver_checks": 57, "layout_checks": 16,
                    "callback_checks": 10, "address_observations": 40,
                }));
            }
            comparisons += 1;
        }
    }
    assert_eq!(comparisons, 8);
    eprintln!(
        "TCG_SCALAR_ZST_FIELD comparisons=8 native=16 checks_per_run=57 layout_checks_per_run=16 callback_checks_per_run=10 address_observations_per_run=40"
    );
    eprintln!(
        "TCG_NATIVE_RUNTIME_TEST NativeRun scalar_zst_field_matches_llvm certificates=off frontend_verify=off"
    );
    eprintln!(
        "TCG_BRIDGE_SCALAR_ZST_EXECUTION {}",
        serde_json::json!({
            "schema": 1, "target": "aarch64-unknown-linux-gnu",
            "backend_sha256": backend_before, "compiler_sha256": compiler_before,
            "comparisons": comparisons, "lanes": lanes,
            "certificates": "off", "frontend_verify": "off",
        })
    );
    eprintln!("retained scalar ZST field evidence: {}", root.display());
}
