//! Source-shaped opaque next-header loop with a real thin raw-pointer local.
//! Baseline CG O0-O3 refused this exact loop before code emission; independent
//! LLVM provider/caller pass. They check actual returned addresses, header
//! contents, and unchanged input memory. No pointer/call VC semantics are assumed.
#![cfg(all(target_os = "linux", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

const PROVIDER: &str = include_str!("support/ancillary_pointer_loop/provider.rs");
const CALLEE: &str = include_str!("support/ancillary_pointer_loop/callee.rs");
const CALLER: &str = include_str!("support/ancillary_pointer_loop/caller.rs");
const MARKER: &str = "ANCILLARY_POINTER_NEXT|checks=73|layouts=5";

fn run(command: &mut Command, log: &Path, limit: Duration) -> ExitStatus {
    let mut output = std::fs::File::create(log).expect("create pointer loop fixture log");
    writeln!(output, "{command:?}").expect("record pointer loop fixture command");
    command
        .stdout(Stdio::from(
            output.try_clone().expect("clone pointer loop log"),
        ))
        .stderr(Stdio::from(
            output.try_clone().expect("clone pointer loop log"),
        ));
    let mut child = command
        .spawn()
        .expect("execute pointer loop fixture command");
    let started = Instant::now();
    loop {
        match child.try_wait().expect("poll pointer loop fixture command") {
            Some(status) => {
                writeln!(output, "status={status:?}").expect("record pointer loop fixture status");
                return status;
            }
            None if started.elapsed() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                writeln!(output, "timed out after {limit:?}").expect("record pointer loop timeout");
                panic!(
                    "pointer loop fixture timed out; diagnostics {}",
                    log.display()
                );
            }
            None => std::thread::sleep(Duration::from_millis(5)),
        }
    }
}

fn compile(
    dir: &Path,
    crate_name: &str,
    source: &Path,
    output: &Path,
    library: bool,
    backend: Option<&Path>,
    opt: u8,
    externs: &[(&str, &Path)],
) {
    let mut command = toolchain_support::rustc_command_with_edition("2021");
    command
        .args([
            "-Cpanic=abort",
            "-Coverflow-checks=off",
            "-Ccodegen-units=1",
        ])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("--crate-name={crate_name}"))
        .arg(format!("-Ldependency={}", dir.display()));
    if library {
        command.arg("--crate-type=rlib");
    }
    if let Some(backend) = backend {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    for (name, path) in externs {
        command
            .arg("--extern")
            .arg(format!("{name}={}", path.display()));
    }
    for (key, _) in std::env::vars_os() {
        let name = key.to_string_lossy();
        if name.starts_with("TCG_") || name.starts_with("AY_") || name.starts_with("TRUST_IR_CG_") {
            command.env_remove(key);
        }
    }
    command.env_remove("CARGO_MAKEFLAGS");
    command.arg(source).arg("-o").arg(output).current_dir(dir);
    let log = output.with_extension("compile.log");
    let status = run(&mut command, &log, Duration::from_secs(240));
    assert!(
        status.success(),
        "pointer loop fixture compilation failed: {status:?}; {}",
        log.display()
    );
}

#[test]
fn ancillary_pointer_loop_matches_llvm() {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read current build backend");
    let compiler = PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let compiler_before = std::fs::read(&compiler).expect("read exact build compiler");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-ancillary-pointer-loop.XXXXXX"])
        .output()
        .expect("create pointer loop fixture directory");
    assert!(temp.status.success());
    let root = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("pointer loop state artifacts: {}", root.display());
    let provider_source = root.join("provider.rs");
    let callee_source = root.join("callee.rs");
    let caller_source = root.join("caller.rs");
    for (path, source) in [
        (&provider_source, PROVIDER),
        (&callee_source, CALLEE),
        (&caller_source, CALLER),
    ] {
        std::fs::write(path, source).expect("write exact pointer loop fixture source");
    }
    // The opaque next-header provider and final caller are always LLVM-built.
    // Only the separately linked pointer-loop callee varies by backend.
    let provider = root.join("libancillary_pointer_provider.rlib");
    compile(
        &root,
        "ancillary_pointer_provider",
        &provider_source,
        &provider,
        true,
        None,
        0,
        &[],
    );
    let mut cells = 0;
    for opt in 0..=3 {
        for callee_cg in [false, true] {
            let callee = root.join(format!(
                "libancillary_pointer_callee_{callee_cg}_{opt}.rlib"
            ));
            compile(
                &root,
                "ancillary_pointer_callee",
                &callee_source,
                &callee,
                true,
                callee_cg.then_some(backend.as_path()),
                opt,
                &[("ancillary_pointer_provider", provider.as_path())],
            );
            let caller = root.join(format!("caller_{callee_cg}_{opt}"));
            compile(
                &root,
                "ancillary_pointer_caller",
                &caller_source,
                &caller,
                false,
                None,
                opt,
                &[
                    ("ancillary_pointer_provider", provider.as_path()),
                    ("ancillary_pointer_callee", callee.as_path()),
                ],
            );
            let log = caller.with_extension("run.log");
            let status = run(&mut Command::new(&caller), &log, Duration::from_secs(30));
            assert!(
                status.success(),
                "pointer loop native O{opt} callee_cg={callee_cg}: {status:?}; {}",
                log.display()
            );
            let text = std::fs::read_to_string(&log).expect("read pointer loop native log");
            let markers: Vec<_> = text
                .lines()
                .filter(|line| line.starts_with("ANCILLARY_POINTER_NEXT|"))
                .collect();
            assert_eq!(
                markers,
                [MARKER],
                "both pointer/content checks must execute; {}",
                log.display()
            );
            assert!(
                !text
                    .lines()
                    .any(|line| line.trim_start().starts_with("SKIP")),
                "native pointer loop skipped; {}",
                log.display()
            );
            assert_eq!(
                std::fs::read(&backend).expect("reread backend"),
                backend_before,
                "backend changed during pointer-loop execution"
            );
            assert_eq!(
                std::fs::read(&compiler).expect("reread compiler"),
                compiler_before,
                "compiler changed during pointer-loop execution"
            );
            for (path, source) in [
                (&provider_source, PROVIDER),
                (&callee_source, CALLEE),
                (&caller_source, CALLER),
            ] {
                assert_eq!(
                    std::fs::read_to_string(path).expect("reread fixture"),
                    source,
                    "pointer-loop fixture changed during execution"
                );
            }
            cells += 1;
        }
    }
    assert_eq!(cells, 8, "all four LLVM/CG optimization pairs must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during pointer loop execution"
    );
    assert_eq!(
        std::fs::read(&compiler).expect("reread compiler"),
        compiler_before,
        "compiler changed during pointer loop execution"
    );
    for (path, source) in [
        (&provider_source, PROVIDER),
        (&callee_source, CALLEE),
        (&caller_source, CALLER),
    ] {
        assert_eq!(
            std::fs::read_to_string(path).expect("reread fixture"),
            source,
            "pointer loop fixture changed during execution"
        );
    }
    eprintln!(
        "TCG_ANCILLARY_POINTER_LOOP_NATIVE cells=8 checks_per_cell=73 total_checks=584 layouts_per_cell=5 total_layouts=40 panic=abort provider=LLVM caller=LLVM frontend=off certs=off"
    );
    if std::env::var_os("TRUST_ANCILLARY_POINTER_LOOP_KEEP_FIXTURES")
        .is_some_and(|value| value == "1")
    {
        eprintln!("retained pointer loop state artifacts: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).expect("remove successful pointer loop fixtures");
    }
}
