//! Actual unwind cleanup state across independent LLVM provider/caller rlibs.
//! The baseline CG backend refused these shapes; that is not native wrong-code
//! evidence. Each admitted cell must execute all 17 ownership/drop scenarios.
//! Frontend verification and machine proof certificates are disabled equally
//! for this native codegen differential; it does not qualify an all-CG sysroot.
#![cfg(all(target_os = "linux", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

const PROVIDER: &str = include_str!("support/cleanup_state/provider.rs");
const CALLEE: &str = include_str!("support/cleanup_state/callee.rs");
const CALLER: &str = include_str!("support/cleanup_state/caller.rs");
const MARKER: &str = "CLEANUP_STATE|scenarios=17|box_join=6|box_call_result=5|scalar_join=6";

fn run(command: &mut Command, log: &Path, limit: Duration) -> ExitStatus {
    let mut output = std::fs::File::create(log).expect("create cleanup fixture log");
    writeln!(output, "{command:?}").expect("record cleanup fixture command");
    command
        .stdout(Stdio::from(output.try_clone().expect("clone cleanup log")))
        .stderr(Stdio::from(output.try_clone().expect("clone cleanup log")));
    let mut child = command.spawn().expect("execute cleanup fixture command");
    let started = Instant::now();
    loop {
        match child.try_wait().expect("poll cleanup fixture command") {
            Some(status) => {
                writeln!(output, "status={status:?}").expect("record cleanup fixture status");
                return status;
            }
            None if started.elapsed() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                writeln!(output, "timed out after {limit:?}").expect("record cleanup timeout");
                panic!("cleanup fixture timed out; diagnostics {}", log.display());
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
            "-Cpanic=unwind",
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
        "cleanup fixture compilation failed: {status:?}; {}",
        log.display()
    );
}

#[test]
fn cleanup_state_survives_real_unwind() {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read current build backend");
    let compiler = PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let compiler_before = std::fs::read(&compiler).expect("read exact build compiler");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-cleanup-state.XXXXXX"])
        .output()
        .expect("create cleanup fixture directory");
    assert!(temp.status.success());
    let root = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("cleanup state artifacts: {}", root.display());
    let provider_source = root.join("provider.rs");
    let callee_source = root.join("callee.rs");
    let caller_source = root.join("caller.rs");
    for (path, source) in [
        (&provider_source, PROVIDER),
        (&callee_source, CALLEE),
        (&caller_source, CALLER),
    ] {
        std::fs::write(path, source).expect("write exact cleanup fixture source");
    }
    // The allocator, panic origin, observation callbacks, and final caller are
    // always LLVM-built. Only the separately linked callee varies by backend.
    let provider = root.join("libcleanup_state_provider.rlib");
    compile(
        &root,
        "cleanup_state_provider",
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
            let callee = root.join(format!("libcleanup_state_callee_{callee_cg}_{opt}.rlib"));
            compile(
                &root,
                "cleanup_state_callee",
                &callee_source,
                &callee,
                true,
                callee_cg.then_some(backend.as_path()),
                opt,
                &[("cleanup_state_provider", provider.as_path())],
            );
            let caller = root.join(format!("caller_{callee_cg}_{opt}"));
            compile(
                &root,
                "cleanup_state_caller",
                &caller_source,
                &caller,
                false,
                None,
                opt,
                &[
                    ("cleanup_state_provider", provider.as_path()),
                    ("cleanup_state_callee", callee.as_path()),
                ],
            );
            let log = caller.with_extension("run.log");
            let status = run(&mut Command::new(&caller), &log, Duration::from_secs(30));
            assert!(
                status.success(),
                "cleanup native O{opt} callee_cg={callee_cg}: {status:?}; {}",
                log.display()
            );
            let text = std::fs::read_to_string(&log).expect("read cleanup native log");
            let markers: Vec<_> = text
                .lines()
                .filter(|line| line.starts_with("CLEANUP_STATE|"))
                .collect();
            assert_eq!(
                markers,
                [MARKER],
                "every cleanup scenario must execute; {}",
                log.display()
            );
            assert!(
                !text
                    .lines()
                    .any(|line| line.trim_start().starts_with("SKIP")),
                "native cleanup skipped; {}",
                log.display()
            );
            cells += 1;
        }
    }
    assert_eq!(cells, 8, "all four LLVM/CG optimization pairs must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during cleanup execution"
    );
    assert_eq!(
        std::fs::read(&compiler).expect("reread compiler"),
        compiler_before,
        "compiler changed during cleanup execution"
    );
    for (path, source) in [
        (&provider_source, PROVIDER),
        (&callee_source, CALLEE),
        (&caller_source, CALLER),
    ] {
        assert_eq!(
            std::fs::read_to_string(path).expect("reread fixture"),
            source,
            "cleanup fixture changed during execution"
        );
    }
    eprintln!(
        "TCG_CLEANUP_STATE_NATIVE cells=8 scenarios_per_cell=17 total_scenarios=136 panic=unwind provider=LLVM caller=LLVM frontend=off certs=off"
    );
    if std::env::var_os("TRUST_CLEANUP_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!("retained cleanup state artifacts: {}", root.display());
    } else {
        std::fs::remove_dir_all(root).expect("remove successful cleanup fixtures");
    }
}
