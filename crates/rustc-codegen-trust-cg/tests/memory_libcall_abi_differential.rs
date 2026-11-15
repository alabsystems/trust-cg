//! Mix genuine C memcpy/memmove/memset calls and their direct core intrinsics.
//! The sealed19 baseline refuses every mixed order at O0–O3 with a call-result
//! arity conflict. Independent LLVM provider/caller controls pass 13560 byte,
//! source-memory, return-pointer and canary checks plus 6 C layout checks.
//! This is Linux AArch64 runtime evidence, not full libc/std/proof qualification.
#![cfg(all(target_os = "linux", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant};

const PROVIDER: &str = include_str!("support/memory_libcall_abi/provider.rs");
const CALLEE: &str = include_str!("support/memory_libcall_abi/callee.rs");
const CALLER: &str = include_str!("support/memory_libcall_abi/caller.rs");
const MARKER: &str = "MIXED_LIBCALLS|checks=13560|layouts=6|runtime_count=LLVM|families=3|orders=2";

fn run(command: &mut Command, log: &Path, limit: Duration) -> ExitStatus {
    let mut output = std::fs::File::create(log).expect("create memory libcall fixture log");
    writeln!(output, "{command:?}").expect("record memory libcall fixture command");
    command
        .stdout(Stdio::from(
            output.try_clone().expect("clone memory libcall log"),
        ))
        .stderr(Stdio::from(
            output.try_clone().expect("clone memory libcall log"),
        ));
    let mut child = command
        .spawn()
        .expect("execute memory libcall fixture command");
    let started = Instant::now();
    loop {
        match child
            .try_wait()
            .expect("poll memory libcall fixture command")
        {
            Some(status) => {
                writeln!(output, "status={status:?}")
                    .expect("record memory libcall fixture status");
                return status;
            }
            None if started.elapsed() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                writeln!(output, "timed out after {limit:?}")
                    .expect("record memory libcall timeout");
                panic!(
                    "memory libcall fixture timed out; diagnostics {}",
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
        "memory libcall fixture compilation failed: {status:?}; {}",
        log.display()
    );
}

#[test]
fn memory_libcall_prototypes_match_llvm() {
    let backend = backend_artifact_support::current_test_backend();
    let backend_before = std::fs::read(&backend).expect("read current build backend");
    let compiler = PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let compiler_before = std::fs::read(&compiler).expect("read exact build compiler");
    let temp = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-memory-libcall.XXXXXX"])
        .output()
        .expect("create memory libcall fixture directory");
    assert!(temp.status.success());
    let root = PathBuf::from(String::from_utf8(temp.stdout).unwrap().trim());
    eprintln!("memory libcall state artifacts: {}", root.display());
    let provider_source = root.join("provider.rs");
    let callee_source = root.join("callee.rs");
    let caller_source = root.join("caller.rs");
    for (path, source) in [
        (&provider_source, PROVIDER),
        (&callee_source, CALLEE),
        (&caller_source, CALLER),
    ] {
        std::fs::write(path, source).expect("write exact memory libcall fixture source");
    }
    // The runtime-count provider and final byte/return-pointer oracle are LLVM-built.
    // Only the separately linked mixed-intrinsic/libcall callee varies by backend.
    let provider = root.join("libmixed_libcall_provider.rlib");
    compile(
        &root,
        "mixed_libcall_provider",
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
            let callee = root.join(format!("libmixed_libcalls_{callee_cg}_{opt}.rlib"));
            compile(
                &root,
                "mixed_libcalls",
                &callee_source,
                &callee,
                true,
                callee_cg.then_some(backend.as_path()),
                opt,
                &[("mixed_libcall_provider", provider.as_path())],
            );
            let caller = root.join(format!("caller_{callee_cg}_{opt}"));
            compile(
                &root,
                "mixed_libcall_caller",
                &caller_source,
                &caller,
                false,
                None,
                opt,
                &[
                    ("mixed_libcall_provider", provider.as_path()),
                    ("mixed_libcalls", callee.as_path()),
                ],
            );
            let log = caller.with_extension("run.log");
            let status = run(&mut Command::new(&caller), &log, Duration::from_secs(30));
            assert!(
                status.success(),
                "memory libcall native O{opt} callee_cg={callee_cg}: {status:?}; {}",
                log.display()
            );
            let text = std::fs::read_to_string(&log).expect("read memory libcall native log");
            let markers: Vec<_> = text
                .lines()
                .filter(|line| line.starts_with("MIXED_LIBCALLS|"))
                .collect();
            assert_eq!(
                markers,
                [MARKER],
                "both pointer/byte/canary checks must execute; {}",
                log.display()
            );
            assert!(
                !text
                    .lines()
                    .any(|line| line.trim_start().starts_with("SKIP")),
                "native memory libcall skipped; {}",
                log.display()
            );
            assert_eq!(
                std::fs::read(&backend).expect("reread backend"),
                backend_before,
                "backend changed during memory-libcall execution"
            );
            assert_eq!(
                std::fs::read(&compiler).expect("reread compiler"),
                compiler_before,
                "compiler changed during memory-libcall execution"
            );
            for (path, source) in [
                (&provider_source, PROVIDER),
                (&callee_source, CALLEE),
                (&caller_source, CALLER),
            ] {
                assert_eq!(
                    std::fs::read_to_string(path).expect("reread fixture"),
                    source,
                    "memory-libcall fixture changed during execution"
                );
            }
            cells += 1;
        }
    }
    assert_eq!(cells, 8, "all four LLVM/CG optimization pairs must execute");
    assert_eq!(
        std::fs::read(&backend).expect("reread backend"),
        backend_before,
        "backend changed during memory libcall execution"
    );
    assert_eq!(
        std::fs::read(&compiler).expect("reread compiler"),
        compiler_before,
        "compiler changed during memory libcall execution"
    );
    for (path, source) in [
        (&provider_source, PROVIDER),
        (&callee_source, CALLEE),
        (&caller_source, CALLER),
    ] {
        assert_eq!(
            std::fs::read_to_string(path).expect("reread fixture"),
            source,
            "memory libcall fixture changed during execution"
        );
    }
    eprintln!(
        "TCG_MEMORY_LIBCALL_NATIVE cells=8 checks_per_cell=13560 total_checks=108480 layouts_per_cell=6 total_layouts=48 panic=abort provider=LLVM caller=LLVM frontend=off certs=off"
    );
    if std::env::var_os("TRUST_MEMORY_LIBCALL_KEEP_FIXTURES").is_some_and(|value| value == "1") {
        eprintln!(
            "retained memory libcall state artifacts: {}",
            root.display()
        );
    } else {
        std::fs::remove_dir_all(root).expect("remove successful memory libcall fixtures");
    }
}
