//! Memory-only loop headers and projected scalar pattern-guard borrows.
//! Both historical controls failed closed before emitting a CG library; neither
//! is evidence of native wrong-code. Every admitted library must pass an
//! independent LLVM C ABI caller at all four optimization levels.
#![cfg(all(target_os = "linux", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

const LOOP_LIBRARY: &str =
    include_str!("support/std_memory_loop_scalar_borrow/loop-header-library.rs");
const LOOP_CALLER: &str =
    include_str!("support/std_memory_loop_scalar_borrow/loop-header-caller.rs");
const LOOP_PROVIDER: &str =
    include_str!("support/std_memory_loop_scalar_borrow/loop-header-provider.rs");
const SCALAR_LIBRARY: &str =
    include_str!("support/std_memory_loop_scalar_borrow/scalar-borrow-library.rs");
const SCALAR_CALLER: &str =
    include_str!("support/std_memory_loop_scalar_borrow/scalar-borrow-caller.rs");

fn run(mut command: Command, directory: &Path, name: &str, limit: Duration) -> Output {
    std::fs::write(
        directory.join(format!("{name}.command.txt")),
        format!("{command:?}\n"),
    )
    .expect("retain actual compiler or native command");
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
    let mut child = command.spawn().expect("execute compiler or native caller");
    let started = Instant::now();
    let status = loop {
        match child
            .try_wait()
            .expect("poll bounded native differential command")
        {
            Some(status) => break status,
            None if started.elapsed() >= limit => {
                let _ = child.kill();
                let _ = child.wait();
                std::fs::write(
                    directory.join(format!("{name}.timeout.txt")),
                    format!("timed out after {limit:?}\n"),
                )
                .expect("record timeout");
                panic!("{name} timed out; retained {}", directory.display());
            }
            None => std::thread::sleep(Duration::from_millis(5)),
        }
    };
    std::fs::write(
        directory.join(format!("{name}.status.txt")),
        format!("status={status:?} elapsed={:?}\n", started.elapsed()),
    )
    .expect("record command status");
    let output = Output {
        status,
        stdout: std::fs::read(stdout_path).expect("read retained stdout"),
        stderr: std::fs::read(stderr_path).expect("read retained stderr"),
    };
    assert!(
        output.status.success(),
        "{name} failed ({:?}); retained {}\n{}",
        output.status,
        directory.display(),
        String::from_utf8_lossy(&output.stderr)
    );
    output
}

fn compiler(opt: u8, crate_name: &str, directory: &Path) -> Command {
    let mut command = toolchain_support::rustc_command_with_edition("2024");
    command
        .args(["-Cpanic=abort", "-Ccodegen-units=1"])
        .arg(format!("-Copt-level={opt}"))
        .arg(format!("--crate-name={crate_name}"))
        .arg(format!("-Ldependency={}", directory.display()));
    command
}

fn guard_bytes(paths: &[(PathBuf, Vec<u8>)]) {
    for (path, expected) in paths {
        assert_eq!(
            std::fs::read(path).expect("reread immutable differential input"),
            *expected,
            "input or artifact changed: {}",
            path.display()
        );
    }
}

#[allow(clippy::too_many_arguments)]
fn lane(
    directory: &Path,
    opt: u8,
    crate_name: &str,
    library_text: &str,
    caller_text: &str,
    provider: Option<&Path>,
    backend: Option<&Path>,
    guards: &[(PathBuf, Vec<u8>)],
) -> Output {
    std::fs::create_dir(directory).expect("create isolated compiler lane");
    let library_source = directory.join("library.rs");
    let caller_source = directory.join("caller.rs");
    std::fs::write(&library_source, library_text).expect("write exact library fixture");
    std::fs::write(&caller_source, caller_text).expect("write exact LLVM caller fixture");
    guard_bytes(guards);
    let library = directory.join(format!("lib{crate_name}.rlib"));
    let mut command = compiler(opt, crate_name, directory);
    command
        .arg("--crate-type=rlib")
        .arg(&library_source)
        .arg("-o")
        .arg(&library);
    if let Some(backend) = backend {
        let mut option = std::ffi::OsString::from("-Zcodegen-backend=");
        option.push(backend);
        command
            .arg(option)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    run(
        command,
        directory,
        "library-compile",
        Duration::from_secs(240),
    );
    guard_bytes(guards);
    let library_bytes = std::fs::read(&library).expect("retain compiled library bytes");

    // Only the library varies by backend. The provider and every separately
    // declared C ABI caller use LLVM, and no LTO can inline away the boundary.
    let binary = directory.join("caller");
    let mut command = compiler(opt, &format!("{crate_name}_caller"), directory);
    command
        .arg(&caller_source)
        .arg("--extern")
        .arg(format!("{crate_name}={}", library.display()))
        .arg("-o")
        .arg(&binary);
    if let Some(provider) = provider {
        command
            .arg("--extern")
            .arg(format!("loop_header_provider={}", provider.display()));
    }
    run(
        command,
        directory,
        "llvm-caller-compile",
        Duration::from_secs(240),
    );
    let binary_bytes = std::fs::read(&binary).expect("retain native caller bytes");
    let output = run(
        Command::new(&binary),
        directory,
        "native",
        Duration::from_secs(30),
    );
    guard_bytes(guards);
    assert_eq!(
        std::fs::read(library).expect("reread library"),
        library_bytes,
        "library changed during native execution"
    );
    assert_eq!(
        std::fs::read(binary).expect("reread caller"),
        binary_bytes,
        "caller changed during native execution"
    );
    assert_eq!(
        std::fs::read_to_string(library_source).expect("reread library fixture"),
        library_text,
        "library fixture changed"
    );
    assert_eq!(
        std::fs::read_to_string(caller_source).expect("reread caller fixture"),
        caller_text,
        "caller fixture changed"
    );
    output
}

#[test]
fn std_memory_loop_and_scalar_borrow_match_llvm() {
    // The typed producer correction is currently Linux AArch64 only. There is
    // no skip or accepted-refusal path in this mandatory native target.
    assert_eq!(usize::BITS, 64);
    let backend = backend_artifact_support::current_test_backend();
    let compiler_path = PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let mut guards = vec![
        (
            backend.clone(),
            std::fs::read(&backend).expect("read exact backend"),
        ),
        (
            compiler_path.clone(),
            std::fs::read(&compiler_path).expect("read exact compiler"),
        ),
    ];
    let root = std::env::temp_dir().join(format!(
        "trust-cg-std-memory-producers-{}",
        std::process::id()
    ));
    assert!(
        !root.exists(),
        "refuse to overwrite retained evidence {}",
        root.display()
    );
    std::fs::create_dir(&root).expect("create retained differential evidence directory");
    eprintln!("retained std memory producer evidence: {}", root.display());
    let provider_source = root.join("provider.rs");
    std::fs::write(&provider_source, LOOP_PROVIDER).expect("write exact LLVM provider fixture");
    let provider = root.join("libloop_header_provider.rlib");
    let mut command = compiler(0, "loop_header_provider", &root);
    command
        .arg("--crate-type=rlib")
        .arg(&provider_source)
        .arg("-o")
        .arg(&provider);
    run(
        command,
        &root,
        "provider-llvm-compile",
        Duration::from_secs(240),
    );
    guards.push((
        provider.clone(),
        std::fs::read(&provider).expect("read exact provider"),
    ));
    guards.push((provider_source.clone(), LOOP_PROVIDER.as_bytes().to_vec()));
    let mut comparisons = 0;
    for opt in 0..=3 {
        for (family, crate_name, library, caller, provider, marker) in [
            (
                "memory-loop",
                "loop_header_library",
                LOOP_LIBRARY,
                LOOP_CALLER,
                Some(provider.as_path()),
                "MEMORY_ONLY_LOOP_HEADER_NATIVE checks=36\n",
            ),
            (
                "scalar-borrow",
                "scalar_borrow_library",
                SCALAR_LIBRARY,
                SCALAR_CALLER,
                None,
                "PROJECTED_SCALAR_PAYLOAD_GUARD_NATIVE checks=32 layouts=2\n",
            ),
        ] {
            let row = root.join(format!("{family}-O{opt}"));
            std::fs::create_dir(&row).expect("create optimization comparison directory");
            let oracle = lane(
                &row.join("llvm"),
                opt,
                crate_name,
                library,
                caller,
                provider,
                None,
                &guards,
            );
            assert_eq!(
                String::from_utf8_lossy(&oracle.stdout),
                marker,
                "LLVM must execute the complete independent oracle"
            );
            let actual = lane(
                &row.join("cg"),
                opt,
                crate_name,
                library,
                caller,
                provider,
                Some(&backend),
                &guards,
            );
            assert_eq!(
                actual.stdout, oracle.stdout,
                "{family}/O{opt}: LLVM caller observed different CG behavior"
            );
            assert_eq!(
                actual.status.code(),
                oracle.status.code(),
                "{family}/O{opt}: native exit differs"
            );
            comparisons += 1;
        }
    }
    guard_bytes(&guards);
    assert_eq!(comparisons, 8);
    eprintln!(
        "TCG_STD_MEMORY_LOOP_SCALAR_BORROW comparisons=8 native=16 memory_loop_checks=288 scalar_checks=256 layout_checks=16 optimization=O0-O3 panic=abort provider=LLVM caller=LLVM frontend=off certs=off"
    );
    eprintln!(
        "TCG_NATIVE_RUNTIME_TEST NativeRun std_memory_loop_and_scalar_borrow_match_llvm certificates=off frontend_verify=off"
    );
}
