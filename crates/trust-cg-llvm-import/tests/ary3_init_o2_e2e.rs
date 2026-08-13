#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / ary3_init_o2_e2e.rs
//
// Deterministic imported-O0 ary3 initialization coverage for #922.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use trust_cg_codegen::compiler::{Compiler, CompilerConfig, CompilerTraceLevel};
use trust_cg_codegen::pipeline::OptLevel;
use trust_cg_codegen::target::TargetSpec;
use trust_cg_llvm_import::import_text;

#[cfg(unix)]
use std::os::unix::process::ExitStatusExt;

const ARY3_INIT_LL: &str = include_str!("fixtures/ary3_init_clang_o0.ll");

fn unique_temp_dir(name: &str) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system time before unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust-cg-import-{name}-{}-{nanos}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).expect("create temp dir");
    dir
}

fn describe_status(status: ExitStatus) -> String {
    if let Some(code) = status.code() {
        return format!("exit {code}");
    }
    #[cfg(unix)]
    if let Some(signal) = status.signal() {
        return format!("signal {signal}");
    }
    "unknown status".to_string()
}

fn compile_to_aarch64_object(src: &str, module_name: &str) -> Vec<u8> {
    let module = import_text(src, module_name).expect("import ary3 init fixture");
    let target_spec = TargetSpec::parse("aarch64-apple-darwin").expect("target spec");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level: OptLevel::O2,
            target: target_spec.architecture,
            emit_proofs: false,
            trace_level: CompilerTraceLevel::None,
            emit_debug: false,
            parallel: false,
            cegis_superopt_budget_sec: None,
            enable_fsym_trust_ir_preflight: false,
            enable_jit_fast_regalloc: false,
            jit_validation_mode_override: None,
            panic_unwind: false,
        },
        target_spec,
    );
    compiler
        .compile(&module)
        .expect("compile ary3 init fixture")
        .object_code
}

fn run_command_output(mut command: Command, timeout: Duration) -> std::process::Output {
    command.stdout(Stdio::piped()).stderr(Stdio::piped());
    let mut child = command.spawn().expect("spawn command");
    let started = Instant::now();
    loop {
        match child.try_wait().expect("poll command") {
            Some(status) => {
                let output = child.wait_with_output().expect("collect command output");
                assert_eq!(
                    output.status, status,
                    "wait status should match poll status"
                );
                return output;
            }
            None if started.elapsed() >= timeout => {
                let _ = child.kill();
                let output = child.wait_with_output().expect("collect killed command");
                panic!(
                    "command timed out after {:?}\nstdout:\n{}\nstderr:\n{}",
                    timeout,
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            None => thread::sleep(Duration::from_millis(10)),
        }
    }
}

fn disassemble_object(obj_path: &Path) -> String {
    let mut command = Command::new("/usr/bin/objdump");
    command.arg("-d").arg(obj_path);
    let output = run_command_output(command, Duration::from_secs(10));
    assert!(
        output.status.success(),
        "objdump failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("objdump output should be utf8")
}

fn link_with_cc(obj_path: &Path, bin_path: &Path) {
    let mut command = Command::new("cc");
    command.arg(obj_path).arg("-o").arg(bin_path);
    let output = run_command_output(command, Duration::from_secs(10));
    assert!(
        output.status.success(),
        "cc failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn ary3_init_imported_o0_o2_vectorizes_and_preserves_tails() {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }
    if !Path::new("/usr/bin/objdump").exists() {
        eprintln!("skipping: /usr/bin/objdump is not available");
        return;
    }

    let dir = unique_temp_dir("ary3-init-o2");
    let obj_path = dir.join("ary3_init.trust-cg.o");
    let bin_path = dir.join("ary3_init.trust-cg");
    let object = compile_to_aarch64_object(ARY3_INIT_LL, "ary3_init_clang_o0");
    fs::write(&obj_path, object).expect("write ary3 init object");

    let disassembly = disassemble_object(&obj_path);
    assert!(
        disassembly.to_ascii_lowercase().contains("st1"),
        "ary3 init loop should contain a NEON ST1 vector store:\n{disassembly}"
    );

    link_with_cc(&obj_path, &bin_path);
    let command = Command::new(&bin_path);
    let output = run_command_output(command, Duration::from_secs(10));
    assert!(
        output.status.success(),
        "linked ary3 init fixture failed with {}\nstdout:\n{}\nstderr:\n{}\ndisassembly:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
        disassembly
    );
    assert!(
        output.stdout.is_empty(),
        "fixture should be silent on success, got stdout:\n{}",
        String::from_utf8_lossy(&output.stdout)
    );
}
