#![cfg(feature = "driver")]

// trust-cg-llvm-import / tests / intmm_o2_e2e.rs
//
// O2 linked-binary regression coverage for the IntMM Initmatrix shape.

use std::fs;
use std::io;
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

const INTMM_INITMATRIX_C: &str = r#"
#include <stdio.h>

#define rowsize 40

long seed;
int ima[rowsize + 1][rowsize + 1];

void Initrand(void) {
    seed = 74755L;
}

int Rand(void) {
    seed = (seed * 1309L + 13849L) & 65535L;
    return (int)seed;
}

void Initmatrix(int m[rowsize + 1][rowsize + 1]) {
    int temp, i, j;
    for (i = 1; i <= rowsize; i++) {
        for (j = 1; j <= rowsize; j++) {
            temp = Rand();
            m[i][j] = temp - (temp / 120) * 120 - 60;
        }
    }
}

int main(void) {
    int first = 1;
    int last = rowsize;
    Initrand();
    Initmatrix(ima);
    printf("%d %d\n", ima[first][first], ima[last][last]);
    return 0;
}
"#;

const INTMM_MAIN_LOOP_C: &str = r#"
#include <stdio.h>

#define rowsize 40

long seed;
int ima[rowsize + 1][rowsize + 1];
int imb[rowsize + 1][rowsize + 1];
int imr[rowsize + 1][rowsize + 1];

void Initrand(void) {
    seed = 74755L;
}

int Rand(void) {
    seed = (seed * 1309L + 13849L) & 65535L;
    return (int)seed;
}

void Initmatrix(int m[rowsize + 1][rowsize + 1]) {
    int temp, i, j;
    for (i = 1; i <= rowsize; i++) {
        for (j = 1; j <= rowsize; j++) {
            temp = Rand();
            m[i][j] = temp - (temp / 120) * 120 - 60;
        }
    }
}

void Innerproduct(int *result, int a[rowsize + 1][rowsize + 1],
                  int b[rowsize + 1][rowsize + 1], int row, int column) {
    int i;
    *result = 0;
    for (i = 1; i <= rowsize; i++) {
        *result += a[row][i] * b[i][column];
    }
}

void Intmm(int run) {
    int i, j;
    Initrand();
    Initmatrix(ima);
    Initmatrix(imb);
    for (i = 1; i <= rowsize; i++) {
        for (j = 1; j <= rowsize; j++) {
            Innerproduct(&imr[i][j], ima, imb, i, j);
        }
    }
    printf("%d\n", imr[run + 1][run + 1]);
}

int main(void) {
    int i;
    for (i = 0; i < 10; i++) {
        Intmm(i);
    }
    return 0;
}
"#;

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

fn ensure_clang_available() -> bool {
    match Command::new("clang").arg("--version").output() {
        Ok(output) if output.status.success() => true,
        Ok(output) => {
            panic!(
                "clang --version failed with {}\nstdout:\n{}\nstderr:\n{}",
                describe_status(output.status),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            );
        }
        Err(err) if err.kind() == io::ErrorKind::NotFound => {
            eprintln!("skipping: clang not found");
            false
        }
        Err(err) => panic!("run clang --version: {err}"),
    }
}

fn run_clang(args: &[&str]) {
    let output = Command::new("clang")
        .args(args)
        .output()
        .expect("run clang");
    assert!(
        output.status.success(),
        "clang {:?} failed with {}\nstdout:\n{}\nstderr:\n{}",
        args,
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn link_with_cc(obj_path: &Path, bin_path: &Path) {
    let output = Command::new("cc")
        .arg(obj_path)
        .arg("-o")
        .arg(bin_path)
        .output()
        .expect("run cc");
    assert!(
        output.status.success(),
        "cc failed with {}\nstdout:\n{}\nstderr:\n{}",
        describe_status(output.status),
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn run_binary(bin_path: &Path) -> Vec<u8> {
    run_binary_with_timeout(bin_path, Duration::from_secs(10))
}

fn run_binary_with_timeout(bin_path: &Path, timeout: Duration) -> Vec<u8> {
    let mut child = Command::new(bin_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn linked binary");
    let started = Instant::now();

    loop {
        match child.try_wait().expect("poll linked binary") {
            Some(status) => {
                let output = child.wait_with_output().expect("collect linked binary");
                assert_eq!(
                    output.status, status,
                    "wait status should match completed status"
                );
                assert!(
                    output.status.success(),
                    "linked binary failed with {}\nstdout:\n{}\nstderr:\n{}",
                    describe_status(output.status),
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
                return output.stdout;
            }
            None if started.elapsed() >= timeout => {
                let _ = child.kill();
                let output = child.wait_with_output().expect("collect killed binary");
                panic!(
                    "linked binary timed out after {:?}\nstdout prefix:\n{}\nstderr prefix:\n{}",
                    timeout,
                    String::from_utf8_lossy(&output.stdout),
                    String::from_utf8_lossy(&output.stderr)
                );
            }
            None => thread::sleep(Duration::from_millis(10)),
        }
    }
}

fn assert_o2_linked_binary_matches_clang_stdout(src: &str, name: &str) {
    if !cfg!(all(target_os = "macos", target_arch = "aarch64")) {
        eprintln!(
            "skipping: test requires aarch64-apple-darwin (host is {} / {})",
            std::env::consts::OS,
            std::env::consts::ARCH
        );
        return;
    }
    if !ensure_clang_available() {
        return;
    }

    let dir = unique_temp_dir(name);
    let c_path = dir.join(format!("{name}.c"));
    let ll_path = dir.join(format!("{name}.ll"));
    let clang_bin = dir.join(format!("{name}.clang"));
    let trust_cg_obj = dir.join(format!("{name}.trust-cg.o"));
    let trust_cg_bin = dir.join(format!("{name}.trust-cg"));

    fs::write(&c_path, src).expect("write C source");
    run_clang(&[
        "-O0",
        "-S",
        "-emit-llvm",
        "-o",
        ll_path.to_str().expect("ll path utf8"),
        c_path.to_str().expect("c path utf8"),
    ]);
    run_clang(&[
        "-O0",
        c_path.to_str().expect("c path utf8"),
        "-o",
        clang_bin.to_str().expect("clang bin path utf8"),
    ]);

    let clang_stdout = run_binary(&clang_bin);
    let ll_src = fs::read_to_string(&ll_path).expect("read generated ll");
    let object = compile_to_aarch64_object(&ll_src, name, OptLevel::O2);
    fs::write(&trust_cg_obj, object).expect("write object");
    link_with_cc(&trust_cg_obj, &trust_cg_bin);
    let trust_cg_stdout = run_binary(&trust_cg_bin);

    assert!(
        trust_cg_stdout == clang_stdout,
        "Trust Codegen O2 stdout should match clang for {name}\nclang:\n{}\ntrust-cg:\n{}",
        String::from_utf8_lossy(&clang_stdout),
        String::from_utf8_lossy(&trust_cg_stdout)
    );
}

fn compile_to_aarch64_object(src: &str, module_name: &str, opt_level: OptLevel) -> Vec<u8> {
    let module = import_text(src, module_name).expect("import");
    let target_spec = TargetSpec::parse("aarch64-apple-darwin").expect("target spec");
    let compiler = Compiler::new_for_target_spec(
        CompilerConfig {
            opt_level,
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
        .unwrap_or_else(|e| panic!("compile `{module_name}` failed: {e}"))
        .object_code
}

#[test]
fn intmm_initmatrix_o2_linked_binary_matches_clang_stdout() {
    assert_o2_linked_binary_matches_clang_stdout(INTMM_INITMATRIX_C, "intmm_initmatrix_o2");
}

#[test]
fn intmm_main_loop_o2_linked_binary_matches_clang_stdout() {
    assert_o2_linked_binary_matches_clang_stdout(INTMM_MAIN_LOOP_C, "intmm_main_loop_o2");
}
