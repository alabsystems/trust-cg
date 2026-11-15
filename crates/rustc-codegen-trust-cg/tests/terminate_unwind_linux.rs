//! Native controls for the current foreign-unwind boundary. Rust panic=abort
//! may still encounter a C++ exception or pthread forced unwind through a
//! C-unwind callee. Unsupported abort-mode edges must refuse before emission;
//! unwind-mode nounwind boundaries use the empty-filter terminate pad, which
//! aborts foreign exceptions and lets pthread forced unwinding pass.
//! These diagnostic compiler differentials grant no proof credit.
#![cfg(all(target_arch = "aarch64", target_os = "linux", target_env = "gnu"))]
#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/toolchain.rs"]
mod toolchain_support;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
const TARGET: &str = "aarch64-unknown-linux-gnu";
const OPT_LEVELS: [u32; 2] = [0, 2];
const DIRECT: &str = r#"extern "C-unwind" {fn ext(x:i32)->i32;}
#[no_mangle] #[inline(never)] pub extern "C" fn caller(x:i32)->i32 {unsafe {ext(x)}}"#;
const INDIRECT: &str = r#"use std::hint::black_box;
extern "C-unwind" {fn ext(x:i32)->i32;}
#[no_mangle] #[inline(never)] pub extern "C" fn caller(x:i32)->i32 {
 let f:unsafe extern "C-unwind" fn(i32)->i32=black_box(ext); unsafe {f(x)}
}"#;
const CLEANUP: &str = r#"extern "C-unwind" {fn ext(x:i32)->i32;}
struct Guard; impl Drop for Guard {fn drop(&mut self){std::hint::black_box(7);}}
#[no_mangle] #[inline(never)] pub extern "C" fn caller(x:i32)->i32 {let _g=Guard;unsafe {ext(x)}}"#;
const CPP: &str = r#"#include <pthread.h>
#include <cstdint>
extern "C" int caller(int);
extern "C" int ext(int x) {
 if(x==1) throw 17;
 if(x==2) pthread_exit(reinterpret_cast<void*>(0x1234));
 return 31;
}
static void* entry(void*) {caller(2);return nullptr;}
extern "C" int test_case(int x) {
 if(x==2) {pthread_t t;void* result=nullptr;if(pthread_create(&t,nullptr,entry,nullptr))return -1;if(pthread_join(t,&result))return -2;return static_cast<int>(reinterpret_cast<uintptr_t>(result));}
 try {return caller(x);} catch(int e) {return e+200;}
}"#;
const DRIVER: &str = r#"extern "C" {fn test_case(x:i32)->i32;}
fn main(){let x=std::env::args().nth(1).unwrap().parse::<i32>().unwrap();println!("{}",unsafe {test_case(x)});}"#;
fn run(command: &mut Command, log: &Path) -> (Output, String) {
    let mut bounded = Command::new("timeout");
    bounded
        .args(["--kill-after=5", "90"])
        .arg(command.get_program())
        .args(command.get_args());
    for (k, v) in command.get_envs() {
        if let Some(v) = v {
            bounded.env(k, v);
        } else {
            bounded.env_remove(k);
        }
    }
    let out = bounded.output().expect("run native compiler/control");
    let transcript = format!(
        "{command:?}\nstatus={}\nstdout={}\nstderr={}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    std::fs::write(log, &transcript).unwrap();
    (out, transcript)
}
fn checked(command: &mut Command, log: &Path) -> Output {
    let (out, text) = run(command, log);
    assert!(out.status.success(), "{text}");
    out
}
fn artifacts() -> PathBuf {
    let out = Command::new("mktemp")
        .args(["-d", "-t", "trust-cg-foreign-unwind.XXXXXX"])
        .output()
        .unwrap();
    assert!(out.status.success());
    PathBuf::from(String::from_utf8(out.stdout).unwrap().trim())
}
fn compile(
    source: &Path,
    out: &Path,
    opt: u32,
    panic: &str,
    backend: Option<&Path>,
    knobs: &[&str],
    log: &Path,
) -> (Output, String) {
    let mut command = toolchain_support::rustc_command();
    command
        .args([
            "--crate-type=lib",
            "--crate-name=fixture",
            "--emit=obj",
            "-Ccodegen-units=1",
            "--target",
            TARGET,
        ])
        .arg(format!("-Cpanic={panic}"))
        .arg(format!("-Copt-level={opt}"));
    if let Some(backend) = backend {
        command
            .arg(format!("-Zcodegen-backend={}", backend.display()))
            .arg(toolchain_support::backend_knobs_arg(knobs));
    }
    command.arg("-o").arg(out).arg(source);
    run(&mut command, log)
}
fn linked(dir: &Path, object: &Path, cpp: &Path, opt: u32, panic: &str) -> PathBuf {
    // The bridge publishes per-function objects for --emit=obj. Gather the
    // compiler's outputs before linking creates any driver object files.
    let objects = if object.is_file() {
        vec![object.to_owned()]
    } else {
        let mut objects: Vec<_> = std::fs::read_dir(dir)
            .unwrap()
            .map(|entry| entry.unwrap().path())
            .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
            .collect();
        objects.sort();
        assert!(
            !objects.is_empty(),
            "compile produced no object files in {}",
            dir.display()
        );
        objects
    };
    let bin = dir.join("driver.elf");
    let mut command = toolchain_support::rustc_command();
    command
        .args(["--target", TARGET])
        .arg(format!("-Cpanic={panic}"))
        .arg(format!("-Copt-level={opt}"))
        .args(
            objects
                .iter()
                .map(|object| format!("-Clink-arg={}", object.display())),
        )
        .arg(format!("-Clink-arg={}", cpp.display()))
        .args(["-Clink-arg=-lstdc++", "-Clink-arg=-lpthread"])
        .arg("-o")
        .arg(&bin)
        .arg(dir.parent().unwrap().join("driver.rs"));
    checked(&mut command, &dir.join("link.log"));
    bin
}
fn runtime_model(dir: &Path, bin: &Path, forced_unwind_passes: bool) {
    for (x, want) in [(0, "31\n")]
        .into_iter()
        .chain(forced_unwind_passes.then_some((2, "4660\n")))
    {
        let (out, text) = run(
            Command::new(bin).arg(x.to_string()),
            &dir.join(format!("run-{x}.log")),
        );
        assert!(out.status.success(), "{text}");
        assert_eq!(String::from_utf8(out.stdout).unwrap(), want, "{text}");
    }
    // Installed LLVM abort-mode nounwind boundaries also terminate forced
    // unwinding. Unwind-mode empty filters must let it reach pthread_exit.
    for x in [1].into_iter().chain((!forced_unwind_passes).then_some(2)) {
        let (out, text) = run(
            Command::new(bin).arg(x.to_string()),
            &dir.join(format!("run-abort-{x}.log")),
        );
        assert_eq!(
            out.status.signal(),
            Some(6),
            "unwind must abort at this nounwind boundary: {text}"
        );
        assert!(
            String::from_utf8_lossy(&out.stderr).contains("panic in a function that cannot unwind"),
            "{text}"
        );
    }
}
#[test]
fn foreign_unwind_abort_edges_refuse_with_llvm_native_controls() {
    assert!(toolchain_support::backend_knobs_supported());
    let dir = artifacts();
    eprintln!("foreign unwind artifacts: {}", dir.display());
    std::fs::write(dir.join("cpp.cc"), CPP).unwrap();
    std::fs::write(dir.join("driver.rs"), DRIVER).unwrap();
    let cpp = dir.join("cpp.o");
    checked(
        Command::new("g++")
            .args([
                "-std=c++17",
                "-fexceptions",
                "-fno-stack-protector",
                "-pthread",
                "-c",
            ])
            .arg(dir.join("cpp.cc"))
            .arg("-o")
            .arg(&cpp),
        &dir.join("cpp.log"),
    );
    let backend = backend_artifact_support::current_test_backend();
    for (name, source) in [
        ("direct", DIRECT),
        ("fn_pointer", INDIRECT),
        ("cleanup", CLEANUP),
    ] {
        std::fs::write(dir.join("fixture.rs"), source).unwrap();
        for opt in OPT_LEVELS {
            let cell = dir.join(format!("{name}-abort-O{opt}"));
            std::fs::create_dir(&cell).unwrap();
            let oracle = cell.join("llvm.o");
            let (out, text) = compile(
                &dir.join("fixture.rs"),
                &oracle,
                opt,
                "abort",
                None,
                &[],
                &cell.join("llvm-compile.log"),
            );
            assert!(out.status.success(), "{text}");
            runtime_model(&cell, &linked(&cell, &oracle, &cpp, opt, "abort"), false);
            let refused = cell.join("cg.o");
            let (out, text) = compile(
                &dir.join("fixture.rs"),
                &refused,
                opt,
                "abort",
                Some(&backend),
                &["no-proof-certs"],
                &cell.join("cg-refusal.log"),
            );
            assert!(
                !out.status.success() && text.contains("[TCG-EH-FOREIGN-ABORT]"),
                "{name} O{opt}: {text}"
            );
            assert!(
                !refused.exists(),
                "refused function emitted a requested object"
            );
            assert!(
                !cell.join("fixture.caller.rcgu.o").exists(),
                "refused caller emitted a callable bridge object"
            );
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}
#[test]
fn empty_filter_terminate_pad_aborts_foreign_and_preserves_forced_unwind() {
    assert!(toolchain_support::backend_knobs_supported());
    let dir = artifacts();
    eprintln!("empty-filter artifacts: {}", dir.display());
    std::fs::write(dir.join("cpp.cc"), CPP).unwrap();
    std::fs::write(dir.join("driver.rs"), DRIVER).unwrap();
    std::fs::write(dir.join("fixture.rs"), DIRECT).unwrap();
    let cpp = dir.join("cpp.o");
    checked(
        Command::new("g++")
            .args([
                "-std=c++17",
                "-fexceptions",
                "-fno-stack-protector",
                "-pthread",
                "-c",
            ])
            .arg(dir.join("cpp.cc"))
            .arg("-o")
            .arg(&cpp),
        &dir.join("cpp.log"),
    );
    let backend = backend_artifact_support::current_test_backend();
    for opt in OPT_LEVELS {
        for (name, selected) in [("llvm", None), ("cg", Some(backend.as_path()))] {
            let cell = dir.join(format!("{name}-unwind-O{opt}"));
            std::fs::create_dir(&cell).unwrap();
            let object = cell.join("fixture.o");
            let (out, text) = compile(
                &dir.join("fixture.rs"),
                &object,
                opt,
                "unwind",
                selected,
                &["no-proof-certs"],
                &cell.join("compile.log"),
            );
            assert!(out.status.success(), "{text}");
            runtime_model(&cell, &linked(&cell, &object, &cpp, opt, "unwind"), true);
        }
    }
    std::fs::remove_dir_all(dir).unwrap();
}
