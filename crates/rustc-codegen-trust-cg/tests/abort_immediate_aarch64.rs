// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Native diagnostic only: Trust verification and proof certificates are off.
// Immediate abort must trap; std::process::abort must keep its libc SIGABRT.
#![cfg(all(target_os = "macos", target_arch = "aarch64"))]

#[path = "support/backend_artifact.rs"]
mod backend_artifact_support;
#[path = "support/darwin_native_prerequisites.rs"]
mod darwin_native;
#[path = "support/positive_evidence.rs"]
mod positive_evidence;
#[path = "support/toolchain.rs"]
mod toolchain_support;

use std::fs::{self, File};
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

struct Temporary(PathBuf);
impl Drop for Temporary {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("failed abort fixtures retained at {}", self.0.display());
        } else {
            fs::remove_dir_all(&self.0).expect("remove successful abort fixtures");
        }
    }
}

fn bounded(command: &mut Command, root: &Path, label: &str, seconds: u64) -> ExitStatus {
    let stdout = root.join(format!("{label}.stdout"));
    let stderr = root.join(format!("{label}.stderr"));
    let description = format!("{command:?}");
    command
        .stdin(Stdio::null())
        .stdout(File::create(&stdout).unwrap())
        .stderr(File::create(&stderr).unwrap());
    let mut child = command.spawn().expect("spawn abort fixture step");
    let start = Instant::now();
    loop {
        if let Some(status) = child.try_wait().unwrap() {
            fs::write(
                root.join(format!("{label}.command")),
                format!("{description}\nstatus: {status}\n"),
            )
            .unwrap();
            return status;
        }
        if start.elapsed() >= Duration::from_secs(seconds) {
            child.kill().expect("kill timed-out fixture child");
            child.wait().expect("reap timed-out fixture child");
            panic!("abort fixture timed out: {description}");
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn immediate_abort_signals_match_llvm_aarch64() {
    darwin_native::require("immediate_abort_signals_match_llvm_aarch64", &[]);
    let nonce = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let root = Temporary(
        std::env::temp_dir().join(format!("trust-cg-abort-{}-{nonce}", std::process::id())),
    );
    fs::create_dir(&root.0).unwrap();
    let backend = backend_artifact_support::current_test_backend();
    let cases = [
        (
            "intrinsic",
            "#![feature(core_intrinsics)]\n#![allow(internal_features)]\nfn main() { core::intrinsics::abort_immediate(); }\n",
            5,
        ),
        (
            "public",
            "#![feature(abort_immediate)]\nfn main() { core::process::abort_immediate(); }\n",
            5,
        ),
        ("libc_control", "fn main() { std::process::abort(); }\n", 6),
    ];
    let mut executions = 0;
    for (name, source, expected_signal) in cases {
        let src = root.0.join(format!("{name}.rs"));
        fs::write(&src, source).unwrap();
        for panic in ["abort", "unwind"] {
            for opt in 0..=3 {
                let mut oracle = None;
                for lane in ["llvm", "cg"] {
                    let label = format!("{name}-{panic}-O{opt}-{lane}");
                    let exe = root.0.join(&label);
                    let mut compile = toolchain_support::rustc_command_with_edition("2021");
                    for (key, _) in std::env::vars_os() {
                        if key
                            .to_str()
                            .is_some_and(|k| k.starts_with("TRUST_CG_") || k.starts_with("TCG_"))
                        {
                            compile.env_remove(key);
                        }
                    }
                    compile
                        .args(["--target", "aarch64-apple-darwin", "-Ccodegen-units=1"])
                        .arg(format!("-Copt-level={opt}"))
                        .arg(format!("-Cpanic={panic}"));
                    if lane == "cg" {
                        compile
                            .arg(format!("-Zcodegen-backend={}", backend.display()))
                            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
                    }
                    compile.arg(&src).arg("-o").arg(&exe);
                    let status = bounded(&mut compile, &root.0, &format!("{label}-compile"), 300);
                    assert!(
                        status.success(),
                        "{label}: {}",
                        fs::read_to_string(root.0.join(format!("{label}-compile.stderr"))).unwrap()
                    );
                    // Limit core dumps in this tiny child only; exec preserves its signal.
                    let mut run = Command::new("/bin/sh");
                    run.args(["-c", "ulimit -c 0; exec \"$@\"", "abort-fixture"])
                        .arg(&exe);
                    let status = bounded(&mut run, &root.0, &label, 30);
                    let outcome = (
                        status.signal(),
                        fs::read(root.0.join(format!("{label}.stdout"))).unwrap(),
                        fs::read(root.0.join(format!("{label}.stderr"))).unwrap(),
                    );
                    assert_eq!(outcome, (Some(expected_signal), vec![], vec![]), "{label}");
                    if lane == "llvm" {
                        oracle = Some(outcome);
                    } else {
                        assert_eq!(Some(outcome), oracle, "{label}: LLVM mismatch");
                    }
                    executions += 1;
                }
            }
        }
    }
    assert_eq!(executions, 48);
    println!(
        "TCG_ABORT_IMMEDIATE_DARWIN fixtures=3 executions=48 opts=0,1,2,3 panic=abort,unwind trap=5 libc_abort=6"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
