// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Native diagnostic only: Trust verification and proof certificates are off.
// This target's marker requires actual execution, not a compile or early skip.
//
// The validity intrinsics `assert_zero_valid`, `assert_mem_uninitialized_valid`
// and `assert_inhabited` on AArch64 macOS. rustc emits them inside
// `mem::zeroed` / `MaybeUninit::assume_init` and friends; the bridge answers
// rustc's own `check_validity_requirement` query (with its strict-init
// policy), continues for a valid instantiation, and lowers an invalid one to
// rustc's `panic_nounwind` with rustc's message, so the panic hook runs and
// the process aborts without running cleanups. The full lane was qualified on
// AArch64 Linux only (`residual_conversion::intrinsic_validity`). Elsewhere a
// fallback admitted `assert_inhabited` for an inhabited type and refused
// `assert_zero_valid` / `assert_mem_uninitialized_valid` as unsupported
// intrinsics, which left every `mem::zeroed::<T>()` instance in `std` a failed
// root of the Darwin std census.
//
// THE GATE. For each fixture, LLVM (same compiler, same optimization level)
// and the bridge compile its callee crate to objects; an LLVM-built driver
// links each and runs, re-running itself once per invalid case and requiring
// SIGABRT with exactly one hook line for that case. Both lanes must print the
// same PASS line, at O0-O3, under panic=abort and panic=unwind, with and
// without `-Zstrict-init-checks`.
// - The Linux fixture, unchanged. rustc's InstSimplify folds every valid
//   assert whose type is concrete, so its valid branch reaches the bridge only
//   through `core::mem::zeroed` instances at O0/O1, and its hook checks the
//   message by prefix and suffix.
// - `generic`: every intrinsic behind a generic `#[inline(never)]` wrapper,
//   which neither InstSimplify nor the MIR inliner can fold, so valid and
//   invalid instantiations of all three reach the bridge at every level; its
//   hook requires rustc's exact message.
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
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

const TARGET: &str = "aarch64-apple-darwin";
const OPT_LEVELS: [u32; 4] = [0, 1, 2, 3];
const LANES: [&str; 2] = ["llvm", "cg"];

struct Temporary(PathBuf);

impl Temporary {
    fn new(stem: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-validity-{stem}-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir(&path).expect("create this fixture's unique directory");
        Self(path.canonicalize().expect("resolve this fixture directory"))
    }
}

impl Drop for Temporary {
    fn drop(&mut self) {
        if std::thread::panicking() {
            eprintln!("failed fixture artifacts retained at {}", self.0.display());
            return;
        }
        if let Err(error) = fs::remove_dir_all(&self.0) {
            eprintln!("fixture artifacts remain at {}: {error}", self.0.display());
        }
    }
}

struct Run {
    status: ExitStatus,
    stdout: String,
    stderr: String,
}

fn run_bounded(command: &mut Command, seconds: u64, log: &Path) -> Run {
    let stdout_path = log.with_extension("stdout.log");
    let stderr_path = log.with_extension("stderr.log");
    command
        .stdin(Stdio::null())
        .stdout(File::create(&stdout_path).unwrap())
        .stderr(File::create(&stderr_path).unwrap());
    let description = format!("{command:?}");
    let mut child = command.spawn().expect("spawn bounded fixture step");
    let started = Instant::now();
    let (status, timed_out) = loop {
        if let Some(status) = child.try_wait().expect("poll fixture child") {
            break (status, false);
        }
        if started.elapsed() >= Duration::from_secs(seconds) {
            child.kill().expect("kill timed-out fixture child");
            break (child.wait().expect("reap timed-out fixture child"), true);
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let stdout = fs::read_to_string(stdout_path).unwrap();
    let stderr = fs::read_to_string(stderr_path).unwrap();
    let transcript =
        format!("command: {description}\nstatus: {status}\nstdout:\n{stdout}\nstderr:\n{stderr}");
    fs::write(log, &transcript).expect("retain complete fixture step");
    assert!(
        !timed_out,
        "mandatory fixture step timed out after {seconds}s:\n{transcript}"
    );
    Run {
        status,
        stdout,
        stderr,
    }
}

fn checked(command: &mut Command, seconds: u64, log: &Path) -> Run {
    let output = run_bounded(command, seconds, log);
    assert!(
        output.status.success(),
        "mandatory fixture step failed at {}:\n{}\n{}",
        log.display(),
        output.stdout,
        output.stderr
    );
    output
}

/// The exact build compiler in its unverified diagnostic lane, on the edition
/// the Linux fixture is compiled with; no `TRUST_CG_*`/`TCG_*` control leaks in.
fn rustc() -> Command {
    let mut command = toolchain_support::rustc_command_with_edition("2024");
    for (key, _) in std::env::vars_os() {
        if key
            .to_str()
            .is_some_and(|name| name.starts_with("TRUST_CG_") || name.starts_with("TCG_"))
        {
            command.env_remove(key);
        }
    }
    command
}

/// A callee crate, its LLVM-built driver, and the PASS line the driver prints
/// without and with `-Zstrict-init-checks`.
struct Fixture {
    name: &'static str,
    corpus: &'static str,
    driver: &'static str,
    pass: [&'static str; 2],
}

const FIXTURES: [Fixture; 2] = [
    Fixture {
        name: "linux",
        corpus: include_str!("support/residual_conversion/intrinsic_validity.rs"),
        driver: include_str!("support/residual_conversion/intrinsic_validity_driver.rs"),
        pass: [
            "PASS intrinsic_validity checks=20480 aborts=6\n",
            "PASS intrinsic_validity checks=20480 aborts=7\n",
        ],
    },
    Fixture {
        name: "generic",
        corpus: include_str!("support/intrinsic_validity_darwin/generic.rs"),
        driver: include_str!("support/intrinsic_validity_darwin/generic_driver.rs"),
        pass: [
            "PASS generic_validity checks=4096 aborts=5\n",
            "PASS generic_validity checks=4096 aborts=6\n",
        ],
    },
];

/// Run one fixture at O0-O3 on both lanes under one panic strategy and
/// strict-init policy; returns the number of native runs.
fn run_case(root: &Path, backend: &Path, fixture: &Fixture, panic: &str, strict: bool) -> usize {
    let dir = root.join(format!("{}-{panic}-strict{strict}", fixture.name));
    fs::create_dir(&dir).unwrap();
    fs::write(dir.join("corpus.rs"), fixture.corpus).unwrap();
    fs::write(dir.join("driver.rs"), fixture.driver).unwrap();
    let expected = fixture.pass[usize::from(strict)];
    let mut runs = 0;
    for opt in OPT_LEVELS {
        for lane in LANES {
            let stem = format!("{lane}-O{opt}");
            let out = dir.join(&stem);
            fs::create_dir(&out).unwrap();
            let mut compile = rustc();
            compile
                .args(["--crate-type=lib", "--emit=obj", "-Ccodegen-units=1"])
                .args(["--target", TARGET])
                .arg(format!("-Copt-level={opt}"))
                .arg(format!("-Cpanic={panic}"));
            if strict {
                compile.arg("-Zstrict-init-checks=yes");
            }
            if lane == "cg" {
                compile
                    .arg(format!("-Zcodegen-backend={}", backend.display()))
                    .arg(toolchain_support::backend_knobs_arg(&[
                        "diag-json",
                        "no-proof-certs",
                    ]));
            }
            compile
                .arg(dir.join("corpus.rs"))
                .arg("--out-dir")
                .arg(&out);
            checked(&mut compile, 300, &out.join("compile.log"));
            let mut objects: Vec<_> = fs::read_dir(&out)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty(), "no objects from {stem}");
            checked(
                Command::new("ar")
                    .arg("crs")
                    .arg(out.join("libvalidity.a"))
                    .args(&objects),
                60,
                &out.join("archive.log"),
            );
            let executable = out.join("driver");
            let mut link = rustc();
            link.args(["--target", TARGET, "-Clink-dead-code=yes"])
                .arg(format!("-Cpanic={panic}"));
            if strict {
                link.arg("--cfg=strict_init");
            }
            checked(
                link.arg(dir.join("driver.rs"))
                    .arg("-L")
                    .arg(&out)
                    .arg("-lstatic=validity")
                    .arg("-o")
                    .arg(&executable),
                180,
                &out.join("link.log"),
            );
            let run = checked(&mut Command::new(&executable), 120, &out.join("run.log"));
            assert_eq!(
                run.stdout, expected,
                "{} {stem} panic={panic} strict={strict}: stdout differs; stderr:\n{}",
                fixture.name, run.stderr
            );
            runs += 1;
        }
    }
    runs
}

#[test]
fn intrinsic_validity_matches_llvm_aarch64() {
    darwin_native::require("intrinsic_validity_matches_llvm_aarch64", &[]);
    let root = Temporary::new("cases");
    let backend = backend_artifact_support::current_test_backend();
    let mut runs = 0;
    for fixture in &FIXTURES {
        for panic in ["abort", "unwind"] {
            for strict in [false, true] {
                runs += run_case(&root.0, &backend, fixture, panic, strict);
            }
        }
    }
    assert_eq!(runs, 64);
    println!(
        "TCG_INTRINSIC_VALIDITY_DARWIN fixtures=linux,generic executions={runs} opts=0,1,2,3 panic=abort,unwind strict=no,yes"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
