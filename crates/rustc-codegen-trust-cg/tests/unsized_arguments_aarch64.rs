// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Native diagnostic only: Trust verification and proof certificates are off.
// This target's markers require actual execution, not a compile or early skip.
//
// Unsized by-value slice and str parameters (`fn f(s: [T])`, enabled by
// `unsized_fn_params`) on AArch64 macOS. The `unsized_arguments` lane passes
// such a parameter as rustc's Rust-ABI indirect pair (data pointer, length) and
// rewrites the body to address the caller's storage through a `&mut [T]` view.
// It was qualified against LLVM on AArch64 Linux only
// (`support/unsized_arguments.rs`, included by `aarch64_c_fnabi_aggregate_linux`)
// and refused everywhere else, which left alloc's
// `<[&str] as SpecExtendStr>::spec_extend_into` as a failed root of the Darwin
// alloc census. This target is the Darwin qualification its admission rests on.
//
// THE GATE. For every row, LLVM (same compiler, same optimization level) and the
// bridge compile the callee crate to objects; an LLVM-built driver links each
// set and runs. Both lanes must print the same PASS line, which the driver
// prints only after every check passed: return values that fold in every
// element and the length, and the data address the callee saw (the caller's
// own storage, never a copy). The drivers also count a heap-balance check per
// iteration; it guards the LLVM-built driver only, since neither callee crate
// links an allocator, and the `checks=` totals (inherited from the Linux
// marker) count it and the LLVM-lane runs alike.
// - `unsized_arguments_corpus_matches_llvm_aarch64` runs the Linux corpus
//   unchanged: `[u64]` with 0..9 scalar prefixes, both call directions, `str`,
//   64-byte-aligned and zero-sized elements, fn-pointer and virtual calls.
// - `unsized_str_slice_arguments_match_llvm_aarch64` adds the Darwin rows:
//   `[&str]` (a wide-pointer element) through a mirror of root 1's by-value
//   `self`, element reads through the view, the pair split across x7 and the
//   stack (plain AAPCS64, as in the corpus's `receive7`), and the pair behind
//   narrow scalars that AArch64 macOS packs on the stack where Linux gives
//   each an eight-byte slot. Both panic strategies.
// - `unsized_arguments_admission_controls_aarch64`: an element with drop glue
//   (`[Item]`, `[String]`) must still be refused, since the view alone would
//   make the payload's destruction disappear; an uninhabited companion
//   argument must compile.
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
const CORPUS_PASS: &str = "PASS unsized_arguments checks=114048\n";
const STR_PASS: &str = "PASS unsized_str_arguments checks=22464\n";

struct Temporary(PathBuf);

impl Temporary {
    fn new(stem: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-unsized-{stem}-{}-{nonce}",
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
/// the Linux corpus is compiled with; no `TRUST_CG_*`/`TCG_*` control leaks in.
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

fn sha256(path: &Path, log: &Path) -> String {
    let output = checked(
        Command::new("shasum").args(["-a", "256"]).arg(path),
        30,
        log,
    );
    let hash = output
        .stdout
        .split_whitespace()
        .next()
        .expect("SHA256 digest");
    assert!(hash.len() == 64 && hash.bytes().all(|byte| byte.is_ascii_hexdigit()));
    hash.to_owned()
}

struct Backend {
    path: PathBuf,
    digest: String,
}

impl Backend {
    fn current(dir: &Path) -> Self {
        let path = backend_artifact_support::current_test_backend();
        let digest = sha256(&path, &dir.join("backend-sha256.log"));
        Self { path, digest }
    }

    /// The bridge arguments of a `cg` compile.
    fn args(&self, command: &mut Command) {
        command
            .arg(format!("-Zcodegen-backend={}", self.path.display()))
            .arg(toolchain_support::backend_knobs_arg(&[
                "diag-json",
                "no-proof-certs",
            ]));
    }

    fn unchanged(&self, log: &Path, during: &str) {
        assert_eq!(
            sha256(&self.path, log),
            self.digest,
            "backend changed during {during}"
        );
    }
}

/// One differential: a shared types rlib, a callee crate compiled by each lane
/// at each level, and an LLVM-built driver that must print `expected`.
struct Differential<'a> {
    name: &'a str,
    types_crate: &'a str,
    types: &'a str,
    callee: &'a str,
    driver: &'a str,
    expected: &'a str,
    panic: &'a str,
}

/// Run `case` at O0-O3 on both lanes; returns the number of native runs.
fn run_differential(root: &Path, backend: &Backend, case: &Differential) -> usize {
    let dir = root.join(format!("{}-{}", case.name, case.panic));
    fs::create_dir(&dir).unwrap();
    for (file, text) in [
        ("types.rs", case.types),
        ("callee.rs", case.callee),
        ("driver.rs", case.driver),
    ] {
        fs::write(dir.join(file), text).unwrap();
    }
    let types = dir.join(format!("lib{}.rlib", case.types_crate));
    let extern_types = format!("--extern={}={}", case.types_crate, types.display());
    checked(
        rustc()
            .args(["--crate-type=rlib", "--target", TARGET])
            .arg(format!("--crate-name={}", case.types_crate))
            .arg(format!("-Cpanic={}", case.panic))
            .arg(dir.join("types.rs"))
            .arg("-o")
            .arg(&types),
        180,
        &dir.join("types-compile.log"),
    );
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
                .arg(format!("-Cpanic={}", case.panic))
                .arg(&extern_types);
            if lane == "cg" {
                backend.args(&mut compile);
            }
            compile
                .arg(dir.join("callee.rs"))
                .arg("--out-dir")
                .arg(&out);
            checked(&mut compile, 300, &out.join("compile.log"));
            let mut objects: Vec<_> = fs::read_dir(&out)
                .unwrap()
                .map(|entry| entry.unwrap().path())
                .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
                .collect();
            objects.sort();
            assert!(!objects.is_empty(), "{}: no objects from {stem}", case.name);
            checked(
                Command::new("ar")
                    .arg("crs")
                    .arg(out.join("libcallee.a"))
                    .args(&objects),
                60,
                &out.join("archive.log"),
            );
            let executable = out.join("driver");
            checked(
                rustc()
                    .args(["--target", TARGET, "-Clink-dead-code=yes"])
                    .arg(format!("-Cpanic={}", case.panic))
                    .arg(&extern_types)
                    .arg(dir.join("driver.rs"))
                    .arg("-L")
                    .arg(&out)
                    .arg("-lstatic=callee")
                    .arg("-o")
                    .arg(&executable),
                180,
                &out.join("link.log"),
            );
            let run = checked(&mut Command::new(&executable), 60, &out.join("run.log"));
            assert_eq!(
                run.stdout, case.expected,
                "{} {stem} panic={}: stdout differs; stderr:\n{}",
                case.name, case.panic, run.stderr
            );
            assert!(
                run.stderr.is_empty(),
                "{} {stem}: stderr {}",
                case.name,
                run.stderr
            );
            backend.unchanged(&out.join("backend-sha256.log"), &stem);
            runs += 1;
        }
    }
    runs
}

#[test]
fn unsized_arguments_corpus_matches_llvm_aarch64() {
    darwin_native::require("unsized_arguments_corpus_matches_llvm_aarch64", &["shasum"]);
    let root = Temporary::new("corpus");
    let backend = Backend::current(&root.0);
    let runs = run_differential(
        &root.0,
        &backend,
        &Differential {
            name: "corpus",
            types_crate: "unsized_arguments_types",
            types: include_str!("support/unsized_arguments/types.rs"),
            callee: include_str!("support/unsized_arguments/corpus.rs"),
            driver: include_str!("support/unsized_arguments/driver.rs"),
            expected: CORPUS_PASS,
            panic: "abort",
        },
    );
    assert_eq!(runs, 8);
    println!(
        "TCG_UNSIZED_ARGUMENT_DARWIN_CORPUS executions={runs} checks={} opts=0,1,2,3 panic=abort",
        runs * 114048
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn unsized_str_slice_arguments_match_llvm_aarch64() {
    darwin_native::require(
        "unsized_str_slice_arguments_match_llvm_aarch64",
        &["shasum"],
    );
    let root = Temporary::new("str-slices");
    let backend = Backend::current(&root.0);
    let mut runs = 0;
    for panic in ["abort", "unwind"] {
        runs += run_differential(
            &root.0,
            &backend,
            &Differential {
                name: "str-slices",
                types_crate: "unsized_str_types",
                types: include_str!("support/unsized_arguments_darwin/str_types.rs"),
                callee: include_str!("support/unsized_arguments_darwin/strs.rs"),
                driver: include_str!("support/unsized_arguments_darwin/str_driver.rs"),
                expected: STR_PASS,
                panic,
            },
        );
    }
    assert_eq!(runs, 16);
    println!(
        "TCG_UNSIZED_ARGUMENT_DARWIN_STR_SLICES executions={runs} checks={} opts=0,1,2,3 panic=abort,unwind",
        runs * 22464
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn unsized_arguments_admission_controls_aarch64() {
    darwin_native::require("unsized_arguments_admission_controls_aarch64", &["shasum"]);
    let root = Temporary::new("admission");
    let backend = Backend::current(&root.0);
    let mut refusals = 0;
    let mut compiled = 0;
    for (name, source, refusal) in [
        (
            "uninhabited",
            include_str!("support/unsized_arguments/uninhabited.rs"),
            None,
        ),
        (
            "drop",
            include_str!("support/unsized_arguments/negative_drop.rs"),
            Some("requires unsized payload destruction"),
        ),
        (
            "strings",
            include_str!("support/unsized_arguments_darwin/negative_strings.rs"),
            Some("requires unsized payload destruction"),
        ),
    ] {
        let source_path = root.0.join(format!("{name}.rs"));
        fs::write(&source_path, source).unwrap();
        for opt in OPT_LEVELS {
            for lane in LANES {
                let dir = root.0.join(format!("{name}-{lane}-O{opt}"));
                fs::create_dir(&dir).unwrap();
                let mut command = rustc();
                command
                    .args(["--crate-type=lib", "--emit=obj", "-Cpanic=abort"])
                    .args(["-Ccodegen-units=1", "--target", TARGET])
                    .arg(format!("-Copt-level={opt}"));
                if lane == "cg" {
                    backend.args(&mut command);
                }
                command.arg(&source_path).arg("--out-dir").arg(&dir);
                let output = run_bounded(&mut command, 180, &dir.join("compile.log"));
                match refusal.filter(|_| lane == "cg") {
                    Some(reason) => {
                        assert_eq!(
                            output.status.code(),
                            Some(1),
                            "{name} O{opt}: the bridge must refuse:\n{}",
                            output.stderr
                        );
                        assert!(
                            output.stderr.contains("TCG-UNSIZED-ARG")
                                && output.stderr.contains(reason),
                            "{name} O{opt}: wrong refusal:\n{}",
                            output.stderr
                        );
                        refusals += 1;
                    }
                    None => {
                        assert!(
                            output.status.success(),
                            "{name} {lane} O{opt}:\n{}",
                            output.stderr
                        );
                        compiled += 1;
                    }
                }
                backend.unchanged(&dir.join("backend-sha256.log"), name);
            }
        }
    }
    assert_eq!((refusals, compiled), (8, 16));
    println!(
        "TCG_UNSIZED_ARGUMENT_DARWIN_ADMISSION fixtures=3 compilations=24 refusals={refusals} opts=0,1,2,3"
    );
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}
