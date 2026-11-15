// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Native codegen diagnostic only: Trust verification and proof certificates
// are explicitly off. Another host builds no test, never an unevaluated pass.
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

const TARGET: &str = "aarch64-apple-darwin";
const OPT_LEVELS: &[&str] = &["0", "1", "2", "3"];
const CASES: &[&str] = &[
    "add",
    "sub",
    "mul",
    "div_overflow",
    "rem_overflow",
    "shl",
    "shr",
    "neg",
    "div_zero",
    "rem_zero",
    "bounds",
    "misaligned",
    "null",
    "null_reference",
    "bounds_max",
    "chain",
    "inline",
    "boundary",
];

struct Temporary(PathBuf);

impl Temporary {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-assert-panic-{}-{nonce}",
            std::process::id()
        ));
        // Refuse an existing path rather than clearing a directory selected by
        // an earlier process. Drop removes only this freshly created directory.
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
    // Files prevent a verbose compiler or abort diagnostic from filling a
    // pipe while this thread waits for process completion.
    let stdout_path = log.with_extension("stdout.log");
    let stderr_path = log.with_extension("stderr.log");
    command
        .stdin(Stdio::null())
        .stdout(File::create(&stdout_path).unwrap())
        .stderr(File::create(&stderr_path).unwrap());
    let description = format!("{command:?}");
    let mut child = command
        .spawn()
        .expect("spawn bounded assertion fixture step");
    let started = Instant::now();
    let (status, timed_out) = loop {
        if let Some(status) = child.try_wait().expect("poll assertion fixture child") {
            break (status, false);
        }
        if started.elapsed() >= Duration::from_secs(seconds) {
            child
                .kill()
                .expect("kill timed-out assertion fixture child");
            break (child.wait().expect("reap timed-out fixture child"), true);
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let stdout = fs::read_to_string(stdout_path).unwrap();
    let stderr = fs::read_to_string(stderr_path).unwrap();
    let transcript =
        format!("command: {description}\nstatus: {status}\nstdout:\n{stdout}\nstderr:\n{stderr}");
    fs::write(log, &transcript).expect("retain complete assertion fixture step");
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

fn clear_untracked_controls(command: &mut Command) {
    for (key, _) in std::env::vars_os() {
        if key
            .to_str()
            .is_some_and(|name| name.starts_with("TRUST_CG_") || name.starts_with("TCG_"))
        {
            command.env_remove(key);
        }
    }
}

/// The compiler that built this backend, in its named unverified diagnostic
/// lane. The shared helper supplies -Ztrust-verify=off to BOTH backends.
fn unverified_trust_command() -> Command {
    let mut command = toolchain_support::rustc_command();
    clear_untracked_controls(&mut command);
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

fn mir_function<'a>(mir: &'a str, name: &str) -> &'a str {
    let start = mir
        .find(&format!("fn {name}("))
        .unwrap_or_else(|| panic!("emitted MIR has no mandatory function {name}"));
    let function = &mir[start..];
    let end = function.find("\nfn ").unwrap_or(function.len());
    &function[..end]
}

fn require_mir_inventory(path: &Path, panic: &str, opt: &str, lane: &str) {
    let mir = fs::read_to_string(path).expect("actual emitted source MIR");
    let entries = [
        ("assert_add", "attempt to compute `{} + {}`", false),
        ("assert_sub", "attempt to compute `{} - {}`", false),
        ("assert_mul", "attempt to compute `{} * {}`", false),
        ("assert_div_overflow", "attempt to compute `{} / {}`", false),
        (
            "assert_rem_overflow",
            "attempt to compute the remainder of `{} % {}`",
            false,
        ),
        ("assert_shl", "attempt to shift left by `{}`", false),
        ("assert_shr", "attempt to shift right by `{}`", false),
        ("assert_neg", "attempt to negate `{}`", false),
        ("assert_div_zero", "attempt to divide `{}` by zero", false),
        (
            "assert_rem_zero",
            "attempt to calculate the remainder of `{}` with a divisor of zero",
            false,
        ),
        (
            "assert_bounds",
            "index out of bounds: the length is {} but the index is {}",
            false,
        ),
        (
            "assert_misaligned",
            "misaligned pointer dereference: address must be a multiple of {} but is {}",
            true,
        ),
        ("assert_null", "null pointer dereference occurred", true),
        ("assert_null_reference", "null reference produced", true),
    ];
    for (name, message, nounwind) in entries {
        let function = mir_function(&mir, name);
        let assertions: Vec<_> = function
            .lines()
            .filter(|line| line.contains("assert(") && line.contains(message))
            .collect();
        assert!(
            !assertions.is_empty(),
            "{lane}/{panic}/O{opt}: {name} has no source Assert for {message:?}"
        );
        for assertion in assertions {
            if nounwind {
                assert!(
                    assertion.contains("unwind unreachable"),
                    "pointer Assert lost its nounwind edge: {assertion}"
                );
            } else if panic == "unwind" {
                assert!(
                    assertion.contains("unwind: bb"),
                    "source Assert has no live cleanup edge: {assertion}"
                );
                assert!(
                    function.contains("(cleanup)"),
                    "source Assert's cleanup was not emitted in {name}"
                );
            }
            if name == "assert_bounds" || name == "assert_misaligned" {
                assert!(
                    assertion.matches(',').count() >= 3,
                    "source Assert lost its two failure payload operands: {assertion}"
                );
            }
        }
    }
    let boundary = mir_function(&mir, "assert_plain_div");
    assert!(
        boundary.contains("assert(") && boundary.contains("attempt to divide `{}` by zero"),
        "{lane}/{panic}/O{opt}: the untracked boundary has no source division Assert"
    );
    let chain = mir_function(&mir, "assert_bounds_chain");
    assert!(
        chain.contains("assert_bounds("),
        "{lane}/{panic}/O{opt}: the tracked forwarding chain does not call the compiled bounds body"
    );
    if matches!(opt, "2" | "3") {
        let inlined = mir_function(&mir, "assert_inline_bounds");
        assert!(
            inlined.contains("(inlined #[track_caller] inline_bounds)")
                && inlined.contains("index out of bounds: the length is {} but the index is {}"),
            "{lane}/{panic}/O{opt}: the annotated inline control has no actual inlined Assert scope"
        );
    }
    println!("ASSERT_PANIC_MIR entries=14 lane={lane} strategy={panic} opt={opt}");
}

fn compile_cell(
    root: &Path,
    dir: &Path,
    panic: &str,
    opt: &str,
    backend: Option<&Path>,
) -> PathBuf {
    fs::create_dir(dir).unwrap();
    let mut compile = unverified_trust_command();
    compile
        .args([
            "--crate-name=assert_panic_callee",
            "--crate-type=rlib",
            "--emit=link,mir",
            "-Ccodegen-units=1",
            "-Cforce-unwind-tables=yes",
            "-Coverflow-checks=yes",
            "-Cdebug-assertions=yes",
            "-Zub-checks=yes",
            "--target",
            TARGET,
        ])
        .arg(format!("-Cpanic={panic}"))
        .arg(format!("-Copt-level={opt}"))
        .arg(root.join("corpus.rs"))
        .arg("--out-dir")
        .arg(dir);
    if let Some(backend) = backend {
        let mut argument = std::ffi::OsString::from("-Zcodegen-backend=");
        argument.push(backend);
        compile
            .arg(argument)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    checked(&mut compile, 180, &dir.join("compile.log"));
    let lane = if backend.is_some() { "cg" } else { "llvm" };
    require_mir_inventory(&dir.join("assert_panic_callee.mir"), panic, opt, lane);
    let rlib = dir.join("libassert_panic_callee.rlib");
    assert!(rlib.is_file(), "the mandatory source rlib was not emitted");
    let executable = dir.join("driver");
    checked(
        unverified_trust_command()
            .args(["--target", TARGET, "-Copt-level=2", "-Ccodegen-units=1"])
            .arg(format!("-Cpanic={panic}"))
            .arg("--extern")
            .arg(format!("assert_panic_callee={}", rlib.display()))
            .arg(root.join("driver.rs"))
            .arg("-o")
            .arg(&executable),
        180,
        &dir.join("link.log"),
    );
    executable
}

fn run_case(executable: &Path, case: &str, must_abort: bool, dir: &Path) -> Run {
    let mode = if must_abort { "abort" } else { "catch" };
    let output = run_bounded(
        Command::new("sh")
            .args(["-c", "ulimit -c 0; exec \"$@\"", "assert-panic"])
            .arg(executable)
            .arg(case)
            .arg(mode),
        30,
        &dir.join(format!("run-{case}.log")),
    );
    assert_eq!(
        output
            .stdout
            .lines()
            .filter(|line| line.starts_with("HOOK_OK="))
            .count(),
        1,
        "{case}: exactly one returning hook must run: {}",
        output.stdout
    );
    assert!(
        output.stdout.contains("HOOK_OK=1 "),
        "{case}: wrong payload or full caller location: {}",
        output.stdout
    );
    assert!(
        !output.stdout.contains("AFTER_ASSERT"),
        "{case}: failed assertion continued: {}",
        output.stdout
    );
    if must_abort {
        assert_eq!(
            output.status.signal(),
            Some(6),
            "{case}: must SIGABRT after the hook, status={}\n{}\n{}",
            output.status,
            output.stdout,
            output.stderr
        );
        assert!(
            !output.stdout.contains("DROP="),
            "{case}: abort ran cleanup: {}",
            output.stdout
        );
        assert!(
            !output.stdout.contains("CAUGHT_OK"),
            "{case}: nounwind or abort panic was caught"
        );
    } else {
        assert!(
            output.status.success(),
            "{case}: unwind did not reach Rust catch: {}\n{}\n{}",
            output.status,
            output.stdout,
            output.stderr
        );
        assert!(
            output.stdout.contains("CAUGHT_OK=1"),
            "{case}: caught payload/cleanup was not checked"
        );
        assert_eq!(
            output
                .stdout
                .lines()
                .filter(|line| line.starts_with("DROP="))
                .count(),
            1,
            "{case}: source frame must run exactly one Guard Drop"
        );
        assert!(
            output.stderr.is_empty(),
            "{case}: unexpected unwind stderr: {}",
            output.stderr
        );
    }
    output
}

#[test]
fn source_assert_panic_payload_location_cleanup_match_llvm_aarch64() {
    darwin_native::require("assert_panic_differential_aarch64", &["shasum"]);
    let artifacts = Temporary::new();
    let root = &artifacts.0;
    fs::write(
        root.join("corpus.rs"),
        include_str!("support/assert_panic/corpus.rs"),
    )
    .unwrap();
    fs::write(
        root.join("driver.rs"),
        include_str!("support/assert_panic/driver.rs"),
    )
    .unwrap();
    let backend = backend_artifact_support::current_test_backend();
    let compiler = PathBuf::from(toolchain_support::rustc_driver_command().get_program());
    let backend_digest = sha256(&backend, &root.join("backend-before.log"));
    let compiler_digest = sha256(&compiler, &root.join("compiler-before.log"));
    let mut identity_command = toolchain_support::rustc_driver_command();
    clear_untracked_controls(&mut identity_command);
    let identity = checked(
        identity_command.arg("-vV"),
        30,
        &root.join("compiler-identity.log"),
    );
    assert!(
        identity.stdout.contains("binary: trustc\n"),
        "the selected compiler is not branded Trust"
    );
    assert!(
        identity.stdout.contains(&format!("host: {TARGET}\n")),
        "the selected Trust compiler is not native Darwin ARM64"
    );
    println!(
        "ASSERT_PANIC_COMPILER {}",
        identity.stdout.replace('\n', " | ")
    );
    let (mut cells, mut runs, mut controls, mut caught, mut aborts) = (0, 0, 0, 0, 0);
    for panic in ["unwind", "abort"] {
        for opt in OPT_LEVELS {
            let mut expected = Vec::new();
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("{lane}-{panic}-O{opt}"));
                let executable = compile_cell(
                    root,
                    &dir,
                    panic,
                    opt,
                    (lane == "cg").then_some(backend.as_path()),
                );
                let passing = checked(
                    Command::new(&executable).arg("controls"),
                    30,
                    &dir.join("controls.log"),
                );
                assert!(
                    passing.stdout.contains("CONTROLS_OK=17"),
                    "passing source assertions were not checked"
                );
                assert!(
                    passing.stderr.is_empty(),
                    "passing controls emitted stderr: {}",
                    passing.stderr
                );
                if lane == "llvm" {
                    expected.push(passing.stdout);
                } else {
                    assert_eq!(
                        passing.stdout, expected[0],
                        "passing source controls disagree"
                    );
                }
                controls += 17;
                runs += 1;
                for (index, case) in CASES.iter().enumerate() {
                    let nounwind = matches!(*case, "misaligned" | "null" | "null_reference");
                    let must_abort = panic == "abort" || nounwind;
                    let output = run_case(&executable, case, must_abort, &dir);
                    if lane == "llvm" {
                        expected.push(output.stdout);
                    } else {
                        assert_eq!(
                            output.stdout,
                            expected[index + 1],
                            "{panic}/O{opt}/{case}: hook, location or cleanup differs from LLVM"
                        );
                    }
                    runs += 1;
                    if must_abort {
                        aborts += 1;
                    } else {
                        caught += 1;
                    }
                }
                assert_eq!(
                    sha256(&backend, &dir.join("backend-after.log")),
                    backend_digest,
                    "current test backend changed during qualification"
                );
                assert_eq!(
                    sha256(&compiler, &dir.join("compiler-after.log")),
                    compiler_digest,
                    "selected Trust compiler changed during qualification"
                );
                cells += 1;
            }
            assert_eq!(
                expected.len(),
                19,
                "the mandatory LLVM row denominator changed"
            );
        }
    }
    assert_eq!(
        (cells, runs, controls, caught, aborts),
        (16, 304, 272, 120, 168)
    );
    println!(
        "ASSERT_PANIC_KINDS entries=14 cells=16 cases=18 native_runs=304 controls=272 caught=120 aborts=168 backend_sha256={backend_digest} compiler_sha256={compiler_digest}"
    );
    println!("ASSERT_PANIC_ROUTES llvm_runs=152 cg_runs=152 opts=0,1,2,3 strategies=abort,unwind");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
