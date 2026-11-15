// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Native diagnostic only: Trust verification and proof certificates are off.
// This target's marker requires actual execution, not a compile or early skip.
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
const CASES: &[&str] = &["abi", "cleanup"];
const FOREIGN_CASES: &[&str] = &["foreign-drop", "foreign-guard", "foreign-nested"];
const MAX_SOURCE_OBJECTS: usize = 16;
// The region callee defines several dozen exception-handling frames, and the
// bridge emits each such frame, each runtime helper and each generic instance
// they reach (fn-pointer and vtable shims, `Box<dyn Fn>` drop glue, `ptr::write`
// precondition checks) as an object of its own: 167 at O0 since the review
// rows. The bound only keeps a runaway emission visible.
const MAX_REGION_OBJECTS: usize = 192;
// The unwind-built region callee: 35 bridge objects at every level when its
// rows were measured.
const MAX_UNWIND_REGION_OBJECTS: usize = 48;

// These are source roots, not fabricated MIR or hand-declared panic entries.
// LLVM must first compile them and expose the relevant strategy-specific MIR.
const FOREIGN_POINTER_SOURCE: &str = r#"#![no_std]
extern crate std;
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn foreign_pointer_abort(callback: unsafe extern "C-unwind" fn(u64), value: u64) {
    unsafe { callback(value); }
}
"#;
const FOREIGN_VARIADIC_SOURCE: &str = r#"#![no_std]
extern crate std;
unsafe extern "C-unwind" { fn terminate_foreign_variadic(value: u64, ...); }
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn foreign_variadic_abort(value: u64) {
    unsafe { terminate_foreign_variadic(value, 1_u64); }
}
"#;
const NOUNWIND_SOURCE: &str = r#"#![no_std]
extern crate std;
unsafe extern "C" { fn terminate_nounwind_c(value: u64); }
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe fn nounwind_c_abort(value: u64) {
    unsafe { terminate_nounwind_c(value); }
}
#[unsafe(no_mangle)]
#[inline(never)]
pub fn nounwind_rust_pointer_abort(callback: fn(u64), value: u64) {
    callback(value);
}
"#;
const FOREIGN_ABI_PROBE: &str = r#"#![no_std]
extern crate std;
use terminate_panic_callee as callee;
pub const DROP_EXPORT: extern "C-unwind" fn(u64) -> u64 = callee::terminate_foreign_drop_control;
pub const GUARD_EXPORT: extern "C-unwind" fn(u64) -> u64 = callee::terminate_foreign_guard_control;
"#;

struct Temporary(PathBuf);

impl Temporary {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-terminate-panic-{}-{nonce}",
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
    let mut child = command.spawn().expect("spawn bounded termination step");
    let started = Instant::now();
    let (status, timed_out) = loop {
        if let Some(status) = child.try_wait().expect("poll termination fixture child") {
            break (status, false);
        }
        if started.elapsed() >= Duration::from_secs(seconds) {
            child
                .kill()
                .expect("kill timed-out termination fixture child");
            break (child.wait().expect("reap timed-out fixture child"), true);
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let stdout = fs::read_to_string(stdout_path).unwrap();
    let stderr = fs::read_to_string(stderr_path).unwrap();
    let transcript =
        format!("command: {description}\nstatus: {status}\nstdout:\n{stdout}\nstderr:\n{stderr}");
    fs::write(log, &transcript).expect("retain complete termination fixture step");
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

/// Invoke the exact build compiler in its named Trust unverified diagnostic
/// lane; the shared helper turns frontend verification off for both backends.
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

fn source_objects(dir: &Path, crate_name: &str, lane: &str) -> Vec<PathBuf> {
    source_objects_bounded(dir, crate_name, lane, MAX_SOURCE_OBJECTS)
}

/// rustc's own form for an output name longer than 143 bytes
/// (`maybe_strip_file_name`, rust-lang/rust#49914): a stable hash of the cut
/// prefix in unpadded lowercase hex, a hyphen and the name's tail. A
/// per-function object whose mangled symbol is long gets it.
fn rustc_shortened_object_name(name: &str) -> bool {
    name.len() <= 143
        && name.ends_with(".rcgu.o")
        && name.split_once('-').is_some_and(|(hash, tail)| {
            (1..=16).contains(&hash.len())
                && hash
                    .bytes()
                    .all(|byte| matches!(byte, b'0'..=b'9' | b'a'..=b'f'))
                && !tail.is_empty()
        })
}

fn source_objects_bounded(dir: &Path, crate_name: &str, lane: &str, max: usize) -> Vec<PathBuf> {
    let mut objects = Vec::new();
    for entry in fs::read_dir(dir).expect("read this compile's owned output directory") {
        let entry = entry.expect("read compiler output entry");
        let file_name = entry.file_name();
        let name = file_name
            .to_str()
            .expect("compiler output name must be UTF-8");
        if !name.ends_with(".o") {
            continue;
        }
        assert!(
            entry.file_type().unwrap().is_file() && entry.metadata().unwrap().len() > 0,
            "source compiler emitted an empty or nonregular object: {}",
            entry.path().display()
        );
        let admitted = match lane {
            "llvm" => name == format!("{crate_name}.o"),
            "cg" => {
                name.strip_prefix(&format!("{crate_name}."))
                    .and_then(|rest| rest.strip_suffix(".rcgu.o"))
                    .is_some_and(|module| !module.is_empty())
                    || rustc_shortened_object_name(name)
            }
            _ => panic!("unknown source object lane"),
        };
        assert!(admitted, "unexpected {lane} source object: {name}");
        assert!(
            objects.len() < max,
            "source object set exceeded its fixed bound"
        );
        objects.push(entry.path());
    }
    objects.sort();
    assert!(
        !objects.is_empty() && objects.len() <= max,
        "{lane} source object set must be nonempty and bounded: {objects:?}"
    );
    if lane == "llvm" {
        assert_eq!(
            objects.len(),
            1,
            "LLVM must emit its unique canonical object"
        );
    }
    objects
}

struct ForeignBuild {
    executable: PathBuf,
    objects: Vec<(PathBuf, String)>,
    metadata: (PathBuf, String),
}

fn require_stable_foreign_objects(dir: &Path, lane: &str, build: &ForeignBuild, phase: &str) {
    let paths = source_objects(dir, "terminate_panic_callee", lane);
    let expected: Vec<_> = build.objects.iter().map(|(path, _)| path.clone()).collect();
    assert_eq!(
        paths, expected,
        "compiler-emitted source object set changed during {phase}"
    );
    for (index, (path, digest)) in build.objects.iter().enumerate() {
        assert_eq!(
            sha256(path, &dir.join(format!("object-{index}-{phase}.log"))),
            *digest,
            "actual source object changed during {phase}: {}",
            path.display()
        );
    }
    let (metadata, digest) = &build.metadata;
    assert!(
        fs::symlink_metadata(metadata)
            .unwrap()
            .file_type()
            .is_file()
            && metadata.metadata().unwrap().len() > 0,
        "actual source metadata stopped being a nonempty regular file during {phase}"
    );
    assert_eq!(
        sha256(metadata, &dir.join(format!("metadata-{phase}.log"))),
        *digest,
        "authenticated source C-unwind metadata changed during {phase}"
    );
}

fn mir_function_body(function: &str) -> &str {
    // MIR prints a function's closing brace at column zero. Stopping at the
    // next `fn` instead includes intervening const CTFE bodies: the source
    // location constants have their own Assert/Cleanup MIR even with abort.
    let end = function
        .find("\n}")
        .expect("emitted MIR function has no top-level closing brace");
    let body = &function[..end + 2];
    assert!(
        !body.contains("\nfn ") && !body.contains("\nconst "),
        "emitted MIR function crossed into a separate top-level item"
    );
    body
}

fn mir_function<'a>(mir: &'a str, name: &str) -> &'a str {
    let start = mir
        .find(&format!("fn {name}("))
        .unwrap_or_else(|| panic!("emitted MIR has no mandatory function {name}"));
    mir_function_body(&mir[start..])
}

fn mir_guard_drop(mir: &str) -> &str {
    let headers: Vec<_> = mir
        .lines()
        .filter(|line| line.starts_with("fn <impl at ") && line.contains(">::drop("))
        .collect();
    assert_eq!(
        headers.len(),
        1,
        "source corpus must have exactly one Guard Drop body"
    );
    let start = mir.find(headers[0]).unwrap();
    mir_function_body(&mir[start..])
}

fn mir_cleanup_block<'a>(function: &'a str, label: &str) -> &'a str {
    assert!(
        label.strip_prefix("bb").is_some_and(|number| {
            !number.is_empty() && number.bytes().all(|byte| byte.is_ascii_digit())
        }),
        "source Assert has a malformed MIR cleanup successor {label:?}"
    );
    let header = format!("\n    {label} (cleanup): {{");
    let start = function
        .find(&header)
        .unwrap_or_else(|| panic!("source Assert successor {label} is not a cleanup block"));
    let block = &function[start + 1..];
    let end = block
        .find("\n    }")
        .expect("MIR cleanup block is unterminated");
    &block[..end + 6]
}

fn source_assertions(function: &str) -> Vec<&str> {
    function
        .lines()
        .filter(|line| line.contains("assert(") && line.contains("attempt to divide `{}` by zero"))
        .collect()
}

fn mir_successor<'a>(line: &'a str, edge: &str) -> &'a str {
    line.split_once(edge)
        .map(|(_, rest)| rest.split([',', ']']).next().unwrap().trim())
        .unwrap_or_else(|| panic!("actual MIR terminator lacks {edge:?}: {line}"))
}

fn require_foreign_abort_mir(path: &Path, opt: &str, lane: &str) {
    let mir = fs::read_to_string(path).expect("actual abort source MIR for foreign controls");
    let guard_drop = mir_guard_drop(&mir);
    let callbacks: Vec<_> = guard_drop
        .lines()
        .filter(|line| line.contains("terminate_panic_cleanup_callback("))
        .collect();
    assert_eq!(callbacks.len(), 1, "Guard Drop lost its real foreign call");
    let callback = callbacks[0];
    if !callback.contains("unwind terminate(abi)") {
        let cleanup = mir_cleanup_block(guard_drop, mir_successor(callback, "unwind: "));
        assert!(
            cleanup.lines().any(|line| line.trim() == "terminate(abi);"),
            "{lane}/abort/O{opt}: foreign callback must terminate at the abort-defined Drop's ABI boundary"
        );
        assert!(!cleanup.contains("terminate(cleanup)") && !cleanup.contains("resume;"));
    }
    let source = mir_function(&mir, "terminate_source_foreign_guard");
    assert!(
        !source.contains("assert(") && !source.contains("resume;"),
        "foreign-guard control gained an unrelated source assertion or abort-frame resume"
    );
    let source_calls: Vec<_> = source
        .lines()
        .filter(|line| line.contains("terminate_panic_cleanup_callback("))
        .collect();
    assert_eq!(source_calls.len(), 1, "source foreign call was removed");
    let cleanup = mir_cleanup_block(source, mir_successor(source_calls[0], "unwind: "));
    let cleanup_drops: Vec<_> = cleanup
        .lines()
        .filter(|line| line.contains("drop("))
        .collect();
    assert_eq!(
        cleanup_drops.len(),
        1,
        "foreign exception lost its live Guard Drop"
    );
    assert!(
        cleanup_drops[0].contains("unwind terminate(cleanup)"),
        "source cleanup Drop lost its actual MIR termination contract"
    );
    let terminate = mir_cleanup_block(source, mir_successor(cleanup_drops[0], "return: "));
    assert!(
        terminate
            .lines()
            .any(|line| line.trim() == "terminate(abi);"),
        "{lane}/abort/O{opt}: completed foreign cleanup must reach actual UnwindTerminate(Abi)"
    );
    assert!(
        source
            .lines()
            .any(|line| line.contains("drop(") && line.contains("unwind unreachable")),
        "abort-defined Drop lost its nounwind normal-path edge"
    );
    for export in [
        "terminate_foreign_drop_control",
        "terminate_foreign_guard_control",
    ] {
        let body = mir_function(&mir, export);
        assert!(
            body.lines()
                .any(|line| line.contains(" -> [") && line.contains("unwind unreachable"))
                && !body.contains("(cleanup)"),
            "{lane}/abort/O{opt}: actual C-unwind export must retain its source nounwind call: {body}"
        );
    }
    println!(
        "TERMINATE_FOREIGN_ABORT_MIR cases=3 lane={lane} callee_strategy=abort driver_strategy=unwind opt={opt} guard_cleanup=1 guard_drop_abi=1"
    );
}

fn require_mir_inventory(path: &Path, strategy: &str, opt: &str, lane: &str) {
    let mir = fs::read_to_string(path).expect("actual emitted source MIR");
    let boundary = mir_function(&mir, "terminate_source_boundary");
    let boundary_assertions = source_assertions(boundary);
    assert_eq!(
        boundary_assertions.len(),
        1,
        "{lane}/{strategy}/O{opt}: C boundary lacks its unique source division Assert"
    );
    assert!(
        !boundary.contains("(cleanup)") && !boundary.contains("drop("),
        "{lane}/{strategy}/O{opt}: C-boundary control gained unrelated cleanup"
    );
    let cleanup = mir_function(&mir, "terminate_source_cleanup");
    let cleanup_assertions = source_assertions(cleanup);
    assert_eq!(
        cleanup_assertions.len(),
        1,
        "{lane}/{strategy}/O{opt}: Guard body lacks its unique source division Assert"
    );
    let guard_drop = mir_guard_drop(&mir);
    for callee in [
        "terminate_panic_record_drop(",
        "terminate_panic_cleanup_callback(",
    ] {
        assert_eq!(
            guard_drop
                .lines()
                .filter(|line| line.contains(callee))
                .count(),
            1,
            "{lane}/{strategy}/O{opt}: Guard Drop lacks its unique actual call to {callee}"
        );
    }
    if strategy == "unwind" {
        assert!(
            boundary_assertions[0].contains("unwind terminate(abi)"),
            "C boundary lost Terminate(Abi): {}",
            boundary_assertions[0]
        );
        assert!(
            cleanup_assertions[0].contains("unwind: bb") && cleanup.contains("(cleanup)"),
            "source failure must first reach the Guard cleanup: {}",
            cleanup_assertions[0]
        );
        let successor = cleanup_assertions[0]
            .split_once("unwind: ")
            .and_then(|(_, successor)| successor.strip_suffix("];"))
            .expect("source failure must name its actual cleanup successor");
        let failure_cleanup = mir_cleanup_block(cleanup, successor);
        assert!(
            failure_cleanup.lines().any(|line| {
                line.contains("drop(") && line.contains("unwind terminate(cleanup)")
            }),
            "{lane}/{strategy}/O{opt}: source Assert's cleanup Drop lacks Terminate(InCleanup)"
        );
    } else {
        assert_eq!(strategy, "abort", "unrecognized mandatory panic strategy");
        assert!(
            boundary_assertions[0].contains("unwind unreachable")
                && cleanup_assertions[0].contains("unwind unreachable"),
            "abort-mode source failure must not acquire an unwind edge"
        );
        assert!(
            !cleanup.contains("(cleanup)")
                && cleanup
                    .lines()
                    .any(|line| { line.contains("drop(") && line.contains("unwind unreachable") }),
            "{lane}/{strategy}/O{opt}: abort source Guard body gained failure cleanup or lost its normal Drop"
        );
    }
    println!(
        "TERMINATE_PANIC_MIR cases=2 lane={lane} strategy={strategy} opt={opt} abi_without_cleanup=1"
    );
}

fn compile_cell(
    root: &Path,
    dir: &Path,
    strategy: &str,
    opt: &str,
    backend: Option<&Path>,
) -> PathBuf {
    fs::create_dir(dir).unwrap();
    let mut compile = unverified_trust_command();
    compile
        .args([
            "--crate-name=terminate_panic_callee",
            "--crate-type=rlib",
            "--emit=link,mir",
            "-Ccodegen-units=1",
            "-Cforce-unwind-tables=yes",
            "-Coverflow-checks=yes",
            "--target",
            TARGET,
        ])
        .arg(format!("-Cpanic={strategy}"))
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
    require_mir_inventory(&dir.join("terminate_panic_callee.mir"), strategy, opt, lane);
    let rlib = dir.join("libterminate_panic_callee.rlib");
    assert!(rlib.is_file(), "the mandatory source rlib was not emitted");
    let executable = dir.join("driver");
    checked(
        unverified_trust_command()
            .args(["--target", TARGET, "-Copt-level=2", "-Ccodegen-units=1"])
            .arg(format!("-Cpanic={strategy}"))
            .arg("--extern")
            .arg(format!("terminate_panic_callee={}", rlib.display()))
            .arg(root.join("driver.rs"))
            .arg("-o")
            .arg(&executable),
        180,
        &dir.join("link.log"),
    );
    executable
}

fn run_case(executable: &Path, case: &str, strategy: &str, dir: &Path) -> Run {
    let output = run_bounded(
        Command::new("sh")
            .args(["-c", "ulimit -c 0; exec \"$@\"", "terminate-panic"])
            .arg(executable)
            .arg(case),
        30,
        &dir.join(format!("run-{case}.log")),
    );
    assert_eq!(
        output.status.signal(),
        Some(6),
        "{case}/{strategy}: must SIGABRT, status={}\n{}\n{}",
        output.status,
        output.stdout,
        output.stderr
    );
    assert!(
        !output.stdout.contains("AFTER_TERMINATE"),
        "{case}/{strategy}: termination returned or was caught: {}",
        output.stdout
    );
    let lines: Vec<_> = output.stdout.lines().collect();
    let expected_hooks = if strategy == "abort" {
        1
    } else if case == "abi" {
        2
    } else {
        3
    };
    let hooks: Vec<_> = lines
        .iter()
        .copied()
        .filter(|line| line.starts_with("HOOK "))
        .collect();
    assert_eq!(
        hooks.len(),
        expected_hooks,
        "{case}/{strategy}: wrong hook count: {}",
        output.stdout
    );
    for (index, hook) in hooks.iter().enumerate() {
        assert!(
            hook.starts_with(&format!("HOOK seq={} valid=1 ", index + 1)),
            "{case}/{strategy}: wrong payload, full location or order: {hook}"
        );
    }
    assert!(
        hooks[0].contains("payload=\"attempt to divide by zero\""),
        "the first hook must be the actual source division panic"
    );
    let drops = lines
        .iter()
        .filter(|line| line.starts_with("DROP="))
        .count();
    let callbacks = lines
        .iter()
        .filter(|line| line.starts_with("CALLBACK="))
        .count();
    if strategy == "unwind" {
        let reason = if case == "abi" {
            "panic in a function that cannot unwind"
        } else {
            "panic in a destructor during cleanup"
        };
        assert!(
            hooks
                .last()
                .unwrap()
                .contains(&format!("payload={reason:?}")),
            "{case}: wrong termination reason: {}",
            output.stdout
        );
        assert_eq!(
            lines.last().copied(),
            Some("WRONG_REASON=0"),
            "the wrong-reason control was not checked"
        );
        assert!(
            output
                .stderr
                .contains("thread caused non-unwinding panic. aborting."),
            "{case}: termination did not use the actual nounwind Rust runtime: {}",
            output.stderr
        );
        if case == "cleanup" {
            assert_eq!(
                (drops, callbacks),
                (1, 1),
                "source Guard Drop count differs"
            );
            assert_eq!(lines.len(), 6, "unexpected cleanup event trace");
            assert_eq!(lines[1], "DROP=7");
            assert_eq!(lines[2], "CALLBACK=7");
            assert_eq!(
                lines[3], hooks[1],
                "callback hook ran before the source Drop"
            );
            assert!(hooks[1].contains("payload=\"panic from LLVM cleanup callback\""));
        } else {
            assert_eq!((drops, callbacks), (0, 0), "C boundary gained cleanup");
            assert_eq!(lines.len(), 3, "unexpected C boundary event trace");
        }
    } else {
        assert_eq!((drops, callbacks), (0, 0), "abort ran source cleanup");
        assert_eq!(lines.len(), 1, "abort gained a termination or cleanup hook");
    }
    output
}

fn compile_foreign_driver(
    root: &Path,
    dir: &Path,
    opt: &str,
    lane: &str,
    backend: Option<&Path>,
) -> ForeignBuild {
    // The compiler forbids abort rlib metadata in a final unwind executable.
    // Keep that policy: build actual source-defined C-unwind exports as an
    // object, check their metadata in a same-strategy consumer, then C-link it.
    // A plain C declaration leaves the driver's calls outside its catch table
    // and can terminate search before the source cleanup runs. The matched
    // C-unwind interface retains that caller table; the abort-defined source
    // body still obeys its compiler-derived nounwind ABI and terminates there.
    fs::create_dir(dir).unwrap();
    assert!(
        fs::read_dir(dir).unwrap().next().is_none(),
        "mixed source output directory must start empty"
    );
    let mut compile = unverified_trust_command();
    compile
        .args([
            "--crate-name=terminate_panic_callee",
            "--crate-type=rlib",
            "--emit=obj,mir,metadata",
            "--cfg=terminate_foreign_object",
            "-Ccodegen-units=1",
            "-Cforce-unwind-tables=yes",
            "-Coverflow-checks=yes",
            "-Cpanic=abort",
            "--target",
            TARGET,
        ])
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
    checked(&mut compile, 180, &dir.join("foreign-compile.log"));
    require_foreign_abort_mir(&dir.join("terminate_panic_callee.mir"), opt, lane);
    let objects = source_objects(dir, "terminate_panic_callee", lane)
        .into_iter()
        .enumerate()
        .map(|(index, path)| {
            let digest = sha256(&path, &dir.join(format!("object-{index}-emitted.log")));
            (path, digest)
        })
        .collect();
    let metadata = dir.join("libterminate_panic_callee.rmeta");
    assert!(
        fs::symlink_metadata(&metadata)
            .unwrap()
            .file_type()
            .is_file()
            && metadata.metadata().unwrap().len() > 0,
        "mixed source actual metadata was not emitted as a nonempty regular file"
    );
    let metadata_digest = sha256(&metadata, &dir.join("metadata-emitted.log"));
    checked(
        unverified_trust_command()
            .args([
                "--crate-name=terminate_foreign_abi_probe",
                "--crate-type=lib",
                "--emit=metadata",
                "--target",
                TARGET,
                "-Cpanic=abort",
            ])
            .arg("--extern")
            .arg(format!("terminate_panic_callee={}", metadata.display()))
            .arg(root.join("foreign_abi_probe.rs"))
            .arg("--out-dir")
            .arg(dir),
        180,
        &dir.join("foreign-abi-probe.log"),
    );
    assert!(
        dir.join("libterminate_foreign_abi_probe.rmeta").is_file(),
        "actual C-unwind metadata probe did not complete"
    );
    println!(
        "TERMINATE_FOREIGN_ABORT_ABI lane={lane} opt={opt} actual_c_unwind_exports=2 metadata_probe_strategy=abort hidden_location=0"
    );
    let executable = dir.join("foreign-driver");
    let build = ForeignBuild {
        executable,
        objects,
        metadata: (metadata, metadata_digest),
    };
    require_stable_foreign_objects(dir, lane, &build, "before-link");
    let mut link = unverified_trust_command();
    link.args([
        "--target",
        TARGET,
        "-Copt-level=2",
        "-Ccodegen-units=1",
        "-Cpanic=unwind",
        "--cfg=terminate_foreign_object",
    ]);
    for (object, _) in &build.objects {
        let mut argument = std::ffi::OsString::from("-Clink-arg=");
        argument.push(object);
        link.arg(argument);
    }
    link.arg(root.join("driver.rs"))
        .arg("-o")
        .arg(&build.executable);
    checked(&mut link, 180, &dir.join("foreign-link.log"));
    require_stable_foreign_objects(dir, lane, &build, "after-link");
    build
}

fn run_foreign_case(executable: &Path, case: &str, dir: &Path) -> Run {
    let output = run_bounded(
        Command::new("sh")
            .args(["-c", "ulimit -c 0; exec \"$@\"", "terminate-foreign-abort"])
            .arg(executable)
            .arg(case),
        30,
        &dir.join(format!("run-{case}.log")),
    );
    assert_eq!(
        output.status.signal(),
        Some(6),
        "{case}: foreign exception must SIGABRT at the abort Rust boundary: {}\n{}\n{}",
        output.status,
        output.stdout,
        output.stderr
    );
    assert!(
        !output.stdout.contains("AFTER_TERMINATE"),
        "foreign exception returned or was caught"
    );
    let lines: Vec<_> = output.stdout.lines().collect();
    let hooks: Vec<_> = lines
        .iter()
        .copied()
        .filter(|line| line.starts_with("HOOK "))
        .collect();
    let expected_hooks = 2;
    assert_eq!(
        hooks.len(),
        expected_hooks,
        "{case}: wrong hook count: {}",
        output.stdout
    );
    for (index, hook) in hooks.iter().enumerate() {
        assert!(
            hook.starts_with(&format!("HOOK seq={} valid=1 ", index + 1)),
            "{case}: wrong foreign payload, full location or order: {hook}"
        );
        let expected = if case != "foreign-nested" && index + 1 == expected_hooks {
            "panic in a function that cannot unwind"
        } else {
            "panic from LLVM cleanup callback"
        };
        assert!(
            hook.contains(&format!("payload={expected:?}")),
            "{case}: wrong reason/payload: {hook}"
        );
    }
    if case == "foreign-nested" {
        // LLVM's abort-defined cleanup Drop is a nounwind plain call. Its
        // callsite is absent from this source frame's LSDA. The second panic's
        // search therefore fails there before an inner Abi landing pad can
        // run. Match that specific runtime path, never generic SIGABRT credit
        // or a fabricated Abi/InCleanup reason hook.
        assert_eq!(
            output.stderr, "fatal runtime error: failed to initiate panic, error 3, aborting\n",
            "nested foreign panic did not take the authenticated fatal-search path"
        );
        assert!(
            !lines.iter().any(|line| line.starts_with("WRONG_REASON=")),
            "nested fatal search must not claim a reached reason hook"
        );
    } else {
        assert_eq!(lines.last().copied(), Some("WRONG_REASON=0"));
        assert_eq!(
            output.stderr, "thread caused non-unwinding panic. aborting.\n",
            "foreign panic did not reach the actual Abi nounwind runtime entry"
        );
    }
    let drops = lines
        .iter()
        .filter(|line| line.starts_with("DROP="))
        .count();
    let callbacks = lines
        .iter()
        .filter(|line| line.starts_with("CALLBACK="))
        .count();
    assert_eq!(drops, 1, "{case}: lost or repeated source Guard Drop");
    match case {
        "foreign-drop" => {
            assert_eq!(callbacks, 1);
            assert_eq!(
                lines,
                vec!["DROP=7", "CALLBACK=7", hooks[0], hooks[1], "WRONG_REASON=0"]
            );
        }
        "foreign-guard" => {
            assert_eq!(callbacks, 2);
            assert_eq!(
                lines,
                vec![
                    "CALLBACK=7",
                    hooks[0],
                    "DROP=7",
                    "CALLBACK=7",
                    hooks[1],
                    "WRONG_REASON=0"
                ]
            );
        }
        "foreign-nested" => {
            assert_eq!(callbacks, 2);
            assert_eq!(
                lines,
                vec!["CALLBACK=7", hooks[0], "DROP=7", "CALLBACK=7", hooks[1]]
            );
        }
        _ => panic!("unknown mandatory foreign-abort case"),
    }
    output
}

fn compile_source_control(
    source: &Path,
    dir: &Path,
    name: &str,
    opt: &str,
    backend: Option<&Path>,
    disable_unwind: bool,
) -> Run {
    fs::create_dir(dir).unwrap();
    let mut compile = unverified_trust_command();
    compile
        .args([
            "--crate-type=lib",
            "--emit=obj,mir",
            "-Ccodegen-units=1",
            "-Cforce-unwind-tables=yes",
            "-Coverflow-checks=yes",
            "-Cpanic=abort",
            "--target",
            TARGET,
        ])
        .arg(format!("--crate-name={name}"))
        .arg(format!("-Copt-level={opt}"))
        .arg(source)
        .arg("--out-dir")
        .arg(dir);
    if let Some(backend) = backend {
        let mut argument = std::ffi::OsString::from("-Zcodegen-backend=");
        argument.push(backend);
        let knobs: &[&str] = if disable_unwind {
            &["no-proof-certs", "disable-unwind"]
        } else {
            &["no-proof-certs"]
        };
        compile
            .arg(argument)
            .arg(toolchain_support::backend_knobs_arg(knobs));
    } else {
        assert!(
            !disable_unwind,
            "backend control must never be silently omitted"
        );
    }
    run_bounded(&mut compile, 180, &dir.join("compile.log"))
}

fn require_source_control_success(output: &Run, dir: &Path, name: &str, lane: &str) {
    assert!(
        output.status.success(),
        "mandatory compile-only control failed at {}: {}\n{}\n{}",
        dir.display(),
        output.status,
        output.stdout,
        output.stderr
    );
    source_objects(dir, name, lane);
}

fn require_single_call_mir(path: &Path, function: &str, foreign: bool) {
    let mir = fs::read_to_string(path).expect("source-control actual emitted MIR");
    let body = mir_function(&mir, function);
    let calls: Vec<_> = body.lines().filter(|line| line.contains(" -> [")).collect();
    assert_eq!(
        calls.len(),
        1,
        "source control must retain its unique call: {body}"
    );
    if foreign {
        // The abort frame's termination edge has two MIR spellings: inline
        // `unwind terminate(abi)`, or a cleanup successor whose sole statement
        // is `terminate(abi);`. The selected compiler emits the latter for
        // both controls at every opt level, as it does for the Guard Drop's
        // foreign call (`require_foreign_abort_mir` accepts the same two).
        // Anything else -- a resume, a Drop, `terminate(cleanup)`, an
        // unreachable or continuing edge -- is still refused.
        if !calls[0].contains("unwind terminate(abi)") {
            let cleanup = mir_cleanup_block(body, mir_successor(calls[0], "unwind: "));
            let statements: Vec<_> = cleanup
                .lines()
                .skip(1)
                .map(str::trim)
                .filter(|line| !line.is_empty() && *line != "}")
                .collect();
            assert_eq!(
                statements,
                ["terminate(abi);"],
                "foreign source control lacks its real abort-frame termination edge: {}\n{cleanup}",
                calls[0]
            );
        }
    } else {
        assert!(
            calls[0].contains("unwind unreachable") && !body.contains("(cleanup)"),
            "nounwind source control unexpectedly gained a foreign unwind continuation: {body}"
        );
    }
}

fn require_named_foreign_refusal(output: &Run, reason: &str, dir: &Path) {
    assert!(
        !output.status.success() && output.status.signal().is_none(),
        "mandatory refusal must be an actual compiler error at {}: {}\n{}\n{}",
        dir.display(),
        output.status,
        output.stdout,
        output.stderr
    );
    assert!(
        output.stderr.contains("[TCG-EH-FOREIGN-ABORT]") && output.stderr.contains(reason),
        "source root refused for the wrong reason at {}: {}\n{}",
        dir.display(),
        output.stdout,
        output.stderr
    );
}

fn run_foreign_source_controls(root: &Path, backend: &Path) {
    for (name, source) in [
        ("foreign_pointer", FOREIGN_POINTER_SOURCE),
        ("foreign_variadic", FOREIGN_VARIADIC_SOURCE),
        ("nounwind", NOUNWIND_SOURCE),
    ] {
        fs::write(root.join(format!("{name}.rs")), source).unwrap();
    }
    let (mut refusals, mut nounwind_roots, mut llvm_roots) = (0, 0, 0);
    for opt in OPT_LEVELS {
        let disabled = root.join(format!("refuse-disabled-O{opt}"));
        let output = compile_source_control(
            &root.join("corpus.rs"),
            &disabled,
            "terminate_panic_callee",
            opt,
            Some(backend),
            true,
        );
        require_named_foreign_refusal(
            &output,
            "foreign-exception abort adapter is unavailable or EH is disabled",
            &disabled,
        );
        refusals += 1;
        for (name, function, reason) in [
            (
                "foreign_pointer",
                "foreign_pointer_abort",
                "foreign function-pointer abort continuation is not modeled",
            ),
            (
                "foreign_variadic",
                "foreign_variadic_abort",
                "variadic foreign abort continuation is not modeled",
            ),
        ] {
            let source = root.join(format!("{name}.rs"));
            let llvm_dir = root.join(format!("source-llvm-{name}-O{opt}"));
            let llvm = compile_source_control(&source, &llvm_dir, name, opt, None, false);
            require_source_control_success(&llvm, &llvm_dir, name, "llvm");
            require_single_call_mir(&llvm_dir.join(format!("{name}.mir")), function, true);
            llvm_roots += 1;
            let cg_dir = root.join(format!("source-cg-{name}-O{opt}"));
            let cg = compile_source_control(&source, &cg_dir, name, opt, Some(backend), false);
            require_named_foreign_refusal(&cg, reason, &cg_dir);
            refusals += 1;
        }
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("source-{lane}-nounwind-O{opt}"));
            let output = compile_source_control(
                &root.join("nounwind.rs"),
                &dir,
                "nounwind",
                opt,
                (lane == "cg").then_some(backend),
                lane == "cg",
            );
            require_source_control_success(&output, &dir, "nounwind", lane);
            for function in ["nounwind_c_abort", "nounwind_rust_pointer_abort"] {
                require_single_call_mir(&dir.join("nounwind.mir"), function, false);
            }
            if lane == "cg" {
                nounwind_roots += 2;
            } else {
                llvm_roots += 2;
            }
        }
    }
    assert_eq!((refusals, nounwind_roots, llvm_roots), (12, 8, 16));
    println!(
        "TERMINATE_FOREIGN_ABORT_BOUNDARY_CONTROLS expected_refusals=12 compiled_nounwind_roots=8 llvm_source_roots=16 native_runs=0 opts=0,1,2,3"
    );
}

#[test]
fn source_termination_reasons_payload_location_and_drops_match_llvm_aarch64() {
    darwin_native::require("terminate_panic_differential_aarch64", &["shasum"]);
    let artifacts = Temporary::new();
    let root = &artifacts.0;
    // One physical path per source, shared by every LLVM and CG cell, makes
    // full caller locations comparable without rewriting or normalizing them.
    fs::write(
        root.join("corpus.rs"),
        include_str!("support/terminate_panic/corpus.rs"),
    )
    .unwrap();
    fs::write(
        root.join("driver.rs"),
        include_str!("support/terminate_panic/driver.rs"),
    )
    .unwrap();
    fs::write(root.join("foreign_abi_probe.rs"), FOREIGN_ABI_PROBE).unwrap();
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
        "TERMINATE_PANIC_COMPILER {}",
        identity.stdout.replace('\n', " | ")
    );
    let (mut cells, mut runs, mut controls, mut aborts, mut hooks, mut drops) = (0, 0, 0, 0, 0, 0);
    for strategy in ["unwind", "abort"] {
        for opt in OPT_LEVELS {
            let mut expected = Vec::new();
            for lane in ["llvm", "cg"] {
                let dir = root.join(format!("{lane}-{strategy}-O{opt}"));
                let executable = compile_cell(
                    root,
                    &dir,
                    strategy,
                    opt,
                    (lane == "cg").then_some(backend.as_path()),
                );
                let passing = checked(
                    Command::new(&executable).arg("controls"),
                    30,
                    &dir.join("controls.log"),
                );
                assert_eq!(
                    passing.stdout,
                    "DROP=7\nCALLBACK=7\nCONTROLS_OK=2 HOOKS=0 DROPS=1 CALLBACKS=1\n",
                    "passing source operations, Drop and callback were not checked"
                );
                assert!(passing.stderr.is_empty(), "passing controls emitted stderr");
                if lane == "llvm" {
                    expected.push((passing.stdout, passing.stderr));
                } else {
                    assert_eq!(
                        (passing.stdout, passing.stderr),
                        expected[0],
                        "passing source controls disagree with LLVM"
                    );
                }
                controls += 2;
                runs += 1;
                for (index, case) in CASES.iter().enumerate() {
                    let output = run_case(&executable, case, strategy, &dir);
                    if lane == "llvm" {
                        expected.push((output.stdout, output.stderr));
                    } else {
                        assert_eq!(
                            (output.stdout, output.stderr),
                            expected[index + 1],
                            "{strategy}/O{opt}/{case}: complete hook payload/location/reason/Drop trace differs from LLVM"
                        );
                    }
                    hooks += if strategy == "abort" {
                        1
                    } else if *case == "abi" {
                        2
                    } else {
                        3
                    };
                    drops += usize::from(strategy == "unwind" && *case == "cleanup");
                    runs += 1;
                    aborts += 1;
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
            assert_eq!(expected.len(), 3, "the mandatory LLVM denominator changed");
        }
    }
    assert_eq!(
        (cells, runs, controls, aborts, hooks, drops),
        (16, 48, 32, 32, 56, 8)
    );
    println!(
        "TERMINATE_PANIC_KINDS reasons=2 cells=16 cases=2 native_runs=48 controls=32 aborts=32 hooks=56 cleanup_drops=8 backend_sha256={backend_digest} compiler_sha256={compiler_digest}"
    );
    println!("TERMINATE_PANIC_ROUTES llvm_runs=24 cg_runs=24 opts=0,1,2,3 strategies=abort,unwind");
    // The original same-strategy matrix cannot establish foreign unwinding
    // under abort: its abort driver cannot throw. Retain all original rows,
    // then link actual abort source C objects to a genuine unwind LLVM driver.
    let (mut foreign_cells, mut foreign_runs, mut foreign_controls, mut foreign_aborts) =
        (0, 0, 0, 0);
    let (mut foreign_hooks, mut foreign_drops, mut foreign_callbacks) = (0, 0, 0);
    let (mut reached_abi, mut fatal_search) = (0, 0);
    for opt in OPT_LEVELS {
        let mut expected = Vec::new();
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("{lane}-foreign-abort-O{opt}"));
            let build = compile_foreign_driver(
                root,
                &dir,
                opt,
                lane,
                (lane == "cg").then_some(backend.as_path()),
            );
            let passing = checked(
                Command::new(&build.executable).arg("foreign-controls"),
                30,
                &dir.join("foreign-controls.log"),
            );
            require_stable_foreign_objects(&dir, lane, &build, "after-controls");
            assert_eq!(
                passing.stdout,
                "DROP=7\nCALLBACK=7\nCALLBACK=7\nDROP=7\nCALLBACK=7\nFOREIGN_CONTROLS_OK=2 HOOKS=0 DROPS=2 CALLBACKS=3\n",
                "foreign passing controls lost a normal-path call or source Guard Drop"
            );
            assert!(
                passing.stderr.is_empty(),
                "foreign passing controls emitted stderr"
            );
            if lane == "llvm" {
                expected.push((passing.stdout, passing.stderr));
            } else {
                assert_eq!(
                    (passing.stdout, passing.stderr),
                    expected[0],
                    "mixed-strategy passing controls disagree with LLVM"
                );
            }
            foreign_runs += 1;
            foreign_controls += 2;
            for (index, case) in FOREIGN_CASES.iter().enumerate() {
                let output = run_foreign_case(&build.executable, case, &dir);
                require_stable_foreign_objects(&dir, lane, &build, &format!("after-{case}"));
                if lane == "llvm" {
                    expected.push((output.stdout, output.stderr));
                } else {
                    assert_eq!(
                        (output.stdout, output.stderr),
                        expected[index + 1],
                        "abort-callee/unwind-driver/O{opt}/{case}: full foreign payload/location/reason/Drop/callback trace differs from LLVM"
                    );
                }
                foreign_runs += 1;
                foreign_aborts += 1;
                foreign_hooks += 2;
                foreign_drops += 1;
                foreign_callbacks += if *case == "foreign-drop" { 1 } else { 2 };
                if *case == "foreign-nested" {
                    fatal_search += 1;
                } else {
                    reached_abi += 1;
                }
            }
            assert_eq!(
                sha256(&backend, &dir.join("foreign-backend-after.log")),
                backend_digest,
                "test backend changed during mixed-strategy qualification"
            );
            assert_eq!(
                sha256(&compiler, &dir.join("foreign-compiler-after.log")),
                compiler_digest,
                "selected Trust compiler changed during mixed-strategy qualification"
            );
            println!(
                "TERMINATE_FOREIGN_ABORT_OBJECT_SET lane={lane} opt={opt} emitted={} linked={} stable=1 max={MAX_SOURCE_OBJECTS}",
                build.objects.len(),
                build.objects.len()
            );
            foreign_cells += 1;
        }
        assert_eq!(
            expected.len(),
            4,
            "mandatory mixed LLVM denominator changed"
        );
    }
    assert_eq!(
        (
            foreign_cells,
            foreign_runs,
            foreign_controls,
            foreign_aborts,
            foreign_hooks,
            foreign_drops,
            foreign_callbacks,
            reached_abi,
            fatal_search
        ),
        (8, 32, 16, 24, 48, 24, 40, 16, 8)
    );
    println!(
        "TERMINATE_FOREIGN_ABORT_KINDS cells=8 cases=3 native_runs=32 controls=16 aborts=24 hooks=48 throw_drops=24 throw_callbacks=40"
    );
    println!(
        "TERMINATE_FOREIGN_ABORT_OUTCOMES reached_abi=16 fatal_search=8 nested_reason_hooks=0"
    );
    println!(
        "TERMINATE_FOREIGN_ABORT_OBJECTS cells=8 complete_sets=8 stable=1 max_per_cell={MAX_SOURCE_OBJECTS}"
    );
    println!(
        "TERMINATE_FOREIGN_ABORT_ROUTES llvm_runs=16 cg_runs=16 opts=0,1,2,3 callee_strategy=abort driver_strategy=unwind"
    );
    run_foreign_source_controls(root, &backend);
    assert_eq!(
        sha256(&backend, &root.join("backend-final.log")),
        backend_digest,
        "test backend changed during mandatory source controls"
    );
    assert_eq!(
        sha256(&compiler, &root.join("compiler-final.log")),
        compiler_digest,
        "selected Trust compiler changed during mandatory source controls"
    );
    assert_eq!(
        runs + foreign_runs,
        80,
        "complete native denominator changed"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// How a region row ends under LLVM, and therefore must under the backend.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum RegionOutcome {
    /// Nothing panics: the frame returns its argument.
    Returns,
    /// The phase-one search reaches a gap in a frame's table (a region of
    /// direct `nounwind` calls only): the Rust personality reports
    /// `_URC_FATAL_PHASE1_ERROR` after the panic's own hooks.
    FatalSearch,
    /// The search finds a handler (an outer one, through covered regions, or
    /// the panicking `extern "C"` frame's own empty filter), and phase two
    /// enters the nested callee's Abi termination.
    ReachedAbi,
    /// The search keeps unwinding through a covered region to the driver's
    /// `catch_unwind`, and phase two reaches it: one hook, then the caught
    /// payload.
    Caught,
}

/// One region row: `frame` (a `regions.rs` export) is called with `arg`, the
/// callback panics at each 1-based call sequence number set in `mask`, and
/// `catch` wraps the call in `catch_unwind`. LLVM's outcome is `outcome` at
/// O1-O3 and `outcome_o0` at O0. The backend's must equal LLVM's run exactly,
/// except where `earlier_o0` pins OD-58's accepted direction at O0: there its
/// search fails phase one (`FatalSearch`) where LLVM's continues.
struct RegionRow {
    name: &'static str,
    frame: &'static str,
    mask: u64,
    catch: bool,
    arg: u64,
    outcome_o0: RegionOutcome,
    outcome: RegionOutcome,
    earlier_o0: bool,
}

/// What one region-driver run names: the export `frame`, the callback panic
/// `mask`, whether the driver wraps the call in `catch_unwind`, and `arg`.
#[derive(Clone, Copy)]
struct RegionCall {
    name: &'static str,
    frame: &'static str,
    mask: u64,
    catch: bool,
    arg: u64,
}

impl RegionRow {
    fn call(&self) -> RegionCall {
        RegionCall {
            name: self.name,
            frame: self.frame,
            mask: self.mask,
            catch: self.catch,
            arg: self.arg,
        }
    }

    fn outcome_at(&self, opt: &str) -> RegionOutcome {
        if opt == "0" {
            self.outcome_o0
        } else {
            self.outcome
        }
    }

    /// The backend's own outcome at `opt` (LLVM's but for `earlier_o0`).
    fn backend_outcome_at(&self, opt: &str) -> RegionOutcome {
        if opt == "0" && self.earlier_o0 {
            RegionOutcome::FatalSearch
        } else {
            self.outcome_at(opt)
        }
    }
}

const fn region(
    name: &'static str,
    frame: &'static str,
    mask: u64,
    catch: bool,
    arg: u64,
    outcome: RegionOutcome,
) -> RegionRow {
    region_by_opt(name, frame, mask, catch, arg, outcome, outcome)
}

/// A row whose LLVM outcome at O0 differs from O1-O3.
const fn region_by_opt(
    name: &'static str,
    frame: &'static str,
    mask: u64,
    catch: bool,
    arg: u64,
    outcome_o0: RegionOutcome,
    outcome: RegionOutcome,
) -> RegionRow {
    RegionRow {
        name,
        frame,
        mask,
        catch,
        arg,
        outcome_o0,
        outcome,
        earlier_o0: false,
    }
}

/// A row whose backend run at O0 fails phase one earlier than LLVM's
/// (`RegionRow::earlier_o0`), an outcome OD-58 accepts; LLVM's own outcomes
/// stay pinned per level.
const fn region_earlier_o0(
    name: &'static str,
    frame: &'static str,
    mask: u64,
    catch: bool,
    arg: u64,
    outcome_o0: RegionOutcome,
    outcome: RegionOutcome,
) -> RegionRow {
    RegionRow {
        earlier_o0: true,
        ..region_by_opt(name, frame, mask, catch, arg, outcome_o0, outcome)
    }
}

const REGION_ROWS: &[RegionRow] = &[
    // Controls: nothing panics, or the panic reaches an explicit handler.
    region("direct-ok", "direct", 0, true, 5, RegionOutcome::Returns),
    region(
        "indirect-ok",
        "indirect",
        0,
        true,
        5,
        RegionOutcome::Returns,
    ),
    region("mixed-ok", "mixed", 0, true, 5, RegionOutcome::Returns),
    region("loop-ok", "loop", 0, true, 3, RegionOutcome::Returns),
    region(
        "per-region-ok",
        "per_region",
        0,
        true,
        5,
        RegionOutcome::Returns,
    ),
    region(
        "two-guards",
        "two_guards",
        1,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    region(
        "box-dyn-guard",
        "box_dyn_guard",
        1,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    // A region of direct `nounwind` calls only is a gap, as in LLVM's table.
    // The full-coverage filler kept unwinding through each of these.
    region("direct", "direct", 2, true, 5, RegionOutcome::FatalSearch),
    region(
        "direct-uncaught",
        "direct",
        2,
        false,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "two-guards-nested-second",
        "two_guards",
        3,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "two-guards-nested-first",
        "two_guards",
        5,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "loop-nested",
        "loop",
        12,
        true,
        3,
        RegionOutcome::FatalSearch,
    ),
    region(
        "box-dyn-guard-nested",
        "box_dyn_guard",
        3,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "between-invokes",
        "between_invokes",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "per-region-direct",
        "per_region",
        8,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    // A region holding an indirect call keeps unwinding, a direct `nounwind`
    // call in the same region included. A handlers-only table failed phase
    // one at each of these.
    region(
        "indirect",
        "indirect",
        2,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    region(
        "indirect-uncaught",
        "indirect",
        2,
        false,
        5,
        RegionOutcome::ReachedAbi,
    ),
    region("dyn", "dyn", 2, true, 5, RegionOutcome::ReachedAbi),
    region(
        "c-pointer",
        "c_pointer",
        2,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    region(
        "indirect-first",
        "indirect_first",
        1,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    region(
        "guard-indirect",
        "guard_indirect",
        2,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    region(
        "mixed-direct",
        "mixed",
        2,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    region(
        "mixed-indirect",
        "mixed",
        4,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    region(
        "per-region-indirect",
        "per_region",
        2,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    // `memcmp` (rustc's attribute-less `compare_bytes` libcall) is `nounwind`
    // to LLVM only through its attribute inference above O0. At O0 its region
    // keeps unwinding, so the driver catches the panic of the `nounwind` Rust
    // callback that follows it; at O1-O3 the region is a gap.
    region("memcmp-ok", "memcmp", 0, true, 5, RegionOutcome::Returns),
    region_by_opt(
        "memcmp-rust-callback",
        "memcmp",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    // A call the backend creates itself, then the `nounwind` Rust callback.
    // LLVM expands, folds or inlines the operation (a gap: the search fails)
    // or emits a libcall that may unwind (covered: the driver catches), per
    // level; the backend's record of the callee must agree.
    region_by_opt(
        "array-fill",
        "array_fill",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region(
        "array-fill-large",
        "array_fill_large",
        2,
        true,
        5,
        RegionOutcome::Caught,
    ),
    region_by_opt(
        "memset",
        "memset",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region("fma", "fma", 2, true, 5, RegionOutcome::FatalSearch),
    region_by_opt(
        "powi-constant",
        "powi",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region_by_opt(
        "sin-constant",
        "sin_constant",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region(
        "sin-runtime",
        "sin_runtime",
        2,
        true,
        5,
        RegionOutcome::Caught,
    ),
    region(
        "i128-checked-mul",
        "i128_checked_mul",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region("i128-div", "i128_div", 2, true, 5, RegionOutcome::Caught),
    region("rotate", "rotate", 2, true, 5, RegionOutcome::FatalSearch),
    region("print-ok", "print", 0, true, 5, RegionOutcome::Returns),
    region("print", "print", 2, true, 5, RegionOutcome::FatalSearch),
    // The frame's last call: never a tail branch out of this frame's table.
    region("tail-ok", "tail", 0, true, 5, RegionOutcome::Returns),
    region("tail", "tail", 2, true, 5, RegionOutcome::FatalSearch),
    // Calls the backend creates for an operation LLVM expands, narrows, folds
    // or deletes on its own: recorded `nounwind` wherever LLVM may leave no
    // call, so the search never keeps unwinding where LLVM's fails.
    // The dividends pass through `u128::from`, an `#[inline(always)]`
    // conversion LLVM's O0 AlwaysInliner inlines: the O0 rule cannot show its
    // result is a runtime value (an inlined body may return a constant), so it
    // records the routine and the backend's search fails phase one earlier.
    region_earlier_o0(
        "u128-div-literal",
        "u128_div_literal",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region_earlier_o0(
        "u128-narrow-div",
        "u128_narrow_div",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region(
        "dead-f64-to-i128",
        "dead_f64_to_i128",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region_by_opt(
        "fill-folded",
        "fill_folded",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region_by_opt(
        "sin-derived",
        "sin_derived",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    // The TLV descriptor's thunk call never unwinds and is recorded so at
    // every level; LLVM's own thunk call at O0 covers its region, so there the
    // backend's search fails phase one earlier.
    region_earlier_o0(
        "tls-constant",
        "tls_constant",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    // Calls through a `fn` pointer or a vtable whose target the frame states:
    // LLVM calls the `nounwind` target directly (a gap), and so does the
    // backend.
    region(
        "fn-pointer-local",
        "fn_pointer_local",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "fn-pointer-static",
        "fn_pointer_static",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region_by_opt(
        "fn-pointer-table",
        "fn_pointer_table",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region(
        "fn-pointer-closure",
        "fn_pointer_closure",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region_by_opt(
        "dyn-known",
        "dyn_known",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region(
        "box-dyn-fn",
        "box_dyn_fn",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region_by_opt(
        "box-dyn-opaque",
        "box_dyn_opaque",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
        RegionOutcome::Caught,
    ),
    // A frame with no foreign edge of its own that LLVM gives a table by
    // inlining a callee holding a terminate pad.
    region(
        "inlined-pad-ok",
        "inlined_pad",
        0,
        true,
        5,
        RegionOutcome::Returns,
    ),
    region_by_opt(
        "inlined-pad",
        "inlined_pad",
        1,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region(
        "inlined-pad-foreign",
        "inlined_pad",
        2,
        true,
        5,
        RegionOutcome::ReachedAbi,
    ),
    // Review rows (2026-10-10). A parameter, a raw-written local or a
    // `Pin<&dyn>` receiver states no callee: the call stays indirect, and the
    // callback ids show which target ran (a Rust `fn` pointer call is
    // `nounwind` under `panic=abort`, so its region is a gap either way).
    // Constant operands fold at O0 too; `X / X` folds above O0.
    region(
        "fn-pointer-param",
        "fn_pointer_param",
        2,
        true,
        5,
        RegionOutcome::Caught,
    ),
    region(
        "closure-param",
        "closure_param",
        2,
        true,
        5,
        RegionOutcome::Caught,
    ),
    region("dyn-param", "dyn_param", 2, true, 5, RegionOutcome::Caught),
    region_by_opt(
        "box-dyn-param",
        "box_dyn_param",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
        RegionOutcome::Caught,
    ),
    region(
        "closure-raw-written",
        "closure_raw_written",
        2,
        true,
        5,
        RegionOutcome::Caught,
    ),
    region("pin-dyn", "pin_dyn", 0, true, 5, RegionOutcome::Returns),
    region(
        "u128-const-div",
        "u128_const_div",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "f64-const-rem",
        "f64_const_rem",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region_by_opt(
        "u128-self-div",
        "u128_self_div",
        2,
        true,
        5,
        RegionOutcome::Caught,
        RegionOutcome::FatalSearch,
    ),
    region(
        "u128-from-const-div",
        "u128_from_const_div",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "slice-len-div",
        "slice_len_div",
        2,
        true,
        5,
        RegionOutcome::FatalSearch,
    ),
    region(
        "field-raw-written",
        "field_raw_written",
        2,
        true,
        5,
        RegionOutcome::Caught,
    ),
];

const REGION_CALLBACK_PAYLOAD: &str = "region callback panic";
const REGION_ABI_REASON: &str = "panic in a function that cannot unwind";

/// One region test's callee crate (built by the lane under test with `strategy`)
/// and the LLVM-built `-Cpanic=unwind` driver it is linked into.
struct RegionBuild {
    crate_name: &'static str,
    source: &'static str,
    driver: &'static str,
    strategy: &'static str,
    max_objects: usize,
}

const ABORT_REGIONS: RegionBuild = RegionBuild {
    crate_name: "terminate_region_callee",
    source: "regions.rs",
    driver: "regions_driver.rs",
    strategy: "abort",
    max_objects: MAX_REGION_OBJECTS,
};

const UNWIND_REGIONS: RegionBuild = RegionBuild {
    crate_name: "terminate_unwind_region_callee",
    source: "unwind_regions.rs",
    driver: "unwind_regions_driver.rs",
    strategy: "unwind",
    max_objects: MAX_UNWIND_REGION_OBJECTS,
};

fn compile_region_driver(
    root: &Path,
    dir: &Path,
    opt: &str,
    backend: Option<&Path>,
    build: &RegionBuild,
) -> PathBuf {
    fs::create_dir(dir).unwrap();
    let mut compile = unverified_trust_command();
    compile
        .arg(format!("--crate-name={}", build.crate_name))
        .args([
            "--crate-type=rlib",
            "--emit=obj",
            "-Ccodegen-units=1",
            "-Cforce-unwind-tables=yes",
            "-Coverflow-checks=yes",
        ])
        .arg(format!("-Cpanic={}", build.strategy))
        .args(["--target", TARGET])
        .arg(format!("-Copt-level={opt}"))
        .arg(root.join(build.source))
        .arg("--out-dir")
        .arg(dir);
    if let Some(backend) = backend {
        let mut argument = std::ffi::OsString::from("-Zcodegen-backend=");
        argument.push(backend);
        compile
            .arg(argument)
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    checked(&mut compile, 180, &dir.join("regions-compile.log"));
    let lane = if backend.is_some() { "cg" } else { "llvm" };
    let objects = source_objects_bounded(dir, build.crate_name, lane, build.max_objects);
    let executable = dir.join("regions-driver");
    let mut link = unverified_trust_command();
    link.args([
        "--target",
        TARGET,
        "-Copt-level=2",
        "-Ccodegen-units=1",
        "-Cpanic=unwind",
    ]);
    for object in &objects {
        let mut argument = std::ffi::OsString::from("-Clink-arg=");
        argument.push(object);
        link.arg(argument);
    }
    link.arg(root.join(build.driver)).arg("-o").arg(&executable);
    checked(&mut link, 180, &dir.join("regions-link.log"));
    executable
}

fn run_region_row(executable: &Path, row: RegionCall, dir: &Path) -> Run {
    run_bounded(
        Command::new("sh")
            .args(["-c", "ulimit -c 0; exec \"$@\"", "terminate-region"])
            .arg(executable)
            .arg(row.frame)
            .arg(row.mask.to_string())
            .arg(if row.catch { "1" } else { "0" })
            .arg(row.arg.to_string()),
        30,
        &dir.join(format!("run-{}.log", row.name)),
    )
}

/// Pin LLVM's own outcome for `row` at `outcome`, so the comparison below can
/// never pass by agreeing on an unexamined result.
fn require_region_outcome(output: &Run, row: RegionCall, outcome: RegionOutcome) {
    let lines: Vec<_> = output.stdout.lines().collect();
    let hooks: Vec<_> = lines
        .iter()
        .copied()
        .filter(|line| line.starts_with("HOOK "))
        .collect();
    let context = format!(
        "{}: LLVM outcome is not {:?}: {}\n{}\n{}",
        row.name, outcome, output.status, output.stdout, output.stderr
    );
    let callback_hook = format!("payload={REGION_CALLBACK_PAYLOAD:?}");
    match outcome {
        RegionOutcome::Returns => {
            assert!(output.status.success(), "{context}");
            assert!(hooks.is_empty() && output.stderr.is_empty(), "{context}");
            let after = format!("value={}", if row.catch { "Some(" } else { "" });
            assert!(
                lines
                    .last()
                    .is_some_and(|line| line.starts_with("AFTER ") && line.contains(&after)),
                "{context}"
            );
        }
        RegionOutcome::FatalSearch => {
            assert_eq!(output.status.signal(), Some(6), "{context}");
            assert_eq!(
                output.stderr, "fatal runtime error: failed to initiate panic, error 3, aborting\n",
                "{context}"
            );
            assert!(
                !hooks.is_empty() && hooks.iter().all(|hook| hook.contains(&callback_hook)),
                "a fatal search runs only the panics' own hooks: {context}"
            );
            assert!(!output.stdout.contains("AFTER "), "{context}");
        }
        RegionOutcome::ReachedAbi => {
            assert_eq!(output.status.signal(), Some(6), "{context}");
            assert_eq!(
                output.stderr, "thread caused non-unwinding panic. aborting.\n",
                "{context}"
            );
            assert!(
                hooks
                    .last()
                    .is_some_and(|hook| hook.contains(&format!("payload={REGION_ABI_REASON:?}"))),
                "{context}"
            );
            assert!(!output.stdout.contains("AFTER "), "{context}");
        }
        RegionOutcome::Caught => {
            assert!(row.catch, "{context}");
            assert!(output.status.success(), "{context}");
            assert!(output.stderr.is_empty(), "{context}");
            assert!(
                hooks.len() == 1 && hooks[0].contains(&callback_hook),
                "a caught panic runs exactly its own hook: {context}"
            );
            assert!(
                lines.last().is_some_and(|line| {
                    line.starts_with("AFTER caught=true value=None hooks=1 ")
                }),
                "{context}"
            );
        }
    }
}

/// An abort-built `nounwind` frame's exception table keeps unwinding through
/// exactly the regions LLVM's does on these shapes, whose regions hold the same
/// calls under both backends (where LLVM's hold calls this backend's do not,
/// the two differ; see `EhPropagation::NounwindFrame`): one that holds an
/// indirect call (a Rust or `extern "C"` function pointer, a `&dyn` method),
/// before the first invoke, between invokes, or after the last, is covered, and
/// a direct `nounwind` call sharing it is covered with it; a region of direct
/// `nounwind` calls only is a gap where the search fails. `memcmp` counts as
/// `nounwind` only above O0, as LLVM infers it. A call the backend creates
/// itself (an array-fill or slice-reverse helper, libm `fma` / `sin`,
/// compiler-rt `__powidf2` / `__divti3` / `__udivti3` / `__fixdfti`, a
/// `memset`) leaves its region a gap wherever LLVM may expand, narrow, fold or
/// delete the operation and covered only where LLVM certainly calls a libcall,
/// per level (a decoded `print!` is not one: it calls std's own `_print`, as
/// LLVM does); a call through a `fn` pointer or vtable whose target the frame
/// states is the direct call LLVM makes; a frame LLVM gives a table by inlining
/// a callee's terminate pad has that table; and the frame's last call never
/// becomes a tail branch that skips its table. Each row runs against LLVM's own
/// object at O0-O3 and must match its stdout, stderr and status exactly, except
/// a row pinning OD-58's accepted earlier abort at O0
/// (`RegionRow::earlier_o0`: the thread-local thunk call), whose backend run
/// must fail phase one there.
#[test]
fn nounwind_frame_call_site_regions_match_llvm_aarch64() {
    darwin_native::require("terminate_panic_differential_aarch64", &["shasum"]);
    let artifacts = Temporary::new();
    let root = &artifacts.0;
    fs::write(
        root.join("regions.rs"),
        include_str!("support/terminate_panic/regions.rs"),
    )
    .unwrap();
    fs::write(
        root.join("regions_driver.rs"),
        include_str!("support/terminate_panic/regions_driver.rs"),
    )
    .unwrap();
    let backend = backend_artifact_support::current_test_backend();
    let backend_digest = sha256(&backend, &root.join("regions-backend-before.log"));
    let (mut cells, mut llvm_runs, mut cg_runs) = (0, 0, 0);
    let (mut returns, mut fatal_search, mut reached_abi, mut caught) = (0, 0, 0, 0);
    for opt in OPT_LEVELS {
        let mut expected = Vec::new();
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("{lane}-regions-O{opt}"));
            let executable = compile_region_driver(
                root,
                &dir,
                opt,
                (lane == "cg").then_some(backend.as_path()),
                &ABORT_REGIONS,
            );
            for (index, row) in REGION_ROWS.iter().enumerate() {
                let output = run_region_row(&executable, row.call(), &dir);
                let outcome = row.outcome_at(opt);
                if lane == "llvm" {
                    require_region_outcome(&output, row.call(), outcome);
                    expected.push((output.status, output.stdout, output.stderr));
                    llvm_runs += 1;
                } else {
                    let backend_outcome = row.backend_outcome_at(opt);
                    if backend_outcome == outcome {
                        let (status, stdout, stderr) = &expected[index];
                        assert_eq!(
                            (&output.status, &output.stdout, &output.stderr),
                            (status, stdout, stderr),
                            "abort-callee/unwind-driver/O{opt}/{}: status, hooks, drops, \
                             callbacks or termination differ from LLVM ({:?} expected)",
                            row.name,
                            outcome
                        );
                    } else {
                        require_region_outcome(&output, row.call(), backend_outcome);
                    }
                    cg_runs += 1;
                    match backend_outcome {
                        RegionOutcome::Returns => returns += 1,
                        RegionOutcome::FatalSearch => fatal_search += 1,
                        RegionOutcome::ReachedAbi => reached_abi += 1,
                        RegionOutcome::Caught => caught += 1,
                    }
                }
            }
            assert_eq!(
                sha256(&backend, &dir.join("regions-backend-after.log")),
                backend_digest,
                "test backend changed during region qualification"
            );
            cells += 1;
        }
        assert_eq!(
            expected.len(),
            REGION_ROWS.len(),
            "the LLVM denominator changed"
        );
    }
    assert_eq!(
        (
            cells,
            llvm_runs,
            cg_runs,
            returns,
            fatal_search,
            reached_abi,
            caught
        ),
        (8, 272, 272, 40, 135, 48, 49)
    );
    println!(
        "TERMINATE_NOUNWIND_REGIONS rows=68 cells=8 native_runs=544 llvm_runs=272 cg_runs=272 opts=0,1,2,3 callee_strategy=abort driver_strategy=unwind"
    );
    println!(
        "TERMINATE_NOUNWIND_REGION_OUTCOMES returns=40 fatal_search=135 reached_abi=48 caught=49"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

/// One row of the unwind-built region callee (`unwind_regions.rs`): a frame
/// that calls a Rust-defined `extern "C"` callee whose panic reaches it, or a
/// control. LLVM's outcome is `llvm_o0` at O0 and `llvm` at O1-O3.
/// `mir_drops` is the callee's cleanup trace (`DROP=` ids): MIR runs it before
/// the callee's Abi termination, and the backend prints it after LLVM's own
/// output at each level where LLVM's search fails in the caller's table
/// instead (OD-NOUNWIND-CALLEE-EDGE-20261011).
struct UnwindRegionRow {
    call: RegionCall,
    llvm_o0: RegionOutcome,
    llvm: RegionOutcome,
    mir_drops: &'static [u64],
}

impl UnwindRegionRow {
    fn llvm_at(&self, opt: &str) -> RegionOutcome {
        if opt == "0" { self.llvm_o0 } else { self.llvm }
    }
}

const fn unwind_region(
    name: &'static str,
    frame: &'static str,
    mask: u64,
    catch: bool,
    outcome: RegionOutcome,
) -> UnwindRegionRow {
    unwind_region_by_opt(name, frame, mask, catch, outcome, outcome, &[])
}

/// A row whose LLVM outcome differs at O0, or whose LLVM search fails phase
/// one at some level (`mir_drops` is then the callee's MIR cleanup trace).
const fn unwind_region_by_opt(
    name: &'static str,
    frame: &'static str,
    mask: u64,
    catch: bool,
    llvm_o0: RegionOutcome,
    llvm: RegionOutcome,
    mir_drops: &'static [u64],
) -> UnwindRegionRow {
    UnwindRegionRow {
        call: RegionCall {
            name,
            frame,
            mask,
            catch,
            arg: 5,
        },
        llvm_o0,
        llvm,
        mir_drops,
    }
}

const UNWIND_REGION_ROWS: &[UnwindRegionRow] = &[
    // The callee's call sits in a gap of LLVM's table: before the caller's
    // first invoke with nothing that may unwind beside it, between invokes
    // with different pads (each foreign call gets its own), a known `extern
    // "C"` fn pointer (a direct call in LLVM's IR, O0 included), beside a libc
    // call LLVM declares `nounwind`, or a `nounwind` libc `qsort` call whose
    // comparator holds a live Drop, so the search reaches the caller through
    // libc's frame. LLVM's search fails there.
    unwind_region_by_opt(
        "padded-before",
        "padded_before",
        1,
        true,
        RegionOutcome::FatalSearch,
        RegionOutcome::FatalSearch,
        &[1],
    ),
    unwind_region_by_opt(
        "between-foreign",
        "between_foreign",
        2,
        true,
        RegionOutcome::FatalSearch,
        RegionOutcome::FatalSearch,
        &[31],
    ),
    unwind_region_by_opt(
        "c-pointer-known",
        "c_pointer_known",
        2,
        true,
        RegionOutcome::FatalSearch,
        RegionOutcome::FatalSearch,
        &[41],
    ),
    unwind_region_by_opt(
        "libc-region",
        "libc_region",
        2,
        true,
        RegionOutcome::FatalSearch,
        RegionOutcome::FatalSearch,
        &[71],
    ),
    unwind_region_by_opt(
        "libc-qsort-unwinds",
        "libc_qsort_unwinds",
        2,
        true,
        RegionOutcome::FatalSearch,
        RegionOutcome::FatalSearch,
        &[85],
    ),
    // Level-dependent gaps: LLVM merges the two same-pad invokes over the call
    // only above O0, inlines the callee only above O0, and infers `nounwind`
    // for the quiet Rust-ABI neighbour only above O0.
    unwind_region_by_opt(
        "between-shared",
        "between_shared",
        2,
        true,
        RegionOutcome::FatalSearch,
        RegionOutcome::ReachedAbi,
        &[31],
    ),
    unwind_region_by_opt(
        "inlinable-before",
        "inlinable_before",
        1,
        true,
        RegionOutcome::FatalSearch,
        RegionOutcome::ReachedAbi,
        &[1],
    ),
    unwind_region_by_opt(
        "rust-shares-region",
        "rust_shares_region",
        1,
        true,
        RegionOutcome::ReachedAbi,
        RegionOutcome::FatalSearch,
        &[1],
    ),
    // The search passes the caller, so LLVM runs the callee's cleanups and
    // terminates as MIR does: the caller has no table, or a call beside the
    // callee's that may unwind (the guard's normal-path Drop, `_print`, an
    // unknown fn pointer, `_Unwind_Resume`) keeps its region covered, or the
    // call is in the caller's cleanup.
    unwind_region(
        "padded-after",
        "padded_after",
        2,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region(
        "padded-live",
        "padded_live",
        2,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region("no-pads", "no_pads", 1, true, RegionOutcome::ReachedAbi),
    unwind_region(
        "no-pads-uncaught",
        "no_pads",
        1,
        false,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region("c-pointer", "c_pointer", 2, true, RegionOutcome::ReachedAbi),
    unwind_region(
        "cleanup-calls-c",
        "cleanup_calls_c",
        3,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region(
        "cleanup-calls-c-second",
        "cleanup_calls_c",
        2,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region(
        "cleanup-calls-c-inline",
        "cleanup_calls_c_inline",
        3,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region(
        "cleanup-calls-c-inline-second",
        "cleanup_calls_c_inline",
        2,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region(
        "print-region",
        "print_region",
        1,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region(
        "resume-region",
        "resume_region",
        2,
        true,
        RegionOutcome::ReachedAbi,
    ),
    // A panicking `extern "C"` frame with no live Drop (`uw_c_bare`, or the
    // comparator libc `qsort` calls): its own Terminate(Abi) edge carries the
    // empty filter, so the search stops inside it and never reaches a
    // caller's table, whatever that table covers.
    unwind_region(
        "bare-before",
        "bare_before",
        1,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region(
        "libc-qsort",
        "libc_qsort",
        2,
        true,
        RegionOutcome::ReachedAbi,
    ),
    unwind_region(
        "libc-qsort-gap",
        "libc_qsort_gap",
        2,
        true,
        RegionOutcome::ReachedAbi,
    ),
    // Controls: nothing panics, or a callee that may unwind panics and the
    // driver catches it. The `*-unprotected` rows panic from a region with no
    // landing pad of its own, covered only because the call there may unwind:
    // a table that took that callee for `nounwind` would fail the search and
    // turn a caught panic into an abort (LLVM does exactly that, at O0-O3, when
    // the same callee is imported as `extern "C"`: OD-NOUNWIND-CALLEE-EDGE).
    unwind_region(
        "libc-qsort-ok",
        "libc_qsort",
        0,
        true,
        RegionOutcome::Returns,
    ),
    unwind_region(
        "libc-qsort-unwinds-ok",
        "libc_qsort_unwinds",
        0,
        true,
        RegionOutcome::Returns,
    ),
    unwind_region(
        "libc-qsort-unwinds-guard",
        "libc_qsort_unwinds",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "padded-before-later",
        "padded_before",
        2,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "between-shared-first",
        "between_shared",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "between-shared-last",
        "between_shared",
        4,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "between-foreign-first",
        "between_foreign",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "cleanup-calls-c-first",
        "cleanup_calls_c",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "cleanup-calls-c-inline-first",
        "cleanup_calls_c_inline",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region("padded-cu", "padded_cu", 2, true, RegionOutcome::Caught),
    unwind_region("padded-rust", "padded_rust", 2, true, RegionOutcome::Caught),
    unwind_region(
        "resume-region-first",
        "resume_region",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "rust-unprotected",
        "rust_unprotected",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "cu-unprotected",
        "cu_unprotected",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "rust-pointer-unprotected",
        "rust_pointer_unprotected",
        1,
        true,
        RegionOutcome::Caught,
    ),
    unwind_region(
        "dyn-unprotected",
        "dyn_unprotected",
        1,
        true,
        RegionOutcome::Caught,
    ),
];

/// The backend's run of `row` at a level where LLVM's search fails phase one
/// in the caller's table: MIR's own termination. Its stdout is LLVM's (the
/// callbacks and the panic's own hook), then the callee's cleanup trace
/// `mir_drops`, then exactly one hook reporting the Abi termination; it ends
/// as a non-unwinding panic.
fn require_mir_cleanup_after_fatal_search(
    llvm: &Run,
    backend: &Run,
    row: &UnwindRegionRow,
    opt: &str,
) {
    let context = format!(
        "unwind-callee/O{opt}/{}: the backend does not run the callee's MIR cleanups and \
         then its Abi termination after LLVM's output:\nLLVM: {}\n{}{}\nbackend: {}\n{}{}",
        row.call.name,
        llvm.status,
        llvm.stdout,
        llvm.stderr,
        backend.status,
        backend.stdout,
        backend.stderr
    );
    assert!(!row.mir_drops.is_empty(), "{context}");
    assert_eq!(backend.status.signal(), Some(6), "{context}");
    assert_eq!(
        backend.stderr, "thread caused non-unwinding panic. aborting.\n",
        "{context}"
    );
    let rest = backend
        .stdout
        .strip_prefix(llvm.stdout.as_str())
        .unwrap_or_else(|| panic!("{context}"));
    let lines: Vec<_> = rest.lines().collect();
    let drops: Vec<_> = row
        .mir_drops
        .iter()
        .map(|id| format!("DROP={id}"))
        .collect();
    assert_eq!(lines.len(), drops.len() + 1, "{context}");
    assert_eq!(lines[..drops.len()], drops[..], "{context}");
    let hooks = llvm
        .stdout
        .lines()
        .filter(|line| line.starts_with("HOOK "))
        .count();
    assert!(
        lines[drops.len()].starts_with(&format!(
            "HOOK seq={} payload={REGION_ABI_REASON:?} ",
            hooks + 1
        )),
        "{context}"
    );
}

/// A Rust-defined `extern "C"` callee whose panic reaches its unwind-built
/// caller runs its own cleanups and then its Abi termination ("panic in a
/// function that cannot unwind"), as MIR states: the caller's call has no
/// unwind edge (`unwind unreachable`), and the callee's cleanup chain ends in
/// `terminate(abi)`. LLVM's binary does the same wherever its search passes
/// every frame up to a handler, and every such row must match it exactly, as
/// must every control whose panic is caught or never raised.
///
/// Where the call sits in a gap of LLVM's call-site table (rows with
/// `mir_drops`, at the levels LLVM reports `FatalSearch`), LLVM's search fails
/// and the process aborts before any cleanup runs. This backend's
/// full-coverage table lets the search pass the caller, so MIR's cleanups run
/// first; these fixtures' cleanups only print, so both binaries then end in
/// SIGABRT. Ruling OD-NOUNWIND-CALLEE-EDGE-20261011 keeps this. Reproducing
/// LLVM's gaps would need LLVM's inlining, `nounwind` inference and range
/// merging, and one wrong `nounwind` entry would turn a caught panic into an
/// abort, which the `*-unprotected` controls catch.
#[test]
fn extern_c_callee_panics_run_mir_cleanups_aarch64() {
    darwin_native::require("terminate_panic_differential_aarch64", &["shasum"]);
    let artifacts = Temporary::new();
    let root = &artifacts.0;
    fs::write(
        root.join("unwind_regions.rs"),
        include_str!("support/terminate_panic/unwind_regions.rs"),
    )
    .unwrap();
    fs::write(
        root.join("unwind_regions_driver.rs"),
        include_str!("support/terminate_panic/unwind_regions_driver.rs"),
    )
    .unwrap();
    for row in UNWIND_REGION_ROWS {
        let fails_search = [row.llvm_o0, row.llvm].contains(&RegionOutcome::FatalSearch);
        assert_eq!(
            fails_search,
            !row.mir_drops.is_empty(),
            "{}: a cleanup trace belongs exactly to the rows whose LLVM search fails",
            row.call.name
        );
    }
    let backend = backend_artifact_support::current_test_backend();
    let backend_digest = sha256(&backend, &root.join("unwind-regions-backend-before.log"));
    let (mut cells, mut llvm_runs, mut cg_runs) = (0, 0, 0);
    let (mut returns, mut caught, mut reached_abi, mut mir_cleanups) = (0, 0, 0, 0);
    for opt in OPT_LEVELS {
        let mut expected = Vec::new();
        for lane in ["llvm", "cg"] {
            let dir = root.join(format!("{lane}-unwind-regions-O{opt}"));
            let executable = compile_region_driver(
                root,
                &dir,
                opt,
                (lane == "cg").then_some(backend.as_path()),
                &UNWIND_REGIONS,
            );
            for (index, row) in UNWIND_REGION_ROWS.iter().enumerate() {
                let output = run_region_row(&executable, row.call, &dir);
                let outcome = row.llvm_at(opt);
                if lane == "llvm" {
                    require_region_outcome(&output, row.call, outcome);
                    expected.push(output);
                    llvm_runs += 1;
                    continue;
                }
                let llvm = &expected[index];
                if outcome == RegionOutcome::FatalSearch {
                    require_mir_cleanup_after_fatal_search(llvm, &output, row, opt);
                    mir_cleanups += 1;
                } else {
                    assert_eq!(
                        (&output.status, &output.stdout, &output.stderr),
                        (&llvm.status, &llvm.stdout, &llvm.stderr),
                        "unwind-callee/unwind-driver/O{opt}/{}: status, hooks, drops, \
                         callbacks or termination differ from LLVM ({:?} expected)",
                        row.call.name,
                        outcome
                    );
                    match outcome {
                        RegionOutcome::Returns => returns += 1,
                        RegionOutcome::Caught => caught += 1,
                        RegionOutcome::ReachedAbi => reached_abi += 1,
                        RegionOutcome::FatalSearch => unreachable!(),
                    }
                }
                cg_runs += 1;
            }
            assert_eq!(
                sha256(&backend, &dir.join("unwind-regions-backend-after.log")),
                backend_digest,
                "test backend changed during unwind region qualification"
            );
            cells += 1;
        }
        assert_eq!(
            expected.len(),
            UNWIND_REGION_ROWS.len(),
            "the LLVM denominator changed"
        );
    }
    assert_eq!(
        (
            cells,
            llvm_runs,
            cg_runs,
            returns,
            caught,
            reached_abi,
            mir_cleanups
        ),
        (8, 152, 152, 8, 56, 63, 25)
    );
    println!(
        "TERMINATE_UNWIND_CALLEE_REGIONS rows=38 cells=8 native_runs=304 llvm_runs=152 cg_runs=152 opts=0,1,2,3 callee_strategy=unwind driver_strategy=unwind"
    );
    println!(
        "TERMINATE_UNWIND_CALLEE_OUTCOMES returns=8 caught=56 reached_abi=63 mir_cleanup_where_llvm_fails_search=25"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}
