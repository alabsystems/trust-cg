// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
// Native diagnostic only: Trust verification and proof certificates are off.
// This target's markers require actual execution, not a compile or early skip.
//
// A fat-pointer-leaf aggregate stored WHOLE through a field projection
// (`((*_2).0: Box<[u8]>) = move _19`, alloc's `<CStr as ToOwned>::clone_into`)
// and the `Box<DST>` deref idiom reached through a pointer to the box
// (`_6 = copy (((*_1).0: Unique<[u8]>).0: NonNull<[u8]>) as *const [u8]
// (Transmute)`, the first statement of `drop_glue::<Box<[u8]>>`) on AArch64
// macOS. Both were refused there: the store fell through to the scalar-leaf
// deref store, and the transmute had no `{data, len}` destination slot. The
// first is now a whole-image lane copy (`lower_deref_aggregate_memory_store`),
// the second a two-lane load through the pointer (`lower_memory_slice_assign`).
//
// THE GATE. For every subject, LLVM (same compiler, same optimization level)
// and the bridge compile the subject crate; an LLVM-built driver links each
// and runs, and the two runs' stdout and exit status must be equal. Every
// driver the bridge's code runs under installs a size-checking global
// allocator, which flags a free of an unknown pointer or with a different
// layout and exits 3, so a field store that drops or corrupts a length lane is
// a wrong dealloc SIZE rather than going unseen (macOS `free` ignores the
// size). Every value is read back through the stored object: length, content
// hash and the untouched neighbouring fields.
//
// For a `Box<[T]>` whose element has no drop glue, the deref-led transmute's
// `{data, len}` is read only by `drop((*_6))`, a no-op, and the free re-reads
// the box through `_1`. The `strings` subject is where those lanes are
// observed: its elements need drop (`String`, `Box<str>`, `Vec<u64>`, and a
// `Counted` that records each drop and its payload), so `drop((*_6))` calls
// `drop_glue::<[T]>` with that pair, and a wrong length is a wrong drop count,
// a leak or a bad free. `bombs`, built with panic=unwind, has an element whose
// `Drop` panics: the remaining elements must still drop and the box be freed.
// - `deref_field_wide_image_stores_match_llvm_aarch64`: the stores and drops
//   behind alloc root 2, and the drops of `Box<[T]>` whose element needs drop,
//   must compile at O0-O3 and match LLVM.
// - `deref_field_wide_image_store_kinds_aarch64`: other fat-leaf kinds stored
//   whole through a field (`&[u16]`, `NonNull<[u8]>`, `Box<dyn Fn>`,
//   `Rc<[u8]>`/`Arc<str>`, `Option<Box<[u8]>>`, a tuple holding a box, a
//   multi-field struct holding a box) must compile at O0-O3 and match LLVM.
// - `deref_field_wide_image_store_refusals_aarch64`: a box inside a
//   `repr(packed)` container, which the lane copy does not take, must stay
//   refused, at that store.
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

struct Temporary(PathBuf);

impl Temporary {
    fn new(stem: &str) -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "trust-cg-deref-wide-{stem}-{}-{nonce}",
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

/// The exact build compiler in its unverified diagnostic lane; no
/// `TRUST_CG_*`/`TCG_*` control leaks in.
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

/// What the bridge did with one subject at one level.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Outcome {
    /// Compiled, and the driver's stdout and exit status equal LLVM's.
    Matched,
    /// Refused at compile time, naming the function.
    Refused,
}

struct Subject<'a> {
    name: &'a str,
    source: &'a str,
    driver: &'a str,
    /// A line the LLVM driver must print, so a fixture that stopped exercising
    /// the store (or an oracle that stopped running it) is caught.
    oracle_marker: &'a str,
    /// The panic strategy of the subject and of its driver.
    panic: &'a str,
}

/// Compile `subject` as an rlib with LLVM or the bridge, link the LLVM driver
/// against it and run it. `Err` is a bridge refusal, carrying its stderr.
fn build_and_run(
    dir: &Path,
    subject: &Subject,
    opt: u32,
    backend: Option<&Path>,
) -> Result<Run, String> {
    fs::create_dir_all(dir).unwrap();
    let source = dir.join(format!("{}.rs", subject.name));
    let driver = dir.join("driver.rs");
    fs::write(&source, subject.source).unwrap();
    fs::write(&driver, subject.driver).unwrap();
    let mut compile = rustc();
    compile
        .args(["--crate-type=rlib", "--target", TARGET])
        .arg(format!("-Cpanic={}", subject.panic))
        .arg(format!("--crate-name={}", subject.name))
        .arg(format!("-Copt-level={opt}"));
    if let Some(dylib) = backend {
        compile
            .arg(format!("-Zcodegen-backend={}", dylib.display()))
            .arg(toolchain_support::backend_knobs_arg(&["no-proof-certs"]));
    }
    compile.arg(&source).arg("--out-dir").arg(dir);
    let compiled = run_bounded(&mut compile, 300, &dir.join("compile.log"));
    if !compiled.status.success() {
        assert!(
            backend.is_some(),
            "{} O{opt}: LLVM failed to compile the subject:\n{}",
            subject.name,
            compiled.stderr
        );
        assert!(
            compiled.stderr.contains("[TCG-") && compiled.stderr.contains(" - "),
            "{} O{opt}: the bridge failed without naming a refused function:\n{}",
            subject.name,
            compiled.stderr
        );
        return Err(compiled.stderr);
    }
    let executable = dir.join("driver");
    checked(
        rustc()
            .args(["--crate-type=bin", "--target", TARGET])
            .arg(format!("-Cpanic={}", subject.panic))
            .arg(format!("-Copt-level={opt}"))
            .arg(format!(
                "--extern={}={}",
                subject.name,
                dir.join(format!("lib{}.rlib", subject.name)).display()
            ))
            .arg("-L")
            .arg(dir)
            .arg(&driver)
            .arg("-o")
            .arg(&executable),
        180,
        &dir.join("link.log"),
    );
    Ok(run_bounded(
        &mut Command::new(&executable),
        60,
        &dir.join("run.log"),
    ))
}

/// Run `subject` at O0-O3 and return the bridge outcome per level, with the
/// bridge's stderr for each refused level.
fn differential(root: &Path, backend: &Path, subject: &Subject) -> (Vec<Outcome>, Vec<String>) {
    let mut outcomes = Vec::new();
    let mut refusals = Vec::new();
    for opt in OPT_LEVELS {
        let base = root.join(format!("{}-O{opt}", subject.name));
        let oracle = build_and_run(&base.join("llvm"), subject, opt, None)
            .unwrap_or_else(|_| unreachable!("an LLVM compile failure panics inside"));
        assert!(
            oracle.status.success(),
            "{} O{opt}: the LLVM oracle failed:\n{}{}",
            subject.name,
            oracle.stdout,
            oracle.stderr
        );
        assert!(
            oracle
                .stdout
                .lines()
                .any(|line| line == subject.oracle_marker),
            "{} O{opt}: the oracle does not print {:?}; this fixture is measuring something \
             else:\n{}",
            subject.name,
            subject.oracle_marker,
            oracle.stdout
        );
        let bridge = match build_and_run(&base.join("cg"), subject, opt, Some(backend)) {
            Ok(bridge) => bridge,
            Err(stderr) => {
                outcomes.push(Outcome::Refused);
                refusals.push(stderr);
                continue;
            }
        };
        assert_eq!(
            (bridge.status.code(), &bridge.stdout),
            (oracle.status.code(), &oracle.stdout),
            "{} O{opt}: the bridge differs from LLVM; stderr:\n{}",
            subject.name,
            bridge.stderr
        );
        outcomes.push(Outcome::Matched);
    }
    (outcomes, refusals)
}

#[test]
fn deref_field_wide_image_stores_match_llvm_aarch64() {
    darwin_native::require("deref_field_wide_image_stores_match_llvm_aarch64", &[]);
    let root = Temporary::new("stores");
    let backend = backend_artifact_support::current_test_backend();
    let (outcomes, _) = differential(
        &root.0,
        &backend,
        &Subject {
            name: "subject",
            source: include_str!("support/deref_field_wide_image/subject.rs"),
            driver: include_str!("support/deref_field_wide_image/driver.rs"),
            oracle_marker: "allocs 190 frees 185 bad false",
            panic: "abort",
        },
    );
    assert_eq!(
        outcomes,
        [Outcome::Matched; 4],
        "every level must build and match"
    );
    let (strings, _) = differential(
        &root.0,
        &backend,
        &Subject {
            name: "strings",
            source: include_str!("support/deref_field_wide_image/strings.rs"),
            driver: include_str!("support/deref_field_wide_image/strings_driver.rs"),
            oracle_marker: "drop_counted 33: drops 33 sum 1617",
            panic: "abort",
        },
    );
    assert_eq!(
        strings,
        [Outcome::Matched; 4],
        "every level of the needs-drop Box<[T]> rows must build and match"
    );
    // panic=unwind: an element whose `Drop` panics. The element drop is an
    // invoke; its cleanup frees the box, rustc's slice glue drops the
    // remaining elements, and the driver catches the panic.
    let (bombs, _) = differential(
        &root.0,
        &backend,
        &Subject {
            name: "bombs",
            source: include_str!("support/deref_field_wide_image/bombs.rs"),
            driver: include_str!("support/deref_field_wide_image/bombs_driver.rs"),
            oracle_marker: "drop_bombs 8 fuse 3: caught true drops 8 sum 36",
            panic: "unwind",
        },
    );
    assert_eq!(
        bombs,
        [Outcome::Matched; 4],
        "every level of the panicking-element Box<[T]> rows must build and match"
    );
    println!(
        "DEREF_FIELD_WIDE_IMAGE_STORES subjects=subject,strings,bombs opts=0,1,2,3 matched=12 refused=0"
    );
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn deref_field_wide_image_store_kinds_aarch64() {
    darwin_native::require("deref_field_wide_image_store_kinds_aarch64", &[]);
    let root = Temporary::new("kinds");
    let backend = backend_artifact_support::current_test_backend();
    let (outcomes, _) = differential(
        &root.0,
        &backend,
        &Subject {
            name: "kinds",
            source: include_str!("support/deref_field_wide_image/kinds.rs"),
            driver: include_str!("support/deref_field_wide_image/kinds_driver.rs"),
            oracle_marker: "whole a 7 z 9 tag 5 n 8 4038744658729061305",
            panic: "abort",
        },
    );
    assert_eq!(
        outcomes,
        [Outcome::Matched; 4],
        "every fat-leaf kind must build and match"
    );
    println!("DEREF_FIELD_WIDE_IMAGE_KINDS kinds=7 opts=0,1,2,3 matched=4 refused=0");
    positive_evidence::record(
        positive_evidence::Evidence::NativeRun,
        positive_evidence::Certs::Off,
    );
}

#[test]
fn deref_field_wide_image_store_refusals_aarch64() {
    darwin_native::require("deref_field_wide_image_store_refusals_aarch64", &[]);
    let root = Temporary::new("refusals");
    let backend = backend_artifact_support::current_test_backend();
    // A box inside a `repr(packed)` container: the lane copy writes at the
    // leaf's own alignment, which a packed field does not have, so the store
    // keeps its refusal.
    let (packed, packed_refusals) = differential(
        &root.0,
        &backend,
        &Subject {
            name: "packed",
            source: include_str!("support/deref_field_wide_image/packed.rs"),
            driver: include_str!("support/deref_field_wide_image/packed_driver.rs"),
            oracle_marker: "packed a 3 len 5 sum 45",
            panic: "abort",
        },
    );
    assert_eq!(
        packed,
        [Outcome::Refused; 4],
        "a packed container must stay refused"
    );
    for stderr in &packed_refusals {
        assert!(
            stderr.contains("set_packed"),
            "the packed refusal must be the store itself:\n{stderr}"
        );
    }
    println!("DEREF_FIELD_WIDE_IMAGE_REFUSALS subjects=packed opts=0,1,2,3 matched=0 refused=4");
    positive_evidence::record(
        positive_evidence::Evidence::ExpectedRefusal,
        positive_evidence::Certs::Off,
    );
}
