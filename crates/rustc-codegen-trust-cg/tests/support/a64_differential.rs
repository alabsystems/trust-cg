//! The native AArch64 differential harness shared by the bridge's corpus and
//! feature-suite lanes (ledger L06-P3).
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! Each program is built at each optimization level by trustc's own LLVM
//! backend (the ORACLE) and by this backend (`-Zcodegen-backend=<the library
//! of this test build>`) with the same flags, both binaries run natively with
//! a timeout, and they are compared on exit status (code or killing signal),
//! stdout and stderr (std's panic header carries a per-process thread id,
//! `thread 'main' (12345) panicked at`, which is removed on both sides first).
//! Two runs that panic at the same location with the same exit status and
//! stdout but a different panic MESSAGE are their own verdict
//! (`PANIC-MESSAGE`): an output divergence the census must list, never a
//! match. A `#![no_main]` program is emitted as an object and
//! linked by `cc` with `abort()` stubs for core's diverging helpers; any
//! other program is built as an ordinary binary. A bridge compile or link
//! failure is a refusal, classified by its first `[TCG-*]` code (`LINK` for an
//! object the linker rejected, `UNNAMED` for a refusal without a code).
//!
//! The verdict of every cell is compared with a committed census (one line per
//! cell that does not build and match: `<lane> <program> O<opt> <code>`): a
//! divergence from LLVM is a miscompile and always fails; a refusal the census
//! does not list is a coverage regression; a listed cell that now builds and
//! matches fails until its line is removed, so the census only shrinks by
//! review. The caller supplies the proofs-off knob argument, built on its own
//! test thread through `toolchain_support::backend_knobs_arg`, so the knob
//! trace belongs to the test that turned certificates off.
//!
//! Testing evidence for the host that ran it, in the explicit unverified Trust
//! lane (`-Ztrust-verify=off` on both sides); not proof.
#![allow(dead_code)]

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::{Duration, Instant};

/// The AArch64 triple this host links and runs natively.
pub const TARGET: &str = crate::host_target_support::AARCH64_TARGET;

/// Concurrent cells. The runner executes one test at a time on a machine
/// other agents share; three builds keep that bounded.
const WORKERS: usize = 3;

/// A program that runs longer than this is classified as a hang on that side.
const RUN_TIMEOUT: Duration = Duration::from_secs(60);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Lane {
    Llvm,
    /// The backend with proof certificates off (a diagnostic lane).
    ProofsOff,
    /// The backend's default lane: proof certificates required.
    CertsOn,
}

impl Lane {
    pub fn label(self) -> &'static str {
        match self {
            Lane::Llvm => "llvm",
            Lane::ProofsOff => "proofs-off",
            Lane::CertsOn => "certs-on",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Panic {
    Abort,
    Unwind,
}

/// One program of a lane.
#[derive(Clone, Debug)]
pub struct Program {
    /// Unique within the lane; no whitespace.
    pub id: String,
    pub src: String,
    pub panic: Panic,
    /// `-Coverflow-checks=off` on both sides (the corpus's flag); otherwise
    /// the optimization level's default.
    pub overflow_checks_off: bool,
    /// The exit code the program's own suite pins, checked against the oracle.
    pub expected: Option<i32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ending {
    Exited(i32),
    Signalled(i32),
    TimedOut,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Run {
    pub ending: Ending,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
}

#[derive(Clone, Debug)]
pub enum Verdict {
    Matched,
    Refused {
        code: String,
        line: String,
    },
    Diverged {
        detail: String,
    },
    /// LLVM itself cannot build the program for this target (a suite program
    /// written against x86-64 only); the backend is not run.
    OracleUnbuildable {
        line: String,
    },
    /// Both runs panicked at the same location and agree on exit status and
    /// stdout, but the panic MESSAGE differs (the backend raised a panic whose
    /// text it does not lower, e.g. `unwrap_failed`'s). An output divergence,
    /// not a match: the census must list it with code [`PANIC_MESSAGE`].
    PanicMessage {
        detail: String,
    },
}

/// The census code of a [`Verdict::PanicMessage`] cell.
pub const PANIC_MESSAGE: &str = "PANIC-MESSAGE";

/// `stderr` with the per-process thread id of std's panic header removed:
/// `thread 'main' (12345) panicked at` is spelled `thread 'main' panicked at`.
fn normalize_stderr(stderr: &[u8]) -> String {
    let text = String::from_utf8_lossy(stderr);
    let mut out = String::with_capacity(text.len());
    for line in text.split_inclusive('\n') {
        let spelled = line.strip_prefix("thread '").and_then(|rest| {
            let (name, rest) = rest.split_once("' (")?;
            let (id, rest) = rest.split_once(") panicked at ")?;
            id.bytes()
                .all(|b| b.is_ascii_digit())
                .then(|| format!("thread '{name}' panicked at {rest}"))
        });
        out.push_str(spelled.as_deref().unwrap_or(line));
    }
    out
}

/// The `thread '..' panicked at <file:line:col>:` header of a normalized
/// stderr, if it has one.
fn panic_location(stderr: &str) -> Option<&str> {
    stderr
        .lines()
        .find(|line| line.starts_with("thread '") && line.contains("' panicked at "))
}

/// Classify a backend run against the oracle's.
fn compare(oracle: &Run, run: &Run) -> Verdict {
    let (oracle_err, run_err) = (
        normalize_stderr(&oracle.stderr),
        normalize_stderr(&run.stderr),
    );
    if oracle.ending == run.ending && oracle.stdout == run.stdout {
        if oracle_err == run_err {
            return Verdict::Matched;
        }
        if let (Some(at), Some(run_at)) = (panic_location(&oracle_err), panic_location(&run_err)) {
            if at == run_at {
                return Verdict::PanicMessage {
                    detail: format!("llvm: {} | trust-cg: {}", describe(oracle), describe(run)),
                };
            }
        }
    }
    Verdict::Diverged {
        detail: format!("llvm: {} | trust-cg: {}", describe(oracle), describe(run)),
    }
}

#[derive(Clone, Debug)]
pub struct Cell {
    pub id: String,
    pub opt: &'static str,
    /// `None` when LLVM cannot build the program.
    pub oracle: Option<Run>,
    pub expected: Option<i32>,
    pub verdict: Verdict,
}

/// Panic unless every prerequisite of a native run is present: on an AArch64
/// host a missing one is a defect of the host or package, never a pass.
pub fn require_prerequisites(test: &str) {
    let mut missing = Vec::new();
    if !crate::toolchain_support::backend_knobs_supported() {
        missing.push("the build compiler cannot express backend knobs".to_owned());
    }
    if !crate::toolchain_support::target_std_available(TARGET) {
        missing.push(format!(
            "the pinned Trust package ships no rust-std for {TARGET}"
        ));
    }
    for tool in ["cc", "nm"] {
        let answers = Command::new(tool)
            .arg("--version")
            .output()
            .is_ok_and(|output| output.status.success());
        if !answers {
            missing.push(format!("host tool `{tool}` does not answer `--version`"));
        }
    }
    assert!(
        missing.is_empty(),
        "AARCH64_BRIDGE_PREREQUISITE_MISSING {test}: {}",
        missing.join("; ")
    );
}

/// A scratch directory removed when dropped, on success and on failure.
pub struct Scratch(pub PathBuf);

impl Scratch {
    pub fn new(stem: &str) -> Self {
        let dir = std::env::temp_dir().join(format!("tcg_a64_diff_{stem}_{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("create scratch directory");
        Scratch(dir)
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn tail_of(text: &[u8]) -> String {
    let text = String::from_utf8_lossy(text);
    let lines: Vec<&str> = text
        .lines()
        .filter(|line| !line.trim().is_empty())
        .collect();
    lines[lines.len().saturating_sub(4)..].join(" | ")
}

/// The first `[TCG-*]` code at or after byte `from` of `text`.
fn first_code(text: &str, from: usize) -> Option<(usize, &str)> {
    let mut at = from;
    while let Some(found) = text[at..].find("[TCG-") {
        let start = at + found + 1;
        let candidate = &text[start..];
        let len = candidate
            .find(|c: char| !(c.is_ascii_uppercase() || c.is_ascii_digit() || c == '-'))
            .unwrap_or(candidate.len());
        if candidate[len..].starts_with(']') && len > "TCG-".len() {
            return Some((start + len, &candidate[..len]));
        }
        at = start;
    }
    None
}

/// A refusal's name: the first `[TCG-*]` code of its first coded `error`
/// line (else of its output), joined by `/` to the code the
/// first failing function's reason line carries when it has one (the
/// `[TCG-MIR-UNSUPPORTED]` umbrella names its cause there, e.g.
/// `TCG-MIR-UNSUPPORTED/TCG-IR-LOWER`); `UNNAMED` when there is no code.
pub fn refusal_code(stderr: &[u8]) -> String {
    let text = String::from_utf8_lossy(stderr);
    // The first `error` line that carries a code, else any code at all.
    let mut offset = 0;
    let mut error_at = None;
    for line in text.split_inclusive('\n') {
        if line.starts_with("error") && line.contains("[TCG-") {
            error_at = Some(offset);
            break;
        }
        offset += line.len();
    }
    let Some((end, umbrella)) = first_code(&text, error_at.unwrap_or(0)) else {
        return "UNNAMED".to_owned();
    };
    let reason_line = text[end..]
        .lines()
        .skip(1)
        .map(str::trim)
        .find(|line| !line.is_empty());
    let inner = reason_line
        .filter(|line| line.starts_with("- "))
        .and_then(|line| first_code(line, 0).map(|(_, code)| code.to_owned()));
    match inner {
        Some(inner) if inner != umbrella => format!("{umbrella}/{inner}"),
        _ => umbrella.to_owned(),
    }
}

/// The refusal's own diagnostic: the first line naming `code` and the line
/// after it (the backend puts the failing function and reason there), else
/// the first `error` line. The backend's informational notes are not echoed.
fn diagnostic_line(stderr: &[u8], code: &str) -> String {
    let text = String::from_utf8_lossy(stderr);
    let lines: Vec<&str> = text.lines().collect();
    let named = format!("[{}]", code.split('/').next().unwrap_or(code));
    let at = lines
        .iter()
        .position(|line| line.contains(&named))
        .or_else(|| lines.iter().position(|line| line.starts_with("error")));
    let Some(at) = at else {
        return String::new();
    };
    let mut spelled = lines[at].trim().to_owned();
    if let Some(next) = lines.get(at + 1).map(|line| line.trim()) {
        if next.starts_with('-') {
            spelled.push_str(" :: ");
            spelled.push_str(next);
        }
    }
    spelled.chars().take(360).collect()
}

fn signal_of(status: &ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    status.signal().unwrap_or(-1)
}

fn run_with_timeout(bin: &Path) -> Run {
    let mut child = Command::new(bin)
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap_or_else(|error| panic!("spawn {bin:?}: {error}"));
    // Drain both pipes while polling, so a chatty program cannot block.
    let mut stdout = child.stdout.take().expect("stdout pipe");
    let mut stderr = child.stderr.take().expect("stderr pipe");
    let out_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = std::io::Read::read_to_end(&mut stdout, &mut buf);
        buf
    });
    let err_reader = std::thread::spawn(move || {
        let mut buf = Vec::new();
        let _ = std::io::Read::read_to_end(&mut stderr, &mut buf);
        buf
    });
    let start = Instant::now();
    let ending = loop {
        if let Some(status) = child.try_wait().expect("poll a test binary") {
            break match status.code() {
                Some(code) => Ending::Exited(code),
                None => Ending::Signalled(signal_of(&status)),
            };
        }
        if start.elapsed() >= RUN_TIMEOUT {
            let _ = child.kill();
            let _ = child.wait();
            break Ending::TimedOut;
        }
        std::thread::sleep(Duration::from_millis(5));
    };
    Run {
        ending,
        stdout: out_reader.join().expect("stdout reader"),
        stderr: err_reader.join().expect("stderr reader"),
    }
}

enum Built {
    Binary(PathBuf),
    Refused { code: String, line: String },
}

fn build(
    out: &Path,
    src_path: &Path,
    program: &Program,
    opt: &str,
    lane: Lane,
    dylib: &Path,
    proofs_off_knob: &str,
) -> Built {
    std::fs::create_dir_all(out).expect("create lane directory");
    let is_object = program.src.contains("#![no_main]");
    let mut cmd = crate::toolchain_support::rustc_command();
    cmd.arg("--crate-type").arg("bin");
    if lane != Lane::Llvm {
        let mut backend = std::ffi::OsString::from("-Zcodegen-backend=");
        backend.push(dylib);
        cmd.arg(backend);
    }
    if lane == Lane::ProofsOff {
        cmd.arg(proofs_off_knob);
    }
    cmd.args(["--target", TARGET, "-Ccodegen-units=1"]);
    cmd.arg(match program.panic {
        Panic::Abort => "-Cpanic=abort",
        Panic::Unwind => "-Cpanic=unwind",
    });
    if program.overflow_checks_off {
        cmd.arg("-Coverflow-checks=off");
    }
    cmd.arg(format!("-Copt-level={opt}"));
    let bin = out.join("bin");
    if is_object {
        cmd.arg("--emit=obj").arg("--out-dir").arg(out);
    } else {
        cmd.arg("-o").arg(&bin);
    }
    cmd.arg(src_path);
    let output = cmd.output().expect("spawn the build compiler");
    if !output.status.success() {
        let code = refusal_code(&output.stderr);
        return Built::Refused {
            line: diagnostic_line(&output.stderr, &code),
            code,
        };
    }
    if !is_object {
        return Built::Binary(bin);
    }
    let objects: Vec<PathBuf> = std::fs::read_dir(out)
        .expect("read lane directory")
        .filter_map(|entry| entry.ok().map(|entry| entry.path()))
        .filter(|path| path.extension().is_some_and(|ext| ext == "o"))
        .collect();
    assert!(
        !objects.is_empty(),
        "{} ({}): no object",
        program.id,
        lane.label()
    );
    let stubs = crate::toolchain_support::write_abort_stubs(out, &objects);
    let link = Command::new("cc")
        .arg("-o")
        .arg(&bin)
        .args(&objects)
        .arg(&stubs)
        .output()
        .expect("spawn cc");
    if !link.status.success() {
        return Built::Refused {
            code: "LINK".to_owned(),
            line: tail_of(&link.stderr),
        };
    }
    Built::Binary(bin)
}

fn describe(run: &Run) -> String {
    format!(
        "{:?} stdout={:?} stderr={:?}",
        run.ending,
        String::from_utf8_lossy(&run.stdout)
            .chars()
            .take(240)
            .collect::<String>(),
        tail_of(&run.stderr)
    )
}

/// Build and run every program at every level in `lane` with the backend
/// `dylib` (the caller's `backend_artifact_support::current_test_backend()`,
/// the library beside its own test executable), with the LLVM oracle beside
/// it. A program LLVM cannot build is recorded as such (the
/// census must list it), and the backend is not run on it.
pub fn run_cells(
    stem: &str,
    dylib: &Path,
    programs: &[Program],
    opts: &[&'static str],
    lane: Lane,
    proofs_off_knob: &str,
) -> Vec<Cell> {
    assert!(lane != Lane::Llvm, "the oracle runs beside a backend lane");
    assert_eq!(
        lane == Lane::ProofsOff,
        !proofs_off_knob.is_empty(),
        "the proofs-off lane, and only it, carries the knob argument"
    );
    let scratch = Scratch::new(stem);
    let work: Vec<(usize, &'static str)> = (0..programs.len())
        .flat_map(|index| opts.iter().map(move |opt| (index, *opt)))
        .collect();
    let next = AtomicUsize::new(0);
    let cells = Mutex::new(Vec::with_capacity(work.len()));
    std::thread::scope(|scope| {
        for _ in 0..WORKERS {
            scope.spawn(|| {
                loop {
                    let at = next.fetch_add(1, Ordering::SeqCst);
                    let Some(&(index, opt)) = work.get(at) else {
                        break;
                    };
                    let program = &programs[index];
                    let cell_dir = scratch.0.join(format!("{at}"));
                    std::fs::create_dir_all(&cell_dir).expect("create cell directory");
                    // One source path for both sides, so a panic message's
                    // location is spelled identically.
                    let src_path = cell_dir.join("prog.rs");
                    std::fs::write(&src_path, &program.src).expect("write program source");
                    let oracle = match build(
                        &cell_dir.join("llvm"),
                        &src_path,
                        program,
                        opt,
                        Lane::Llvm,
                        dylib,
                        "",
                    ) {
                        Built::Binary(bin) => run_with_timeout(&bin),
                        Built::Refused { line, .. } => {
                            let _ = std::fs::remove_dir_all(&cell_dir);
                            cells.lock().expect("cell list").push(Cell {
                                id: program.id.clone(),
                                opt,
                                oracle: None,
                                expected: program.expected,
                                verdict: Verdict::OracleUnbuildable { line },
                            });
                            continue;
                        }
                    };
                    let verdict = match build(
                        &cell_dir.join(lane.label()),
                        &src_path,
                        program,
                        opt,
                        lane,
                        dylib,
                        proofs_off_knob,
                    ) {
                        Built::Refused { code, line } => Verdict::Refused { code, line },
                        Built::Binary(bin) => {
                            let run = run_with_timeout(&bin);
                            compare(&oracle, &run)
                        }
                    };
                    let _ = std::fs::remove_dir_all(&cell_dir);
                    cells.lock().expect("cell list").push(Cell {
                        id: program.id.clone(),
                        opt,
                        oracle: Some(oracle),
                        expected: program.expected,
                        verdict,
                    });
                }
            });
        }
    });
    let mut cells = cells.into_inner().expect("cell list");
    cells.sort_by(|a, b| (a.id.as_str(), a.opt).cmp(&(b.id.as_str(), b.opt)));
    cells
}

/// `(lane, program, opt) -> code` from a census text; `#` starts a comment.
pub fn parse_census(text: &str) -> BTreeMap<(String, String, String), String> {
    let mut census = BTreeMap::new();
    for (number, line) in text.lines().enumerate() {
        let line = line.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        let [lane, id, opt, code] = fields.as_slice() else {
            panic!(
                "census line {}: expected `<lane> <program> O<opt> <code>`: {line}",
                number + 1
            );
        };
        let opt = opt
            .strip_prefix('O')
            .unwrap_or_else(|| panic!("census line {}: bad level {opt}", number + 1));
        let previous = census.insert(
            ((*lane).to_owned(), (*id).to_owned(), opt.to_owned()),
            (*code).to_owned(),
        );
        assert!(
            previous.is_none(),
            "census line {}: duplicate cell {line}",
            number + 1
        );
    }
    census
}

/// The census lines this run's cells would need, for the failure message.
pub fn census_lines(lane: Lane, cells: &[Cell]) -> String {
    cells
        .iter()
        .filter_map(|cell| match &cell.verdict {
            Verdict::Refused { code, .. } => {
                Some(format!("{} {} O{} {code}", lane.label(), cell.id, cell.opt))
            }
            Verdict::OracleUnbuildable { .. } => Some(format!(
                "{} {} O{} {UNBUILDABLE}",
                Lane::Llvm.label(),
                cell.id,
                cell.opt
            )),
            Verdict::PanicMessage { .. } => Some(format!(
                "{} {} O{} {PANIC_MESSAGE}",
                lane.label(),
                cell.id,
                cell.opt
            )),
            _ => None,
        })
        .collect::<Vec<_>>()
        .join("\n")
}

/// The census code of a program LLVM cannot build for this target.
pub const UNBUILDABLE: &str = "UNBUILDABLE";

/// Counts of one lane's cells.
#[derive(Debug, Default)]
pub struct Tally {
    pub cells: usize,
    pub matched: usize,
    pub refusals: BTreeMap<String, usize>,
    pub diverged: usize,
    /// Cells LLVM cannot build for this target (the backend is not run).
    pub unbuildable: usize,
    /// Cells whose panic message differs from LLVM's (same location, exit
    /// status and stdout).
    pub panic_message: usize,
    /// Cells whose oracle did not exit with the program's pinned code.
    pub oracle_off_pin: usize,
}

impl Tally {
    pub fn of(cells: &[Cell]) -> Self {
        let mut tally = Tally {
            cells: cells.len(),
            ..Tally::default()
        };
        for cell in cells {
            match &cell.verdict {
                Verdict::Matched => tally.matched += 1,
                Verdict::Refused { code, .. } => {
                    *tally.refusals.entry(code.clone()).or_insert(0) += 1
                }
                Verdict::Diverged { .. } => tally.diverged += 1,
                Verdict::OracleUnbuildable { .. } => tally.unbuildable += 1,
                Verdict::PanicMessage { .. } => tally.panic_message += 1,
            }
            let off_pin = match (&cell.oracle, cell.expected) {
                (Some(run), Some(code)) => run.ending != Ending::Exited(code),
                _ => false,
            };
            if off_pin {
                tally.oracle_off_pin += 1;
            }
        }
        tally
    }

    pub fn refused(&self) -> usize {
        self.refusals.values().sum()
    }

    pub fn spell_refusals(&self) -> String {
        if self.refusals.is_empty() {
            return "none".to_owned();
        }
        self.refusals
            .iter()
            .map(|(code, count)| format!("{code}:{count}"))
            .collect::<Vec<_>>()
            .join(",")
    }
}

/// Compare the lane's cells with `census` and return the problems, each
/// carrying the cell's own diagnostic. Nothing is printed for a cell the
/// census accounts for: the census file is that record, and a refusal's text
/// (an iterator `skip`, a proof-wall code) is not echoed into a transcript a
/// runner scans.
pub fn check_against_census(
    lane: Lane,
    cells: &[Cell],
    census: &BTreeMap<(String, String, String), String>,
    owns: &dyn Fn(&str) -> bool,
) -> Vec<String> {
    let mut problems = Vec::new();
    for cell in cells {
        let key = (
            lane.label().to_owned(),
            cell.id.clone(),
            cell.opt.to_owned(),
        );
        let pinned = census.get(&key);
        match &cell.verdict {
            Verdict::Matched => {
                if let Some(code) = pinned {
                    problems.push(format!(
                        "`{}` -Copt-level={} now builds and matches; remove its census line ({code})",
                        cell.id, cell.opt
                    ));
                }
            }
            Verdict::Refused { code, line } => match pinned {
                None => problems.push(format!(
                    "`{}` -Copt-level={} is refused ({code}) but not in the census: {line}",
                    cell.id, cell.opt
                )),
                Some(expected) if expected != code => problems.push(format!(
                    "`{}` -Copt-level={} is refused with {code}, census says {expected}: {line}",
                    cell.id, cell.opt
                )),
                Some(_) if code == "UNNAMED" => problems.push(format!(
                    "`{}` -Copt-level={} is refused without a [TCG-*] code: {line}",
                    cell.id, cell.opt
                )),
                Some(_) => {}
            },
            Verdict::OracleUnbuildable { line } => {
                let oracle_key = (
                    Lane::Llvm.label().to_owned(),
                    cell.id.clone(),
                    cell.opt.to_owned(),
                );
                if census.get(&oracle_key).map(String::as_str) != Some(UNBUILDABLE) {
                    problems.push(format!(
                        "`{}` -Copt-level={}: LLVM cannot build it for this target, and the census \
                         has no `llvm .. {UNBUILDABLE}` line: {line}",
                        cell.id, cell.opt
                    ));
                }
            }
            Verdict::PanicMessage { detail } => {
                if pinned.map(String::as_str) != Some(PANIC_MESSAGE) {
                    problems.push(format!(
                        "`{}` -Copt-level={}: the panic message differs from LLVM's (same \
                         location, exit status and stdout) and the census has no \
                         {PANIC_MESSAGE} line: {detail}",
                        cell.id, cell.opt
                    ));
                }
            }
            Verdict::Diverged { detail } => {
                problems.push(format!(
                    "MISCOMPILE `{}` -Copt-level={} ({}): {detail}",
                    cell.id,
                    cell.opt,
                    lane.label()
                ));
            }
        }
    }
    let ran: BTreeSet<(String, String)> = cells
        .iter()
        .map(|cell| (cell.id.clone(), cell.opt.to_owned()))
        .collect();
    let unbuildable: BTreeSet<(String, String)> = cells
        .iter()
        .filter(|cell| matches!(cell.verdict, Verdict::OracleUnbuildable { .. }))
        .map(|cell| (cell.id.clone(), cell.opt.to_owned()))
        .collect();
    for ((census_lane, id, opt), code) in census {
        let cell = (id.clone(), opt.clone());
        if census_lane == lane.label() && owns(id) && !ran.contains(&cell) {
            problems.push(format!(
                "census line `{census_lane} {id} O{opt} {code}` names no cell of this run"
            ));
        }
        if census_lane == Lane::Llvm.label()
            && owns(id)
            && ran.contains(&cell)
            && !unbuildable.contains(&cell)
        {
            problems.push(format!(
                "census line `{census_lane} {id} O{opt} {code}`: LLVM now builds it; remove the line"
            ));
        }
    }
    problems
}
