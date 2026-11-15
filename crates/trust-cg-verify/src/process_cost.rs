// trust-cg-verify/process_cost.rs - counters of per-process start-up work
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Counters of the work a process does whatever program it compiles: external
//! proof-tool requests and whole-executable content digests.
//!
//! A warm compile of an empty crate measured (Trust 9192 on an M4 Max,
//! 2026-09-28) four `clean` control-proof processes and four executable
//! digests of 91-116 MB each, about 700 M instructions retired, before any
//! per-function work. These counters make that work countable in a real
//! compile: the rustc bridge prints a [`snapshot`] under its `time` knob.
//!
//! They are diagnostics only, never proof authority. Request counters are
//! conservative work budgets, not confirmed OS process counts: constructing
//! an AY command need not spawn it, and a checker probe can fail before spawn.
//! The bridge fixture checks these budgets separately from runtime behavior.
//!
//! The start-path trace ([`set_start_path_trace`], [`mark`]) records when the
//! start-up steps of a compile happen (AY admission, the private copy, the
//! host's first-start assessment, checker probes, the first solve's wait),
//! in milliseconds from the process's start where the OS reports it. It is
//! off unless the bridge's `time` knob enables it, and it changes no decision.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};
use std::time::Instant;

static CHECKER_PROBES: AtomicU64 = AtomicU64::new(0);
static EXECUTABLE_DIGESTS: AtomicU64 = AtomicU64::new(0);
static EXECUTABLE_DIGEST_BYTES: AtomicU64 = AtomicU64::new(0);
static SOLVER_STARTS: AtomicU64 = AtomicU64::new(0);
static ASSESSMENT_SPAWNS: AtomicU64 = AtomicU64::new(0);
static CERTIFICATE_REPLAYS: AtomicU64 = AtomicU64::new(0);

/// The counts so far in this process.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProcessCost {
    /// Requests to run the checker capability control proof, including spawn
    /// failures. Not a count of confirmed `clean` child processes.
    pub checker_probes: u64,
    /// Whole-file content digests of an executable (AY, a checker, its private
    /// copy while it is written); memoized answers are not counted.
    pub executable_digests: u64,
    /// Bytes those digests read.
    pub executable_digest_bytes: u64,
    /// Commands constructed after revalidating an admitted private AY copy.
    /// The legacy field/trace name is retained; dropping a command without
    /// spawning it still counts, while spawning one command twice counts once.
    /// This is not a count of confirmed AY child processes.
    pub solver_starts: u64,
    /// Suspended spawns of a newly published AY copy, each killed before it
    /// ran, that begin the host's first-start assessment early (macOS only;
    /// `ay_private_copy::begin_host_assessment`). Not solver starts.
    pub assessment_spawns: u64,
    /// Stored-certificate replays started by the independent checker (one
    /// `clean` process each), by the compile or by the replay prefetch
    /// (`cert_replay_prefetch`). Memo answers are not counted.
    pub certificate_replays: u64,
}

impl ProcessCost {
    /// One line, `key=value` pairs, for traces.
    pub fn describe(&self) -> String {
        format!(
            "checker_probes={} executable_digests={} executable_digest_mb={:.1} solver_starts={} \
             assessment_spawns={} certificate_replays={}",
            self.checker_probes,
            self.executable_digests,
            self.executable_digest_bytes as f64 / 1_000_000.0,
            self.solver_starts,
            self.assessment_spawns,
            self.certificate_replays,
        )
    }
}

/// The counts so far in this process.
pub fn snapshot() -> ProcessCost {
    ProcessCost {
        checker_probes: CHECKER_PROBES.load(Ordering::Relaxed),
        executable_digests: EXECUTABLE_DIGESTS.load(Ordering::Relaxed),
        executable_digest_bytes: EXECUTABLE_DIGEST_BYTES.load(Ordering::Relaxed),
        solver_starts: SOLVER_STARTS.load(Ordering::Relaxed),
        assessment_spawns: ASSESSMENT_SPAWNS.load(Ordering::Relaxed),
        certificate_replays: CERTIFICATE_REPLAYS.load(Ordering::Relaxed),
    }
}

pub(crate) fn note_checker_probe() {
    CHECKER_PROBES.fetch_add(1, Ordering::Relaxed);
    mark("checker_probe");
}

/// Count one whole-file digest of `bytes` bytes; `label` names it in the
/// start-path trace.
pub(crate) fn note_executable_digest(bytes: u64, label: &'static str) {
    EXECUTABLE_DIGESTS.fetch_add(1, Ordering::Relaxed);
    EXECUTABLE_DIGEST_BYTES.fetch_add(bytes, Ordering::Relaxed);
    mark(label);
}

pub(crate) fn note_solver_start() {
    SOLVER_STARTS.fetch_add(1, Ordering::Relaxed);
    mark("ay_command");
}

pub(crate) fn note_certificate_replay() {
    CERTIFICATE_REPLAYS.fetch_add(1, Ordering::Relaxed);
}

#[cfg_attr(not(target_os = "macos"), allow(dead_code))]
pub(crate) fn note_assessment_spawn() {
    ASSESSMENT_SPAWNS.fetch_add(1, Ordering::Relaxed);
}

// ---------------------------------------------------------------------------
// Start-path trace
// ---------------------------------------------------------------------------

static START_PATH_TRACE: AtomicBool = AtomicBool::new(false);
static START_PATH_MARKS: Mutex<Vec<(&'static str, f64)>> = Mutex::new(Vec::new());

/// The anchor every mark is measured from: an `Instant` and, when the OS
/// reports the process's start time, how many milliseconds after that start
/// the anchor was taken.
fn start_path_origin() -> &'static (Instant, Option<f64>) {
    static ORIGIN: OnceLock<(Instant, Option<f64>)> = OnceLock::new();
    ORIGIN.get_or_init(|| (Instant::now(), process_start_to_now_ms()))
}

/// Turn the start-path trace on or off for this process (the bridge's `time`
/// knob). Enabling it fixes the origin the marks are measured from.
pub fn set_start_path_trace(enabled: bool) {
    if enabled {
        start_path_origin();
    }
    START_PATH_TRACE.store(enabled, Ordering::Relaxed);
}

/// Whether [`mark`] records anything.
pub fn start_path_trace_enabled() -> bool {
    START_PATH_TRACE.load(Ordering::Relaxed)
}

/// Record that the start-up step `label` happened now (no-op unless the
/// trace is on). Repeated labels are kept in order.
pub fn mark(label: &'static str) {
    if !start_path_trace_enabled() {
        return;
    }
    let (anchor, offset) = start_path_origin();
    let ms = offset.unwrap_or(0.0) + anchor.elapsed().as_secs_f64() * 1000.0;
    START_PATH_MARKS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .push((label, ms));
}

/// One line of `label=milliseconds` pairs in the order they were recorded,
/// prefixed by where the clock starts: `origin=process` (the process's start,
/// read from the OS) or `origin=trace` (when the trace was enabled).
pub fn describe_start_path() -> String {
    let origin = if start_path_origin().1.is_some() {
        "process"
    } else {
        "trace"
    };
    let marks = START_PATH_MARKS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    let mut line = format!("origin={origin}");
    for (label, ms) in marks.iter() {
        line.push_str(&format!(" {label}={ms:.1}"));
    }
    line
}

/// Milliseconds from this process's start (as the kernel records it) to now,
/// or `None` where that start time cannot be read.
pub fn process_start_to_now_ms() -> Option<f64> {
    process_start_to_now_ms_impl()
}

#[cfg(target_os = "macos")]
fn process_start_to_now_ms_impl() -> Option<f64> {
    // `proc_pidinfo(PROC_PIDTBSDINFO)` reports the start time as wall-clock
    // seconds and microseconds.
    let mut info = std::mem::MaybeUninit::<libc::proc_bsdinfo>::zeroed();
    let size = libc::c_int::try_from(std::mem::size_of::<libc::proc_bsdinfo>()).ok()?;
    // SAFETY: `info` is a writable, zero-initialized `proc_bsdinfo` of `size`
    // bytes, the buffer this flavor fills; the call writes at most `size`.
    let written = unsafe {
        libc::proc_pidinfo(
            libc::getpid(),
            libc::PROC_PIDTBSDINFO,
            0,
            info.as_mut_ptr().cast(),
            size,
        )
    };
    if written != size {
        return None;
    }
    // SAFETY: the kernel filled all `size` bytes (checked above), and every
    // bit pattern is a valid `proc_bsdinfo`.
    let info = unsafe { info.assume_init() };
    let started = std::time::Duration::from_secs(info.pbi_start_tvsec)
        + std::time::Duration::from_micros(info.pbi_start_tvusec);
    let now = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .ok()?;
    Some(now.checked_sub(started)?.as_secs_f64() * 1000.0)
}

#[cfg(target_os = "linux")]
fn process_start_to_now_ms_impl() -> Option<f64> {
    // Field 22 (1-based) of /proc/self/stat is the start time in clock ticks
    // since boot; the fields after the parenthesised comm are
    // whitespace-separated.
    let stat = std::fs::read_to_string("/proc/self/stat").ok()?;
    let after_comm = stat.get(stat.rfind(')')? + 2..)?;
    let starttime_ticks: f64 = after_comm.split_whitespace().nth(19)?.parse().ok()?;
    let uptime_s: f64 = std::fs::read_to_string("/proc/uptime")
        .ok()?
        .split_whitespace()
        .next()?
        .parse()
        .ok()?;
    // SAFETY: `sysconf` has no memory-safety preconditions.
    let hz = unsafe { libc::sysconf(libc::_SC_CLK_TCK) };
    if hz <= 0 {
        return None;
    }
    Some((uptime_s - starttime_ticks / hz as f64) * 1000.0)
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn process_start_to_now_ms_impl() -> Option<f64> {
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn counters_only_increase_and_describe_every_field() {
        let before = snapshot();
        note_checker_probe();
        note_executable_digest(2_500_000, "digest_test");
        note_solver_start();
        note_assessment_spawn();
        note_certificate_replay();
        let after = snapshot();
        assert!(after.checker_probes > before.checker_probes);
        assert!(after.executable_digests > before.executable_digests);
        assert!(after.executable_digest_bytes >= before.executable_digest_bytes + 2_500_000);
        assert!(after.solver_starts > before.solver_starts);
        assert!(after.assessment_spawns > before.assessment_spawns);
        assert!(after.certificate_replays > before.certificate_replays);
        let line = after.describe();
        for key in [
            "checker_probes=",
            "executable_digests=",
            "executable_digest_mb=",
            "solver_starts=",
            "assessment_spawns=",
            "certificate_replays=",
        ] {
            assert!(line.contains(key), "{line}");
        }
    }

    #[test]
    fn start_path_marks_are_recorded_in_order_only_while_enabled() {
        // Other tests in this binary never enable the trace, so the marks
        // below are the only ones.
        mark("before_enable");
        set_start_path_trace(true);
        mark("first_step");
        mark("second_step");
        set_start_path_trace(false);
        mark("after_disable");
        let line = describe_start_path();
        assert!(!line.contains("before_enable"), "{line}");
        assert!(!line.contains("after_disable"), "{line}");
        let first = line.find(" first_step=").expect(&line);
        let second = line.find(" second_step=").expect(&line);
        assert!(first < second, "{line}");
        let value = |label: &str| -> f64 {
            line.split_whitespace()
                .find_map(|pair| pair.strip_prefix(label)?.strip_prefix('='))
                .and_then(|ms| ms.parse().ok())
                .expect(label)
        };
        let first_ms = value("first_step");
        let second_ms = value("second_step");
        assert!(first_ms.is_finite() && second_ms.is_finite(), "{line}");
        assert!(first_ms >= 0.0 && first_ms <= second_ms, "{line}");
        if cfg!(any(target_os = "macos", target_os = "linux")) {
            assert!(line.starts_with("origin=process"), "{line}");
            // Kernel clock resolution can report zero elapsed time for a
            // process that started before the trace was enabled.
            assert!(
                first_ms < 86_400_000.0 && second_ms < 86_400_000.0,
                "{line}"
            );
        }
    }

    #[cfg(any(target_os = "macos", target_os = "linux"))]
    #[test]
    fn process_start_is_read_from_the_os() {
        let ms = process_start_to_now_ms().expect("the OS reports this process's start");
        // A test process has been running for less than a day; the kernel's
        // clock resolution may report zero elapsed time.
        assert!(ms.is_finite() && (0.0..86_400_000.0).contains(&ms), "{ms}");
    }
}
