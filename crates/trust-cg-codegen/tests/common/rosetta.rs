#![allow(dead_code)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;
use std::fs;
use std::io;
#[cfg(unix)]
use std::os::unix::process::{CommandExt, ExitStatusExt};
#[cfg(windows)]
use std::os::windows::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Output, Stdio};
use std::sync::{
    OnceLock,
    atomic::{AtomicU64, Ordering},
};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

// This runner is also included directly by Linux tests under other module
// names. Own its termination dependency here instead of requiring a sibling
// module or a particular name in the including test crate.
#[path = "aarch64_emulation.rs"]
pub mod aarch64_emulation;
#[path = "process_termination.rs"]
pub mod process_termination;
#[cfg(unix)]
pub fn kill_process_group(pgid: u32) {
    process_termination::kill_process_group(pgid);
}

const DEFAULT_TEST_TIMEOUT_SECS: u64 = 1500;
const DEFAULT_CODEGEN_PROBE_TIMEOUT_SECS: u64 = 10;
const DEFAULT_CODEGEN_ROSETTA_PROBE_TIMEOUT_SECS: u64 = 5;
const DEFAULT_CODEGEN_LINK_TIMEOUT_SECS: u64 = 30;
// 60s (not 10s): the e2e binaries run in <1s normally, so this budget only
// matters under heavy shared-host load (concurrent test runs on the same
// machine), where the program itself can be starved of CPU. Time the OS holds
// a fresh executable before its first instruction is not charged to it on
// macOS (see `DEFAULT_CODEGEN_LAUNCH_ADMISSION_TIMEOUT_SECS`). A genuine
// infinite loop still trips this bound. Tune via the `codegen_run_timeout_sec`
// env var / timeout config.
const DEFAULT_CODEGEN_RUN_TIMEOUT_SECS: u64 = 60;
// macOS holds the `exec` of an executable file it has not assessed before:
// the kernel's AppleSystemPolicy parks the new process ahead of its first
// user-mode instruction (`sample` shows its one thread at `_dyld_start + 0`
// with no CPU time) until syspolicyd's XProtect scan of the file returns
// ("Doing an XProtect scan b/c not exempt"). Those scans are queued host-wide,
// so the hold grows with how many new executables (and scripts) every session
// on the host launches, not with anything the program does. Measured
// 2026-10-04 on an 18-core Apple M5 Pro (macOS 26.6) shared at load 40-60: a
// first launch held 0.25-3 s against 5-10 ms for a relaunch, and 40
// executables launched at once held the last one 10.8 s while each ran under
// 13 ms. Ad-hoc re-signing (`codesign -s -`) did not shorten it; for the
// exemption syspolicyd asks TCC for the responsible app's Developer Tools
// right (`kTCCServiceDeveloperTool`), a host setting. A run deadline therefore
// starts only once the child has started (`wait_launch_aware`); this separate
// budget bounds the hold. Tune via `codegen_launch_admission_timeout_sec`.
const DEFAULT_CODEGEN_LAUNCH_ADMISSION_TIMEOUT_SECS: u64 = 300;

pub struct TimedCommandOutput {
    pub output: Output,
    /// Timeout is authoritative even if exit races with termination. A timeout
    /// status can be synthetic; stderr states whether an exit was observed.
    /// Neither the flag nor a kill request guarantees descendant cleanup.
    pub timed_out: bool,
    /// Lower bound on how long the OS held the child before it executed its
    /// first instruction: spawn to the last poll that still saw it not
    /// started. `None` when no poll saw it not started (a hold shorter than
    /// one poll, or a host where [`launch_state`] cannot tell). The deadline
    /// was not charged for this time.
    pub launch_hold: Option<Duration>,
}

static TIMEOUT_CONFIG: OnceLock<BTreeMap<String, u64>> = OnceLock::new();
static SCRATCH_SEQ: AtomicU64 = AtomicU64::new(0);

fn timeout_config() -> &'static BTreeMap<String, u64> {
    TIMEOUT_CONFIG.get_or_init(|| {
        let Some(root) = Path::new(env!("CARGO_MANIFEST_DIR"))
            .parent()
            .and_then(Path::parent)
            .map(Path::to_path_buf)
        else {
            return BTreeMap::new();
        };
        let Ok(text) = fs::read_to_string(root.join("cargo_wrapper.toml")) else {
            return BTreeMap::new();
        };
        parse_timeout_config(&text)
    })
}

fn parse_timeout_config(text: &str) -> BTreeMap<String, u64> {
    let mut timeouts = BTreeMap::new();
    let mut in_timeouts = false;

    for raw in text.lines() {
        let line = raw.split('#').next().unwrap_or("").trim();
        if line.is_empty() {
            continue;
        }
        if line.starts_with('[') && line.ends_with(']') {
            in_timeouts = line == "[timeouts]";
            continue;
        }
        if !in_timeouts {
            continue;
        }
        let Some((key, value)) = line.split_once('=') else {
            continue;
        };
        let value = value.trim().replace('_', "");
        if let Ok(seconds) = value.parse::<u64>()
            && seconds > 0
        {
            timeouts.insert(key.trim().to_string(), seconds);
        }
    }

    timeouts
}

fn env_timeout_seconds(key: &str) -> Option<u64> {
    let env_key = format!("TRUST_CG_{}", key.to_ascii_uppercase());
    std::env::var(env_key)
        .ok()
        .and_then(|raw| raw.parse::<u64>().ok())
        .filter(|seconds| *seconds > 0)
}

fn timeout_seconds(key: &str, fallback: u64) -> u64 {
    let timeouts = timeout_config();
    let shard_cap = timeouts
        .get("test_timeout_sec")
        .copied()
        .unwrap_or(DEFAULT_TEST_TIMEOUT_SECS)
        .max(1);
    env_timeout_seconds(key)
        .or_else(|| timeouts.get(key).copied())
        .unwrap_or(fallback)
        .max(1)
        .min(shard_cap)
}

pub fn codegen_probe_timeout() -> Duration {
    Duration::from_secs(timeout_seconds(
        "codegen_probe_timeout_sec",
        DEFAULT_CODEGEN_PROBE_TIMEOUT_SECS,
    ))
}

fn rosetta_probe_timeout() -> Duration {
    Duration::from_secs(timeout_seconds(
        "codegen_rosetta_probe_timeout_sec",
        DEFAULT_CODEGEN_ROSETTA_PROBE_TIMEOUT_SECS,
    ))
}

pub fn codegen_link_timeout() -> Duration {
    Duration::from_secs(timeout_seconds(
        "codegen_link_timeout_sec",
        DEFAULT_CODEGEN_LINK_TIMEOUT_SECS,
    ))
}

pub fn codegen_run_timeout() -> Duration {
    Duration::from_secs(timeout_seconds(
        "codegen_run_timeout_sec",
        DEFAULT_CODEGEN_RUN_TIMEOUT_SECS,
    ))
}

/// How long [`command_output_with_timeout`] and [`run_executable_with_timeout`]
/// wait for a child that has not executed its first instruction yet.
pub fn codegen_launch_admission_timeout() -> Duration {
    Duration::from_secs(timeout_seconds(
        "codegen_launch_admission_timeout_sec",
        DEFAULT_CODEGEN_LAUNCH_ADMISSION_TIMEOUT_SECS,
    ))
}

/// Integer multiplier for [`exec_timeout`]. Unset means 1: every call site
/// keeps its hard-coded budget exactly.
pub const EXEC_TIMEOUT_SCALE_ENV: &str = "TRUST_CG_TEST_TIMEOUT_SCALE";
/// Largest accepted scale, so a genuine hang still fails in bounded time.
pub const MAX_EXEC_TIMEOUT_SCALE: u32 = 20;

/// Budget for one execution of a program the test itself compiled: `base`
/// times `TRUST_CG_TEST_TIMEOUT_SCALE`. The shared runners start this clock
/// when the program starts, not while the OS holds its launch (macOS), but a
/// heavily loaded host (load 50-100) can still starve a running binary that
/// finishes in milliseconds, so raise the scale there rather than editing
/// budgets. Never use this for a timeout that is itself the subject of an
/// assertion (the kill path of the timeout machinery).
pub fn exec_timeout(base: Duration) -> Duration {
    scale_exec_timeout(base, std::env::var_os(EXEC_TIMEOUT_SCALE_ENV).as_deref())
}

/// [`exec_timeout`] with the variable's raw value supplied. `None` (unset)
/// returns `base`; anything but an integer in `1..=MAX_EXEC_TIMEOUT_SCALE`
/// panics instead of silently falling back to the default budget.
pub fn scale_exec_timeout(base: Duration, raw: Option<&std::ffi::OsStr>) -> Duration {
    let Some(raw) = raw else {
        return base;
    };
    let scale = raw
        .to_str()
        .and_then(|text| text.parse::<u32>().ok())
        .filter(|scale| (1..=MAX_EXEC_TIMEOUT_SCALE).contains(scale));
    match scale {
        Some(scale) => base * scale,
        None => panic!(
            "{EXEC_TIMEOUT_SCALE_ENV}={raw:?} is invalid: expected an integer in \
             1..={MAX_EXEC_TIMEOUT_SCALE}; unset it to keep the default budgets"
        ),
    }
}

fn timeout_scratch_dir(prefix: &str) -> PathBuf {
    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let seq = SCRATCH_SEQ.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "{}_{}_{}_{}",
        prefix,
        std::process::id(),
        stamp,
        seq
    ))
}

fn timeout_stderr(timeout: Duration, action: &str) -> Vec<u8> {
    format!(
        "[trust-cg-timeout] ERROR: Command timed out after {:.3}s (timeout={}s), {}\n",
        timeout.as_secs_f64(),
        timeout.as_secs().max(1),
        action
    )
    .into_bytes()
}

/// Whether a supervised child has executed any of its own code yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LaunchState {
    /// The process exists, and the kernel has counted no system call, no page
    /// fault and no user CPU time for its task: no instruction of it has run.
    NotStarted,
    /// The kernel has counted execution for its task.
    Started,
    /// Not observable here: not macOS, or the counters could not be read (the
    /// process has exited or is a zombie). Callers treat it as `Started`.
    Unknown,
}

/// The kernel's account of whether process `pid` has begun executing.
///
/// macOS reads `proc_pidinfo(PROC_PIDTASKINFO)`. A task `posix_spawn` creates
/// starts with those counters at zero, and its first instruction (dyld's, for
/// every dynamically linked image) moves at least one of them. They belong to
/// the task, which survives `exec`, so a child that ran anything before
/// exec-ing (a shell's `exec`, fork then exec) reads `Started` while its new
/// image is still held: the probe can miss a hold, but it never reports
/// `NotStarted` for a task that has executed code.
pub fn launch_state(pid: u32) -> LaunchState {
    #[cfg(target_os = "macos")]
    {
        darwin_task_counters::launch_state(pid)
    }
    #[cfg(not(target_os = "macos"))]
    {
        let _ = pid;
        LaunchState::Unknown
    }
}

#[cfg(target_os = "macos")]
mod darwin_task_counters {
    use super::LaunchState;
    use std::ffi::c_void;

    /// `struct proc_taskinfo` from `<sys/proc_info.h>`.
    #[repr(C)]
    #[derive(Default)]
    struct ProcTaskInfo {
        virtual_size: u64,
        resident_size: u64,
        total_user: u64,
        total_system: u64,
        threads_user: u64,
        threads_system: u64,
        policy: i32,
        faults: i32,
        pageins: i32,
        cow_faults: i32,
        messages_sent: i32,
        messages_received: i32,
        syscalls_mach: i32,
        syscalls_unix: i32,
        csw: i32,
        threadnum: i32,
        numrunning: i32,
        priority: i32,
    }

    /// `PROC_PIDTASKINFO` from `<sys/proc_info.h>`.
    const PROC_PIDTASKINFO: i32 = 4;

    unsafe extern "C" {
        fn proc_pidinfo(
            pid: i32,
            flavor: i32,
            arg: u64,
            buffer: *mut c_void,
            buffersize: i32,
        ) -> i32;
    }

    pub(super) fn launch_state(pid: u32) -> LaunchState {
        let Ok(pid) = i32::try_from(pid) else {
            return LaunchState::Unknown;
        };
        if pid <= 1 {
            return LaunchState::Unknown;
        }
        let mut info = ProcTaskInfo::default();
        let size = std::mem::size_of::<ProcTaskInfo>() as i32;
        // SAFETY: `info` is a live, writable `proc_taskinfo` of exactly `size`
        // bytes, and `proc_pidinfo` writes at most `buffersize` bytes into it.
        let filled = unsafe {
            proc_pidinfo(
                pid,
                PROC_PIDTASKINFO,
                0,
                (&raw mut info).cast::<c_void>(),
                size,
            )
        };
        if filled != size {
            return LaunchState::Unknown;
        }
        // System time and context switches are left out: the kernel's own
        // `exec` work is charged to the new task before it is released.
        if info.total_user == 0
            && info.syscalls_unix == 0
            && info.syscalls_mach == 0
            && info.faults == 0
        {
            LaunchState::NotStarted
        } else {
            LaunchState::Started
        }
    }
}

/// A child a launch-aware deadline can supervise.
pub trait SupervisedProcess: process_termination::TimeoutProcess {
    fn launch_state(&self) -> LaunchState;
}

impl SupervisedProcess for std::process::Child {
    fn launch_state(&self) -> LaunchState {
        launch_state(self.id())
    }
}

/// How [`wait_launch_aware`] ended.
#[derive(Debug)]
pub enum LaunchAwareEnd {
    Exited(ExitStatus),
    /// Still running when the run budget, counted from its start, ran out.
    RanPastBudget,
    /// Never observed executing before the admission budget ran out.
    NeverStarted,
}

#[derive(Debug)]
pub struct LaunchAwareWait {
    pub end: LaunchAwareEnd,
    /// See [`TimedCommandOutput::launch_hold`].
    pub launch_hold: Option<Duration>,
}

const LAUNCH_AWARE_POLL: Duration = Duration::from_millis(20);
/// Holds at least this long are reported on the test's stderr.
const LAUNCH_HOLD_REPORT: Duration = Duration::from_secs(1);

/// Poll `child`, charging `run_budget` only from the moment it starts.
///
/// While [`SupervisedProcess::launch_state`] reports `NotStarted` no
/// instruction of the child has run, so a hang in it is impossible; that
/// phase is bounded by `admission_budget` alone and ends `NeverStarted`. The
/// run clock starts at the last poll that still saw the child not started (at
/// the call when no poll did, or when the state is `Unknown`), which is never
/// later than its real start, so a child that hangs once running ends
/// `RanPastBudget` no later than `run_budget` plus one poll after it started.
/// The caller spawns `child` immediately before calling this and terminates
/// it on either deadline.
pub fn wait_launch_aware(
    child: &mut impl SupervisedProcess,
    run_budget: Duration,
    admission_budget: Duration,
) -> io::Result<LaunchAwareWait> {
    let spawned = Instant::now();
    let mut launch_hold = None;
    let mut run_origin = None;
    loop {
        if let Some(status) = child.try_wait()? {
            return Ok(LaunchAwareWait {
                end: LaunchAwareEnd::Exited(status),
                launch_hold,
            });
        }
        let now = Instant::now();
        let origin = match run_origin {
            Some(origin) => origin,
            None if child.launch_state() == LaunchState::NotStarted => {
                let held = now.duration_since(spawned);
                launch_hold = Some(held);
                if held >= admission_budget {
                    return Ok(LaunchAwareWait {
                        end: LaunchAwareEnd::NeverStarted,
                        launch_hold,
                    });
                }
                thread::sleep(LAUNCH_AWARE_POLL);
                continue;
            }
            None => *run_origin.insert(spawned + launch_hold.unwrap_or_default()),
        };
        if now.duration_since(origin) >= run_budget {
            return Ok(LaunchAwareWait {
                end: LaunchAwareEnd::RanPastBudget,
                launch_hold,
            });
        }
        thread::sleep(LAUNCH_AWARE_POLL);
    }
}

/// Regular files that receive a child's stdout and stderr.
struct CapturedStdio {
    dir: PathBuf,
    stdout: PathBuf,
    stderr: PathBuf,
}

impl CapturedStdio {
    fn new(prefix: &str) -> io::Result<Self> {
        let dir = timeout_scratch_dir(prefix);
        fs::create_dir_all(&dir)?;
        Ok(Self {
            stdout: dir.join("stdout"),
            stderr: dir.join("stderr"),
            dir,
        })
    }

    /// Spawn `cmd` in its own process group with stdin closed and stdout and
    /// stderr going to the capture files.
    fn spawn(&self, cmd: &mut Command) -> io::Result<std::process::Child> {
        cmd.stdin(Stdio::null())
            .stdout(Stdio::from(fs::File::create(&self.stdout)?))
            .stderr(Stdio::from(fs::File::create(&self.stderr)?));
        #[cfg(unix)]
        cmd.process_group(0);
        cmd.spawn()
    }

    /// Read both files and remove the scratch directory.
    fn finish(self) -> (Vec<u8>, Vec<u8>) {
        let stdout = fs::read(&self.stdout).unwrap_or_default();
        let stderr = fs::read(&self.stderr).unwrap_or_default();
        let _ = fs::remove_dir_all(&self.dir);
        (stdout, stderr)
    }
}

/// How a runner reports a child's status.
#[derive(Clone, Copy, PartialEq, Eq)]
enum StatusReport {
    /// The child's own status; after a timeout, the observed one when the
    /// termination poll saw an exit, else a synthetic SIGKILL.
    AsObserved,
    /// The executable runner's shell convention: an exit code as is, death by
    /// signal `s` as exit code `128 + s`, and a timeout as raw status 9.
    ShellConvention,
}

/// Supervise a child [`CapturedStdio::spawn`] just started.
fn supervise(
    mut child: std::process::Child,
    capture: CapturedStdio,
    timeout: Duration,
    report: StatusReport,
) -> io::Result<TimedCommandOutput> {
    let waited = wait_launch_aware(&mut child, timeout, codegen_launch_admission_timeout());
    let waited = match waited {
        Ok(waited) => waited,
        Err(error) => {
            let _ = process_termination::terminate(&mut child);
            let _ = capture.finish();
            return Err(error);
        }
    };
    let launch_hold = waited.launch_hold;
    if let Some(held) = launch_hold.filter(|held| *held >= LAUNCH_HOLD_REPORT) {
        // Captured by the test harness unless the test fails or runs with
        // `--nocapture`: evidence that a deadline did not include this time.
        eprintln!(
            "[trust-cg-launch-hold] child pid={} had executed nothing {:.3}s after spawn \
             (not charged to its {:.3}s deadline)",
            child.id(),
            held.as_secs_f64(),
            timeout.as_secs_f64()
        );
    }
    let (budget, what) = match waited.end {
        LaunchAwareEnd::Exited(status) => {
            let (stdout, stderr) = capture.finish();
            let status = match report {
                StatusReport::AsObserved => status,
                StatusReport::ShellConvention => shell_convention(status),
            };
            return Ok(TimedCommandOutput {
                output: Output {
                    status,
                    stdout,
                    stderr,
                },
                timed_out: false,
                launch_hold,
            });
        }
        LaunchAwareEnd::RanPastBudget => (
            timeout,
            match launch_hold {
                Some(held) => format!(
                    "run deadline counted from its start, after a {:.3}s launch hold",
                    held.as_secs_f64()
                ),
                None => "run deadline counted from its spawn".to_owned(),
            },
        ),
        LaunchAwareEnd::NeverStarted => (
            codegen_launch_admission_timeout(),
            "it never started: no system call, page fault or user time was counted for \
             it (the OS held its exec; on macOS, syspolicyd's first-launch assessment)"
                .to_owned(),
        ),
    };
    let termination = process_termination::terminate(&mut child);
    let status = match report {
        StatusReport::AsObserved => termination.status.unwrap_or_else(killed_status),
        StatusReport::ShellConvention => killed_status(),
    };
    let (stdout, mut stderr) = capture.finish();
    stderr.extend_from_slice(&timeout_stderr(
        budget,
        &format!(
            "child pid={}: {}; {what}",
            child.id(),
            termination.diagnostic()
        ),
    ));
    Ok(TimedCommandOutput {
        output: Output {
            status,
            stdout,
            stderr,
        },
        timed_out: true,
        launch_hold,
    })
}

/// Raw wait status 9: killed by SIGKILL (Unix), exit code 9 (Windows).
fn killed_status() -> ExitStatus {
    ExitStatus::from_raw(9)
}

/// `128 + signal` for a child a signal killed, as `/bin/sh` reports it.
fn shell_convention(status: ExitStatus) -> ExitStatus {
    #[cfg(unix)]
    if let Some(signal) = status.signal() {
        return ExitStatus::from_raw((128 + signal) << 8);
    }
    status
}

/// Run `cmd` directly and capture its output in regular files.
///
/// `timeout` is charged only once the child has started executing; the OS's
/// hold before that is bounded by [`codegen_launch_admission_timeout`]
/// instead (see [`wait_launch_aware`]). Neither deadline bounds OS spawn or
/// filesystem operations. On timeout, request termination and poll once
/// without waiting for reaping. Kernel-blocked children or escaped
/// descendants can remain alive; do not treat a returned timeout as
/// permission to reuse an unhealthy execution host.
pub fn command_output_with_timeout(
    cmd: &mut Command,
    timeout: Duration,
) -> io::Result<TimedCommandOutput> {
    let capture = CapturedStdio::new("trust_cg_cmd_output_timeout")?;
    match capture.spawn(cmd) {
        Ok(child) => supervise(child, capture, timeout, StatusReport::AsObserved),
        Err(error) => {
            let _ = capture.finish();
            Err(error)
        }
    }
}

/// Run an executable with no arguments under [`command_output_with_timeout`]'s
/// deadlines, reporting statuses by the shell's `128 + signal` convention.
///
/// The executable is spawned directly, so it is the supervised child and its
/// launch hold is visible to [`launch_state`]. When the kernel refuses to
/// start it at all (`ENOEXEC`, `EACCES`, a wrong architecture, ...) it is
/// rerun through `/bin/sh`, which keeps that shell's established results for
/// such a file: 126 or 127 with the shell's message on stderr, or a
/// shebang-less text file run as a script.
pub fn run_executable_with_timeout(
    program: &Path,
    timeout: Duration,
) -> io::Result<TimedCommandOutput> {
    if let Some(mut command) = aarch64_emulation::configured_command(program)? {
        let capture = CapturedStdio::new("trust_cg_emulated_cmd_timeout")?;
        let child = match capture.spawn(&mut command) {
            Ok(child) => child,
            Err(error) => {
                let _ = capture.finish();
                return Err(error);
            }
        };
        return supervise(child, capture, timeout, StatusReport::ShellConvention);
    }
    #[cfg(not(unix))]
    {
        let mut cmd = Command::new(program);
        return command_output_with_timeout(&mut cmd, timeout);
    }

    #[cfg(unix)]
    {
        let capture = CapturedStdio::new("trust_cg_cmd_timeout")?;
        let child = match capture.spawn(&mut Command::new(program)) {
            Ok(child) => child,
            Err(_) => {
                // The shell's own stdio stays closed; only the program's
                // streams are redirected into the capture files, as before
                // direct spawning.
                let mut shell = Command::new("/bin/sh");
                shell
                    .arg("-c")
                    .arg(r#""$1" >"$2" 2>"$3"; status=$?; exit "$status""#)
                    .arg("trust-cg-rosetta-probe")
                    .arg(program)
                    .arg(&capture.stdout)
                    .arg(&capture.stderr)
                    .stdin(Stdio::null())
                    .stdout(Stdio::null())
                    .stderr(Stdio::null())
                    .process_group(0);
                match shell.spawn() {
                    Ok(child) => child,
                    Err(error) => {
                        let _ = capture.finish();
                        return Err(error);
                    }
                }
            }
        };
        supervise(child, capture, timeout, StatusReport::ShellConvention)
    }
}

fn output_text(output: &Output) -> (String, String) {
    (
        String::from_utf8_lossy(&output.stdout).to_string(),
        String::from_utf8_lossy(&output.stderr).to_string(),
    )
}

fn probe_timeout() -> Duration {
    rosetta_probe_timeout()
}

/// Environment variable naming the x86-64 C driver on a host whose own `cc`
/// does not target x86-64, as a whitespace-separated command line (for example
/// `x86_64-linux-gnu-gcc` or `clang --target=x86_64-linux-gnu`). When set it is
/// the only candidate the probe tries.
pub const X86_64_CC_ENV: &str = "TRUST_CG_X86_64_CC";

/// The GNU cross driver tried on a Linux host that is not itself x86-64.
const LINUX_X86_64_CROSS_CC: &str = "x86_64-linux-gnu-gcc";

/// Line the probe program prints once it actually executes.
const X86_64_PROBE_MARKER: &str = "trust-cg-x86_64-link-run-probe";

/// The probe program refuses to compile unless the driver targets x86-64, so a
/// native non-x86 `cc` cannot pass for an x86-64 one.
const X86_64_PROBE_SOURCE: &str = "#include <stdio.h>\n\
#if !defined(__x86_64__)\n\
#error \"this C driver does not target x86-64\"\n\
#endif\n\
int main(void) { puts(\"trust-cg-x86_64-link-run-probe\"); return 0; }\n";

/// A C driver that this host has been proven to link AND run x86-64
/// executables with: [`x86_64_link_run`] compiled a program that only builds
/// for x86-64, checked that the linked executable's header names x86-64, and
/// ran it to its marker line.
#[derive(Debug, Clone)]
pub struct X86_64LinkRun {
    program: String,
    target_args: Vec<String>,
}

impl X86_64LinkRun {
    /// A fresh `Command` for the proven driver, already carrying its x86-64
    /// selection arguments (`-arch x86_64` on macOS); callers append the rest.
    pub fn command(&self) -> Command {
        let mut command = Command::new(&self.program);
        command.args(&self.target_args);
        command
    }

    /// The driver's command line for evidence and diagnostics.
    pub fn describe(&self) -> String {
        std::iter::once(self.program.as_str())
            .chain(self.target_args.iter().map(String::as_str))
            .collect::<Vec<_>>()
            .join(" ")
    }
}

/// The C driver that should link x86-64 executables on this host.
fn x86_64_driver_candidate() -> Result<X86_64LinkRun, String> {
    let driver = |program: &str, target_args: &[&str]| X86_64LinkRun {
        program: program.to_owned(),
        target_args: target_args.iter().map(|arg| (*arg).to_owned()).collect(),
    };
    if let Some(raw) = std::env::var_os(X86_64_CC_ENV) {
        let raw = raw.to_string_lossy().into_owned();
        let words: Vec<&str> = raw.split_whitespace().collect();
        return match words.split_first() {
            Some((program, target_args)) => Ok(driver(program, target_args)),
            None => Err(format!("{X86_64_CC_ENV} is set but empty")),
        };
    }
    if cfg!(target_os = "macos") {
        // Apple's driver selects the slice with `-arch` (native x86-64, or
        // Rosetta 2 on Apple silicon).
        Ok(driver("cc", &["-arch", "x86_64"]))
    } else if cfg!(target_arch = "x86_64") {
        Ok(driver("cc", &[]))
    } else if cfg!(target_os = "linux") {
        // The host `cc` links native (non-x86) executables here; only a cross
        // driver produces x86-64 ones, and running them needs a binfmt_misc
        // handler (qemu-user).
        Ok(driver(LINUX_X86_64_CROSS_CC, &[]))
    } else {
        Err(format!(
            "no x86-64 C driver is known for a {}-{} host; name one in {X86_64_CC_ENV}",
            std::env::consts::ARCH,
            std::env::consts::OS
        ))
    }
}

/// `Ok` when `image` is an x86-64 executable (ELF `EM_X86_64` `ET_EXEC`/`ET_DYN`
/// or thin Mach-O `CPU_TYPE_X86_64` `MH_EXECUTE`); otherwise what it is.
fn check_x86_64_executable_header(image: &[u8]) -> Result<(), String> {
    const EM_X86_64: u16 = 62;
    const MH_MAGIC_64: u32 = 0xfeed_facf;
    const CPU_TYPE_X86_64: u32 = 0x0100_0007;
    const MH_EXECUTE: u32 = 2;
    let u16_at = |offset: usize| u16::from_le_bytes([image[offset], image[offset + 1]]);
    let u32_at = |offset: usize| {
        u32::from_le_bytes([
            image[offset],
            image[offset + 1],
            image[offset + 2],
            image[offset + 3],
        ])
    };
    if image.len() >= 20 && image[..4] == *b"\x7fELF" {
        let (e_type, e_machine) = (u16_at(16), u16_at(18));
        return if e_machine == EM_X86_64 && matches!(e_type, 2 | 3) {
            Ok(())
        } else {
            Err(format!(
                "linked an ELF image with e_machine={e_machine} e_type={e_type}, not an x86-64 \
                 executable (e_machine={EM_X86_64})"
            ))
        };
    }
    if image.len() >= 16 && u32_at(0) == MH_MAGIC_64 {
        let (cputype, filetype) = (u32_at(4), u32_at(12));
        return if cputype == CPU_TYPE_X86_64 && filetype == MH_EXECUTE {
            Ok(())
        } else {
            Err(format!(
                "linked a Mach-O image with cputype={cputype:#x} filetype={filetype}, not an \
                 x86-64 MH_EXECUTE (cputype={CPU_TYPE_X86_64:#x})"
            ))
        };
    }
    Err(format!(
        "linked {} bytes that are neither a 64-bit ELF nor a thin 64-bit Mach-O executable",
        image.len()
    ))
}

/// Link the probe program with one candidate driver and run it.
fn probe_x86_64_driver(driver: &X86_64LinkRun) -> Result<(), String> {
    let dir = timeout_scratch_dir("trust_cg_x86_64_cc_check");
    let result = probe_x86_64_driver_in(driver, &dir);
    let _ = fs::remove_dir_all(&dir);
    result
}

fn probe_x86_64_driver_in(driver: &X86_64LinkRun, dir: &Path) -> Result<(), String> {
    fs::create_dir_all(dir).map_err(|e| format!("create {}: {e}", dir.display()))?;
    let src = dir.join("check.c");
    let exe = dir.join("check");
    fs::write(&src, X86_64_PROBE_SOURCE).map_err(|e| format!("write probe source: {e}"))?;

    let mut compile = driver.command();
    compile.args(["-o", exe.to_str().unwrap(), src.to_str().unwrap()]);
    let compiled = match command_output_with_timeout(&mut compile, probe_timeout()) {
        Ok(result) => result,
        Err(e) if e.kind() == io::ErrorKind::NotFound => {
            return Err("not found on PATH".to_owned());
        }
        Err(e) => return Err(format!("failed to start: {e}")),
    };
    if compiled.timed_out || !compiled.output.status.success() {
        let (stdout, stderr) = output_text(&compiled.output);
        return Err(format!(
            "compile+link of the x86-64 probe program {} (status {:?}); stdout={}, stderr={}",
            if compiled.timed_out {
                format!("timed out after {:?}", probe_timeout())
            } else {
                "failed".to_owned()
            },
            compiled.output.status.code(),
            stdout.trim(),
            stderr.trim()
        ));
    }
    let image = fs::read(&exe).map_err(|e| format!("read linked probe: {e}"))?;
    check_x86_64_executable_header(&image)?;

    let ran = run_executable_with_timeout(&exe, probe_timeout())
        .map_err(|e| format!("linked an x86-64 executable but could not start it: {e}"))?;
    let (stdout, stderr) = output_text(&ran.output);
    if ran.timed_out || !ran.output.status.success() || stdout.trim() != X86_64_PROBE_MARKER {
        return Err(format!(
            "linked an x86-64 executable but running it {} (status {:?}); stdout={}, stderr={}",
            if ran.timed_out {
                format!("timed out after {:?}", probe_timeout())
            } else {
                "did not print the probe marker".to_owned()
            },
            ran.output.status.code(),
            stdout.trim(),
            stderr.trim()
        ));
    }
    Ok(())
}

/// The binfmt_misc x86-64 handlers registered on a Linux host that is not
/// itself x86-64, for the skip reason; empty elsewhere.
fn linux_binfmt_x86_64_note() -> String {
    if !cfg!(target_os = "linux") || cfg!(target_arch = "x86_64") {
        return String::new();
    }
    let registered = fs::read_dir("/proc/sys/fs/binfmt_misc")
        .map(|entries| {
            entries
                .filter_map(Result::ok)
                .map(|entry| entry.file_name().to_string_lossy().into_owned())
                .filter(|name| name.contains("x86_64") || name.contains("x86-64"))
                .collect::<Vec<_>>()
        })
        .unwrap_or_default();
    if registered.is_empty() {
        "; binfmt_misc has no x86-64 handler registered (running x86-64 executables here \
         needs qemu-user)"
            .to_owned()
    } else {
        format!("; binfmt_misc x86-64 handler(s): {}", registered.join(", "))
    }
}

fn probe_x86_64_link_run() -> Result<X86_64LinkRun, String> {
    if cfg!(all(target_os = "macos", target_arch = "aarch64"))
        && std::env::var_os("TRUST_CG_RUN_ROSETTA_LINKRUN").is_none()
    {
        return Err(
            "Rosetta x86_64 link/run disabled on aarch64 macOS host; set \
             TRUST_CG_RUN_ROSETTA_LINKRUN=1 only on a healthy Rosetta host (#582)"
                .to_owned(),
        );
    }
    let driver = x86_64_driver_candidate()?;
    match probe_x86_64_driver(&driver) {
        Ok(()) => Ok(driver),
        Err(failure) => Err(format!(
            "no C driver on this {}-{} host links and runs an x86-64 executable (probe: `{}` \
             {failure}{}); set {X86_64_CC_ENV} to an x86-64 driver whose output this host can \
             execute",
            std::env::consts::ARCH,
            std::env::consts::OS,
            driver.describe(),
            linux_binfmt_x86_64_note()
        )),
    }
}

/// The one host-capability probe for x86-64 link-and-run legs: the proven C
/// driver, or why this host cannot link and run an x86-64 executable. Probed
/// once per test binary by actually linking and running a program that only
/// compiles for x86-64 (native x86-64, Rosetta 2 on opted-in Apple silicon, or
/// a cross driver plus binfmt_misc/qemu-user), then cached.
pub fn x86_64_link_run() -> Result<&'static X86_64LinkRun, &'static str> {
    static PROBE: OnceLock<Result<X86_64LinkRun, String>> = OnceLock::new();
    PROBE
        .get_or_init(probe_x86_64_link_run)
        .as_ref()
        .map_err(String::as_str)
}

/// Whether [`x86_64_link_run`] proved an x86-64 driver on this host.
pub fn has_cc_x86_64_link_run() -> bool {
    x86_64_link_run().is_ok()
}

/// A `Command` for the proven x86-64 C driver. Callers gate on
/// [`x86_64_link_run_or_skip`] (or [`has_cc_x86_64_link_run`]) first; reaching
/// this on a host without one is a harness bug and panics with the probe result.
pub fn x86_64_cc() -> Command {
    match x86_64_link_run() {
        Ok(driver) => driver.command(),
        Err(reason) => panic!(
            "an x86-64 link/run leg ran on a host that cannot link and run x86-64 \
             executables: {reason}"
        ),
    }
}

/// Gate for an x86-64 link/run leg: `true` when [`x86_64_link_run`] proved a
/// driver; otherwise prints `SKIP: <test>: <leg> not run: <probe result>` and
/// returns `false`, so the caller skips only that leg and keeps every
/// compilation and object-inspection leg before it.
pub fn x86_64_link_run_or_skip(test: &str, leg: &str) -> bool {
    match x86_64_link_run() {
        Ok(_) => true,
        Err(reason) => {
            eprintln!("SKIP: {test}: {leg} not run: {reason}");
            false
        }
    }
}
