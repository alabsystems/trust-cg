// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(unix)]

mod common;

#[path = "common/watchdog.rs"]
mod watchdog;

use common::rosetta::process_termination::{TimeoutProcess, terminate};
use common::rosetta::{
    TimedCommandOutput, command_output_with_timeout, run_executable_with_timeout,
};
use std::fs;
use std::io;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::process::ExitStatusExt;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus};
use std::sync::{
    Mutex, OnceLock,
    atomic::{AtomicU64, Ordering},
};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

static SCRATCH_SEQ: AtomicU64 = AtomicU64::new(0);
static COMMAND_TIMEOUT_TEST_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
const COMMAND_TIMEOUT_REGRESSION_TIMEOUT: Duration = Duration::from_secs(15);

struct DelayedTermination {
    polls: usize,
    kills: usize,
    next_poll: io::Result<Option<ExitStatus>>,
    kill_fails: bool,
}

impl TimeoutProcess for DelayedTermination {
    fn request_kill(&mut self) -> io::Result<()> {
        self.kills += 1;
        if self.kill_fails {
            Err(io::Error::from(io::ErrorKind::PermissionDenied))
        } else {
            Ok(())
        }
    }

    fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        self.polls += 1;
        std::mem::replace(&mut self.next_poll, Ok(None))
    }
}

#[test]
fn termination_model_exposes_a_pending_poll_without_blocking() {
    let mut process = DelayedTermination {
        polls: 0,
        kills: 0,
        next_poll: Ok(None),
        kill_fails: false,
    };
    assert!(process.try_wait().expect("model poll").is_none());
    assert_eq!((process.kills, process.polls), (0, 1));
}

#[test]
fn termination_pending_after_kill_does_not_block_or_invent_an_exit_status() {
    let mut process = DelayedTermination {
        polls: 0,
        kills: 0,
        next_poll: Ok(None),
        kill_fails: false,
    };
    let result = terminate(&mut process);
    assert_eq!((process.kills, process.polls), (1, 1));
    assert!(result.status.is_none());
    assert!(result.kill_error.is_none());
    assert!(result.poll_error.is_none());
    assert!(result.diagnostic().contains("child exit not confirmed"));
}

#[test]
fn termination_preserves_an_observed_exit_even_when_kill_races_with_exit() {
    let mut process = DelayedTermination {
        polls: 0,
        kills: 0,
        next_poll: Ok(Some(ExitStatus::from_raw(7 << 8))),
        kill_fails: true,
    };
    let result = terminate(&mut process);
    assert_eq!((process.kills, process.polls), (1, 1));
    assert!(result.diagnostic().contains("observed child status"));
    assert_eq!(result.status.and_then(|status| status.code()), Some(7));
    assert_eq!(
        result.kill_error.map(|error| error.kind()),
        Some(io::ErrorKind::PermissionDenied)
    );
    assert!(result.poll_error.is_none());
}

#[test]
fn termination_preserves_kill_and_poll_errors_without_blocking_retry() {
    let mut process = DelayedTermination {
        polls: 0,
        kills: 0,
        next_poll: Err(io::Error::from(io::ErrorKind::Other)),
        kill_fails: true,
    };
    let result = terminate(&mut process);
    assert_eq!((process.kills, process.polls), (1, 1));
    let diagnostic = result.diagnostic();
    assert!(diagnostic.contains("child exit not confirmed"));
    assert!(diagnostic.contains("direct-child kill:"));
    assert!(diagnostic.contains("exit-status poll:"));
    assert!(result.status.is_none());
    assert_eq!(
        result.kill_error.map(|error| error.kind()),
        Some(io::ErrorKind::PermissionDenied)
    );
    assert_eq!(
        result.poll_error.map(|error| error.kind()),
        Some(io::ErrorKind::Other)
    );
}

#[test]
fn thread_watchdog_returns_the_worker_value() {
    assert_eq!(watchdog::run_with_watchdog("value control", || 42), 42);
}

#[test]
fn thread_watchdog_preserves_a_worker_panic_instead_of_reporting_timeout() {
    #[derive(Debug, PartialEq)]
    struct OriginalFailure(u32);
    let error = std::panic::catch_unwind(|| {
        watchdog::run_with_watchdog("panic control", || {
            std::panic::panic_any(OriginalFailure(7))
        })
    })
    .expect_err("worker panic must fail the caller");
    assert_eq!(
        error.downcast_ref::<OriginalFailure>(),
        Some(&OriginalFailure(7))
    );
}

#[test]
fn thread_watchdog_bounds_the_wait_but_does_not_claim_to_cancel_the_worker() {
    let (release, wait) = std::sync::mpsc::channel::<()>();
    let (finished, completion) = std::sync::mpsc::channel();
    let started = Instant::now();
    let error = std::panic::catch_unwind(|| {
        watchdog::run_with_timeout("timeout control", Duration::from_millis(100), move || {
            let _ = wait.recv();
            let _ = finished.send(());
        })
    })
    .expect_err("blocked worker must not be reported as successful");
    let elapsed = started.elapsed();
    // Clean up the deliberately blocked thread even if a later assertion fails.
    drop(release);
    completion
        .recv_timeout(Duration::from_secs(5))
        .expect("worker cleanup");
    let message = error.downcast_ref::<String>().expect("watchdog diagnostic");
    assert!(message.contains("timeout control") && message.contains("worker is not cancelled"));
    assert!(elapsed >= Duration::from_millis(100));
    assert!(
        elapsed < Duration::from_secs(4),
        "watchdog took {elapsed:?}"
    );
}

const STDIO_HOLDER_C: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

static void write_all(int fd, const char *text) {
    (void)write(fd, text, strlen(text));
}

int main(int argc, char **argv) {
    if (argc != 3) {
        return 2;
    }

    write_all(STDOUT_FILENO, "parent-out\n");
    write_all(STDERR_FILENO, "parent-err\n");

    pid_t pid = fork();
    if (pid < 0) {
        return 3;
    }

    if (pid == 0) {
        if (setsid() < 0) {
            _exit(4);
        }
        FILE *pid_file = fopen(argv[2], "w");
        if (pid_file != NULL) {
            fprintf(pid_file, "%ld\n", (long)getpid());
            fclose(pid_file);
        }
        write_all(STDOUT_FILENO, "descendant-out\n");
        write_all(STDERR_FILENO, "descendant-err\n");
        sleep(60);
        _exit(0);
    }

    if (argv[1][0] == 'e') {
        return 7;
    }

    sleep(60);
    return 0;
}
"#;

#[test]
fn command_output_timeout_retains_output_and_reports_termination_observations() {
    let _guard = COMMAND_TIMEOUT_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let mut command = Command::new("/bin/sh");
    command.args([
        "-c",
        "printf 'direct-out\\n'; printf 'direct-err\\n' >&2; exec sleep 60",
    ]);
    let start = Instant::now();
    let result = command_output_with_timeout(&mut command, Duration::from_secs(1))
        .expect("run direct timeout control");
    assert!(start.elapsed() < Duration::from_secs(4));
    assert!(result.timed_out);
    assert!(!result.output.status.success());
    assert_eq!(result.output.stdout, b"direct-out\n");
    let diagnostic = String::from_utf8_lossy(&result.output.stderr);
    assert!(diagnostic.starts_with("direct-err\n"));
    assert!(diagnostic.contains("[trust-cg-timeout]"));
    assert!(diagnostic.contains("child pid="));
    assert!(diagnostic.contains("termination requested"));
    assert!(
        diagnostic.contains("observed child status")
            || diagnostic.contains("child exit not confirmed")
    );
}

fn scratch_dir(prefix: &str) -> PathBuf {
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

/// Wall time since `start`, less the launch hold the runner did not charge to
/// the child: what a deadline assertion about the child itself compares.
fn since_launch(start: Instant, result: &TimedCommandOutput) -> Duration {
    start
        .elapsed()
        .saturating_sub(result.launch_hold.unwrap_or_default())
}

/// First argument every script control here answers by exiting 0 before its
/// body runs ([`warm`]).
const WARM_ARGUMENT: &str = "--trust-cg-fixture-warm";

/// Write a NEW script control that answers [`WARM_ARGUMENT`], then [`warm`] it.
fn warm_script(path: &Path, body: &str) {
    fs::write(
        path,
        format!("#!/bin/sh\ntest \"$1\" = {WARM_ARGUMENT} && exit 0\n{body}"),
    )
    .expect("write script control");
    let mut permissions = fs::metadata(path)
        .expect("stat script control")
        .permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(path, permissions).expect("chmod script control");
    warm(path, &[WARM_ARGUMENT]);
}

/// Start a new fixture executable once, outside every deadline, before its
/// test gives it one. macOS assesses a newly created executable on its first
/// `exec`, inside the child, after `spawn` has already returned: 0.17-6.0 s
/// for a fresh script at load average 32-38 (2026-09-30), and 4 ms for every
/// later start. Started first under a test's deadline, a control could time
/// out, or be killed, before it ran at all. `args` make it exit at once
/// without doing anything its test observes; its status is not the point.
fn warm(path: &Path, args: &[&str]) {
    let mut child = Command::new(path)
        .args(args)
        .stdin(std::process::Stdio::null())
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .spawn()
        .expect("warm the fixture executable");
    // Stopped after 120 s, a hang guard: the deadline under test then pays the
    // rest of the assessment, as it would without this.
    let deadline = Instant::now() + Duration::from_secs(120);
    while child.try_wait().expect("poll the warm-up").is_none() {
        if Instant::now() >= deadline {
            let _ = child.kill();
            eprintln!(
                "the warm-up start of {} was stopped after 120 s",
                path.display()
            );
            break;
        }
        thread::sleep(Duration::from_millis(5));
    }
    let _status = child.wait().expect("reap the warm-up");
}

fn compile_stdio_holder() -> Option<(PathBuf, PathBuf)> {
    let dir = scratch_dir("trust_cg_cmd_timeout_stdio_holder");
    fs::create_dir_all(&dir).expect("create stdio holder scratch dir");
    let src = dir.join("stdio_holder.c");
    let bin = dir.join("stdio_holder");
    fs::write(&src, STDIO_HOLDER_C).expect("write stdio holder source");

    let output = match Command::new("cc").arg(&src).arg("-o").arg(&bin).output() {
        Ok(output) => output,
        Err(err) => {
            eprintln!("SKIP: cc unavailable for command timeout regression helper: {err}");
            let _ = fs::remove_dir_all(&dir);
            return None;
        }
    };
    if !output.status.success() {
        eprintln!(
            "SKIP: cc failed for command timeout regression helper: stdout={}, stderr={}",
            String::from_utf8_lossy(&output.stdout).trim(),
            String::from_utf8_lossy(&output.stderr).trim()
        );
        let _ = fs::remove_dir_all(&dir);
        return None;
    }
    // A new executable: with no arguments it exits 2 at once.
    warm(&bin, &[]);

    Some((dir, bin))
}

fn kill_recorded_pid(pid_path: &Path) {
    let start = Instant::now();
    while start.elapsed() < Duration::from_secs(3) {
        if let Ok(raw) = fs::read_to_string(pid_path) {
            // Parse, never pass raw text to `kill`: a corrupted or partially
            // written pid file containing `-1` would otherwise become
            // `kill -KILL -1`, which util-linux `kill` turns into a signal to
            // EVERY process the user owns (see `common::rosetta::kill_process_group`).
            if let Ok(pid) = raw.trim().parse::<u32>() {
                if pid > 1 {
                    let _ = Command::new("kill")
                        .args(["-KILL", &pid.to_string()])
                        .status();
                }
                return;
            }
        }
        thread::sleep(Duration::from_millis(10));
    }
}

#[test]
fn command_output_returns_when_exited_child_leaves_stdio_open() {
    let _guard = COMMAND_TIMEOUT_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let Some((dir, bin)) = compile_stdio_holder() else {
        return;
    };
    let pid_path = dir.join("descendant.pid");
    let mut cmd = Command::new(&bin);
    cmd.arg("exit").arg(&pid_path);

    let start = Instant::now();
    let result = command_output_with_timeout(&mut cmd, COMMAND_TIMEOUT_REGRESSION_TIMEOUT)
        .expect("run stdio holder");
    let elapsed = since_launch(start, &result);
    kill_recorded_pid(&pid_path);
    let _ = fs::remove_dir_all(&dir);

    assert!(
        elapsed < COMMAND_TIMEOUT_REGRESSION_TIMEOUT + Duration::from_secs(1),
        "command should return after the direct child exits, elapsed={elapsed:?}"
    );
    assert!(!result.timed_out);
    assert_eq!(result.output.status.code(), Some(7));
    assert!(String::from_utf8_lossy(&result.output.stdout).contains("parent-out"));
    assert!(String::from_utf8_lossy(&result.output.stderr).contains("parent-err"));
}

#[test]
fn command_output_timeout_returns_with_escaped_descendant_stdio_open() {
    let _guard = COMMAND_TIMEOUT_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let Some((dir, bin)) = compile_stdio_holder() else {
        return;
    };
    let pid_path = dir.join("descendant.pid");
    let mut cmd = Command::new(&bin);
    cmd.arg("sleep").arg(&pid_path);

    let start = Instant::now();
    let result = command_output_with_timeout(&mut cmd, COMMAND_TIMEOUT_REGRESSION_TIMEOUT)
        .expect("run stdio holder");
    let elapsed = since_launch(start, &result);
    kill_recorded_pid(&pid_path);
    let _ = fs::remove_dir_all(&dir);

    assert!(
        elapsed < COMMAND_TIMEOUT_REGRESSION_TIMEOUT + Duration::from_secs(3),
        "timeout path should not wait for escaped descendant stdio EOF, elapsed={elapsed:?}"
    );
    assert!(result.timed_out);
    assert!(String::from_utf8_lossy(&result.output.stdout).contains("parent-out"));
    assert!(String::from_utf8_lossy(&result.output.stderr).contains("[trust-cg-timeout]"));
}

#[test]
fn run_executable_preserves_exact_nonzero_exit_status() {
    let _guard = COMMAND_TIMEOUT_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let Some((dir, bin)) = compile_stdio_holder() else {
        return;
    };

    // With no arguments the helper exits 2 immediately.  This exercises the
    // executable runner's fast non-zero completion path: it must report the
    // child's actual status rather than infer completion from a separately
    // published status file.
    let result = run_executable_with_timeout(&bin, COMMAND_TIMEOUT_REGRESSION_TIMEOUT)
        .expect("run fast non-zero helper");
    let _ = fs::remove_dir_all(&dir);

    assert!(!result.timed_out);
    assert_eq!(result.output.status.code(), Some(2));
}

#[test]
fn run_executable_timeout_retains_output_and_returns_without_blocking_reap() {
    let _guard = COMMAND_TIMEOUT_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let dir = tempfile::tempdir().expect("owned supervisor-timeout fixture");
    let script = dir.path().join("wait.sh");
    warm_script(&script, "printf 'started\\n'\nexec sleep 60\n");

    let start = Instant::now();
    let result = run_executable_with_timeout(&script, Duration::from_secs(1))
        .expect("run supervised wait helper");
    assert!(since_launch(start, &result) < Duration::from_secs(4));
    assert!(result.timed_out);
    assert!(!result.output.status.success());
    assert_eq!(result.output.stdout, b"started\n");
    assert!(String::from_utf8_lossy(&result.output.stderr).contains("[trust-cg-timeout]"));
}

#[test]
fn run_executable_preserves_shell_signal_status_convention() {
    let _guard = COMMAND_TIMEOUT_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let dir = scratch_dir("trust_cg_cmd_timeout_signal_status");
    fs::create_dir_all(&dir).expect("create signal-status scratch dir");
    let script = dir.join("signal.sh");
    warm_script(&script, "kill -TERM $$\n");

    let result = run_executable_with_timeout(&script, COMMAND_TIMEOUT_REGRESSION_TIMEOUT)
        .expect("run signal helper");
    let _ = fs::remove_dir_all(&dir);

    assert!(!result.timed_out);
    assert_eq!(result.output.status.code(), Some(128 + 15));
}

/// A child `posix_spawn` creates with Apple's `POSIX_SPAWN_START_SUSPENDED`:
/// it exists but executes no instruction until [`Suspended::resume`] sends it
/// SIGCONT. Its task counters read exactly like those of a freshly linked
/// executable macOS is holding at exec, so the hold is deterministic here
/// instead of depending on how busy the host's syspolicyd is.
#[cfg(target_os = "macos")]
mod start_suspended {
    use super::common::rosetta::process_termination::TimeoutProcess;
    use super::common::rosetta::{LaunchState, SupervisedProcess, launch_state};
    use std::ffi::{CString, c_char, c_int, c_short, c_void};
    use std::io;
    use std::os::unix::process::ExitStatusExt;
    use std::process::ExitStatus;
    use std::ptr;

    /// `POSIX_SPAWN_START_SUSPENDED` from `<spawn.h>`.
    const POSIX_SPAWN_START_SUSPENDED: c_short = 0x0080;
    const SIGKILL: c_int = 9;
    const SIGCONT: c_int = 19;
    const WNOHANG: c_int = 1;

    unsafe extern "C" {
        fn posix_spawnattr_init(attr: *mut *mut c_void) -> c_int;
        fn posix_spawnattr_setflags(attr: *mut *mut c_void, flags: c_short) -> c_int;
        fn posix_spawnattr_destroy(attr: *mut *mut c_void) -> c_int;
        fn posix_spawn(
            pid: *mut i32,
            path: *const c_char,
            file_actions: *const c_void,
            attrp: *const *mut c_void,
            argv: *const *const c_char,
            envp: *const *const c_char,
        ) -> c_int;
        fn waitpid(pid: i32, status: *mut c_int, options: c_int) -> i32;
        fn kill(pid: i32, sig: c_int) -> c_int;
    }

    pub struct Suspended {
        pid: i32,
        status: Option<ExitStatus>,
    }

    impl Suspended {
        /// Spawn `argv` (an absolute program path first) suspended, with an
        /// empty environment and this process's stdio.
        pub fn spawn(argv: &[&str]) -> Self {
            let args: Vec<CString> = argv
                .iter()
                .map(|arg| CString::new(*arg).expect("argument without NUL"))
                .collect();
            let mut arg_ptrs: Vec<*const c_char> = args.iter().map(|arg| arg.as_ptr()).collect();
            arg_ptrs.push(ptr::null());
            let env_ptrs: [*const c_char; 1] = [ptr::null()];
            let mut attr: *mut c_void = ptr::null_mut();
            let mut pid = 0;
            // SAFETY: `attr` is initialised before use and destroyed once;
            // `args` and the NULL-terminated pointer arrays outlive the call.
            let spawned = unsafe {
                assert_eq!(posix_spawnattr_init(&mut attr), 0, "posix_spawnattr_init");
                assert_eq!(
                    posix_spawnattr_setflags(&mut attr, POSIX_SPAWN_START_SUSPENDED),
                    0,
                    "posix_spawnattr_setflags"
                );
                let spawned = posix_spawn(
                    &mut pid,
                    args[0].as_ptr(),
                    ptr::null(),
                    &attr,
                    arg_ptrs.as_ptr(),
                    env_ptrs.as_ptr(),
                );
                posix_spawnattr_destroy(&mut attr);
                spawned
            };
            assert_eq!(spawned, 0, "posix_spawn {argv:?}");
            assert!(pid > 1, "posix_spawn returned pid {pid}");
            Self { pid, status: None }
        }

        pub fn pid(&self) -> i32 {
            self.pid
        }

        /// Let a suspended child `pid` run.
        pub fn resume(pid: i32) {
            assert!(pid > 1);
            // SAFETY: signals one child this test spawned (pid > 1).
            assert_eq!(unsafe { kill(pid, SIGCONT) }, 0, "SIGCONT {pid}");
        }
    }

    impl TimeoutProcess for Suspended {
        fn request_kill(&mut self) -> io::Result<()> {
            // SAFETY: signals one child this test spawned (pid > 1).
            if unsafe { kill(self.pid, SIGKILL) } == 0 {
                Ok(())
            } else {
                Err(io::Error::last_os_error())
            }
        }

        fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
            if self.status.is_some() {
                return Ok(self.status);
            }
            let mut raw = 0;
            // SAFETY: polls one child this test spawned and has not reaped.
            match unsafe { waitpid(self.pid, &mut raw, WNOHANG) } {
                0 => Ok(None),
                reaped if reaped == self.pid => {
                    self.status = Some(ExitStatus::from_raw(raw));
                    Ok(self.status)
                }
                _ => Err(io::Error::last_os_error()),
            }
        }
    }

    impl SupervisedProcess for Suspended {
        fn launch_state(&self) -> LaunchState {
            launch_state(self.pid as u32)
        }
    }

    impl Drop for Suspended {
        fn drop(&mut self) {
            if self.status.is_none() {
                let mut raw = 0;
                // SAFETY: kills and reaps one child this test spawned; SIGKILL
                // also ends a task that is still suspended.
                unsafe {
                    kill(self.pid, SIGKILL);
                    waitpid(self.pid, &mut raw, 0);
                }
            }
        }
    }
}

#[cfg(target_os = "macos")]
#[test]
fn launch_probe_reports_a_start_suspended_child_as_not_started_until_resumed() {
    use common::rosetta::process_termination::TimeoutProcess;
    use common::rosetta::{LaunchState, SupervisedProcess};
    use start_suspended::Suspended;

    let mut child = Suspended::spawn(&["/bin/sleep", "60"]);
    thread::sleep(Duration::from_millis(200));
    assert_eq!(child.launch_state(), LaunchState::NotStarted);
    Suspended::resume(child.pid());
    let deadline = Instant::now() + Duration::from_secs(30);
    while child.launch_state() == LaunchState::NotStarted {
        assert!(Instant::now() < deadline, "resumed child never started");
        thread::sleep(Duration::from_millis(10));
    }
    assert_eq!(child.launch_state(), LaunchState::Started);
    assert!(child.try_wait().expect("poll sleeping child").is_none());
}

/// Old behaviour for comparison: a deadline counted from the spawn would end
/// this wait at 2 s while the child was still held and had run nothing.
#[cfg(target_os = "macos")]
#[test]
fn launch_aware_wait_charges_the_run_budget_only_once_the_child_starts() {
    use common::rosetta::{LaunchAwareEnd, wait_launch_aware};
    use start_suspended::Suspended;

    let hold = Duration::from_secs(3);
    let mut child = Suspended::spawn(&["/bin/sh", "-c", "exit 7"]);
    let pid = child.pid();
    let resumer = thread::spawn(move || {
        thread::sleep(hold);
        Suspended::resume(pid);
    });
    let waited = wait_launch_aware(&mut child, Duration::from_secs(2), Duration::from_secs(120))
        .expect("wait for held child");
    resumer.join().expect("resumer thread");
    assert!(
        matches!(waited.end, LaunchAwareEnd::Exited(status) if status.code() == Some(7)),
        "{waited:?}"
    );
    let held = waited.launch_hold.expect("the hold was observed");
    assert!(held >= hold - Duration::from_millis(100), "{waited:?}");
}

#[cfg(target_os = "macos")]
#[test]
fn launch_aware_wait_still_ends_a_child_that_hangs_once_started() {
    use common::rosetta::{LaunchAwareEnd, wait_launch_aware};
    use start_suspended::Suspended;

    let hold = Duration::from_secs(2);
    let run_budget = Duration::from_secs(1);
    let mut child = Suspended::spawn(&["/bin/sleep", "60"]);
    let pid = child.pid();
    let resumer = thread::spawn(move || {
        thread::sleep(hold);
        Suspended::resume(pid);
    });
    let start = Instant::now();
    let waited = wait_launch_aware(&mut child, run_budget, Duration::from_secs(120)).expect("wait");
    let elapsed = start.elapsed();
    resumer.join().expect("resumer thread");
    assert!(
        matches!(waited.end, LaunchAwareEnd::RanPastBudget),
        "{waited:?}"
    );
    let held = waited.launch_hold.expect("the hold was observed");
    assert!(held >= hold - Duration::from_millis(100), "{waited:?}");
    let ran = elapsed.saturating_sub(held);
    assert!(
        ran >= run_budget && ran < run_budget + Duration::from_secs(3),
        "ran {ran:?} after a {held:?} hold"
    );
}

#[cfg(target_os = "macos")]
#[test]
fn launch_aware_wait_bounds_a_launch_that_never_starts() {
    use common::rosetta::{LaunchAwareEnd, wait_launch_aware};
    use start_suspended::Suspended;

    let admission = Duration::from_secs(2);
    let mut child = Suspended::spawn(&["/bin/sleep", "60"]);
    let start = Instant::now();
    let waited = wait_launch_aware(&mut child, Duration::from_secs(1), admission).expect("wait");
    assert!(
        matches!(waited.end, LaunchAwareEnd::NeverStarted),
        "{waited:?}"
    );
    assert!(waited.launch_hold.expect("held") >= admission);
    assert!(start.elapsed() < admission + Duration::from_secs(3));
}

/// A freshly linked executable that starts, says so, then never exits: macOS
/// may hold its launch for seconds under host load, and the runner must still
/// end it one run budget after it starts.
const FRESH_HANG_C: &str = r#"
#include <stdio.h>
#include <unistd.h>

static const char nonce[] = "NONCE";

int main(void) {
    printf("started %s\n", nonce);
    fflush(stdout);
#ifdef SPIN
    for (volatile unsigned long spins = 0;; spins++) {
    }
#else
    for (;;) {
        pause();
    }
#endif
}
"#;

#[test]
fn run_executable_ends_a_fresh_executable_that_hangs_after_it_starts() {
    let run_budget = Duration::from_secs(1);
    for (variant, define) in [("spin", "-DSPIN"), ("block", "-DBLOCK")] {
        let dir = tempfile::tempdir().expect("fresh-hang scratch dir");
        let nonce = format!(
            "{variant}-{}-{}",
            std::process::id(),
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap_or_default()
                .as_nanos()
        );
        let src = dir.path().join("hang.c");
        let bin = dir.path().join("hang");
        fs::write(&src, FRESH_HANG_C.replace("NONCE", &nonce)).expect("write hang source");
        let compiled = match Command::new("cc")
            .arg(define)
            .arg(&src)
            .arg("-o")
            .arg(&bin)
            .output()
        {
            Ok(output) => output,
            Err(err) => {
                eprintln!("SKIP: cc unavailable for the fresh-hang control: {err}");
                return;
            }
        };
        assert!(compiled.status.success(), "cc: {compiled:?}");
        let start = Instant::now();
        let result = run_executable_with_timeout(&bin, run_budget).expect("run fresh hang");
        let ran = since_launch(start, &result);
        let stderr = String::from_utf8_lossy(&result.output.stderr);
        assert!(result.timed_out, "{variant}: {:?}", result.output);
        assert_eq!(
            String::from_utf8_lossy(&result.output.stdout),
            format!("started {nonce}\n"),
            "{variant}: the deadline must end a program that is running"
        );
        assert!(stderr.contains("[trust-cg-timeout]"), "{variant}: {stderr}");
        assert!(
            stderr.contains("run deadline counted from"),
            "{variant}: {stderr}"
        );
        assert!(
            ran >= run_budget && ran < run_budget + Duration::from_secs(3),
            "{variant}: ran {ran:?} after a {:?} launch hold",
            result.launch_hold
        );
        eprintln!(
            "fresh {variant} hang ended {ran:?} after it started; launch hold {:?}",
            result.launch_hold
        );
    }
}
