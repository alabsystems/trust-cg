// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(unix)]

mod common;

use common::rosetta::{command_output_with_timeout, run_executable_with_timeout};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{
    Mutex, OnceLock,
    atomic::{AtomicU64, Ordering},
};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

static SCRATCH_SEQ: AtomicU64 = AtomicU64::new(0);
static COMMAND_TIMEOUT_TEST_LOCK: OnceLock<Mutex<()>> = OnceLock::new();
const COMMAND_TIMEOUT_REGRESSION_TIMEOUT: Duration = Duration::from_secs(15);

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

    Some((dir, bin))
}

fn kill_recorded_pid(pid_path: &Path) {
    let start = Instant::now();
    while start.elapsed() < Duration::from_secs(3) {
        if let Ok(raw) = fs::read_to_string(pid_path) {
            let pid = raw.trim();
            if !pid.is_empty() {
                let _ = Command::new("kill").args(["-KILL", pid]).status();
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
    let elapsed = start.elapsed();
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
    let elapsed = start.elapsed();
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
fn run_executable_preserves_shell_signal_status_convention() {
    let _guard = COMMAND_TIMEOUT_TEST_LOCK
        .get_or_init(|| Mutex::new(()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    let dir = scratch_dir("trust_cg_cmd_timeout_signal_status");
    fs::create_dir_all(&dir).expect("create signal-status scratch dir");
    let script = dir.join("signal.sh");
    fs::write(&script, "#!/bin/sh\nkill -TERM $$\n").expect("write signal helper");
    let mut permissions = fs::metadata(&script)
        .expect("stat signal helper")
        .permissions();
    permissions.set_mode(0o755);
    fs::set_permissions(&script, permissions).expect("chmod signal helper");

    let result = run_executable_with_timeout(&script, COMMAND_TIMEOUT_REGRESSION_TIMEOUT)
        .expect("run signal helper");
    let _ = fs::remove_dir_all(&dir);

    assert!(!result.timed_out);
    assert_eq!(result.output.status.code(), Some(128 + 15));
}
