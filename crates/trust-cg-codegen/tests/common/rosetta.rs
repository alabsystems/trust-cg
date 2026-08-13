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

const DEFAULT_TEST_TIMEOUT_SECS: u64 = 1500;
const DEFAULT_CODEGEN_PROBE_TIMEOUT_SECS: u64 = 10;
const DEFAULT_CODEGEN_ROSETTA_PROBE_TIMEOUT_SECS: u64 = 5;
const DEFAULT_CODEGEN_LINK_TIMEOUT_SECS: u64 = 30;
// 60s (not 10s): the e2e binaries run in <1s normally, so this budget only
// matters under heavy shared-host load (concurrent test runs on the same
// machine), where 10s starves process spawn/exec and produces false "infinite
// loop" timeout flakes. A genuine infinite loop still trips this bound. Tune
// via the `codegen_run_timeout_sec` env var / timeout config.
const DEFAULT_CODEGEN_RUN_TIMEOUT_SECS: u64 = 60;

pub struct TimedCommandOutput {
    pub output: Output,
    pub timed_out: bool,
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

pub fn command_output_with_timeout(
    cmd: &mut Command,
    timeout: Duration,
) -> io::Result<TimedCommandOutput> {
    let dir = timeout_scratch_dir("trust_cg_cmd_output_timeout");
    fs::create_dir_all(&dir)?;
    let stdout_path = dir.join("stdout");
    let stderr_path = dir.join("stderr");
    let stdout_file = fs::File::create(&stdout_path)?;
    let stderr_file = fs::File::create(&stderr_path)?;

    cmd.stdin(Stdio::null())
        .stdout(Stdio::from(stdout_file))
        .stderr(Stdio::from(stderr_file));
    #[cfg(unix)]
    cmd.process_group(0);
    let mut child = match cmd.spawn() {
        Ok(child) => child,
        Err(err) => {
            let _ = fs::remove_dir_all(&dir);
            return Err(err);
        }
    };
    #[cfg(unix)]
    let child_id = child.id();
    let start = Instant::now();

    loop {
        if let Some(status) = child.try_wait()? {
            let stdout = fs::read(&stdout_path).unwrap_or_default();
            let stderr = fs::read(&stderr_path).unwrap_or_default();
            let _ = fs::remove_dir_all(&dir);
            return Ok(TimedCommandOutput {
                output: Output {
                    status,
                    stdout,
                    stderr,
                },
                timed_out: false,
            });
        }

        if start.elapsed() >= timeout {
            #[cfg(unix)]
            {
                let group = format!("-{}", child_id);
                let _ = Command::new("kill").args(["-KILL", &group]).status();
            }
            let _ = child.kill();
            let status = child.wait().unwrap_or_else(|_| ExitStatus::from_raw(9));
            let stdout = fs::read(&stdout_path).unwrap_or_default();
            let mut stderr = fs::read(&stderr_path).unwrap_or_default();
            stderr.extend_from_slice(&timeout_stderr(timeout, "killing process group"));
            let _ = fs::remove_dir_all(&dir);
            return Ok(TimedCommandOutput {
                output: Output {
                    status,
                    stdout,
                    stderr,
                },
                timed_out: true,
            });
        }

        thread::sleep(Duration::from_millis(20));
    }
}

pub fn run_executable_with_timeout(
    program: &Path,
    timeout: Duration,
) -> io::Result<TimedCommandOutput> {
    #[cfg(not(unix))]
    {
        let mut cmd = Command::new(program);
        return command_output_with_timeout(&mut cmd, timeout);
    }

    #[cfg(unix)]
    {
        let dir = timeout_scratch_dir("trust_cg_cmd_timeout");
        fs::create_dir_all(&dir)?;
        let stdout_path = dir.join("stdout");
        let stderr_path = dir.join("stderr");

        // Poll the supervising shell's authoritative `ExitStatus`; do not use
        // a status-file sentinel. Shell redirection creates a file before
        // `printf` fills it, so under scheduler pressure a polling thread can
        // observe an empty file and invent a fallback status. The shell stays
        // alive only to preserve this runner's established signal convention:
        // a signal-killed executable is reported as `128 + signum` rather than
        // as an `ExitStatus` with no numeric code.
        let mut shell = Command::new("/bin/sh");
        shell
            .arg("-c")
            .arg(r#""$1" >"$2" 2>"$3"; status=$?; exit "$status""#)
            .arg("trust-cg-rosetta-probe")
            .arg(program)
            .arg(&stdout_path)
            .arg(&stderr_path)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null());
        shell.process_group(0);

        let mut child = shell.spawn()?;
        let child_id = child.id();
        let start = Instant::now();

        loop {
            if let Some(status) = child.try_wait()? {
                let stdout = fs::read(&stdout_path).unwrap_or_default();
                let stderr = fs::read(&stderr_path).unwrap_or_default();
                let _ = fs::remove_dir_all(&dir);
                return Ok(TimedCommandOutput {
                    output: Output {
                        status,
                        stdout,
                        stderr,
                    },
                    timed_out: false,
                });
            }

            if start.elapsed() >= timeout {
                let group = format!("-{}", child_id);
                let _ = Command::new("kill").args(["-KILL", &group]).status();
                let _ = child.try_wait();
                let stdout = fs::read(&stdout_path).unwrap_or_default();
                let mut stderr = fs::read(&stderr_path).unwrap_or_default();
                stderr.extend_from_slice(&timeout_stderr(timeout, "killing process group"));
                let _ = fs::remove_dir_all(&dir);
                return Ok(TimedCommandOutput {
                    output: Output {
                        status: ExitStatus::from_raw(9),
                        stdout,
                        stderr,
                    },
                    timed_out: true,
                });
            }

            thread::sleep(Duration::from_millis(20));
        }
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

fn probe_cc_x86_64_link_run() -> bool {
    if cfg!(all(target_os = "macos", target_arch = "aarch64"))
        && std::env::var_os("TRUST_CG_RUN_ROSETTA_LINKRUN").is_none()
    {
        eprintln!(
            "SKIP: Rosetta x86_64 link/run disabled on aarch64 macOS host; \
             set TRUST_CG_RUN_ROSETTA_LINKRUN=1 only on a healthy Rosetta host (#582)"
        );
        return false;
    }

    let stamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "trust_cg_x86_64_cc_check_{}_{}",
        std::process::id(),
        stamp
    ));
    let _ = fs::create_dir_all(&dir);
    let src = dir.join("check.c");
    let out = dir.join("check");
    let _ = fs::write(&src, "int main(void) { return 0; }\n");

    let mut compile_cmd = Command::new("cc");
    compile_cmd.args([
        "-arch",
        "x86_64",
        "-o",
        out.to_str().unwrap(),
        src.to_str().unwrap(),
    ]);
    let compiled = match command_output_with_timeout(&mut compile_cmd, probe_timeout()) {
        Ok(result) if !result.timed_out && result.output.status.success() => true,
        Ok(result) => {
            let (stdout, stderr) = output_text(&result.output);
            eprintln!(
                "SKIP: cc -arch x86_64 compile probe {} after {:?}; stdout={}, stderr={}",
                if result.timed_out {
                    "timed out"
                } else {
                    "failed"
                },
                probe_timeout(),
                stdout.trim(),
                stderr.trim()
            );
            false
        }
        Err(e) => {
            eprintln!("SKIP: cc -arch x86_64 compile probe failed to start: {e}");
            false
        }
    };

    let ran = if compiled {
        match run_executable_with_timeout(&out, probe_timeout()) {
            Ok(result) if !result.timed_out && result.output.status.success() => true,
            Ok(result) => {
                let (stdout, stderr) = output_text(&result.output);
                eprintln!(
                    "SKIP: Rosetta x86_64 run probe {} after {:?}; stdout={}, stderr={}",
                    if result.timed_out {
                        "timed out"
                    } else {
                        "failed"
                    },
                    probe_timeout(),
                    stdout.trim(),
                    stderr.trim()
                );
                false
            }
            Err(e) => {
                eprintln!("SKIP: Rosetta x86_64 run probe failed to start: {e}");
                false
            }
        }
    } else {
        false
    };

    let _ = fs::remove_dir_all(&dir);
    ran
}

pub fn has_cc_x86_64_link_run() -> bool {
    static HAS_CC_X86_64_LINK_RUN: OnceLock<bool> = OnceLock::new();
    *HAS_CC_X86_64_LINK_RUN.get_or_init(probe_cc_x86_64_link_run)
}
