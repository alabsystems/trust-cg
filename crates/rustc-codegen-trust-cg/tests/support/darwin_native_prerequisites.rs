//! Host prerequisites of the aarch64-apple-darwin native bridge fixtures.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! Each fixture that calls [`require`] is compiled only on an
//! aarch64-apple-darwin host (`#![cfg(all(target_os = "macos", target_arch =
//! "aarch64"))]`), so another host builds it with no test in it rather than
//! with a test that passes without running. On this host a missing
//! prerequisite is a defect of the host or package, not a reason to pass:
//! [`require`] panics and names every missing piece. The fixtures used to
//! return early instead (ledger L06-P10).
//!
//! [`run_with_deadline`] bounds a fixture's native run in process: macOS ships
//! no GNU `timeout`, so the bound cannot be a host tool. It uses only `std`, so
//! the host-target oracle `reference_union_semantics.rs`, which every host
//! compiles, bounds its runs with it too.
#![allow(dead_code)]

use std::io::Read;
use std::process::{Command, Output, Stdio};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// The only target these fixtures compile for.
pub const TARGET: &str = "aarch64-apple-darwin";

/// Panic unless the build compiler carries the backend-knob option, the
/// package ships `TARGET`'s rust-std, and every tool in `tools` answers
/// `--version`. `test` names the fixture in the panic message.
pub fn require(test: &str, tools: &[&str]) {
    let mut missing = Vec::new();
    if !crate::toolchain_support::backend_knobs_supported() {
        missing.push(format!(
            "the build compiler lists no `{}` in `-Z help`, so the backend knobs this \
             fixture passes cannot be expressed",
            crate::toolchain_support::BACKEND_KNOBS_OPTION
        ));
    }
    if !crate::toolchain_support::target_std_available(TARGET) {
        missing.push(format!(
            "the pinned Trust package ships no rust-std for {TARGET}"
        ));
    }
    for tool in tools {
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
        "DARWIN_BRIDGE_PREREQUISITE_MISSING {test}: {}; this fixture runs only on an \
         aarch64-apple-darwin host, where each of these is required, so it fails instead \
         of passing without running",
        missing.join("; ")
    );
}

/// Run `command` with stdin closed and stdout/stderr captured, killing it once
/// `limit` has elapsed. `Ok` is a run that exited by itself; `Err` is a run
/// this function killed at the deadline, with whatever it printed before.
pub fn run_with_deadline(command: &mut Command, limit: Duration) -> Result<Output, Output> {
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    let mut child = match command.spawn() {
        Ok(child) => child,
        Err(error) => panic!("spawn {command:?}: {error}"),
    };
    // Drained on their own threads, so a child that fills a pipe cannot block
    // before it exits or reaches the deadline.
    let stdout = drain(child.stdout.take().expect("piped stdout"));
    let stderr = drain(child.stderr.take().expect("piped stderr"));
    let deadline = Instant::now() + limit;
    let (status, killed) = loop {
        if let Some(status) = child.try_wait().expect("poll bounded child") {
            break (status, false);
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            break (child.wait().expect("reap killed child"), true);
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    let output = Output {
        status,
        stdout: stdout.join().expect("stdout drain thread"),
        stderr: stderr.join().expect("stderr drain thread"),
    };
    if killed { Err(output) } else { Ok(output) }
}

fn drain<R: Read + Send + 'static>(mut pipe: R) -> JoinHandle<Vec<u8>> {
    std::thread::spawn(move || {
        let mut bytes = Vec::new();
        let _ = pipe.read_to_end(&mut bytes);
        bytes
    })
}
