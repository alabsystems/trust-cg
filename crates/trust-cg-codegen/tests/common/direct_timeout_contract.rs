// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native shell controls for adapters, without loading compiler-generated EH.

use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// What a timeout adapter reports back: the child's exit status (`None` when it
/// was killed), its captured stdout and stderr, and whether the deadline fired.
type AdapterOutcome = (Option<i32>, String, String, bool);

/// First argument every control answers by exiting 0 before its body runs.
const WARM_ARGUMENT: &str = "--trust-cg-fixture-warm";

/// Write a NEW control script and start it once, outside every deadline.
///
/// macOS assesses a newly created executable on its first `exec`, inside the
/// child, after `spawn` has already returned: 0.17-6.0 s for a fresh script at
/// load average 32-38 (2026-09-30), and 4 ms for every later start. Started
/// first under the deadlines below (5 s, then 1 s), a control could time out
/// before it ran at all. The warm-up argument makes it exit before its body.
fn control(dir: &Path, name: &str, body: &str) -> PathBuf {
    let script = dir.join(name);
    fs::write(
        &script,
        format!("#!/bin/sh\ntest \"$1\" = {WARM_ARGUMENT} && exit 0\n{body}"),
    )
    .expect("write timeout-adapter control");
    fs::set_permissions(&script, fs::Permissions::from_mode(0o755)).expect("chmod control");
    let mut child = Command::new(&script)
        .arg(WARM_ARGUMENT)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .spawn()
        .expect("warm the control");
    // Stopped after 120 s, a hang guard: the deadline under test then pays the
    // rest of the assessment, as it would without this.
    let deadline = Instant::now() + Duration::from_secs(120);
    while child.try_wait().expect("poll the warm-up").is_none() {
        if Instant::now() >= deadline {
            let _ = child.kill();
            eprintln!(
                "the warm-up start of {} was stopped after 120 s",
                script.display()
            );
            break;
        }
        std::thread::sleep(Duration::from_millis(5));
    }
    let status = child.wait().expect("reap the warm-up");
    assert!(
        status.success() || Instant::now() >= deadline,
        "warming {} failed: {status}",
        script.display()
    );
    script
}

pub fn check(run: fn(&Path, Duration) -> AdapterOutcome) {
    let dir = tempfile::tempdir().expect("owned timeout-adapter fixture");
    let script = control(
        dir.path(),
        "exit.sh",
        "printf 'out\\n'\nprintf 'err\\n' >&2\nexit 7\n",
    );
    let (status, stdout, stderr, timed_out) = run(&script, Duration::from_secs(5));
    assert_eq!((status, timed_out), (Some(7), false));
    assert_eq!(stdout, "out\n");
    assert_eq!(stderr, "err\n");

    let script = control(dir.path(), "signal.sh", "kill -TERM $$\n");
    let (status, _, _, timed_out) = run(&script, Duration::from_secs(5));
    // Direct-child adapters must not silently adopt the executable runner's
    // supervising-shell convention of reporting this signal as numeric 143.
    assert_eq!((status, timed_out), (None, false));

    let script = control(
        dir.path(),
        "timeout.sh",
        "printf 'started\\n'\nexec sleep 60\n",
    );
    let start = Instant::now();
    let (status, stdout, stderr, timed_out) = run(&script, Duration::from_secs(1));
    assert!(start.elapsed() < Duration::from_secs(4));
    assert_eq!((status, timed_out), (None, true));
    assert_eq!(stdout, "started\n");
    assert!(stderr.contains("[trust-cg-timeout]"));
    assert!(stderr.contains("termination requested"));
}
