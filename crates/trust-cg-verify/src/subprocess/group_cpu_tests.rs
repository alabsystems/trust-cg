// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Controls for the process-group CPU measurement: the `/proc/<pid>/stat`
//! parser, the units (against the kernel's own `wait4` accounting of the same
//! child), a forked member of the group being counted, and a group that is not
//! live being refused.

use super::*;

#[test]
fn proc_stat_fields_are_counted_after_the_last_parenthesis() {
    // pid (comm) state ppid pgrp session tty tpgid flags minflt cminflt
    // majflt cmajflt utime stime cutime cstime ...
    let plain = "4242 (ay) R 4241 4242 4000 0 -1 4194304 10 0 0 0 150 25 7 3 20 0 1 0 1 2 3";
    assert_eq!(parse_proc_stat(plain), Some((4242, 185)));
    // A command name with spaces and parentheses cannot shift the fields.
    let tricky = "77 (a) b (c) d) S 1 70 70 0 -1 0 0 0 0 0 1 2 3 4 20 0 1 0";
    assert_eq!(parse_proc_stat(tricky), Some((70, 10)));
    for malformed in [
        "",
        "4242 ay R 4241 4242",
        "4242 (ay) R 4241 4242 4000 0 -1 4194304 10 0 0 0 150 25 7",
        "4242 (ay) R 4241 x 4000 0 -1 4194304 10 0 0 0 150 25 7 3",
        "4242 (ay) R 4241 4242 4000 0 -1 4194304 10 0 0 0 150 25 -7 3",
    ] {
        assert_eq!(parse_proc_stat(malformed), None, "{malformed:?}");
    }
}

/// A single-process busy child in its own group: the measurement, taken just
/// before the kill, agrees with the CPU time `wait4` then reports for the
/// reaped child. A unit error (Apple silicon's `rusage_info` times are Mach
/// units, 125/3 ns each, not nanoseconds) would be a factor of about 40.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
// The child is reaped by `wait4` in `reap`, which also returns its CPU time.
#[allow(clippy::zombie_processes)]
fn the_measurement_agrees_with_the_reaped_total() {
    let mut command = std::process::Command::new("/bin/sh");
    command.args(["-c", "while :; do :; done"]);
    crate::subprocess::configure_process_group(&mut command);
    let child = command.spawn().expect("spawn a busy child");
    let pid = child.id();
    let started = std::time::Instant::now();
    while process_group_cpu(pid).is_none_or(|cpu| cpu < Duration::from_millis(300))
        && started.elapsed() < Duration::from_secs(30)
    {
        std::thread::sleep(Duration::from_millis(20));
    }
    let before_sample = std::time::Instant::now();
    let sampled = process_group_cpu(pid);
    // SAFETY: the child is this test's own unreaped child, leading its group.
    unsafe { libc::kill(-(pid as i32), libc::SIGKILL) };
    let gap = before_sample.elapsed();
    let reaped = reap(pid);
    let sampled = sampled.expect("a live group is measured here");
    assert!(
        reaped >= Duration::from_millis(100),
        "the busy child ran: {reaped:?}"
    );
    let slack = Duration::from_millis(30);
    assert!(
        sampled <= reaped + slack,
        "measured {sampled:?} > reaped {reaped:?}"
    );
    assert!(
        reaped <= sampled + gap + slack,
        "measured {sampled:?} falls short of reaped {reaped:?} by more than the {gap:?} between them"
    );
}

/// The group's members are counted, not only the direct child: here the
/// direct child only waits while a forked subshell computes, the shape AY
/// has (a supervising parent and a solving worker).
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
// The child is reaped by `wait4` in `reap`, which also returns its CPU time.
#[allow(clippy::zombie_processes)]
fn a_forked_member_of_the_group_is_counted() {
    let mut command = std::process::Command::new("/bin/sh");
    command.args(["-c", "(while :; do :; done) & wait"]);
    crate::subprocess::configure_process_group(&mut command);
    let child = command.spawn().expect("spawn a supervising child");
    let pid = child.id();
    let started = std::time::Instant::now();
    let mut measured = None;
    while started.elapsed() < Duration::from_secs(30) {
        measured = process_group_cpu(pid);
        if measured.is_some_and(|cpu| cpu >= Duration::from_millis(300)) {
            break;
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    // SAFETY: the child is this test's own unreaped child, leading its group.
    unsafe { libc::kill(-(pid as i32), libc::SIGKILL) };
    let direct = reap(pid);
    let measured = measured.expect("a live group is measured here");
    assert!(
        measured >= Duration::from_millis(300),
        "the computing member is counted: {measured:?}"
    );
    assert!(
        direct < Duration::from_millis(100),
        "the direct child only waited: {direct:?}"
    );
}

#[cfg(unix)]
#[test]
fn a_group_that_is_not_live_is_not_measured() {
    assert_eq!(process_group_cpu(0), None);
    assert_eq!(process_group_cpu(1), None);
    let mut done = std::process::Command::new("/bin/sh");
    done.args(["-c", "exit 0"]);
    crate::subprocess::configure_process_group(&mut done);
    let mut child = done.spawn().expect("spawn");
    let pid = child.id();
    child.wait().expect("reap");
    assert_eq!(process_group_cpu(pid), None, "a reaped child's group");
}

/// Reap `pid` and return the CPU time (user + system) `wait4` reports for it.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn reap(pid: u32) -> Duration {
    let mut status = 0;
    // SAFETY: an all-zero `rusage` is a valid value of this plain record.
    let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
    // SAFETY: valid output storage; `pid` is this test's own unreaped child.
    let reaped = unsafe { libc::wait4(pid as i32, &raw mut status, 0, &raw mut usage) };
    assert_eq!(reaped, pid as i32, "wait4");
    let time = |value: libc::timeval| {
        Duration::from_secs(value.tv_sec as u64) + Duration::from_micros(value.tv_usec as u64)
    };
    time(usage.ru_utime) + time(usage.ru_stime)
}
