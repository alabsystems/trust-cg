use super::*;
use std::collections::VecDeque;

enum ReadEvent {
    Bytes(&'static [u8]),
    End,
    Error(io::ErrorKind),
    InvalidCount,
}
struct ModelReader(VecDeque<ReadEvent>);

impl Read for ModelReader {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        match self.0.pop_front().expect("unexpected model read") {
            ReadEvent::Bytes(bytes) => {
                buffer[..bytes.len()].copy_from_slice(bytes);
                Ok(bytes.len())
            }
            ReadEvent::End => Ok(0),
            ReadEvent::Error(kind) => Err(kind.into()),
            ReadEvent::InvalidCount => Ok(usize::MAX),
        }
    }
}

impl ReadyRead for ModelReader {
    fn configure(&self) -> io::Result<()> {
        Ok(())
    }
    fn read_ready(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        self.read(buffer)
    }
}

#[test]
fn subprocess_capture_would_block_and_interrupt_are_not_eof() {
    let mut capture = Capture::new(ModelReader(VecDeque::from([
        ReadEvent::Error(io::ErrorKind::WouldBlock),
        ReadEvent::Error(io::ErrorKind::Interrupted),
        ReadEvent::Bytes(b"complete"),
        ReadEvent::End,
    ])))
    .expect("configure model");
    for _ in 0..2 {
        assert!(!capture.step().expect("poll"));
        assert!(!capture.eof);
    }
    assert!(capture.step().expect("read data"));
    assert_eq!(capture.bytes, b"complete");
    assert!(!capture.eof);
    assert!(capture.step().expect("read EOF"));
    assert!(capture.eof);
    assert!(!capture.step().expect("EOF is sticky without another read"));
}

#[test]
fn subprocess_capture_read_failure_cannot_complete_a_partial_transcript() {
    let mut capture = Capture::new(ModelReader(VecDeque::from([
        ReadEvent::Bytes(b"partial"),
        ReadEvent::Error(io::ErrorKind::Other),
    ])))
    .expect("configure model");
    assert!(capture.step().expect("partial read"));
    assert_eq!(
        capture.step().expect_err("read failure").kind(),
        io::ErrorKind::Other
    );
    assert!(!capture.eof);
}

#[test]
fn subprocess_capture_rejects_an_impossible_read_count_before_slicing() {
    let mut capture = Capture::new(ModelReader(VecDeque::from([ReadEvent::InvalidCount])))
        .expect("configure model");
    assert_eq!(
        capture.step().expect_err("invalid reader count").kind(),
        io::ErrorKind::InvalidData
    );
    assert!(capture.bytes.is_empty());
    assert!(!capture.eof);
}

#[test]
fn subprocess_reap_pending_or_interrupted_cannot_extend_an_expired_allowance() {
    for interrupted in [false, true] {
        let mut polls = 0;
        let (status, error) = reap_with_limit(
            || {
                polls += 1;
                if interrupted {
                    Err(io::ErrorKind::Interrupted.into())
                } else {
                    Ok(None)
                }
            },
            Duration::ZERO,
        );
        assert_eq!(polls, 1);
        assert!(status.is_none());
        assert!(error.is_none());
    }
}

#[test]
fn subprocess_reap_poll_failure_is_retained_without_retry() {
    let mut polls = 0;
    let (status, error) = reap_with_limit(
        || {
            polls += 1;
            Err(io::ErrorKind::PermissionDenied.into())
        },
        REAP_ALLOWANCE,
    );
    assert_eq!(polls, 1);
    assert!(status.is_none());
    assert_eq!(
        error.expect("poll error").kind(),
        io::ErrorKind::PermissionDenied
    );
}

#[cfg(unix)]
#[test]
fn subprocess_group_special_ids_are_rejected_before_signaling() {
    for pid in [0, 1, u32::MAX] {
        assert_eq!(
            signal_group(pid).expect_err("invalid group").kind(),
            io::ErrorKind::InvalidInput
        );
    }
}

#[cfg(unix)]
fn shell(body: &str) -> Command {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", body]);
    command
}

#[cfg(unix)]
#[test]
fn subprocess_native_capture_preserves_small_result() {
    let output = run(
        &mut shell("printf 'out'; printf 'err' >&2; exit 7"),
        Some(Duration::from_secs(2)),
    )
    .expect("complete native capture");
    assert_eq!(output.status.code(), Some(7));
    assert_eq!(output.stdout, b"out");
    assert_eq!(output.stderr, b"err");
}

#[cfg(unix)]
#[test]
fn subprocess_native_closed_streams_do_not_replace_child_exit() {
    let start = Instant::now();
    let result = run(
        &mut shell("exec 1>&- 2>&-; exec sleep 3"),
        Some(Duration::from_millis(100)),
    );
    assert!(matches!(result, Err(RunError::Timeout(_))), "{result:?}");
    assert!(start.elapsed() < Duration::from_secs(1));
}

/// A deadline expiry reports what the child's process group consumed under
/// the deadline, measured before the kill: a waiting child next to nothing, a
/// computing one (a forked member of the group, the shape of AY's solving
/// worker) a nonzero CPU time that one computing process cannot make exceed
/// the wall clock. An error that is not an expiry reports none.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn subprocess_native_deadline_expiry_reports_the_process_group_cpu() {
    let limit = Duration::from_millis(400);
    let waiting = run(&mut shell("sleep 3"), Some(limit)).expect_err("outlasts its deadline");
    let expiry = waiting.expiry().expect("a deadline expiry");
    assert_eq!(expiry.limit, limit);
    let cpu = expiry.cpu.expect("measured on this platform");
    assert!(cpu < limit / 2, "a waiting child used {cpu:?}");
    assert!(
        waiting.to_string().contains("process-group CPU"),
        "{waiting}"
    );

    let started = Instant::now();
    let computing = run(&mut shell("(while :; do :; done) & wait"), Some(limit))
        .expect_err("outlasts its deadline");
    let elapsed = started.elapsed();
    let cpu = computing
        .expiry()
        .and_then(|expiry| expiry.cpu)
        .expect("measured on this platform");
    assert!(cpu > Duration::ZERO, "the computing member is counted");
    assert!(
        cpu <= elapsed + Duration::from_millis(30),
        "one computing process used {cpu:?} in {elapsed:?}"
    );

    let refused = run(
        &mut Command::new("/nonexistent/trust-cg-subprocess-control"),
        Some(limit),
    )
    .expect_err("cannot spawn");
    assert_eq!(refused.expiry(), None);
}

/// A completed child reports its wall-clock time and the CPU time its process
/// group consumed, read at the exit while the leader is still unreaped: a
/// waiting child next to nothing; a supervising child whose forked worker
/// computed and was reaped before the exit (AY's shape) the worker's CPU
/// time, which one computing process cannot make exceed the wall clock.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn subprocess_native_completion_reports_the_process_group_cpu() {
    let waited =
        run_measured(&mut shell("sleep 0.3"), Some(Duration::from_secs(10))).expect("completes");
    assert!(waited.output.status.success(), "{:?}", waited.output);
    assert!(
        waited.wall >= Duration::from_millis(250),
        "{:?}",
        waited.wall
    );
    let cpu = waited.cpu.expect("measured on this platform");
    assert!(
        cpu < waited.wall / 2,
        "a waiting child used {cpu:?} in {:?}",
        waited.wall
    );

    // A fixed amount of work, so its CPU time does not depend on load, well
    // over the 100 ms asked below under any `/bin/sh`: 60,000 iterations took
    // about 40 ms of CPU under dash (Linux AArch64's `/bin/sh`, reported by
    // the 2026-10-16 diagnosis there) and 120 ms under `/bin/dash` on
    // aarch64-apple-darwin at load 50 (2026-10-22), so a fast dash host could
    // not show the bound; 600,000 took 1.1 s of CPU under dash and 1.9 s
    // under bash on the latter.
    let worked = run_measured(
        &mut shell("(i=0; while [ $i -lt 600000 ]; do i=$((i+1)); done) & wait"),
        Some(Duration::from_secs(120)),
    )
    .expect("completes");
    assert!(worked.output.status.success(), "{:?}", worked.output);
    let cpu = worked.cpu.expect("measured on this platform");
    assert!(
        cpu >= Duration::from_millis(100),
        "the reaped worker is counted: {cpu:?} in {:?}",
        worked.wall
    );
    assert!(
        cpu <= worked.wall + Duration::from_millis(30),
        "one computing process used {cpu:?} in {:?}",
        worked.wall
    );
}

#[cfg(unix)]
#[test]
fn subprocess_native_huge_duration_does_not_overflow_an_instant() {
    for limit in [None, Some(Duration::MAX)] {
        let result = run(&mut shell("printf 'complete'"), limit).expect("large/unlimited policy");
        assert!(result.status.success());
        assert_eq!(result.stdout, b"complete");
    }
}

#[cfg(unix)]
#[test]
fn subprocess_native_zero_duration_cannot_publish_output() {
    let result = run(&mut shell("exit 0"), Some(Duration::ZERO));
    assert!(matches!(result, Err(RunError::Timeout(_))), "{result:?}");
}

#[cfg(unix)]
#[test]
fn subprocess_native_child_identity_stays_unreaped_until_group_cleanup() {
    let mut command = shell("exit 7");
    configure_process_group(&mut command);
    let mut process = OwnedChild {
        child: command.spawn().expect("spawn owned control"),
        disarmed: false,
    };
    let start = Instant::now();
    while !child_has_exited(&mut process.child).expect("observe owned child") {
        assert!(start.elapsed() < Duration::from_secs(2));
        std::thread::sleep(POLL_INTERVAL);
    }
    // Repeating WNOWAIT succeeds: observation has not released the PID. The
    // terminating cleanup may see an already-exited child, whose status wins.
    assert!(child_has_exited(&mut process.child).expect("observe without reaping"));
    let cleanup = process.stop();
    assert_eq!(cleanup.status.and_then(|status| status.code()), Some(7));
}
