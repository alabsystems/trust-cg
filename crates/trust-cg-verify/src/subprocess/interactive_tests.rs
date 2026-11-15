use super::*;
use std::collections::VecDeque;

enum ReadEvent {
    Bytes(&'static [u8]),
    Error(io::ErrorKind),
    End,
    InvalidCount,
}

struct Reader(VecDeque<ReadEvent>);
impl Read for Reader {
    fn read(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        match self.0.pop_front().expect("unexpected read") {
            ReadEvent::Bytes(bytes) => {
                buffer[..bytes.len()].copy_from_slice(bytes);
                Ok(bytes.len())
            }
            ReadEvent::Error(kind) => Err(kind.into()),
            ReadEvent::End => Ok(0),
            ReadEvent::InvalidCount => Ok(usize::MAX),
        }
    }
}
impl ReadyRead for Reader {
    fn configure(&self) -> io::Result<()> {
        Ok(())
    }
    fn read_ready(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        self.read(buffer)
    }
}

#[test]
fn resident_io_lines_preserve_fragmented_utf8_crlf_and_eof_tail() {
    let mut lines = Lines::new(Reader(VecDeque::from([
        ReadEvent::Bytes(b"\xc3"),
        ReadEvent::Bytes(b"\xa9\r\nsecond\ntail\r"),
        ReadEvent::End,
    ])))
    .expect("model");
    let mut actual = Vec::new();
    for _ in 0..12 {
        match lines.poll().expect("valid lines") {
            LinePoll::Line(line) => actual.push(line),
            LinePoll::Pending { .. } => {}
            LinePoll::End => break,
        }
    }
    assert_eq!(actual, ["é", "second", "tail\r"]);
    assert!(matches!(lines.poll().expect("sticky EOF"), LinePoll::End));
}

#[test]
fn resident_io_pending_and_interrupted_reads_do_not_close_the_stream() {
    let mut lines = Lines::new(Reader(VecDeque::from([
        ReadEvent::Error(io::ErrorKind::WouldBlock),
        ReadEvent::Error(io::ErrorKind::Interrupted),
        ReadEvent::Error(io::ErrorKind::PermissionDenied),
    ])))
    .expect("model");
    for _ in 0..2 {
        assert!(matches!(
            lines.poll().expect("pending"),
            LinePoll::Pending { progress: false }
        ));
        assert!(!lines.eof);
    }
    assert!(matches!(lines.poll(), Err(error) if error.kind() == io::ErrorKind::PermissionDenied));
}

#[test]
fn resident_io_invalid_utf8_and_read_counts_are_errors_not_lines() {
    for event in [ReadEvent::Bytes(b"\xff\n"), ReadEvent::InvalidCount] {
        let mut lines = Lines::new(Reader(VecDeque::from([event]))).expect("model");
        let result = match lines.poll() {
            Ok(LinePoll::Pending { progress: true }) => lines.poll(),
            result => result,
        };
        assert!(matches!(result, Err(error) if error.kind() == io::ErrorKind::InvalidData));
        assert_eq!(lines.consumed, 0);
    }
}

struct Writer {
    results: VecDeque<io::Result<usize>>,
    accepted: Vec<u8>,
    largest_request: usize,
}
impl ReadyWrite for Writer {
    fn configure(&self) -> io::Result<()> {
        Ok(())
    }
    fn write_ready(&mut self, bytes: &[u8]) -> io::Result<usize> {
        self.largest_request = self.largest_request.max(bytes.len());
        let result = self.results.pop_front().expect("unexpected write");
        if let Ok(count) = &result
            && *count <= bytes.len()
        {
            self.accepted.extend_from_slice(&bytes[..*count]);
        }
        result
    }
}
fn writer(results: impl IntoIterator<Item = io::Result<usize>>) -> Writer {
    Writer {
        results: results.into_iter().collect(),
        accepted: Vec::new(),
        largest_request: 0,
    }
}

#[test]
fn resident_io_partial_writes_retain_exact_input_across_pending_polls() {
    let mut writer = writer([
        Err(io::ErrorKind::WouldBlock.into()),
        Ok(2),
        Err(io::ErrorKind::Interrupted.into()),
        Ok(3),
    ]);
    let mut remaining = b"input".as_slice();
    for expected in [false, true, false, true] {
        assert_eq!(
            write_step(&mut writer, &mut remaining).expect("write step"),
            expected
        );
    }
    assert!(remaining.is_empty());
    assert_eq!(writer.accepted, b"input");
    assert!(!write_step(&mut writer, &mut remaining).expect("no empty write"));
}

#[test]
fn resident_io_zero_and_oversized_writes_do_not_advance_input() {
    for (count, kind) in [
        (0, io::ErrorKind::WriteZero),
        (usize::MAX, io::ErrorKind::InvalidData),
    ] {
        let mut writer = writer([Ok(count)]);
        let mut remaining = b"input".as_slice();
        assert_eq!(
            write_step(&mut writer, &mut remaining)
                .expect_err("invalid count")
                .kind(),
            kind
        );
        assert_eq!(remaining, b"input");
    }
}

#[test]
fn resident_io_write_steps_are_bounded_for_fair_duplex_polling() {
    let input = vec![b'x'; 32 * 1024];
    let mut remaining = input.as_slice();
    let mut writer = writer([Ok(16 * 1024), Ok(16 * 1024)]);
    for _ in 0..2 {
        assert!(write_step(&mut writer, &mut remaining).expect("write chunk"));
    }
    assert_eq!(writer.largest_request, 16 * 1024);
    assert_eq!(writer.accepted, input);
}

#[test]
fn resident_io_deadlines_distinguish_zero_unlimited_and_huge() {
    assert!(Deadline::new(Some(Duration::ZERO)).expired());
    assert!(!Deadline::new(None).expired());
    assert!(!Deadline::new(Some(Duration::MAX)).expired());
}

#[cfg(unix)]
fn shell(body: &str) -> InteractiveProcess {
    let mut command = Command::new("/bin/sh");
    command.args(["-c", body]);
    InteractiveProcess::spawn(&mut command).expect("owned interactive control")
}

#[cfg(unix)]
#[test]
fn resident_io_native_full_duplex_preserves_large_input_and_output() {
    let mut process = shell(
        "dd if=/dev/zero bs=131072 count=1 2>/dev/null; printf '\\n'; resident_input=$(head -c 131072); test \"${#resident_input}\" -eq 131072 || exit 4; case \"$resident_input\" in *[!x]*) exit 5;; esac; printf 'done\\n'",
    );
    let mut lines = Vec::new();
    process
        .exchange(
            &vec![b'x'; 131072],
            Deadline::new(Some(Duration::from_secs(5))),
            |line| {
                lines.push(line.to_owned());
                Ok(line == "done")
            },
        )
        .expect("both full pipes must make progress");
    assert_eq!(lines.len(), 2);
    assert_eq!(lines[0].len(), 131072);
    assert!(lines[0].bytes().all(|byte| byte == 0));
    assert_eq!(lines[1], "done");
}

#[cfg(unix)]
#[test]
fn resident_io_native_frame_boundaries_retain_following_lines() {
    let mut process = shell("printf 'first\\nsecond\\n'; sleep 3");
    for expected in ["first", "second"] {
        let mut actual = Vec::new();
        process
            .exchange(b"", Deadline::new(Some(Duration::from_secs(2))), |line| {
                actual.push(line.to_owned());
                Ok(true)
            })
            .expect("framed exchange");
        assert_eq!(actual, [expected]);
    }
}

#[cfg(unix)]
#[test]
fn resident_io_native_inherited_pipe_keeps_deadline_after_parent_exit() {
    let mut process = shell("(sleep 3; printf 'late\\n') & exit 0");
    let start = Instant::now();
    let result = process.exchange(b"", Deadline::new(Some(Duration::from_millis(500))), |_| {
        Ok(false)
    });
    assert!(matches!(result, Err(RunError::Timeout(_))), "{result:?}");
    assert!(start.elapsed() < Duration::from_secs(2));
    assert!(
        process.stop().is_none(),
        "timeout already performed bounded cleanup"
    );
}

/// A measured exchange reports the CPU time the process group used during
/// THAT exchange: at least 200 ms of earlier computation is not charged to
/// the next exchange's deadline. An unmeasured exchange reports none.
#[cfg(any(target_os = "macos", target_os = "linux"))]
#[test]
fn resident_io_native_measured_exchange_counts_only_its_own_cpu() {
    let mut process = shell(
        "while read line; do [ \"$line\" = burn ] || break; i=0; while [ $i -lt 200000 ]; do i=$((i+1)); done; printf 'ready\\n'; done; sleep 3",
    );
    // Calibrate against measured CPU, rather than assuming a fixed number of
    // shell iterations consumes 200 ms on every host. All preparation batches
    // share one deadline, and each ready line ends the batch before measurement.
    let preparation = Deadline::new(Some(Duration::from_secs(120)));
    let before = loop {
        process
            .exchange(b"burn\n", preparation, |line| Ok(line == "ready"))
            .expect("the preparation exchange completes");
        let before = crate::subprocess::group_cpu::process_group_cpu(process.pid())
            .expect("measured on this platform");
        if before >= Duration::from_millis(200) {
            break before;
        }
    };
    assert!(
        before >= Duration::from_millis(200),
        "the process computed before the exchange: {before:?}"
    );
    let limit = Duration::from_millis(400);
    let expired = process
        .exchange_measuring_cpu(b"go\n", Deadline::new(Some(limit)), |_| Ok(false))
        .expect_err("outlasts its deadline");
    let expiry = expired.expiry().expect("a deadline expiry");
    assert_eq!(expiry.limit, limit);
    let cpu = expiry.cpu.expect("measured on this platform");
    assert!(
        cpu < Duration::from_millis(100) && cpu < before / 2,
        "the exchange only waited, yet {cpu:?} of the process's {before:?} was charged to it"
    );

    let mut unmeasured = shell("sleep 3");
    let expired = unmeasured
        .exchange(b"", Deadline::new(Some(Duration::from_millis(200))), |_| {
            Ok(false)
        })
        .expect_err("outlasts its deadline");
    assert_eq!(expired.expiry().map(|expiry| expiry.cpu), Some(None));
}

#[cfg(unix)]
#[test]
fn resident_io_native_callback_failure_stops_the_owned_process() {
    let mut process = shell("printf 'bad\\nstale\\n'; sleep 3");
    let result = process.exchange(b"", Deadline::new(Some(Duration::from_secs(2))), |_| {
        Err(io::ErrorKind::InvalidData.into())
    });
    assert!(matches!(
        result,
        Err(RunError::Io {
            operation: "response frame",
            ..
        })
    ));
    assert!(process.stop().is_none());
    let reused = process.exchange(b"", Deadline::new(None), |_| Ok(true));
    assert!(matches!(
        reused,
        Err(RunError::Io {
            operation: "closed interactive process",
            ..
        })
    ));
}

#[cfg(unix)]
#[test]
fn resident_io_native_callback_panic_abandons_the_interrupted_exchange() {
    let mut process = shell("printf 'first\\nstale\\n'; sleep 3");
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        process.exchange(b"", Deadline::new(Some(Duration::from_secs(2))), |_| {
            panic!("deliberate frame-handler panic");
        })
    }))
    .expect_err("frame handler unwinds");
    assert_eq!(
        panic.downcast_ref::<&str>(),
        Some(&"deliberate frame-handler panic")
    );
    assert!(
        process.stop().is_none(),
        "unwinding already stopped the process"
    );
    let reused = process.exchange(b"", Deadline::new(None), |_| Ok(true));
    assert!(matches!(
        reused,
        Err(RunError::Io {
            operation: "closed interactive process",
            ..
        })
    ));
}
