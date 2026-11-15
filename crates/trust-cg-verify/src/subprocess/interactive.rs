//! Readiness-driven duplex I/O for a caller-framed resident protocol. Unlike
//! one-shot capture, completion is a protocol boundary, not EOF. No detached I/O
//! worker survives timeout/teardown; callers still own framing and proof
//! authority.
//!
//! The pipes are non-blocking and every read/write is a bounded step, so no call
//! blocks inside the stream. When neither stream moves, the loop waits on fd
//! READINESS (`poll(2)`) rather than sleeping a fixed interval — see
//! [`wait_for_readiness`] for the measurement that motivated it.

use super::*;
use std::io::Write;
use std::process::{ChildStdin, ChildStdout};

#[derive(Clone, Copy)]
pub(crate) struct Deadline {
    start: Instant,
    limit: Option<Duration>,
}

impl Deadline {
    pub(crate) fn new(limit: Option<Duration>) -> Self {
        Self {
            start: Instant::now(),
            limit,
        }
    }

    pub(crate) fn expired(self) -> bool {
        self.limit
            .is_some_and(|limit| self.start.elapsed() >= limit)
    }

    /// Sleep one poll step, bounded by the deadline. Only the non-unix
    /// exchange loop uses it; unix waits on fd readiness instead, and the
    /// resident-server queue no longer spends a solver deadline while waiting.
    #[cfg(not(unix))]
    pub(crate) fn pause(self) {
        let delay = self.limit.map_or(POLL_INTERVAL, |limit| {
            POLL_INTERVAL.min(limit.saturating_sub(self.start.elapsed()))
        });
        std::thread::sleep(delay);
    }

    /// How long this loop iteration may block, bounded by the deadline.
    ///
    /// `WAIT_CAP` is not a latency floor — a readiness wait returns the instant
    /// the peer speaks. It is an upper bound so the loop keeps re-checking
    /// `expired()` and the child's liveness even if a wakeup is ever missed.
    fn wait_budget(self) -> Duration {
        const WAIT_CAP: Duration = Duration::from_millis(100);
        self.limit.map_or(WAIT_CAP, |limit| {
            WAIT_CAP.min(limit.saturating_sub(self.start.elapsed()))
        })
    }
}

/// Block until one of `fds` is ready, the budget elapses, or a signal arrives.
///
/// WHY this exists, measured 2026-09-14. The exchange loop below used to call
/// [`Deadline::pause`] — a flat 5 ms `thread::sleep` — whenever neither stream
/// made progress. Every SMT query to the resident `ay` server therefore paid a
/// multiple of 5 ms in pure sleep, and the queries are serialized process-wide
/// behind one resident solver. Sampling a `trust-ir-cg` compile of 40 trivial
/// functions put **87% of the proof-verifier thread's samples inside that
/// `thread::sleep`**, under
/// `generate_proof_certificates -> ... -> ay_bridge::run_solver_via_server_with_authority`.
/// The backend was not solving slowly; it was sleeping between solves.
///
/// What does NOT change: the pipes stay non-blocking and every read and write
/// still goes through the same `ReadyRead`/`ReadyWrite` step, so no call can
/// block indefinitely inside a read. This only replaces "sleep, then look
/// again" with "wait until there is something to look at".
///
/// Windows keeps the sleep: its `PIPE_NOWAIT` byte pipes have no readiness
/// primitive to wait on, and inventing one is out of scope here.
#[cfg(unix)]
fn wait_for_readiness(
    read_fd: Option<std::os::fd::RawFd>,
    write_fd: Option<std::os::fd::RawFd>,
    budget: Duration,
) {
    let mut fds: [libc::pollfd; 2] = [
        libc::pollfd {
            fd: -1,
            events: 0,
            revents: 0,
        },
        libc::pollfd {
            fd: -1,
            events: 0,
            revents: 0,
        },
    ];
    let mut count = 0usize;
    if let Some(fd) = read_fd {
        fds[count] = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        count += 1;
    }
    if let Some(fd) = write_fd {
        fds[count] = libc::pollfd {
            fd,
            events: libc::POLLOUT,
            revents: 0,
        };
        count += 1;
    }
    if count == 0 {
        // Nothing to wait on: keep the old behaviour rather than spin.
        std::thread::sleep(POLL_INTERVAL.min(budget));
        return;
    }
    // `poll` takes whole milliseconds; roughly-up so a sub-millisecond budget
    // still yields the CPU rather than spinning.
    let millis = budget.as_millis().min(i32::MAX as u128) as i32;
    // SAFETY: `fds[..count]` is initialised, borrowed for the call only, and the
    // fds are owned by the caller's live `ChildStdin`/`ChildStdout`. A `poll`
    // failure (including `EINTR`) is not an error here — the loop re-checks its
    // own state and the deadline on the next iteration either way.
    let _ = unsafe { libc::poll(fds.as_mut_ptr(), count as libc::nfds_t, millis.max(1)) };
}

trait ReadyWrite {
    fn configure(&self) -> io::Result<()>;
    fn write_ready(&mut self, bytes: &[u8]) -> io::Result<usize>;
}

impl ReadyWrite for ChildStdin {
    fn configure(&self) -> io::Result<()> {
        #[cfg(unix)]
        return configure_nonblocking(self);
        #[cfg(windows)]
        {
            use std::ffi::c_void;
            use std::os::windows::io::AsRawHandle;
            #[link(name = "kernel32")]
            unsafe extern "system" {
                fn SetNamedPipeHandleState(
                    handle: *mut c_void,
                    mode: *const u32,
                    collection_count: *const u32,
                    collection_timeout: *const u32,
                ) -> i32;
            }
            // PIPE_NOWAIT | PIPE_READMODE_BYTE. This is synchronous polling,
            // not background overlapped I/O. A full byte pipe accepts only
            // available capacity (possibly zero), without waiting for a reader.
            let mode = 1;
            // SAFETY: exclusively owned spawn-created ChildStdin; Rust 1.97.1's
            // std creates its named-pipe parent with GENERIC_WRITE access
            // (validated there; Trust ships no Windows std to re-check).
            if unsafe {
                SetNamedPipeHandleState(
                    self.as_raw_handle(),
                    &mode,
                    std::ptr::null(),
                    std::ptr::null(),
                )
            } == 0
            {
                return Err(io::Error::last_os_error());
            }
            Ok(())
        }
        #[cfg(not(any(unix, windows)))]
        Err(io::ErrorKind::Unsupported.into())
    }

    fn write_ready(&mut self, bytes: &[u8]) -> io::Result<usize> {
        let result = self.write(bytes);
        #[cfg(windows)]
        if matches!(result, Ok(0)) && !bytes.is_empty() {
            return Err(io::ErrorKind::WouldBlock.into());
        }
        result
    }
}

fn write_step(writer: &mut impl ReadyWrite, remaining: &mut &[u8]) -> io::Result<bool> {
    if remaining.is_empty() {
        return Ok(false);
    }
    let limit = remaining.len().min(16 * 1024);
    match writer.write_ready(&remaining[..limit]) {
        Ok(0) => Err(io::ErrorKind::WriteZero.into()),
        Ok(count) if count <= limit => {
            *remaining = &remaining[count..];
            Ok(true)
        }
        Ok(_) => Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "pipe write exceeded its input",
        )),
        Err(error)
            if matches!(
                error.kind(),
                io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
            ) =>
        {
            Ok(false)
        }
        Err(error) => Err(error),
    }
}

enum LinePoll {
    Line(String),
    Pending { progress: bool },
    End,
}

struct Lines<R> {
    reader: R,
    bytes: Vec<u8>,
    consumed: usize,
    scanned: usize,
    eof: bool,
}

impl<R: ReadyRead> Lines<R> {
    /// The underlying reader, so the exchange loop can wait for it to become
    /// readable instead of sleeping.
    fn reader(&self) -> &R {
        &self.reader
    }

    fn new(reader: R) -> io::Result<Self> {
        reader.configure()?;
        Ok(Self {
            reader,
            bytes: Vec::new(),
            consumed: 0,
            scanned: 0,
            eof: false,
        })
    }

    fn line(&mut self, end: usize, next: usize) -> io::Result<LinePoll> {
        let bytes = &self.bytes[self.consumed..end];
        let text = std::str::from_utf8(bytes)
            .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))?;
        let mut line = String::new();
        line.try_reserve(text.len())
            .map_err(|error| io::Error::new(io::ErrorKind::OutOfMemory, error))?;
        line.push_str(text);
        self.consumed = next;
        self.scanned = next;
        Ok(LinePoll::Line(line))
    }

    fn poll(&mut self) -> io::Result<LinePoll> {
        if let Some(relative) = self.bytes[self.scanned..]
            .iter()
            .position(|&byte| byte == b'\n')
        {
            let newline = self.scanned + relative;
            let end = if newline > self.consumed && self.bytes[newline - 1] == b'\r' {
                newline - 1
            } else {
                newline
            };
            return self.line(end, newline + 1);
        }
        self.scanned = self.bytes.len();
        if self.eof {
            return if self.consumed < self.bytes.len() {
                self.line(self.bytes.len(), self.bytes.len())
            } else {
                Ok(LinePoll::End)
            };
        }
        // Compact only after all complete lines have been consumed, not once
        // per line; scanned prefixes are not searched again on partial reads.
        if self.consumed != 0 {
            self.bytes.drain(..self.consumed);
            self.scanned -= self.consumed;
            self.consumed = 0;
        }
        let mut buffer = [0; 16 * 1024];
        match self.reader.read_ready(&mut buffer) {
            Ok(0) => self.eof = true,
            Ok(count) => {
                let chunk = buffer.get(..count).ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidData, "pipe read exceeded its buffer")
                })?;
                self.bytes
                    .try_reserve(count)
                    .map_err(|error| io::Error::new(io::ErrorKind::OutOfMemory, error))?;
                self.bytes.extend_from_slice(chunk);
            }
            Err(error)
                if matches!(
                    error.kind(),
                    io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted
                ) =>
            {
                return Ok(LinePoll::Pending { progress: false });
            }
            Err(error) => return Err(error),
        }
        Ok(LinePoll::Pending { progress: true })
    }
}

pub(crate) struct InteractiveProcess {
    process: OwnedChild,
    stdin: ChildStdin,
    stdout: Lines<ChildStdout>,
}

struct ExchangeGuard<'a> {
    process: &'a mut OwnedChild,
    completed: bool,
}

impl Drop for ExchangeGuard<'_> {
    fn drop(&mut self) {
        // Errors already stop the process. Unwinding must also abandon the
        // interrupted frame, even if its owner catches the panic and survives.
        if !self.completed && !self.process.disarmed {
            let _ = self.process.stop();
        }
    }
}

impl InteractiveProcess {
    pub(crate) fn spawn(command: &mut Command) -> Result<Self, RunError> {
        command
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null());
        configure_process_group(command);
        let child = command.spawn().map_err(|source| RunError::Io {
            operation: "spawn",
            source,
            cleanup: None,
        })?;
        let mut process = OwnedChild {
            child,
            disarmed: false,
        };
        let stdin = process
            .child
            .stdin
            .take()
            .ok_or_else(|| process.error("stdin setup", io::ErrorKind::BrokenPipe.into()))?;
        stdin
            .configure()
            .map_err(|error| process.error("stdin configuration", error))?;
        let stdout = process
            .child
            .stdout
            .take()
            .ok_or_else(|| process.error("stdout setup", io::ErrorKind::BrokenPipe.into()))?;
        let stdout =
            Lines::new(stdout).map_err(|error| process.error("stdout configuration", error))?;
        Ok(Self {
            process,
            stdin,
            stdout,
        })
    }

    pub(crate) fn pid(&self) -> u32 {
        self.process.child.id()
    }

    pub(crate) fn stop(&mut self) -> Option<Termination> {
        (!self.process.disarmed).then(|| self.process.stop())
    }

    /// Feed all input and consume lines until the caller's frame boundary.
    /// The same deadline covers both directions, including pipe backpressure.
    /// Bytes after the boundary remain buffered for the next exchange. A
    /// deadline expiry does not measure the CPU time the process used
    /// ([`super::DeadlineExpiry::cpu`] is `None`); see
    /// [`Self::exchange_measuring_cpu`].
    pub(crate) fn exchange(
        &mut self,
        input: &[u8],
        deadline: Deadline,
        on_line: impl FnMut(&str) -> io::Result<bool>,
    ) -> Result<(), RunError> {
        self.exchange_with(input, deadline, false, on_line)
    }

    /// [`Self::exchange`], and a deadline expiry reports the CPU time the
    /// process's group consumed during THIS exchange: its total when the
    /// exchange begins (before any of the request is written) is subtracted
    /// from its total at the expiry, so the work of earlier exchanges on the
    /// same resident process is not counted. The starting measurement lists
    /// the process group, so only callers that use the evidence ask for it.
    pub(crate) fn exchange_measuring_cpu(
        &mut self,
        input: &[u8],
        deadline: Deadline,
        on_line: impl FnMut(&str) -> io::Result<bool>,
    ) -> Result<(), RunError> {
        self.exchange_with(input, deadline, true, on_line)
    }

    fn exchange_with(
        &mut self,
        mut input: &[u8],
        deadline: Deadline,
        measure_cpu: bool,
        mut on_line: impl FnMut(&str) -> io::Result<bool>,
    ) -> Result<(), RunError> {
        if self.process.disarmed {
            return Err(RunError::Io {
                operation: "closed interactive process",
                source: io::ErrorKind::NotConnected.into(),
                cleanup: None,
            });
        }
        let since = if measure_cpu {
            super::group_cpu::process_group_cpu(self.pid())
        } else {
            None
        };
        let mut exchange = ExchangeGuard {
            process: &mut self.process,
            completed: false,
        };
        let mut complete = false;
        // STALL DIAGNOSTIC. A resident-solver exchange that makes no progress
        // for a long time is indistinguishable, from the outside, from a compile
        // that is merely slow: measured 2026-09-14, eight `library/std` compilers
        // sat at 0.0% CPU for 1h45 with their `ay --incremental` children idle,
        // and nothing said so. Say so — once per minute of zero progress, with
        // the facts a reader needs (how much of the request is still unwritten,
        // whether the sentinel has arrived, whether a deadline exists at all).
        let stall_since = Instant::now();
        let mut last_progress = Instant::now();
        let mut last_report = Instant::now();
        loop {
            if deadline.expired()
                && let Some(limit) = deadline.limit
            {
                return Err(exchange.process.expire(limit, since));
            }
            let mut progress = write_step(&mut self.stdin, &mut input)
                .map_err(|error| exchange.process.error("stdin write", error))?;
            if !complete {
                match self
                    .stdout
                    .poll()
                    .map_err(|error| exchange.process.error("stdout read", error))?
                {
                    LinePoll::Line(line) => {
                        complete = on_line(&line)
                            .map_err(|error| exchange.process.error("response frame", error))?;
                        progress = true;
                    }
                    LinePoll::Pending {
                        progress: read_progress,
                    } => progress |= read_progress,
                    LinePoll::End => {
                        return Err(exchange
                            .process
                            .error("response EOF", io::ErrorKind::UnexpectedEof.into()));
                    }
                }
            }
            if complete && input.is_empty() && !deadline.expired() {
                exchange.completed = true;
                return Ok(());
            }
            if progress {
                last_progress = Instant::now();
            } else if last_progress.elapsed() >= Duration::from_secs(60)
                && last_report.elapsed() >= Duration::from_secs(60)
            {
                last_report = Instant::now();
                eprintln!(
                    "trust-cg-verify: resident solver exchange STALLED for {}s (child pid {}, \
                     {} request byte(s) still unwritten, sentinel seen: {}, deadline: {}); \
                     the compile is waiting, not working",
                    stall_since.elapsed().as_secs(),
                    exchange.process.child.id(),
                    input.len(),
                    complete,
                    if deadline.limit.is_some() {
                        "set"
                    } else {
                        "NONE (no timeout)"
                    },
                );
            }
            if !progress {
                // Neither stream moved. Wait until one of them CAN move rather
                // than sleeping a fixed interval; see `wait_for_readiness`.
                #[cfg(unix)]
                {
                    use std::os::fd::AsRawFd;
                    wait_for_readiness(
                        (!complete).then(|| self.stdout.reader().as_raw_fd()),
                        (!input.is_empty()).then(|| self.stdin.as_raw_fd()),
                        deadline.wait_budget(),
                    );
                }
                #[cfg(not(unix))]
                deadline.pause();
            }
        }
    }
}

#[cfg(test)]
#[path = "interactive_tests.rs"]
mod tests;
