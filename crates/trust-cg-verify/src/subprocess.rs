//! Deadline-aware subprocess capture for verification tools, without authority policy.
//!
//! Success requires an observed direct-child exit AND EOF on both output streams.
//! No reader thread, blocking reap, or pipe-EOF wait survives a deadline. The
//! deadline covers polling/capture after spawn, plus a bounded cleanup allowance;
//! it cannot bound OS spawn/syscall scheduling or guarantee escaped-child cleanup.

use std::fmt;
use std::io::{self, Read};
use std::process::{Child, Command, ExitStatus, Output, Stdio};
use std::time::{Duration, Instant};

const POLL_INTERVAL: Duration = Duration::from_millis(5);
const REAP_ALLOWANCE: Duration = Duration::from_millis(100);

mod group_cpu;
mod interactive;
pub(crate) use interactive::{Deadline, InteractiveProcess};

#[derive(Debug)]
pub(crate) struct Termination {
    pid: u32,
    status: Option<ExitStatus>,
    request_error: Option<io::Error>,
    reap_error: Option<io::Error>,
}

impl fmt::Display for Termination {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "termination requested for pid {}", self.pid)?;
        match self.status {
            Some(status) => write!(f, "; observed exit: {status}")?,
            None => write!(f, "; exit not confirmed")?,
        }
        if let Some(error) = &self.request_error {
            write!(f, "; termination request: {error}")?;
        }
        if let Some(error) = &self.reap_error {
            write!(f, "; exit-status poll: {error}")?;
        }
        Ok(())
    }
}

/// What a child's process group had consumed when its deadline expired.
///
/// A deadline is wall-clock time, so its expiry alone does not say whether the
/// child used the budget or spent it waiting for a processor on a loaded host.
/// `cpu` is the CPU time (user + system) of the child's whole process group
/// under that deadline, measured immediately before the kill
/// (`group_cpu::process_group_cpu`); `None` when it was not measured (no
/// per-process accounting on this platform, a member that could not be read,
/// or a caller that did not ask for the measurement).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct DeadlineExpiry {
    /// The wall-clock budget that expired.
    pub(crate) limit: Duration,
    /// CPU time the child's process group consumed under it.
    pub(crate) cpu: Option<Duration>,
}

impl fmt::Display for DeadlineExpiry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.cpu {
            Some(cpu) => write!(
                f,
                "process-group CPU {} ms under a {} ms deadline",
                cpu.as_millis(),
                self.limit.as_millis()
            ),
            None => write!(
                f,
                "process-group CPU not measured under a {} ms deadline",
                self.limit.as_millis()
            ),
        }
    }
}

/// A deadline that expired: what the child had consumed under it, then the
/// kill and reap that followed.
#[derive(Debug)]
pub(crate) struct Expired {
    pub(crate) expiry: DeadlineExpiry,
    pub(crate) cleanup: Termination,
}

#[derive(Debug)]
pub(crate) enum RunError {
    Timeout(Expired),
    Io {
        operation: &'static str,
        source: io::Error,
        cleanup: Option<Termination>,
    },
}

#[cfg(test)]
impl RunError {
    /// The deadline expiry this error reports; `None` for every other error.
    pub(crate) fn expiry(&self) -> Option<DeadlineExpiry> {
        match self {
            Self::Timeout(expired) => Some(expired.expiry),
            Self::Io { .. } => None,
        }
    }
}

impl fmt::Display for RunError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Timeout(Expired { expiry, cleanup }) => {
                write!(f, "subprocess deadline expired; {cleanup}; {expiry}")
            }
            Self::Io {
                operation,
                source,
                cleanup,
            } => {
                write!(f, "subprocess {operation}: {source}")?;
                if let Some(cleanup) = cleanup {
                    write!(f, "; {cleanup}")?;
                }
                Ok(())
            }
        }
    }
}

pub(crate) fn configure_process_group(command: &mut Command) {
    #[cfg(unix)]
    {
        use std::os::unix::process::CommandExt;
        command.process_group(0);
    }
    #[cfg(not(unix))]
    let _ = command;
}

/// Terminate an exclusively owned child spawned in its own Unix process group.
/// The caller must not have reaped it or arranged an external SIGCHLD reaper.
/// Windows retains direct-child handle ownership but has no process-group kill.
pub(crate) fn terminate(child: &mut Child) -> Termination {
    let pid = child.id();
    let start = Instant::now();
    let request_error = loop {
        match request_termination(child) {
            Err(error)
                if error.kind() == io::ErrorKind::Interrupted
                    && start.elapsed() < REAP_ALLOWANCE =>
            {
                std::thread::sleep(
                    POLL_INTERVAL.min(REAP_ALLOWANCE.saturating_sub(start.elapsed())),
                );
            }
            result => break result.err(),
        }
    };
    let (status, reap_error) = reap_with_limit(
        || child.try_wait(),
        REAP_ALLOWANCE.saturating_sub(start.elapsed()),
    );
    Termination {
        pid,
        status,
        request_error,
        reap_error,
    }
}

fn reap_with_limit(
    mut poll: impl FnMut() -> io::Result<Option<ExitStatus>>,
    allowance: Duration,
) -> (Option<ExitStatus>, Option<io::Error>) {
    let start = Instant::now();
    loop {
        match poll() {
            Ok(Some(status)) => return (Some(status), None),
            Ok(None) => {}
            Err(poll_error) if poll_error.kind() == io::ErrorKind::Interrupted => {}
            Err(poll_error) => return (None, Some(poll_error)),
        }
        if start.elapsed() >= allowance {
            return (None, None);
        }
        std::thread::sleep(POLL_INTERVAL.min(allowance.saturating_sub(start.elapsed())));
    }
}

fn request_termination(child: &mut Child) -> io::Result<()> {
    #[cfg(unix)]
    {
        // WNOWAIT verifies that this remains our unreaped child before using
        // its numeric process-group identity. Preserve that identity until the
        // group signal has been requested; never kill a re-used, reaped PID.
        let _ = child_has_exited(child)?;
        let group = signal_group(child.id());
        let direct = child.kill();
        group.and(direct)
    }
    #[cfg(not(unix))]
    child.kill()
}

#[cfg(unix)]
fn signal_group(pid: u32) -> io::Result<()> {
    if pid <= 1 || pid > i32::MAX as u32 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "invalid child process-group ID",
        ));
    }
    // SAFETY: callers retain exclusive ownership of the unreaped child and
    // created its group with process_group(0). The guard excludes 0 and -1.
    if unsafe { libc::kill(-(pid as i32), libc::SIGKILL) } == 0 {
        Ok(())
    } else {
        let error = io::Error::last_os_error();
        if error.raw_os_error() == Some(libc::ESRCH) {
            Ok(())
        } else {
            Err(error)
        }
    }
}

#[cfg(unix)]
fn child_has_exited(child: &mut Child) -> io::Result<bool> {
    // SAFETY: siginfo_t is an OS integer/pointer record; zero initialization
    // also handles platforms that leave it unchanged on WNOHANG/no status.
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    // SAFETY: valid output storage; select only this exclusively owned child.
    // WNOWAIT leaves the PID reserved until cleanup and the final try_wait.
    let result = unsafe {
        libc::waitid(
            libc::P_PID,
            child.id() as libc::id_t,
            &mut info,
            libc::WEXITED | libc::WNOHANG | libc::WNOWAIT,
        )
    };
    if result != 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: waitid populated the SIGCHLD view or left its zero sentinel.
    Ok(unsafe { info.si_pid() } != 0)
}

#[cfg(not(unix))]
fn child_has_exited(child: &mut Child) -> io::Result<bool> {
    // Windows Child caches the exit and retains its OS process handle. Unlike
    // Unix group signaling, later direct-child kill cannot target a reused PID.
    child.try_wait().map(|status| status.is_some())
}

struct OwnedChild {
    child: Child,
    disarmed: bool,
}

impl OwnedChild {
    fn stop(&mut self) -> Termination {
        self.disarmed = true;
        terminate(&mut self.child)
    }

    fn error(&mut self, operation: &'static str, source: io::Error) -> RunError {
        RunError::Io {
            operation,
            source,
            cleanup: Some(self.stop()),
        }
    }

    /// The deadline `limit` expired: measure the CPU time the child's process
    /// group consumed under it, THEN stop the child (after the kill there is
    /// no group left to measure). `since` is the group's CPU time when the
    /// deadline's window began (`Duration::ZERO` for a child spawned under
    /// it); `None` leaves the expiry unmeasured. A total below `since` is not
    /// a measurement either.
    fn expire(&mut self, limit: Duration, since: Option<Duration>) -> RunError {
        let cpu = since
            .and_then(|since| group_cpu::process_group_cpu(self.child.id())?.checked_sub(since));
        RunError::Timeout(Expired {
            expiry: DeadlineExpiry { limit, cpu },
            cleanup: self.stop(),
        })
    }
}

impl Drop for OwnedChild {
    fn drop(&mut self) {
        if !self.disarmed {
            let _ = self.stop();
        }
    }
}

trait ReadyRead: Read {
    fn configure(&self) -> io::Result<()>;
    fn read_ready(&mut self, buffer: &mut [u8]) -> io::Result<usize>;
}

// Only spawn-created child pipes participate in the platform implementation;
// in particular, do not accept arbitrary synchronous Windows file handles.
trait CapturedChildPipe: Read {}
impl CapturedChildPipe for std::process::ChildStdout {}
impl CapturedChildPipe for std::process::ChildStderr {}

#[cfg(unix)]
impl<T: CapturedChildPipe + std::os::fd::AsRawFd> ReadyRead for T {
    fn configure(&self) -> io::Result<()> {
        configure_nonblocking(self)
    }
    fn read_ready(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        self.read(buffer)
    }
}

#[cfg(unix)]
fn configure_nonblocking(pipe: &impl std::os::fd::AsRawFd) -> io::Result<()> {
    let fd = pipe.as_raw_fd();
    // SAFETY: the borrowed, privately owned pipe stays open throughout these
    // operations. Only this parent's pipe end has its status flags changed.
    let flags = unsafe { libc::fcntl(fd, libc::F_GETFL) };
    if flags < 0 {
        return Err(io::Error::last_os_error());
    }
    if unsafe { libc::fcntl(fd, libc::F_SETFL, flags | libc::O_NONBLOCK) } < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

#[cfg(windows)]
impl<T: CapturedChildPipe + std::os::windows::io::AsRawHandle> ReadyRead for T {
    fn configure(&self) -> io::Result<()> {
        Ok(())
    }

    fn read_ready(&mut self, buffer: &mut [u8]) -> io::Result<usize> {
        use std::ffi::c_void;
        #[link(name = "kernel32")]
        unsafe extern "system" {
            fn PeekNamedPipe(
                handle: *mut c_void,
                buffer: *mut c_void,
                size: u32,
                read: *mut u32,
                available: *mut u32,
                remaining: *mut u32,
            ) -> i32;
        }
        let mut available = 0;
        // SAFETY: this runner creates ChildStdout/ChildStderr with Stdio::piped,
        // whose parent handles are asynchronous in Rust 1.97.1's std (validated
        // there; Trust ships no Windows std, so this cfg(windows) arm is only
        // built by a stock toolchain and needs re-validation if one ships). It owns
        // the only reader; after peeking, read at most the available bytes.
        // Do not extend this to caller-provided synchronous/shared pipe handles.
        let ok = unsafe {
            PeekNamedPipe(
                self.as_raw_handle(),
                std::ptr::null_mut(),
                0,
                std::ptr::null_mut(),
                &mut available,
                std::ptr::null_mut(),
            )
        };
        if ok == 0 {
            let error = io::Error::last_os_error();
            return if matches!(error.raw_os_error(), Some(109 | 233)) {
                Ok(0)
            } else {
                Err(error)
            };
        }
        if available == 0 {
            return Err(io::ErrorKind::WouldBlock.into());
        }
        let count = buffer.len().min(available as usize);
        self.read(&mut buffer[..count])
    }
}

#[cfg(not(any(unix, windows)))]
impl<T: CapturedChildPipe> ReadyRead for T {
    fn configure(&self) -> io::Result<()> {
        Err(io::ErrorKind::Unsupported.into())
    }
    fn read_ready(&mut self, _buffer: &mut [u8]) -> io::Result<usize> {
        Err(io::ErrorKind::Unsupported.into())
    }
}

struct Capture<T> {
    reader: T,
    bytes: Vec<u8>,
    eof: bool,
}

impl<T: ReadyRead> Capture<T> {
    /// The underlying pipe, so the capture loop can wait for it to become
    /// readable instead of sleeping.
    fn reader(&self) -> &T {
        &self.reader
    }

    fn new(reader: T) -> io::Result<Self> {
        reader.configure()?;
        Ok(Self {
            reader,
            bytes: Vec::new(),
            eof: false,
        })
    }

    fn step(&mut self) -> io::Result<bool> {
        if self.eof {
            return Ok(false);
        }
        let mut buffer = [0; 16 * 1024];
        match self.reader.read_ready(&mut buffer) {
            Ok(0) => {
                self.eof = true;
                Ok(true)
            }
            Ok(count) => {
                let chunk = buffer.get(..count).ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidData, "pipe read exceeded its buffer")
                })?;
                self.bytes
                    .try_reserve(count)
                    .map_err(|error| io::Error::new(io::ErrorKind::OutOfMemory, error))?;
                self.bytes.extend_from_slice(chunk);
                Ok(true)
            }
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
}

/// A child that ran to completion under [`run_measured`].
#[derive(Debug)]
pub(crate) struct Completed {
    pub(crate) output: Output,
    /// Wall-clock time from the spawn to the observed exit.
    pub(crate) wall: Duration,
    /// CPU time (user + system) the child's process group consumed in that
    /// time, read at the exit while the exited leader is still unreaped (it is
    /// still listed in its group, and its record includes the children it
    /// reaped: AY's solving worker). `None` when it was not measured
    /// (`group_cpu::process_group_cpu`).
    pub(crate) cpu: Option<Duration>,
}

/// `None` explicitly disables the deadline; zero duration expires immediately.
/// Both output streams must reach EOF before a successful result is returned.
pub(crate) fn run(command: &mut Command, timeout: Option<Duration>) -> Result<Output, RunError> {
    run_measured(command, timeout).map(|completed| completed.output)
}

/// [`run`], also reporting the completed child's wall-clock and process-group
/// CPU time.
pub(crate) fn run_measured(
    command: &mut Command,
    timeout: Option<Duration>,
) -> Result<Completed, RunError> {
    command
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped());
    configure_process_group(command);
    let child = command.spawn().map_err(|source| RunError::Io {
        operation: "spawn",
        source,
        cleanup: None,
    })?;
    let spawned = Instant::now();
    let mut process = OwnedChild {
        child,
        disarmed: false,
    };
    let stdout = process
        .child
        .stdout
        .take()
        .ok_or_else(|| process.error("stdout setup", io::ErrorKind::BrokenPipe.into()))?;
    let stderr = process
        .child
        .stderr
        .take()
        .ok_or_else(|| process.error("stderr setup", io::ErrorKind::BrokenPipe.into()))?;
    let mut stdout =
        Capture::new(stdout).map_err(|error| process.error("stdout configuration", error))?;
    let mut stderr =
        Capture::new(stderr).map_err(|error| process.error("stderr configuration", error))?;
    let start = Instant::now();
    // Stall diagnostic — same rationale as the resident exchange's: a fresh solver
    // that neither writes nor exits for a minute is reported, not silently waited on.
    let mut last_progress = Instant::now();
    let mut last_report = Instant::now();
    loop {
        if let Some(limit) = timeout
            && start.elapsed() >= limit
        {
            // A one-shot child was spawned under this deadline: everything its
            // group consumed, it consumed under it.
            return Err(process.expire(limit, Some(Duration::ZERO)));
        }
        // One bounded read per stream keeps a noisy writer from starving its
        // peer or the deadline. A busy stream does not make us sleep afterward.
        let out_progress = stdout
            .step()
            .map_err(|error| process.error("stdout read", error))?;
        let err_progress = stderr
            .step()
            .map_err(|error| process.error("stderr read", error))?;
        if stdout.eof && stderr.eof {
            match child_has_exited(&mut process.child) {
                Ok(true) => {
                    // Output is complete and the direct child has exited.
                    // Measured before the group signal and the reap, while
                    // the exited leader is still listed in its group.
                    let wall = spawned.elapsed();
                    let cpu = group_cpu::process_group_cpu(process.child.id());
                    // Group cleanup is best effort (Darwin can deny a signal
                    // to a group containing only the exited leader); it is
                    // not authority to replace the child's observed status.
                    #[cfg(unix)]
                    let _ = signal_group(process.child.id());
                    if let Some(status) = process
                        .child
                        .try_wait()
                        .map_err(|error| process.error("completed child reap", error))?
                    {
                        process.disarmed = true;
                        return Ok(Completed {
                            output: Output {
                                status,
                                stdout: stdout.bytes,
                                stderr: stderr.bytes,
                            },
                            wall,
                            cpu,
                        });
                    }
                }
                Ok(false) => {}
                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                Err(error) => return Err(process.error("exit-status poll", error)),
            }
        }
        if out_progress || err_progress {
            last_progress = Instant::now();
        } else if last_progress.elapsed() >= Duration::from_secs(60)
            && last_report.elapsed() >= Duration::from_secs(60)
        {
            last_report = Instant::now();
            // Named by its program: a Clean proof check that runs past a
            // minute (OD-223) is not a stalled solver.
            eprintln!(
                "trust-cg-verify: verification subprocess `{}` STALLED for {}s (child pid {}, \
                 stdout eof: {}, stderr eof: {}, deadline: {}); the compile is waiting, not working",
                std::path::Path::new(command.get_program())
                    .file_name()
                    .unwrap_or(command.get_program())
                    .to_string_lossy(),
                start.elapsed().as_secs(),
                process.child.id(),
                stdout.eof,
                stderr.eof,
                if timeout.is_some() {
                    "set"
                } else {
                    "NONE (no timeout)"
                },
            );
        }
        if !out_progress && !err_progress {
            // Neither stream moved. Wait until one of them CAN move rather than
            // sleeping a fixed interval.
            //
            // This is the SECOND of two sleep-poll loops in this module, and it is
            // the one the FRESH-process solver path uses — `ay_bridge::
            // run_fresh_authority_query -> run_solver_command_with_authority ->
            // subprocess::run`. Measured 2026-09-14 on a live `library/core`
            // compile through trust-ir-cg, this call site held **1411 of 1413**
            // samples of the proof-verifier thread. Fixing only the resident-server
            // exchange in `interactive.rs` left this path exactly as slow, which is
            // why `core` still crawled after that change: the two loops look alike,
            // serve different solver lanes, and only one of them had been fixed.
            //
            // When BOTH streams are at EOF there is no fd left to wait on — the loop
            // is then only waiting for the direct child to be reapable, which has no
            // readiness primitive here — so that case keeps the short sleep.
            #[cfg(unix)]
            {
                use std::os::fd::AsRawFd;
                let read_fds = [
                    (!stdout.eof).then(|| stdout.reader().as_raw_fd()),
                    (!stderr.eof).then(|| stderr.reader().as_raw_fd()),
                ];
                if read_fds.iter().any(Option::is_some) {
                    let budget = timeout.map_or(READY_WAIT_CAP, |limit| {
                        READY_WAIT_CAP.min(limit.saturating_sub(start.elapsed()))
                    });
                    wait_for_readable(read_fds[0], read_fds[1], budget);
                    continue;
                }
            }
            let delay = timeout.map_or(POLL_INTERVAL, |limit| {
                POLL_INTERVAL.min(limit.saturating_sub(start.elapsed()))
            });
            std::thread::sleep(delay);
        }
    }
}

/// Upper bound on one readiness wait. Not a latency floor — `poll` returns the
/// instant the peer writes — only a cap so the loop keeps re-checking the deadline
/// and the child's liveness even if a wakeup is ever missed.
const READY_WAIT_CAP: Duration = Duration::from_millis(100);

/// Block until one of the given fds is readable, the budget elapses, or a signal
/// arrives. See the call site for the measurement that motivated it.
#[cfg(unix)]
fn wait_for_readable(
    first: Option<std::os::fd::RawFd>,
    second: Option<std::os::fd::RawFd>,
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
    for fd in [first, second].into_iter().flatten() {
        fds[count] = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        count += 1;
    }
    if count == 0 {
        std::thread::sleep(POLL_INTERVAL.min(budget));
        return;
    }
    let millis = budget.as_millis().min(i32::MAX as u128) as i32;
    // SAFETY: `fds[..count]` is initialised and borrowed for the call only; the
    // descriptors are owned by the caller's live `Capture`s. A `poll` failure
    // (`EINTR` included) is not an error here — the loop re-checks its own state
    // and the deadline on the next iteration either way.
    let _ = unsafe { libc::poll(fds.as_mut_ptr(), count as libc::nfds_t, millis.max(1)) };
}

#[cfg(test)]
#[path = "subprocess_tests.rs"]
mod tests;
