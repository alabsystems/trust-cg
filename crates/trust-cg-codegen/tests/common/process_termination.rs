//! Nonblocking termination of test children launched in their own process group.

use std::io;
use std::process::{Child, ExitStatus};

#[cfg(unix)]
unsafe extern "C" {
    fn kill(pid: i32, sig: i32) -> i32;
}

/// SIGKILL one owned process group using the syscall, never an external `kill`
/// command whose option parsing can reinterpret a negative process-group ID.
/// IDs 0 and 1, and values outside the signed PID range, must never be signaled.
#[cfg(unix)]
pub fn kill_process_group(pgid: u32) {
    if pgid > 1 && pgid <= i32::MAX as u32 {
        let pgid = pgid as i32;
        // SAFETY: `kill(2)` with a negative pid signals a process group; the
        // guard above excludes -1 (all processes) and 0 (caller's own group).
        unsafe {
            let _ = kill(-pgid, 9);
        }
    }
}

/// Minimal process boundary, also used to model delayed or failed termination.
pub trait TimeoutProcess {
    fn request_kill(&mut self) -> io::Result<()>;
    fn try_wait(&mut self) -> io::Result<Option<ExitStatus>>;
}

impl TimeoutProcess for Child {
    fn request_kill(&mut self) -> io::Result<()> {
        // Callers must have set process_group(0) before spawning this child.
        #[cfg(unix)]
        kill_process_group(self.id());
        self.kill()
    }

    fn try_wait(&mut self) -> io::Result<Option<ExitStatus>> {
        Child::try_wait(self)
    }
}

/// Observations after requesting termination; a signal is not an exit status.
pub struct Termination {
    pub status: Option<ExitStatus>,
    pub kill_error: Option<io::Error>,
    pub poll_error: Option<io::Error>,
}

impl Termination {
    pub fn diagnostic(&self) -> String {
        let mut message = match self.status {
            Some(status) => format!("termination requested; observed child status: {status}"),
            None => "termination requested; child exit not confirmed".into(),
        };
        if let Some(error) = &self.kill_error {
            message.push_str(&format!("; direct-child kill: {error}"));
        }
        if let Some(error) = &self.poll_error {
            message.push_str(&format!("; exit-status poll: {error}"));
        }
        message
    }
}

/// Request termination, then poll once. Never wait for signal delivery/reaping.
///
/// A child blocked in the kernel may survive SIGKILL until its kernel wait
/// completes. Returning None does not assert that it or its descendants exited;
/// the enclosing process supervisor remains responsible for host cleanup.
pub fn terminate(child: &mut impl TimeoutProcess) -> Termination {
    let kill_error = child.request_kill().err();
    let (status, poll_error) = match child.try_wait() {
        Ok(status) => (status, None),
        Err(error) => (None, Some(error)),
    };
    Termination {
        status,
        kill_error,
        poll_error,
    }
}
