// trust-cg-fuzz/src/sandbox.rs - Fork-based execution sandbox for JIT'd code.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Randomly generated trust_ir can compile to perfectly valid x86_64 that still
// executes a hardware-trapping instruction at run time: `idiv` raises #DE
// (delivered as SIGFPE) on divide-by-zero AND on INT_MIN / -1, a bad load
// raises SIGSEGV/SIGBUS, etc. These traps are NOT Rust panics, so
// `std::panic::catch_unwind` cannot stop them — they kill the whole process. A
// single such program would otherwise abort the entire fuzz campaign before any
// JSON summary is written.
//
// To survive them we run each JIT-compiled function in a forked CHILD process.
// The JIT's executable buffer is plain mmap'd RX memory in the parent's address
// space; after `fork()` the child inherits it copy-on-write, so the same
// function pointer is callable in the child. The child runs the function,
// publishes its result into a MAP_SHARED scratch page, and `_exit(0)`s. A trap
// kills only the child; the parent observes the child's wait status and decodes
// it: clean exit with a published result => Value; killed by a signal => Trapped
// (a genuine hardware trap); over the per-invoke deadline => Timeout.
//
// SOUNDNESS: this only changes how a JIT result is *obtained*, never how results
// are *compared*. A trap is reported faithfully as `Trapped(signal)` so the diff
// logic can distinguish "JIT trapped" from "JIT produced value V"; it is the
// caller's classification rules (jit_diff::classify_*) that decide a verdict,
// and they treat a trap as OK only when the oracle also lacked a defined value.

#![cfg(unix)]

use std::time::{Duration, Instant};

/// Result of running a sandboxed JIT call in a forked child.
#[derive(Debug, Clone)]
pub enum SandboxResult<T> {
    /// Child exited cleanly and published a value.
    Value(T),
    /// Child was killed by a hardware trap / signal (SIGFPE, SIGSEGV, ...).
    /// Carries the terminating signal number for diagnostics.
    Trapped(i32),
    /// Child did not finish within the per-invoke deadline (infinite loop).
    Timeout,
    /// The sandbox machinery itself failed (fork/mmap error, or the child
    /// exited abnormally without trapping or publishing). Treated by callers as
    /// a harness-level error, not a codegen defect.
    SandboxError(String),
}

/// How long to sleep between `waitpid(WNOHANG)` checks once the initial spin
/// window is exhausted (i.e. for slow / looping children). Coarse enough to not
/// busy-burn the parent, fine enough to bound timeout-kill latency.
const POLL_INTERVAL: Duration = Duration::from_micros(500);

/// Non-blocking reap attempts to spin before falling back to sleeping. Tuned so
/// the overwhelmingly common case (a non-looping JIT'd program that finishes in
/// microseconds) is reaped without ever sleeping.
const SPIN_LIMIT: u32 = 20_000;

/// A MAP_SHARED scratch page the child uses to publish its result to the parent.
///
/// Layout (offsets into the shared page):
///   [0]        published flag (0 = not yet, 1 = published)
///   [8..16]    i64 scalar return value (native-endian)
///   [16..]     optional opaque payload bytes (e.g. consumer status buffer)
///
/// The flag lets the parent distinguish "child finished the call and wrote a
/// result then exited" from "child exited(0) for some other reason" — only a set
/// flag is trusted as a real Value.
struct SharedPage {
    ptr: *mut u8,
    len: usize,
}

impl SharedPage {
    fn new(payload_len: usize) -> Result<Self, String> {
        let len = payload_len
            .checked_add(16)
            .filter(|len| *len <= isize::MAX as usize)
            .ok_or_else(|| {
                "sandbox payload length exceeds the addressable allocation size".to_string()
            })?;
        // SAFETY: standard anonymous shared mapping; ptr validity checked below.
        let ptr = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                len,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED | libc::MAP_ANONYMOUS,
                -1,
                0,
            )
        };
        if ptr == libc::MAP_FAILED {
            return Err("mmap MAP_SHARED failed".to_string());
        }
        let ptr = ptr as *mut u8;
        // Zero the header so the published flag starts at 0.
        // SAFETY: ptr owns `len` writable bytes.
        unsafe {
            std::ptr::write_bytes(ptr, 0, len);
        }
        Ok(SharedPage { ptr, len })
    }

    #[inline]
    fn published(&self) -> bool {
        // SAFETY: offset 0 is in-bounds; volatile read sees the child's write
        // (MAP_SHARED memory is coherent across the fork).
        unsafe { std::ptr::read_volatile(self.ptr) == 1 }
    }

    #[inline]
    fn read_i64(&self) -> i64 {
        let mut bytes = [0u8; 8];
        // SAFETY: bytes [8..16) are in-bounds for `len >= 16`.
        unsafe {
            std::ptr::copy_nonoverlapping(self.ptr.add(8), bytes.as_mut_ptr(), 8);
        }
        i64::from_ne_bytes(bytes)
    }

    #[inline]
    fn read_payload(&self, out: &mut [u8]) {
        let n = out.len().min(self.len.saturating_sub(16));
        if n == 0 {
            return;
        }
        // SAFETY: bytes [16..16+n) are in-bounds.
        unsafe {
            std::ptr::copy_nonoverlapping(self.ptr.add(16), out.as_mut_ptr(), n);
        }
    }

    /// Child-side: publish the scalar result then mark the page published.
    /// MUST be async-signal-safe (only raw memory writes); runs post-fork.
    ///
    /// # Safety
    /// Caller must be the forked child, before `_exit`. `payload` length must not
    /// exceed the page's payload capacity.
    #[inline]
    unsafe fn publish(&self, ret: i64, payload: &[u8]) {
        let bytes = ret.to_ne_bytes();
        let cap = self.len.saturating_sub(16);
        let n = payload.len().min(cap);
        // SAFETY: header byte and [8..16) / [16..16+n) are all in-bounds for
        // `len >= 16 + cap`; the page is MAP_SHARED so writes reach the parent.
        unsafe {
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), self.ptr.add(8), 8);
            if n > 0 {
                std::ptr::copy_nonoverlapping(payload.as_ptr(), self.ptr.add(16), n);
            }
            // Publish flag LAST so a reader that sees flag==1 also sees the result.
            std::ptr::write_volatile(self.ptr, 1u8);
        }
    }
}

impl Drop for SharedPage {
    fn drop(&mut self) {
        // SAFETY: ptr/len came from our own mmap.
        unsafe {
            libc::munmap(self.ptr as *mut libc::c_void, self.len);
        }
    }
}

/// Run `call` (which performs the actual JIT invocation) inside a forked child,
/// enforcing `deadline`.
///
/// `call` receives a `&mut [u8]` payload scratch of length `payload_len` (the
/// max opaque bytes published alongside the scalar return; 0 for plain scalar
/// shapes) and returns the scalar `i64`. It runs in the CHILD only and MUST be
/// async-signal-safe: no heap allocation, no locks, no Rust unwinding across the
/// call boundary. In practice it transmutes a function pointer, calls extern "C"
/// machine code, and writes a few bytes into the (pre-allocated) scratch — all
/// safe post-fork. The scratch buffer is allocated in the PARENT before the fork
/// so the child never touches the allocator.
///
/// # Safety
/// The caller guarantees the function pointer captured by `call` refers to live
/// executable memory (the JIT buffer) that remains mapped for the duration of
/// the child, and that `call` itself is async-signal-safe.
pub unsafe fn run_sandboxed<F>(
    payload_len: usize,
    deadline: Duration,
    call: F,
) -> SandboxResult<(i64, Vec<u8>)>
where
    F: FnOnce(&mut [u8]) -> i64,
{
    let page = match SharedPage::new(payload_len) {
        Ok(p) => p,
        Err(e) => return SandboxResult::SandboxError(e),
    };
    // Pre-allocate the child's payload scratch in the PARENT, before fork, so the
    // child writes into already-mapped memory and never calls the allocator.
    let mut scratch = vec![0u8; payload_len];

    // SAFETY: `fork` splits the process; the child path below is async-signal-
    // safe (extern "C" call + raw byte copies + `_exit`), and the parent only
    // calls `waitpid`/`kill` on its own child pid `pid`.
    let pid = unsafe { libc::fork() };
    if pid < 0 {
        return SandboxResult::SandboxError("fork failed".to_string());
    }

    if pid == 0 {
        // ---- CHILD ----
        // Async-signal-safe region only. If the JIT'd code traps, this process
        // dies here with a signal and never reaches `_exit`, leaving the
        // published flag clear.
        let ret = call(&mut scratch);
        // SAFETY: we are the child, pre-_exit; scratch fits the page capacity.
        unsafe {
            page.publish(ret, &scratch);
            // Bypass at-exit handlers / destructors: go straight to the kernel.
            libc::_exit(0);
        }
    }

    // ---- PARENT ----
    let start = Instant::now();
    let mut status: libc::c_int = 0;
    // Most JIT'd programs finish in microseconds. Spin a short, bounded window
    // of non-blocking reaps first (no sleep floor on the hot path), then fall
    // back to a sleep-poll loop bounded by `deadline` for slow / looping ones.
    let mut spins: u32 = 0;
    loop {
        // SAFETY: pid is our child; status is a valid out-param.
        let w = unsafe { libc::waitpid(pid, &mut status, libc::WNOHANG) };
        if w == pid {
            return decode_status(&page, status);
        }
        if w < 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() != std::io::ErrorKind::Interrupted {
                return SandboxResult::SandboxError(format!("waitpid failed: {error}"));
            }
            // EINTR says nothing about child completion. Keep the next wait
            // nonblocking and check the deadline below; a blocking retry here
            // would let a runaway child evade its watchdog after a signal.
        }
        if start.elapsed() >= deadline {
            // Over the per-invoke budget: kill and reap the child.
            // SAFETY: `pid` is our own child process.
            unsafe {
                libc::kill(pid, libc::SIGKILL);
            }
            if let Err(error) = reap_child(pid, &mut status) {
                return SandboxResult::SandboxError(format!(
                    "failed to reap timed-out child: {error}"
                ));
            }
            return SandboxResult::Timeout;
        }
        if spins < SPIN_LIMIT {
            spins += 1;
            std::hint::spin_loop();
        } else {
            std::thread::sleep(POLL_INTERVAL);
        }
    }
}

/// Blocking waits are only used after SIGKILL. Retry interrupted reaps so a
/// signal cannot leave the terminated child as a zombie.
fn reap_child(pid: libc::pid_t, status: &mut libc::c_int) -> std::io::Result<()> {
    loop {
        // SAFETY: pid identifies our child and status is a valid out-parameter.
        let result = unsafe { libc::waitpid(pid, status, 0) };
        if result == pid {
            return Ok(());
        }
        let error = std::io::Error::last_os_error();
        if error.kind() != std::io::ErrorKind::Interrupted {
            return Err(error);
        }
    }
}

fn decode_status(page: &SharedPage, status: libc::c_int) -> SandboxResult<(i64, Vec<u8>)> {
    if libc::WIFSIGNALED(status) {
        // Killed by a hardware trap (SIGFPE/SIGSEGV/SIGBUS/SIGILL) or SIGKILL.
        return SandboxResult::Trapped(libc::WTERMSIG(status));
    }
    if libc::WIFEXITED(status) {
        let code = libc::WEXITSTATUS(status);
        if code == 0 && page.published() {
            let ret = page.read_i64();
            let payload_len = page.len.saturating_sub(16);
            let mut payload = vec![0u8; payload_len];
            page.read_payload(&mut payload);
            return SandboxResult::Value((ret, payload));
        }
        // Exited cleanly but never published a result: anomalous (should not
        // happen for our child code). Treat as a sandbox error, not a defect.
        return SandboxResult::SandboxError(format!(
            "child exited code={} without publishing result",
            code
        ));
    }
    SandboxResult::SandboxError("child stopped/continued unexpectedly".to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sandbox_rejects_unrepresentable_payload_lengths() {
        for length in [usize::MAX, isize::MAX as usize] {
            // SAFETY: the closure is async-signal-safe; these invalid sizes
            // must be rejected before allocation or fork.
            let result = unsafe { run_sandboxed(length, Duration::ZERO, |_| 0) };
            assert!(
                matches!(result, SandboxResult::SandboxError(error) if error.contains("payload length"))
            );
        }
    }

    #[test]
    fn sandbox_returns_clean_value_and_payload() {
        // SAFETY: closure does only arithmetic + a byte write; no FFI fn ptr.
        let r = unsafe {
            run_sandboxed(4, Duration::from_secs(5), |payload: &mut [u8]| {
                payload.copy_from_slice(&[1, 2, 3, 4]);
                0x1234_5678_9abc_def0u64 as i64
            })
        };
        match r {
            SandboxResult::Value((v, p)) => {
                assert_eq!(v, 0x1234_5678_9abc_def0u64 as i64);
                assert_eq!(p, vec![1u8, 2, 3, 4]);
            }
            other => panic!("expected Value, got {:?}", other),
        }
    }

    #[test]
    fn sandbox_reports_signal_death_as_trapped() {
        // `decode_status` maps any signal death to `Trapped(WTERMSIG)`, and a
        // raise() is a software signal, not an idiv #DE, so a core-dump signal
        // proves nothing more here, while on macOS it made ReportCrash write a
        // report on every run. SIGTERM also differs from the SIGKILL the
        // timeout path sends, which reports `Timeout` anyway.
        const CHILD_SIG: libc::c_int = libc::SIGTERM;
        let r = unsafe {
            run_sandboxed(0, Duration::from_secs(5), |_p: &mut [u8]| {
                libc::raise(CHILD_SIG);
                0
            })
        };
        match r {
            SandboxResult::Trapped(sig) => assert_eq!(sig, CHILD_SIG),
            other => panic!("expected Trapped(SIGTERM), got {:?}", other),
        }
    }

    #[test]
    fn sandbox_kills_and_reports_timeout_on_runaway_child() {
        // Child spins past the deadline; parent must SIGKILL it and report
        // Timeout rather than hang.
        let r = unsafe {
            run_sandboxed(0, Duration::from_millis(150), |_p: &mut [u8]| {
                // Busy-loop well past the deadline (the kill ends it early).
                let start = Instant::now();
                while start.elapsed() < Duration::from_secs(30) {
                    std::hint::spin_loop();
                }
                0
            })
        };
        assert!(matches!(r, SandboxResult::Timeout), "got {:?}", r);
    }
}
