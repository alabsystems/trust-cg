// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

/// Existing MIR compilation fixtures use an eight-minute diagnostic deadline.
pub fn run_with_watchdog<T: Send + 'static>(
    what: &str,
    f: impl FnOnce() -> T + Send + 'static,
) -> T {
    run_with_timeout(what, Duration::from_secs(480), f)
}

/// Bound the caller's wait and preserve the worker's original panic payload.
///
/// This cannot cancel a Rust thread. A real timeout leaves the worker running;
/// the enclosing test process still needs process-level supervision. Catching
/// unwind only transports the failure to the caller, never resumes computation
/// with potentially poisoned worker state. Aborting panics remain process-fatal.
pub fn run_with_timeout<T: Send + 'static>(
    what: &str,
    timeout: Duration,
    f: impl FnOnce() -> T + Send + 'static,
) -> T {
    let (tx, rx) = mpsc::channel();
    std::thread::spawn(move || {
        let _ = tx.send(catch_unwind(AssertUnwindSafe(f)));
    });
    match rx.recv_timeout(timeout) {
        Ok(Ok(value)) => value,
        Ok(Err(panic)) => resume_unwind(panic),
        Err(RecvTimeoutError::Timeout) => {
            panic!(
                "WATCHDOG: `{what}` did not complete within {timeout:?}; worker is not cancelled"
            )
        }
        Err(RecvTimeoutError::Disconnected) => {
            panic!("WATCHDOG: `{what}` worker disconnected without returning an outcome")
        }
    }
}
