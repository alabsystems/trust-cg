// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! Per-thread platform precondition for the interval using a separate SP.
//!
//! A source frame bound says nothing about an ordinary signal handler's stack
//! use. This guard blocks every maskable Darwin signal and checks the actual
//! readback before the adapter runs. The exact prior mask is restored only on
//! the host stack. It does not make a signal-safe arbitrary native-call API:
//! consumers still require the closed, syscall/callback-free, normally returning
//! source/byte domain. Unmaskable process stop/termination, synchronous platform
//! faults and Mach exception machinery remain platform TCB, not proved memory
//! permission or recovery behavior. No extra stack slack discharges this guard.

use super::EntryStackError;
use std::marker::PhantomData;
use std::rc::Rc;

type Result<T> = std::result::Result<T, EntryStackError>;

// Darwin sys/signal.h: NSIG=32, signals 1..31, SIGUSR2=31. libc's
// target-selected declaration supplies sigset_t and the native calls. Refuse
// unsupported ABI drift instead of truncating or guessing the signal domain.
const _: () = assert!(std::mem::size_of::<libc::sigset_t>() == 4 && libc::SIGUSR2 == 31);

fn refusal(operation: &str, code: i32) -> EntryStackError {
    EntryStackError::SignalContract(format!("{operation} failed ({code})"))
}

fn read_mask() -> Result<libc::sigset_t> {
    let mut mask = 0;
    // SAFETY: null set requests only a readback for this thread; mask points
    // to the correctly sized live target-selected sigset_t object.
    let code = unsafe { libc::pthread_sigmask(libc::SIG_SETMASK, std::ptr::null(), &mut mask) };
    if code != 0 {
        return Err(refusal("signal-mask readback", code));
    }
    Ok(mask)
}

fn membership(mask: &libc::sigset_t, signal: i32) -> Result<i32> {
    // SAFETY: mask is live; signal is inside the complete target domain.
    let bit = unsafe { libc::sigismember(mask, signal) };
    if !matches!(bit, 0 | 1) {
        return Err(refusal("signal membership", bit));
    }
    Ok(bit)
}

fn check_blocked(mask: &libc::sigset_t) -> Result<()> {
    for signal in 1..=libc::SIGUSR2 {
        if signal != libc::SIGKILL && signal != libc::SIGSTOP && membership(mask, signal)? != 1 {
            return Err(EntryStackError::SignalContract(format!(
                "maskable signal {signal} is unblocked"
            )));
        }
    }
    Ok(())
}

fn check_same(expected: &libc::sigset_t, actual: &libc::sigset_t) -> Result<()> {
    for signal in 1..=libc::SIGUSR2 {
        if membership(expected, signal)? != membership(actual, signal)? {
            return Err(EntryStackError::SignalContract(format!(
                "restored signal {signal} differs from the prior mask"
            )));
        }
    }
    Ok(())
}

/// Thread-bound guard; this value cannot transfer a mask restore to another
/// thread. Its private construction checks the current OS-reported mask.
pub(super) struct BlockedSignals {
    previous: libc::sigset_t,
    active: bool,
    not_send: PhantomData<Rc<()>>,
}

impl BlockedSignals {
    pub(super) fn enter() -> Result<Self> {
        let mut full = 0;
        // SAFETY: full is a live target-selected signal-set object.
        if unsafe { libc::sigfillset(&mut full) } != 0 {
            return Err(refusal("full signal set", -1));
        }
        let mut previous = 0;
        // SAFETY: both sets are live target-selected objects. This changes only
        // the current thread and atomically retains its actual previous mask.
        let code = unsafe { libc::pthread_sigmask(libc::SIG_SETMASK, &full, &mut previous) };
        if code != 0 {
            return Err(refusal("block signals", code));
        }
        let owner = Self {
            previous,
            active: true,
            not_send: PhantomData,
        };
        // On every failure Drop restores the prior mask on the host stack.
        check_blocked(&read_mask()?)?;
        Ok(owner)
    }

    /// Called only after the fixed adapter has restored the actual host SP.
    pub(super) fn restore(mut self) -> Result<()> {
        // SAFETY: previous is this thread's actual captured native mask; this
        // !Send owner remains on its originating thread and on the host stack.
        let code = unsafe {
            libc::pthread_sigmask(libc::SIG_SETMASK, &self.previous, std::ptr::null_mut())
        };
        if code != 0 {
            return Err(refusal("restore signal mask", code));
        }
        self.active = false;
        check_same(&self.previous, &read_mask()?)
    }
}

impl Drop for BlockedSignals {
    fn drop(&mut self) {
        if self.active {
            // SAFETY: scope exit/error remains on the host stack and originating
            // thread. Best-effort error cleanup cannot license an invocation.
            let _ = unsafe {
                libc::pthread_sigmask(libc::SIG_SETMASK, &self.previous, std::ptr::null_mut())
            };
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_mask_blocks_every_maskable_handler_and_restores_the_previous_mask() {
        let before = read_mask().unwrap();
        let owner = BlockedSignals::enter().unwrap();
        check_blocked(&read_mask().unwrap()).unwrap();
        owner.restore().unwrap();
        check_same(&before, &read_mask().unwrap()).unwrap();
    }

    #[test]
    fn absent_handler_blocking_and_altered_restore_state_are_refused() {
        let mut empty = 0;
        // SAFETY: empty is a correctly sized live native signal set.
        assert_eq!(unsafe { libc::sigemptyset(&mut empty) }, 0);
        assert!(check_blocked(&empty).is_err());
        let mut changed = empty;
        // SAFETY: SIGUSR1 is within the supported Darwin signal domain.
        assert_eq!(unsafe { libc::sigaddset(&mut changed, libc::SIGUSR1) }, 0);
        assert!(check_same(&empty, &changed).is_err());
    }
}
