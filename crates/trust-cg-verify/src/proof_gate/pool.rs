// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Admission-bounded scheduling, independent of proof verdicts.

use std::sync::{
    Mutex, OnceLock,
    atomic::{AtomicUsize, Ordering},
};
use std::time::{Duration, Instant};
thread_local! { static ACTIVE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
struct Restore(bool);
impl Drop for Restore {
    fn drop(&mut self) {
        ACTIVE.with(|active| active.set(self.0));
    }
}

pub(super) struct Failure<R> {
    pub results: Option<Vec<R>>,
    pub detail: std::borrow::Cow<'static, str>,
}

/// Refuse inherited executor state before any process-global mutex or solver probe.
pub(super) fn check_process() -> Result<(), std::borrow::Cow<'static, str>> {
    if crate::resource_limits::proof_verifier_process_owned() {
        Ok(())
    } else {
        Err("inherited proof-gate executor admission refused".into())
    }
}

pub(super) fn validate_policy() -> Result<(), std::borrow::Cow<'static, str>> {
    check_process()?;
    crate::resource_limits::try_proof_verifier_worker_limit()
        .map(|_| ())
        .map_err(|error| error.to_string().into())
}

/// One discharge admission, using the existing memory-admitted large-stack pool.
/// Every loop installs the caller's complete authority/environment snapshot.
pub(super) fn ordered<R: Send + Sync>(
    rows: usize,
    workers: usize,
    operation: impl Fn(usize) -> R + Sync,
    refused: impl Fn(usize, Duration) -> R + Sync,
) -> Result<Vec<R>, Failure<R>> {
    let failure = |detail: std::borrow::Cow<'static, str>| Failure {
        results: None,
        detail,
    };
    check_process().map_err(failure)?;
    if ACTIVE.with(std::cell::Cell::get) {
        return Err(failure("reentrant proof worker admission refused".into()));
    }
    crate::resource_limits::try_proof_verifier_worker_limit()
        .map_err(|error| failure(error.to_string().into()))?;
    let pool = crate::resource_limits::proof_verifier_pool()
        .ok_or_else(|| failure("proof verifier pool construction refused".into()))?;
    static ADMISSION: Mutex<()> = Mutex::new(());
    // A shared worker must never block while another gate needs that pool.
    let guard = if rayon::current_thread_index().is_some() {
        ADMISSION.try_lock().map_err(|_| {
            failure("busy or poisoned proof gate admission refused on Rayon worker".into())
        })?
    } else {
        ADMISSION
            .lock()
            .map_err(|_| failure("poisoned proof gate admission refused".into()))?
    };
    let environment = trust_cg_process_env::EnvOverrideSnapshot::capture_current_thread();
    let mut slots = Vec::new();
    slots
        .try_reserve_exact(rows)
        .map_err(|_| failure("proof worker result allocation refused".into()))?;
    slots.resize_with(rows, OnceLock::new);
    let next = AtomicUsize::new(0);
    let workers = workers
        .clamp(1, crate::ay_bridge::MAX_PROOF_GATE_WORKERS)
        .min(pool.current_num_threads())
        .min(rows.max(1));
    let work = |lane| {
        environment.run(|| {
            crate::ay_bridge::with_proof_gate_lane(lane, || {
                let _restore = Restore(ACTIVE.with(|active| active.replace(true)));
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    if index >= rows {
                        break;
                    }
                    let started = Instant::now();
                    let result =
                        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| operation(index)))
                            .unwrap_or_else(|_| refused(index, started.elapsed()));
                    let _ = slots[index].set(result);
                }
            })
        })
    };
    let infrastructure_failed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        pool.scope(|scope| {
            for lane in 0..workers {
                let work = &work;
                scope.spawn(move |_| work(lane));
            }
        });
    }))
    .is_err();
    let mut failed = infrastructure_failed;
    let mut results = Vec::new();
    results
        .try_reserve_exact(rows)
        .map_err(|_| failure("proof worker report allocation refused".into()))?;
    for (index, slot) in slots.into_iter().enumerate() {
        results.push(slot.into_inner().unwrap_or_else(|| {
            failed = true;
            refused(index, Duration::ZERO)
        }));
    }
    drop(guard);
    if failed {
        Err(Failure {
            results: Some(results),
            detail: "proof worker infrastructure failed; gate certification refused".into(),
        })
    } else {
        Ok(results)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn concurrent_work_preserves_order_and_visits_every_row_once() {
        let width = crate::resource_limits::proof_verifier_pool()
            .unwrap()
            .current_num_threads()
            .min(3);
        let barrier = std::sync::Barrier::new(width);
        let active = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        let visits = (0..17).map(|_| AtomicUsize::new(0)).collect::<Vec<_>>();
        let results = ordered(
            17,
            3,
            |index| {
                visits[index].fetch_add(1, Ordering::SeqCst);
                let now = active.fetch_add(1, Ordering::SeqCst) + 1;
                peak.fetch_max(now, Ordering::SeqCst);
                if index < width {
                    barrier.wait();
                }
                active.fetch_sub(1, Ordering::SeqCst);
                index * 7
            },
            |_, _| usize::MAX,
        )
        .unwrap_or_else(|failure| panic!("{}", failure.detail));
        assert_eq!(results, (0..17).map(|i| i * 7).collect::<Vec<_>>());
        assert_eq!(peak.load(Ordering::SeqCst), width);
        eprintln!("ordered proof control observed {width} simultaneous workers");
        assert!(visits.iter().all(|v| v.load(Ordering::SeqCst) == 1));
    }

    #[test]
    fn panic_is_a_row_refusal_and_does_not_skip_later_obligations() {
        let result = ordered(
            9,
            3,
            |index| {
                if index == 2 {
                    panic!("deliberate verifier failure");
                }
                Some(index)
            },
            |_, _| None,
        )
        .unwrap_or_else(|failure| panic!("{}", failure.detail));
        assert_eq!(
            result,
            (0..9)
                .map(|i| if i == 2 { None } else { Some(i) })
                .collect::<Vec<_>>()
        );
    }
    #[test]
    fn recursive_admission_refuses_without_waiting_on_its_own_pool() {
        let outer = ordered(
            1,
            1,
            |_| {
                let inner = ordered(1, 1, |_| true, |_, _| false);
                matches!(inner, Err(Failure { results: None, .. }))
            },
            |_, _| false,
        )
        .unwrap_or_else(|failure| panic!("{}", failure.detail));
        assert_eq!(outer, [true]);
    }
    #[test]
    fn every_loop_keeps_scoped_checker_and_cache_controls() {
        trust_cg_process_env::with_env_overrides(
            &[
                ("TCG_EXTERNAL_CLEAN_CHECKER", "/explicit/missing/checker"),
                ("TCG_NO_PROOF_CACHE", "1"),
            ],
            || {
                let width = crate::resource_limits::proof_verifier_pool()
                    .unwrap()
                    .current_num_threads()
                    .min(3);
                let barrier = std::sync::Barrier::new(width);
                let rows = ordered(
                    width,
                    3,
                    |index| {
                        barrier.wait();
                        (
                            index,
                            crate::env_lock::var("TCG_EXTERNAL_CLEAN_CHECKER").ok(),
                            crate::env_lock::var("TCG_NO_PROOF_CACHE").ok(),
                        )
                    },
                    |index, _| (index, None, None),
                )
                .unwrap_or_else(|error| panic!("{}", error.detail));
                for (index, checker, cache) in rows {
                    assert!(index < 3);
                    assert_eq!(checker.as_deref(), Some("/explicit/missing/checker"));
                    assert_eq!(cache.as_deref(), Some("1"));
                }
            },
        );
    }
    #[cfg(unix)]
    #[test]
    fn fork_from_external_thread_refuses_inherited_live_admission() {
        use std::sync::{Arc, Barrier};
        let entered = Arc::new(Barrier::new(2));
        let release = Arc::new(Barrier::new(2));
        let worker_entered = Arc::clone(&entered);
        let worker_release = Arc::clone(&release);
        let owner = std::thread::spawn(move || {
            ordered(
                1,
                1,
                |_| {
                    worker_entered.wait();
                    worker_release.wait();
                    true
                },
                |_, _| false,
            )
            .unwrap_or_else(|error| panic!("{}", error.detail))
        });
        entered.wait();
        // Child performs only the inherited-admission refusal, then _exit;
        // no solver or shared executor is allowed to run there.
        let child = unsafe { libc::fork() };
        if child == 0 {
            let refused = matches!(
                ordered(1, 1, |_| true, |_, _| false),
                Err(Failure { results: None, .. })
            );
            unsafe {
                libc::_exit(if refused { 0 } else { 1 });
            }
        }
        let mut status = 0;
        let deadline = Instant::now() + Duration::from_secs(5);
        let mut reaped = false;
        if child > 0 {
            while Instant::now() < deadline {
                if unsafe { libc::waitpid(child, &mut status, libc::WNOHANG) } == child {
                    reaped = true;
                    break;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
            if !reaped {
                unsafe {
                    libc::kill(child, libc::SIGKILL);
                    libc::waitpid(child, &mut status, 0);
                }
            }
        }
        release.wait();
        assert_eq!(owner.join().unwrap(), [true]);
        assert!(
            child > 0 && reaped && libc::WIFEXITED(status) && libc::WEXITSTATUS(status) == 0,
            "forked child must refuse without waiting on the parent's admission"
        );
    }

    #[test]
    fn competing_shared_worker_never_blocks_an_active_gate() {
        let pool = crate::resource_limits::proof_verifier_pool().unwrap();
        if pool.current_num_threads() == 1 {
            let result = ordered(
                1,
                1,
                |_| ordered(1, 1, |_| true, |_, _| false).is_err(),
                |_, _| false,
            )
            .unwrap_or_else(|error| panic!("{}", error.detail));
            assert_eq!(result, [true]);
            return;
        }
        let entered = std::sync::Arc::new(std::sync::Barrier::new(2));
        let release = std::sync::Arc::new(std::sync::Barrier::new(2));
        let worker_entered = std::sync::Arc::clone(&entered);
        let worker_release = std::sync::Arc::clone(&release);
        let owner = std::thread::spawn(move || {
            ordered(
                1,
                1,
                |_| {
                    worker_entered.wait();
                    worker_release.wait();
                    true
                },
                |_, _| false,
            )
            .unwrap_or_else(|error| panic!("{}", error.detail))
        });
        entered.wait();
        let competitor = pool.install(|| ordered(1, 1, |_| true, |_, _| false));
        release.wait();
        assert_eq!(owner.join().unwrap(), [true]);
        assert!(matches!(competitor, Err(Failure { results: None, .. })));
    }
    #[test]
    fn foreign_rayon_worker_refuses_busy_admission_before_owner_release() {
        let entered = std::sync::Arc::new(std::sync::Barrier::new(2));
        let release = std::sync::Arc::new(std::sync::Barrier::new(2));
        let worker_entered = std::sync::Arc::clone(&entered);
        let worker_release = std::sync::Arc::clone(&release);
        let owner = std::thread::spawn(move || {
            ordered(
                1,
                1,
                |_| {
                    worker_entered.wait();
                    worker_release.wait();
                    true
                },
                |_, _| false,
            )
            .unwrap_or_else(|error| panic!("{}", error.detail))
        });
        entered.wait();
        let (send, receive) = std::sync::mpsc::channel();
        let competitor = std::thread::spawn(move || {
            // A foreign executor models an embedding's pool, not a second
            // production proof executor. No proof operation may run there.
            let foreign = rayon::ThreadPoolBuilder::new()
                .num_threads(1)
                .build()
                .unwrap();
            let result = foreign.install(|| ordered(1, 1, |_| true, |_, _| false));
            send.send(matches!(result, Err(Failure { results: None, .. })))
                .unwrap();
        });
        let refusal = receive.recv_timeout(Duration::from_secs(2));
        release.wait();
        assert_eq!(owner.join().unwrap(), [true]);
        competitor.join().unwrap();
        assert!(
            refusal.unwrap_or(false),
            "foreign Rayon admission must not wait for owner release"
        );
    }
}
