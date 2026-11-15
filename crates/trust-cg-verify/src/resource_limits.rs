// trust-cg-verify/resource_limits.rs - Verification worker resource policy
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared resource policy for recursive proof verification.
//!
//! Proof evaluation needs a substantially larger stack than an ordinary Rayon
//! worker. Keep every verification entry point on one process-wide pool so
//! function-level certificate fanout and x86 per-instruction fanout share the
//! same fixed set of large stacks instead of multiplying them.

use std::num::NonZeroUsize;
use std::sync::{Mutex, OnceLock};

use trust_cg_process_env::resource_budget::{
    ArtifactNeutralExecutorBudget, ArtifactNeutralExecutorDefaults, HostResourceSnapshot,
    ResourceBudgetError, capture_positive_usize_control,
};

/// Environment variable controlling Trust Codegen-owned parallelism.
pub use trust_cg_process_env::resource_budget::TRUST_CG_MAX_PARALLELISM_ENV;

/// Stack reserved for each proof-verifier worker.
///
/// Recursive SMT-expression evaluation can overflow Rust's ordinary worker
/// stack. This retains the established 32 MiB safety margin while bounding how
/// many such stacks exist at once.
pub use trust_cg_process_env::resource_budget::PROOF_VERIFIER_STACK_BYTES as PROOF_VERIFIER_STACK_SIZE;

/// Process-local default for the shared large-stack verifier pool.
///
/// Without an external Cargo job share, two workers reserve at most64MiB.
/// An admitted positive Cargo share guides only an unconfigured default.
/// Hosts that parallelize compiler processes (the rustc bridge) can install one
/// before capture. An explicit Trust cap selects width within the Cargo,
/// host and memory ceilings. The captured process budget never widens late.
const DEFAULT_PROOF_VERIFIER_WORKERS: usize = 2;

static EXECUTOR_PID: std::sync::atomic::AtomicU32 = std::sync::atomic::AtomicU32::new(0);

/// Check process ownership before touching inherited executor/policy locks.
pub(crate) fn proof_verifier_process_owned() -> bool {
    use std::sync::atomic::Ordering::SeqCst;
    let pid = std::process::id();
    match EXECUTOR_PID.compare_exchange(0, pid, SeqCst, SeqCst) {
        Ok(_) => true,
        Err(owner) => owner == pid,
    }
}

static DEFAULT_WORKER_LIMIT: OnceLock<usize> = OnceLock::new();
struct CapturedVerifierBudget {
    budget: ArtifactNeutralExecutorBudget,
    configured_cap: Option<NonZeroUsize>,
    default_limit: usize,
    cargo_share: Option<NonZeroUsize>,
}
static PROOF_VERIFIER_BUDGET: OnceLock<CapturedVerifierBudget> = OnceLock::new();

/// Cargo's external job share is a ceiling, including over scoped hints.
pub(crate) fn admitted_job_share() -> Result<Option<NonZeroUsize>, ResourceBudgetError> {
    const KEY: &str = "CARGO_BUILD_JOBS";
    let external = std::env::var_os(KEY)
        .map(|value| {
            let value = value
                .to_str()
                .ok_or(ResourceBudgetError::NonUnicode { key: KEY })?;
            trust_cg_process_env::resource_budget::parse_positive_usize_control(KEY, value)
        })
        .transpose()?;
    let scoped = capture_positive_usize_control(KEY)?;
    Ok(match (external, scoped) {
        (Some(external), Some(scoped)) => Some(external.min(scoped)),
        (Some(external), None) => Some(external),
        (None, scoped) => scoped,
    })
}

// Serialize default installation with the read-and-publication of its budget.
// A check of BUDGET followed by a separate DEFAULT.set would race first use.
static WORKER_POLICY_LOCK: Mutex<()> = Mutex::new(());
static PROOF_VERIFIER_POOL: OnceLock<Option<rayon::ThreadPool>> = OnceLock::new();
static SERIAL_FALLBACK_LOCK: Mutex<()> = Mutex::new(());

/// Override the process-local verifier worker default before first budget/pool
/// use.
///
/// This changes only the default. A positive `TRUST_CG_MAX_PARALLELISM` value
/// remains authoritative. Returns true for a first or identical installation,
/// false for a conflict, poisoned policy, or first installation after budget
/// capture. Equal explicit installations remain compatible after capture.
#[must_use]
pub fn configure_proof_verifier_default_worker_limit(worker_limit: usize) -> bool {
    if !proof_verifier_process_owned() {
        return false;
    }
    let Ok(_guard) = WORKER_POLICY_LOCK.lock() else {
        return false;
    };
    let requested = worker_limit.max(1);
    if let Some(installed) = DEFAULT_WORKER_LIMIT.get() {
        if *installed != requested {
            return false;
        }
        // A budget may predate the bridge's first cap installation. An equal
        // default alone does not make that earlier captured cap compatible.
        return PROOF_VERIFIER_BUDGET.get().is_none_or(|captured| {
            requested == captured.default_limit
                && capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV)
                    == Ok(captured.configured_cap)
                && admitted_job_share() == Ok(captured.cargo_share)
        });
    }
    if PROOF_VERIFIER_BUDGET.get().is_some() {
        return false;
    }
    DEFAULT_WORKER_LIMIT.set(requested).is_ok()
}

/// Resolve the worker limit used by the shared large-stack verifier pool.
#[must_use]
pub fn proof_verifier_worker_limit() -> usize {
    try_proof_verifier_worker_limit()
        .unwrap_or_else(|error| panic!("invalid Trust Codegen execution resource budget: {error}"))
}

/// Validate executor controls and admit the shared verifier budget without
/// unwinding. Successful admission fixes the process-wide pool size; rejected
/// controls are not cached and may be corrected by the caller.
pub fn try_proof_verifier_worker_limit() -> Result<usize, ResourceBudgetError> {
    if !proof_verifier_process_owned() {
        return Err(ResourceBudgetError::InheritedExecutorProcess {
            owner: EXECUTOR_PID.load(std::sync::atomic::Ordering::SeqCst),
            current: std::process::id(),
        });
    }
    let _guard =
        WORKER_POLICY_LOCK
            .lock()
            .map_err(|_| ResourceBudgetError::InstalledPolicyPoisoned {
                key: "proof-walk-workers",
            })?;
    if let Some(captured) = PROOF_VERIFIER_BUDGET.get() {
        let current_cap = capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV)?;
        let current_share = admitted_job_share()?;
        if current_cap != captured.configured_cap || current_share != captured.cargo_share {
            return Err(ResourceBudgetError::InstalledPolicyConflict {
                key: "proof-walk-workers",
            });
        }
        return Ok(captured.budget.large_stack_slots().get());
    }
    let host = HostResourceSnapshot::capture();
    let share = admitted_job_share()?;
    let default_limit = DEFAULT_WORKER_LIMIT
        .get()
        .copied()
        .unwrap_or_else(|| share.map_or(DEFAULT_PROOF_VERIFIER_WORKERS, NonZeroUsize::get));
    let budget = capture_verifier_budget(host, default_limit, share)?;
    Ok(PROOF_VERIFIER_BUDGET
        .get_or_init(|| budget)
        .budget
        .large_stack_slots()
        .get())
}

fn capture_verifier_budget(
    host: HostResourceSnapshot,
    default_limit: usize,
    share: Option<NonZeroUsize>,
) -> Result<CapturedVerifierBudget, ResourceBudgetError> {
    let defaults = ArtifactNeutralExecutorDefaults::new(
        share.map_or(host.available_parallelism(), |share| {
            share.min(host.available_parallelism())
        }),
        NonZeroUsize::new(default_limit).unwrap_or(NonZeroUsize::MIN),
        NonZeroUsize::MIN.saturating_add(PROOF_VERIFIER_STACK_SIZE - 1),
    );
    let captured_cap = capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV)?;
    // An explicit Trust cap still selects width, but cannot exceed the job's
    // external CPU admission. Host and memory ceilings remain authoritative.
    let selected_cap = captured_cap.map(|cap| share.map_or(cap, |share| cap.min(share)));
    let budget = ArtifactNeutralExecutorBudget::resolve(defaults, host, selected_cap)?;
    Ok(CapturedVerifierBudget {
        budget,
        configured_cap: captured_cap,
        default_limit,
        cargo_share: share,
    })
}

pub(crate) fn proof_verifier_pool() -> Option<&'static rayon::ThreadPool> {
    if !proof_verifier_process_owned() {
        return None;
    }
    let admitted = proof_verifier_worker_limit();
    PROOF_VERIFIER_POOL
        .get_or_init(|| {
            rayon::ThreadPoolBuilder::new()
                .num_threads(admitted)
                .stack_size(PROOF_VERIFIER_STACK_SIZE)
                .thread_name(|index| format!("trust-cg-proof-verifier-{index}"))
                .build()
                .ok()
        })
        .as_ref()
}

/// Return the shared verifier pool when it has enough workers for parallel
/// work. Callers retain their serial path when the configured limit is one or
/// pool construction failed.
pub(crate) fn proof_verifier_parallel_pool() -> Option<&'static rayon::ThreadPool> {
    let pool = proof_verifier_pool()?;
    (pool.current_num_threads() >= 2).then_some(pool)
}

/// Run recursive proof work on the shared large-stack verifier pool.
///
/// Concurrent function verification calls submit to this one pool, so at most
/// [`proof_verifier_worker_limit`] large-stack workers exist in the process.
/// Nested x86 pre-pass fanout uses the same pool and therefore cannot create a
/// second full-width set of 32 MiB stacks.
pub fn run_on_proof_verifier_stack<R, F>(name: &str, operation: F) -> R
where
    R: Send,
    F: FnOnce() -> R + Send,
{
    assert!(
        proof_verifier_process_owned(),
        "inherited proof executor refused"
    );
    // Safe compiler overrides are thread-local by design. Verification is one
    // logical continuation of the caller's compile, so transfer an owned
    // snapshot explicitly into whichever large-stack worker executes it.
    let environment = trust_cg_process_env::EnvOverrideSnapshot::capture_current_thread();
    let operation = move || environment.run(operation);
    if let Some(pool) = proof_verifier_pool() {
        return pool.install(operation);
    }

    // A pool allocation failure must not move recursive evaluation back onto a
    // small caller stack. Serialize the established scoped-thread fallback so
    // concurrent functions still cannot multiply 32 MiB stacks.
    let _fallback_guard = SERIAL_FALLBACK_LOCK
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner);
    std::thread::scope(|scope| {
        let handle = std::thread::Builder::new()
            .name(name.to_owned())
            .stack_size(PROOF_VERIFIER_STACK_SIZE)
            .spawn_scoped(scope, operation)
            .expect("failed to spawn proof verifier thread");
        match handle.join() {
            Ok(result) => result,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    })
}

/// Schedule process-lifetime cache warming on the shared verifier pool.
///
/// This is the non-blocking companion to [`run_on_proof_verifier_stack`]. It is
/// intended only for idempotent warm-up work whose result is published through
/// its own synchronization primitive. Normal verification should use the
/// blocking entry point so panics and results propagate to the caller. If the
/// bounded pool could not be created, optional warm-up is skipped rather than
/// allocating an untracked large-stack thread while the host is under pressure.
#[must_use]
pub fn spawn_on_proof_verifier_stack<F>(_name: &str, operation: F) -> bool
where
    F: FnOnce() + Send + 'static,
{
    if !proof_verifier_process_owned() {
        return false;
    }
    if try_proof_verifier_worker_limit().is_err() {
        return false;
    }
    let environment = trust_cg_process_env::EnvOverrideSnapshot::capture_current_thread();
    let operation = move || environment.run(operation);
    if let Some(pool) = proof_verifier_pool() {
        pool.spawn(operation);
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn worker_policy_startup_capture_and_poison_contract() {
        const CHILD: &str = "WORKER_POLICY_CONTRACT_CHILD";
        let Ok(mode) = std::env::var(CHILD) else {
            for mode in [
                "install_first",
                "capture_first",
                "retry",
                "race",
                "poison",
                "late_cap",
                "late_scope",
            ] {
                let output = std::process::Command::new(std::env::current_exe().unwrap())
                    .args([
                        "--exact",
                        "resource_limits::tests::worker_policy_startup_capture_and_poison_contract",
                        "--nocapture",
                        "--test-threads=1",
                    ])
                    .env(CHILD, mode)
                    .env_remove(TRUST_CG_MAX_PARALLELISM_ENV)
                    .output()
                    .unwrap();
                println!("{mode}: {}", String::from_utf8_lossy(&output.stdout));
                eprintln!("{}", String::from_utf8_lossy(&output.stderr));
                assert!(output.status.success(), "{mode}: {}", output.status);
            }
            return;
        };
        match mode.as_str() {
            "late_scope" => {
                let first = trust_cg_process_env::with_env_overrides(
                    &[(TRUST_CG_MAX_PARALLELISM_ENV, "6")],
                    || try_proof_verifier_worker_limit().unwrap(),
                );
                trust_cg_process_env::with_env_overrides(
                    &[(TRUST_CG_MAX_PARALLELISM_ENV, "6")],
                    || {
                        assert_eq!(try_proof_verifier_worker_limit(), Ok(first));
                    },
                );
                trust_cg_process_env::with_env_overrides(
                    &[(TRUST_CG_MAX_PARALLELISM_ENV, "1")],
                    || {
                        assert_eq!(
                            try_proof_verifier_worker_limit(),
                            Err(ResourceBudgetError::InstalledPolicyConflict {
                                key: "proof-walk-workers"
                            })
                        );
                    },
                );
                trust_cg_process_env::with_env_overrides(
                    &[(TRUST_CG_MAX_PARALLELISM_ENV, "0")],
                    || {
                        assert_eq!(
                            try_proof_verifier_worker_limit(),
                            Err(ResourceBudgetError::InvalidPositiveInteger {
                                key: TRUST_CG_MAX_PARALLELISM_ENV
                            })
                        );
                    },
                );
                #[cfg(unix)]
                trust_cg_process_env::with_env_edits(|editor| {
                    use std::os::unix::ffi::OsStringExt;
                    editor.set(
                        TRUST_CG_MAX_PARALLELISM_ENV,
                        std::ffi::OsString::from_vec(vec![0xff]),
                    );
                    assert_eq!(
                        try_proof_verifier_worker_limit(),
                        Err(ResourceBudgetError::NonUnicode {
                            key: TRUST_CG_MAX_PARALLELISM_ENV
                        })
                    );
                });
                trust_cg_process_env::with_env_overrides(
                    &[(TRUST_CG_MAX_PARALLELISM_ENV, "6")],
                    || {
                        assert_eq!(try_proof_verifier_worker_limit(), Ok(first));
                    },
                );
            }
            "install_first" => {
                // Requested identity, not effective host-clamped slot count.
                assert!(configure_proof_verifier_default_worker_limit(999));
                assert!(try_proof_verifier_worker_limit().is_ok());
                assert_eq!(PROOF_VERIFIER_BUDGET.get().unwrap().default_limit, 999);
                assert!(configure_proof_verifier_default_worker_limit(999));
                assert!(!configure_proof_verifier_default_worker_limit(1));
            }
            "capture_first" => {
                assert!(try_proof_verifier_worker_limit().is_ok());
                assert!(!configure_proof_verifier_default_worker_limit(1));
                assert!(DEFAULT_WORKER_LIMIT.get().is_none());
                assert_eq!(
                    PROOF_VERIFIER_BUDGET.get().unwrap().default_limit,
                    admitted_job_share()
                        .unwrap()
                        .map_or(DEFAULT_PROOF_VERIFIER_WORKERS, NonZeroUsize::get)
                );
            }
            "retry" => {
                assert!(configure_proof_verifier_default_worker_limit(1));
                trust_cg_process_env::with_env_overrides(
                    &[(TRUST_CG_MAX_PARALLELISM_ENV, "0")],
                    || {
                        assert!(try_proof_verifier_worker_limit().is_err());
                    },
                );
                assert!(PROOF_VERIFIER_BUDGET.get().is_none());
                assert!(configure_proof_verifier_default_worker_limit(1));
                assert!(try_proof_verifier_worker_limit().is_ok());
            }
            "race" => {
                // Hold the exact production lock until both contenders have
                // started. Neither may publish across this exclusion boundary.
                let guard = WORKER_POLICY_LOCK.lock().unwrap();
                let (ready_tx, ready_rx) = std::sync::mpsc::channel();
                let (done_tx, done_rx) = std::sync::mpsc::channel();
                let installer = std::thread::spawn({
                    let ready_tx = ready_tx.clone();
                    let done_tx = done_tx.clone();
                    move || {
                        ready_tx.send(()).unwrap();
                        let accepted = configure_proof_verifier_default_worker_limit(999);
                        done_tx.send(()).unwrap();
                        accepted
                    }
                });
                let capture = std::thread::spawn(move || {
                    ready_tx.send(()).unwrap();
                    let result = try_proof_verifier_worker_limit();
                    done_tx.send(()).unwrap();
                    result
                });
                ready_rx.recv().unwrap();
                ready_rx.recv().unwrap();
                assert!(
                    done_rx
                        .recv_timeout(std::time::Duration::from_millis(25))
                        .is_err()
                );
                assert!(DEFAULT_WORKER_LIMIT.get().is_none());
                assert!(PROOF_VERIFIER_BUDGET.get().is_none());
                drop(guard);
                let accepted = installer.join().unwrap();
                capture.join().unwrap().unwrap();
                let expected = if accepted {
                    999
                } else {
                    admitted_job_share()
                        .unwrap()
                        .map_or(DEFAULT_PROOF_VERIFIER_WORKERS, NonZeroUsize::get)
                };
                assert_eq!(PROOF_VERIFIER_BUDGET.get().unwrap().default_limit, expected);
                assert_eq!(DEFAULT_WORKER_LIMIT.get().copied(), accepted.then_some(999));
                assert_eq!(configure_proof_verifier_default_worker_limit(999), accepted);
            }
            "poison" => {
                assert!(
                    std::panic::catch_unwind(|| {
                        let _guard = WORKER_POLICY_LOCK.lock().unwrap();
                        panic!("deliberate worker policy poison");
                    })
                    .is_err()
                );
                assert!(!configure_proof_verifier_default_worker_limit(1));
                assert_eq!(
                    try_proof_verifier_worker_limit(),
                    Err(ResourceBudgetError::InstalledPolicyPoisoned {
                        key: "proof-walk-workers"
                    })
                );
            }
            "late_cap" => {
                assert!(configure_proof_verifier_default_worker_limit(1));
                try_proof_verifier_worker_limit().unwrap();
                assert!(
                    trust_cg_process_env::resource_budget::install_positive_usize_control(
                        TRUST_CG_MAX_PARALLELISM_ENV,
                        NonZeroUsize::new(8).unwrap()
                    )
                );
                assert!(!configure_proof_verifier_default_worker_limit(1));
            }
            _ => panic!("unexpected child mode"),
        }
    }

    fn host(available: usize) -> HostResourceSnapshot {
        HostResourceSnapshot::new(
            NonZeroUsize::new(available).unwrap_or(NonZeroUsize::MIN),
            None,
        )
    }

    fn resolve_worker_limit(
        configured: Option<usize>,
        available: usize,
        default_limit: usize,
    ) -> usize {
        let host = host(available);
        let defaults = ArtifactNeutralExecutorDefaults::new(
            host.available_parallelism(),
            NonZeroUsize::new(default_limit).unwrap_or(NonZeroUsize::MIN),
            NonZeroUsize::new(PROOF_VERIFIER_STACK_SIZE).unwrap(),
        );
        ArtifactNeutralExecutorBudget::resolve(
            defaults,
            host,
            configured.and_then(NonZeroUsize::new),
        )
        .expect("deterministic test host has no memory ceiling")
        .large_stack_slots()
        .get()
    }

    #[test]
    fn default_worker_limit_is_small_and_host_bounded() {
        assert_eq!(
            resolve_worker_limit(None, 64, DEFAULT_PROOF_VERIFIER_WORKERS),
            2
        );
        assert_eq!(
            resolve_worker_limit(None, 1, DEFAULT_PROOF_VERIFIER_WORKERS),
            1
        );
        assert_eq!(resolve_worker_limit(None, 64, 1), 1);
    }

    #[test]
    fn proof_verifier_worker_receives_explicit_environment_snapshot() {
        const KEY: &str = "TCG_PROOF_WORKER_OVERRIDE_TRANSFER_TEST";
        trust_cg_process_env::with_env_overrides(&[(KEY, "captured")], || {
            let observed = run_on_proof_verifier_stack("override-transfer-test", || {
                trust_cg_process_env::var(KEY).ok()
            });
            assert_eq!(observed.as_deref(), Some("captured"));
        });
    }

    #[test]
    fn explicit_worker_limit_wins_over_embedding_default() {
        assert_eq!(resolve_worker_limit(Some(8), 64, 1), 8);
        assert_eq!(resolve_worker_limit(Some(1), 64, 8), 1);
        assert_eq!(resolve_worker_limit(Some(999), 4, 1), 4);
    }

    #[test]
    fn zero_embedding_defaults_are_conservatively_one() {
        assert_eq!(resolve_worker_limit(None, 0, 0), 1);
    }
    #[test]
    fn cargo_share_preserves_bridge_default_and_caps_explicit_width_and_memory() {
        let share = NonZeroUsize::new(6);
        let roomy = HostResourceSnapshot::new(NonZeroUsize::new(32).unwrap(), None);
        trust_cg_process_env::with_env_overrides_removed(&[TRUST_CG_MAX_PARALLELISM_ENV], || {
            let budget = capture_verifier_budget(roomy, 1, share).unwrap();
            assert_eq!(budget.budget.large_stack_slots().get(), 1);
        });
        trust_cg_process_env::with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, "8")], || {
            let budget = capture_verifier_budget(roomy, 1, share).unwrap();
            assert_eq!(budget.budget.cpu_slots().get(), 6);
            assert_eq!(budget.budget.large_stack_slots().get(), 6);
            let memory = std::num::NonZeroU64::new((PROOF_VERIFIER_STACK_SIZE * 2) as u64);
            let limited = HostResourceSnapshot::new(NonZeroUsize::new(32).unwrap(), memory);
            let budget = capture_verifier_budget(limited, 1, share).unwrap();
            assert_eq!(budget.budget.large_stack_slots().get(), 2);
        });
    }

    #[test]
    fn scoped_cargo_hint_cannot_widen_external_admission() {
        let external = std::env::var("CARGO_BUILD_JOBS")
            .ok()
            .and_then(|value| value.parse::<usize>().ok());
        trust_cg_process_env::with_env_overrides(&[("CARGO_BUILD_JOBS", "999")], || {
            let captured = admitted_job_share().unwrap().unwrap().get();
            assert_eq!(captured, external.map_or(999, |value| value.min(999)));
        });
        trust_cg_process_env::with_env_overrides(&[("CARGO_BUILD_JOBS", "1")], || {
            assert_eq!(admitted_job_share().unwrap().unwrap().get(), 1);
        });
    }
}
