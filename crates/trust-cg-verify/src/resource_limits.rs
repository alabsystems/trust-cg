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
/// Two workers reserve at most 64 MiB of verifier stacks in a normal embedding.
/// Hosts that already parallelize across compiler processes (the rustc bridge)
/// lower this default to one before the pool is initialized. An explicit
/// [`TRUST_CG_MAX_PARALLELISM_ENV`] value always takes precedence.
const DEFAULT_PROOF_VERIFIER_WORKERS: usize = 2;

static DEFAULT_WORKER_LIMIT: OnceLock<usize> = OnceLock::new();
static PROOF_VERIFIER_BUDGET: OnceLock<ArtifactNeutralExecutorBudget> = OnceLock::new();
static PROOF_VERIFIER_POOL: OnceLock<Option<rayon::ThreadPool>> = OnceLock::new();
static SERIAL_FALLBACK_LOCK: Mutex<()> = Mutex::new(());

/// Override the process-local verifier worker default before first budget/pool
/// use.
///
/// This changes only the default. A positive `TRUST_CG_MAX_PARALLELISM` value
/// remains authoritative. The first caller wins, which lets an embedding set a
/// conservative policy during its initialization without later library code
/// silently widening it.
#[must_use]
pub fn configure_proof_verifier_default_worker_limit(worker_limit: usize) -> bool {
    if PROOF_VERIFIER_BUDGET.get().is_some() {
        return false;
    }
    DEFAULT_WORKER_LIMIT.set(worker_limit.max(1)).is_ok()
}

/// Resolve the worker limit used by the shared large-stack verifier pool.
#[must_use]
pub fn proof_verifier_worker_limit() -> usize {
    PROOF_VERIFIER_BUDGET
        .get_or_init(|| {
            let host = HostResourceSnapshot::capture();
            let default_limit = DEFAULT_WORKER_LIMIT
                .get()
                .copied()
                .unwrap_or(DEFAULT_PROOF_VERIFIER_WORKERS);
            capture_verifier_budget(host, default_limit)
        })
        .large_stack_slots()
        .get()
}

fn capture_verifier_budget(
    host: HostResourceSnapshot,
    default_limit: usize,
) -> ArtifactNeutralExecutorBudget {
    let defaults = ArtifactNeutralExecutorDefaults::new(
        host.available_parallelism(),
        NonZeroUsize::new(default_limit).unwrap_or(NonZeroUsize::MIN),
        NonZeroUsize::new(PROOF_VERIFIER_STACK_SIZE)
            .expect("proof-verifier stack reservation must be positive"),
    );
    ArtifactNeutralExecutorBudget::capture_for_host(defaults, host)
        .unwrap_or_else(|error| panic!("invalid Trust Codegen execution resource budget: {error}"))
}

fn proof_verifier_pool() -> Option<&'static rayon::ThreadPool> {
    PROOF_VERIFIER_POOL
        .get_or_init(|| {
            rayon::ThreadPoolBuilder::new()
                .num_threads(proof_verifier_worker_limit())
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
    if let Some(pool) = proof_verifier_pool() {
        pool.spawn(operation);
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn explicit_worker_limit_wins_over_embedding_default() {
        assert_eq!(resolve_worker_limit(Some(8), 64, 1), 8);
        assert_eq!(resolve_worker_limit(Some(1), 64, 8), 1);
        assert_eq!(resolve_worker_limit(Some(999), 4, 1), 4);
    }

    #[test]
    fn zero_embedding_defaults_are_conservatively_one() {
        assert_eq!(resolve_worker_limit(None, 0, 0), 1);
    }
}
