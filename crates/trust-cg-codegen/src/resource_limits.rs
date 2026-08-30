// trust-cg-codegen/resource_limits.rs - Shared host resource limits
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared host resource limits for Trust Codegen-owned compilation paths.

use std::num::NonZeroUsize;
use std::path::Path;

use trust_cg_process_env::resource_budget::{
    ArtifactNeutralExecutorBudget, ArtifactNeutralExecutorDefaults, HostResourceSnapshot,
    PROOF_VERIFIER_STACK_BYTES,
};

/// Environment variable controlling the maximum Rayon worker count used by
/// Trust Codegen-owned compilation fanout.
pub use trust_cg_process_env::resource_budget::TRUST_CG_MAX_PARALLELISM_ENV;

/// Environment variable controlling the maximum input file size accepted by
/// the trust_ir loader before reading the whole module into memory.
pub const TRUST_CG_MAX_INPUT_BYTES_ENV: &str = "TRUST_CG_MAX_INPUT_BYTES";

/// Floor for the regalloc+encode fanout when host memory cannot be determined.
///
/// This is the historical fixed cap. It is now a FLOOR rather than the value:
/// see [`memory_adaptive_parallelism_default_for_host`].
const DEFAULT_MAX_PARALLELISM: usize = 2;

/// Memory budgeted per concurrent regalloc+encode worker.
///
/// The fanout's peak footprint is dominated by one in-flight function's
/// liveness + interference + encode buffers. 1 GiB per worker is deliberately
/// generous: the point is to stay safe on small hosts, not to squeeze the last
/// worker out of a large one.
const PARALLELISM_MEMORY_BUDGET_PER_WORKER: u64 = 1024 * 1024 * 1024;

const DEFAULT_MAX_INPUT_BYTES: u64 = 512 * 1024 * 1024;

/// Fewest work items a worker must be given before spawning it is worth it.
///
/// The width used to be `min(memory_cap, item_count)` — one worker per item,
/// however small the item. That is a memory-headroom answer to a
/// work-scheduling question, and on ordinary crates it LOSES. Measured on the
/// 18-program `beat-llvm` corpus (median-of-11, interleaved, aarch64, one CGU
/// of 9-11 functions), against the same compile pinned to one worker:
///
/// ```text
/// workers   CPU      wall
/// 1         1.000    1.000
/// 2         1.017    0.999
/// 9-11      1.081    1.002
/// ```
///
/// The full-width fanout burns 8% more CPU and finishes no sooner — the
/// functions are ~0.5ms each, so spawning ten OS threads (twice: two pools are
/// built per compile) costs more than the overlap saves. For a compiler invoked
/// by cargo under `-j N`, that CPU is taken from other crates, so it is a real
/// loss and not just a metric artifact.
///
/// 16 keeps ordinary crates serial while a genuinely large module still fans
/// out (a 129-function module gets 8 workers). It bounds the waste rather than
/// claiming an optimum: the crossover is workload-dependent, and the fanout's
/// own efficiency is a separate open question — a 128-function module measured
/// only 1.03x concurrency, which no width can fix.
const MIN_ITEMS_PER_WORKER: usize = 16;

/// Effective Rayon worker count for a parallel operation over `item_count`
/// independent work items.
#[must_use]
pub fn worker_count_for_items(item_count: usize) -> Option<usize> {
    if item_count < 2 {
        return None;
    }
    // Width is bounded by the WORK as well as by memory and item count: a
    // worker that would be handed fewer than `MIN_ITEMS_PER_WORKER` items does
    // not pay for its own spawn. See the constant's note for the measurement.
    let by_work = item_count / MIN_ITEMS_PER_WORKER;
    let workers = configured_parallelism_limit().min(item_count).min(by_work);
    (workers >= 2).then_some(workers)
}

/// Effective Rayon worker count for the per-function PROOF-CERTIFICATE lane
/// (CT-7).
///
/// Proof evaluation recursively walks SMT trees and therefore runs on the
/// shared 32 MiB-stack pool owned by `trust-cg-verify`. Function-level fanout
/// uses the SAME worker limit so concurrent functions submit to that fixed pool
/// instead of spawning one large-stack OS thread per function. The default is
/// deliberately small and memory-bounded; the rustc bridge lowers it to one
/// because Cargo already parallelizes across compiler processes. An explicit
/// `TRUST_CG_MAX_PARALLELISM` still wins. Worker count never affects output: the
/// cert lane collects into a function-ordered vector, so the bundle is
/// byte-identical at any width
/// (`test_x86_parallel_and_serial_multi_function_byte_identical`).
#[must_use]
pub fn verification_worker_count_for_items(item_count: usize) -> Option<usize> {
    verification_worker_count_for_items_with_limit(
        item_count,
        trust_cg_verify::resource_limits::proof_verifier_worker_limit(),
    )
}

fn verification_worker_count_for_items_with_limit(
    item_count: usize,
    worker_limit: usize,
) -> Option<usize> {
    let workers = worker_limit.max(1).min(item_count);
    (workers >= 2).then_some(workers)
}

/// Bound Rayon's GLOBAL pool, once, at backend startup.
///
/// Every other fanout in this crate runs inside a pool built by
/// [`build_rayon_pool`], so `TRUST_CG_MAX_PARALLELISM` bounds it. Rayon's
/// GLOBAL pool is different: it is created lazily, at
/// `available_parallelism()` wide, by the first unscoped parallel iterator
/// anywhere in the process — including in DEPENDENCIES we do not control.
/// `trust_ir_build::validate_module` has one (`validate.rs`, the enum-layout
/// walk), and that runs on every compile, so every compile was spawning a
/// full-width global pool no matter what the operator asked for.
///
/// The cost is not the work — it is the idling. Measured on `fn main(){}`,
/// aarch64, 20 cores, via `strace -c`:
///
/// ```text
/// backend            sched_yield   threads spawned
/// LLVM                         1                 5
/// trust-cg                  2126                24
/// trust-cg, bounded           88                 5
/// ```
///
/// Those ~2100 yields per compile are pure `sys` time, and sys was where the
/// remaining compile-time deficit lived: +103ms of +130ms CPU across the
/// 18-program corpus. Bounding the global pool moved the corpus from 1.086x
/// LLVM to 0.959x on CPU and 1.002x to 0.962x on wall.
///
/// An explicit `TRUST_CG_MAX_PARALLELISM` wins, exactly as for every other
/// fanout; otherwise this uses [`DEFAULT_MAX_PARALLELISM`], which is both the
/// documented default and the width that measured best (corpus CPU 0.959 at 2
/// workers, against 0.967 at 1 and 1.000 at 4).
///
/// Idempotent and non-fatal: `build_global` errors if the global pool already
/// exists, which means something else — plausibly the host compiler — got there
/// first and owns the policy. We defer to it rather than fight over it.
pub fn bound_global_rayon_pool() {
    let workers = artifact_neutral_parallelism_limit(
        NonZeroUsize::new(DEFAULT_MAX_PARALLELISM).expect("global pool default must be positive"),
    )
    .get();
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .thread_name(|idx| format!("trust-cg-global-{idx}"))
        .build_global();
}

/// Resolve a compatibility worker cap through the shared typed contract.
///
/// This helper is only for work-complete, order-stable lanes. Search lanes must
/// carry an identity-bound search policy instead. A malformed or zero
/// `TRUST_CG_MAX_PARALLELISM` fails closed with a deterministic panic because
/// legacy callers return an integer rather than `Result`.
#[must_use]
pub fn artifact_neutral_parallelism_limit(default_limit: NonZeroUsize) -> NonZeroUsize {
    capture_executor_budget(
        default_limit.get(),
        1,
        HostResourceSnapshot::capture_cpu_only(),
    )
    .cpu_slots()
}

/// Resolve a large-stack worker cap through the shared memory-aware contract.
///
/// Unlike [`artifact_neutral_parallelism_limit`], this captures host memory and
/// ensures `slots * 32 MiB` does not exceed known available memory. A frontend
/// can impose a lower lane-specific `hard_limit` without re-parsing ambient
/// controls.
#[must_use]
pub fn artifact_neutral_large_stack_slot_limit(
    default_limit: NonZeroUsize,
    hard_limit: NonZeroUsize,
) -> NonZeroUsize {
    let host = HostResourceSnapshot::capture();
    let resolved =
        capture_executor_budget(default_limit.get(), default_limit.get(), host).large_stack_slots();
    NonZeroUsize::new(resolved.get().min(hard_limit.get())).unwrap_or(NonZeroUsize::MIN)
}

/// Build a bounded Rayon pool for Trust Codegen-owned fanout.
pub fn build_rayon_pool(
    worker_count: usize,
) -> Result<rayon::ThreadPool, rayon::ThreadPoolBuildError> {
    rayon::ThreadPoolBuilder::new()
        .num_threads(worker_count.max(1))
        .thread_name(|idx| format!("trust-cg-worker-{idx}"))
        .build()
}

pub(crate) fn read_file_bounded(path: &Path) -> Result<Vec<u8>, String> {
    let limit = configured_input_byte_limit();
    let len = std::fs::metadata(path)
        .map_err(|err| format!("I/O error: {err}"))?
        .len();
    check_input_len(path, len, limit)?;

    let bytes = std::fs::read(path).map_err(|err| format!("I/O error: {err}"))?;
    check_input_len(path, bytes.len() as u64, limit)?;
    Ok(bytes)
}

pub(crate) fn read_utf8_bounded(path: &Path) -> Result<String, String> {
    let bytes = read_file_bounded(path)?;
    String::from_utf8(bytes).map_err(|err| format!("I/O error: {err}"))
}

fn configured_parallelism_limit() -> usize {
    let host = HostResourceSnapshot::capture();
    let default = memory_adaptive_parallelism_default_for_host(host);
    capture_executor_budget(default, 1, host).cpu_slots().get()
}

fn capture_executor_budget(
    default_cpu_slots: usize,
    default_large_stack_slots: usize,
    host: HostResourceSnapshot,
) -> ArtifactNeutralExecutorBudget {
    let defaults = ArtifactNeutralExecutorDefaults::new(
        NonZeroUsize::new(default_cpu_slots).expect("executor CPU default must be positive"),
        NonZeroUsize::new(default_large_stack_slots)
            .expect("executor large-stack default must be positive"),
        NonZeroUsize::new(PROOF_VERIFIER_STACK_BYTES)
            .expect("proof-verifier stack reservation must be positive"),
    );
    ArtifactNeutralExecutorBudget::capture_for_host(defaults, host)
        .unwrap_or_else(|error| panic!("invalid Trust Codegen execution resource budget: {error}"))
}

/// Default worker cap for the memory-hungry regalloc+encode fanout, scaled to
/// what the host can actually hold.
///
/// The historical default was a flat `2` regardless of host. That is correct on
/// a laptop and leaves an order of magnitude unused on a many-core server: the
/// fanout is the dominant proofs-off compile-time cost, so capping it at 2 on a
/// 20-core host caps compile throughput at 2/20 of the machine.
///
/// This scales by available memory instead, because memory — not cores — is the
/// resource the cap exists to protect. It never returns less than the
/// historical [`DEFAULT_MAX_PARALLELISM`], never exceeds host parallelism, and
/// falls back to the historical value when memory is unknown. An explicit
/// `TRUST_CG_MAX_PARALLELISM` still wins through the shared typed executor
/// budget.
///
/// Worker count never affects output — the fanout collects into a
/// function-ordered vector, so artifacts are byte-identical at any width.
#[must_use]
#[cfg(test)]
fn memory_adaptive_parallelism_default(available_parallelism: usize) -> usize {
    memory_adaptive_parallelism_default_for_host(HostResourceSnapshot::new(
        NonZeroUsize::new(available_parallelism).unwrap_or(NonZeroUsize::MIN),
        HostResourceSnapshot::capture().available_memory_bytes(),
    ))
}

fn memory_adaptive_parallelism_default_for_host(host: HostResourceSnapshot) -> usize {
    let available_parallelism = host.available_parallelism().get();
    let Some(mem) = host.available_memory_bytes().map(std::num::NonZeroU64::get) else {
        // ⚑ Clamp here too. This early return is the ONLY path that skipped
        // `.min(available_parallelism)`, so on any host where the memory probe
        // yields nothing — every non-Linux target, which is where the probe is
        // unimplemented — a single-core host was told to schedule 2 workers.
        // The function's contract, and its test, is "never above host
        // parallelism".
        return DEFAULT_MAX_PARALLELISM.min(available_parallelism.max(1));
    };
    let by_memory = (mem / PARALLELISM_MEMORY_BUDGET_PER_WORKER) as usize;
    by_memory
        .max(DEFAULT_MAX_PARALLELISM)
        .min(available_parallelism.max(1))
}

fn configured_input_byte_limit() -> u64 {
    parse_input_byte_limit(std::env::var(TRUST_CG_MAX_INPUT_BYTES_ENV).ok().as_deref())
}

fn parse_input_byte_limit(raw: Option<&str>) -> u64 {
    raw.and_then(|value| value.trim().parse::<u64>().ok())
        .filter(|value| *value > 0)
        .unwrap_or(DEFAULT_MAX_INPUT_BYTES)
}

fn check_input_len(path: &Path, len: u64, limit: u64) -> Result<(), String> {
    if len <= limit {
        return Ok(());
    }
    Err(format!(
        "input '{}' is {} bytes, exceeding the Trust Codegen input limit of {} bytes; \
         set {TRUST_CG_MAX_INPUT_BYTES_ENV} to a larger positive byte count only \
         for trusted large modules",
        path.display(),
        len,
        limit
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;

    #[test]
    fn parallelism_limit_defaults_to_bounded_host_cap() {
        trust_cg_process_env::with_env_overrides_removed(&[TRUST_CG_MAX_PARALLELISM_ENV], || {
            let host = HostResourceSnapshot::new(NonZeroUsize::new(64).unwrap(), None);
            let budget = capture_executor_budget(DEFAULT_MAX_PARALLELISM, 1, host);
            assert_eq!(budget.cpu_slots().get(), DEFAULT_MAX_PARALLELISM);
        });
    }

    #[test]
    fn worker_count_disables_parallelism_below_two_workers() {
        trust_cg_process_env::with_env_overrides_removed(&[TRUST_CG_MAX_PARALLELISM_ENV], || {
            assert_eq!(worker_count_for_items(0), None);
            assert_eq!(worker_count_for_items(1), None);
            // Work-aware width: a handful of items stays SERIAL rather than
            // spawning a thread per item. An ordinary crate's CGU is this size, and
            // the full-width fanout measured 8% more CPU for no wall gain there.
            assert_eq!(worker_count_for_items(2), None, "2 items must not fan out");
            assert_eq!(
                worker_count_for_items(9),
                None,
                "corpus-sized CGU stays serial"
            );
            assert_eq!(
                worker_count_for_items(31),
                None,
                "under 2 workers' worth of items"
            );
            // Genuinely large modules still fan out, bounded by items/16.
            assert!(
                worker_count_for_items(32).is_some_and(|w| w >= 2),
                "32 items is two workers' worth"
            );
            assert!(
                worker_count_for_items(129).is_some_and(|w| w >= 2 && w <= 8),
                "129 items yields at most items/16 workers"
            );
        });
    }

    #[test]
    fn verification_worker_count_is_deterministically_limit_bounded() {
        assert_eq!(verification_worker_count_for_items_with_limit(0, 8), None);
        assert_eq!(verification_worker_count_for_items_with_limit(1, 8), None);
        assert_eq!(verification_worker_count_for_items_with_limit(8, 1), None);
        assert_eq!(
            verification_worker_count_for_items_with_limit(8, 2),
            Some(2)
        );
        assert_eq!(
            verification_worker_count_for_items_with_limit(3, 8),
            Some(3)
        );
    }

    /// The adaptive default is bounded on both sides: never below the historical
    /// conservative cap, never above host parallelism.
    #[test]
    fn memory_adaptive_default_is_bounded_by_host_parallelism_and_floor() {
        for cores in [1usize, 2, 4, 20, 256] {
            let d = memory_adaptive_parallelism_default(cores);
            assert!(
                d >= DEFAULT_MAX_PARALLELISM.min(cores.max(1)),
                "adaptive default {d} fell below the historical floor at {cores} cores"
            );
            assert!(
                d <= cores.max(1),
                "adaptive default {d} exceeded host parallelism {cores}"
            );
            assert!(d >= 1, "adaptive default must schedule at least one worker");
        }
    }

    /// Regression pin for the reason this exists: on a host with many cores AND
    /// enough memory to back them, the fanout must not still be capped at 2.
    /// Skipped on hosts that genuinely cannot back more than 2 workers.
    #[test]
    fn many_core_host_with_memory_is_not_capped_at_two() {
        let cores = std::thread::available_parallelism().map_or(1, usize::from);
        let Some(mem) = HostResourceSnapshot::capture()
            .available_memory_bytes()
            .map(std::num::NonZeroU64::get)
        else {
            return; // memory unknown -> conservative fallback is correct
        };
        let backable = (mem / PARALLELISM_MEMORY_BUDGET_PER_WORKER) as usize;
        if cores <= DEFAULT_MAX_PARALLELISM || backable <= DEFAULT_MAX_PARALLELISM {
            return; // small host: the conservative cap IS the right answer
        }
        assert!(
            memory_adaptive_parallelism_default(cores) > DEFAULT_MAX_PARALLELISM,
            "host has {cores} cores and can back {backable} workers, but the fanout \
             default is still pinned at {DEFAULT_MAX_PARALLELISM}"
        );
    }

    #[test]
    fn input_byte_limit_defaults_and_rejects_invalid_values() {
        assert_eq!(parse_input_byte_limit(None), DEFAULT_MAX_INPUT_BYTES);
        assert_eq!(parse_input_byte_limit(Some("1024")), 1024);
        assert_eq!(parse_input_byte_limit(Some("0")), DEFAULT_MAX_INPUT_BYTES);
        assert_eq!(parse_input_byte_limit(Some("bad")), DEFAULT_MAX_INPUT_BYTES);
    }

    #[test]
    fn oversized_input_error_names_override_env() {
        let error = check_input_len(Path::new("huge.tmbc"), 11, 10).unwrap_err();
        assert!(error.contains("huge.tmbc"));
        assert!(error.contains(TRUST_CG_MAX_INPUT_BYTES_ENV));
    }
}
