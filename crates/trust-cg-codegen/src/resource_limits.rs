// trust-cg-codegen/resource_limits.rs - Shared host resource limits
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared host resource limits for Trust Codegen-owned compilation paths.

use std::io::Read;
use std::num::NonZeroUsize;
use std::path::Path;

use trust_cg_process_env::resource_budget::{
    ArtifactNeutralExecutorBudget, ArtifactNeutralExecutorDefaults, HostResourceSnapshot,
    PROOF_VERIFIER_STACK_BYTES, ResourceBudgetError, capture_positive_usize_control,
};

/// Environment variable controlling the maximum Rayon worker count used by
/// Trust Codegen-owned compilation fanout.
pub use trust_cg_process_env::resource_budget::TRUST_CG_MAX_PARALLELISM_ENV;

/// Environment variable controlling the maximum input file size accepted by
/// the trust_ir loader. The limit bounds both metadata and the actual read;
/// malformed controls are rejected before opening the input.
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
/// Local pool construction has a fixed cost, so memory headroom alone is not
/// a reason to spawn more workers. Small modules stay serial; larger modules
/// receive at most `item_count / MIN_ITEMS_PER_WORKER` workers, additionally
/// capped by host resources and operator configuration. The crossover depends
/// on workload; current performance evidence belongs in the benchmark ledger.
const MIN_ITEMS_PER_WORKER: usize = 16;

/// Functions per worker of the DEFAULT width of the x86-64 per-function
/// encode fan-out ([`x86_encode_worker_count_for_items`]), past its first two
/// workers.
///
/// The memory-adaptive default limit is as wide as the host; filling it at
/// [`MIN_ITEMS_PER_WORKER`] costs that fan-out CPU for little wall time
/// (ruling OD-X86-ENCODE-DEFAULT-WIDTH-20261111 carries the measurements and
/// the wall-time cost). It applies to no other fan-out and not to an
/// operator-configured `TRUST_CG_MAX_PARALLELISM`.
const X86_ENCODE_DEFAULT_ITEMS_PER_WORKER: usize = 100;

/// Effective Rayon worker count for a parallel operation over `item_count`
/// independent work items.
///
/// Invalid operator configuration is rejected even when the work is serial.
pub fn worker_count_for_items(item_count: usize) -> Result<Option<usize>, ResourceBudgetError> {
    try_worker_count_for_items(item_count)
}

/// Validate the execution budget and select a work-aware input worker count.
///
/// Validation runs even for a single input or a caller that will execute
/// serially: invalid operator controls must not be accepted or rejected based
/// on input count. The shared budget error names malformed controls without
/// panicking or choosing a fallback; a host-memory reading only narrows the
/// large-stack width (never below one slot).
pub fn try_worker_count_for_items(item_count: usize) -> Result<Option<usize>, ResourceBudgetError> {
    let host = HostResourceSnapshot::capture();
    let default = memory_adaptive_parallelism_default_for_host(host);
    let budget = capture_executor_budget(default, NonZeroUsize::MIN, host)?;
    Ok(worker_count_for_items_with_limit(
        item_count,
        budget.cpu_slots().get(),
    ))
}

/// Worker count for the x86-64 per-function encode fan-out over `item_count`
/// functions: [`try_worker_count_for_items`] with the same validation, and the
/// default width additionally bounded by
/// [`X86_ENCODE_DEFAULT_ITEMS_PER_WORKER`].
pub(crate) fn x86_encode_worker_count_for_items(
    item_count: usize,
) -> Result<Option<usize>, ResourceBudgetError> {
    let workers = try_worker_count_for_items(item_count)?;
    let configured = capture_positive_usize_control(TRUST_CG_MAX_PARALLELISM_ENV)?;
    Ok(x86_encode_width(item_count, workers, configured.is_some()))
}

/// Narrow the shared policy's `workers` for `item_count` functions to the
/// x86-64 encode default width. `limit_is_configured` says the limit is the
/// operator's `TRUST_CG_MAX_PARALLELISM` rather than the host default; a
/// configured limit is returned unchanged.
fn x86_encode_width(
    item_count: usize,
    workers: Option<usize>,
    limit_is_configured: bool,
) -> Option<usize> {
    if limit_is_configured {
        return workers;
    }
    let by_default_width = (item_count / X86_ENCODE_DEFAULT_ITEMS_PER_WORKER).max(2);
    workers.map(|workers| workers.min(by_default_width))
}

/// Admit both compiler and verifier resources before a compilation can enter
/// legacy verifier execution routines. The compiler controls are checked for
/// every request, while the successful shared verifier budget is fixed once.
pub(crate) fn admit_compilation_budget() -> Result<(), ResourceBudgetError> {
    try_worker_count_for_items(0)?;
    trust_cg_verify::resource_limits::try_proof_verifier_worker_limit()?;
    Ok(())
}

fn worker_count_for_items_with_limit(item_count: usize, worker_limit: usize) -> Option<usize> {
    // Bound width by work as well as resources to amortize pool construction.
    let by_work = item_count / MIN_ITEMS_PER_WORKER;
    let workers = worker_limit.min(item_count).min(by_work);
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
#[must_use = "the verification worker limit must be handled"]
pub fn verification_worker_count_for_items(
    item_count: usize,
) -> Result<Option<usize>, ResourceBudgetError> {
    // Reject malformed current-request controls even after the shared verifier
    // has captured its process-lifetime budget.
    try_worker_count_for_items(0)?;
    Ok(verification_worker_count_for_items_with_limit(
        item_count,
        trust_cg_verify::resource_limits::try_proof_verifier_worker_limit()?,
    ))
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
/// An explicit `TRUST_CG_MAX_PARALLELISM` wins, exactly as for every other
/// fanout; otherwise this uses [`DEFAULT_MAX_PARALLELISM`], which is both the
/// conservative fallback and the fixed global-pool default.
///
/// Idempotent and non-fatal: `build_global` errors if the global pool already
/// exists, which means something else — plausibly the host compiler — got there
/// first and owns the policy. We defer to it rather than fight over it.
pub fn bound_global_rayon_pool() -> Result<(), ResourceBudgetError> {
    let workers = artifact_neutral_parallelism_limit(default_parallelism())?.get();
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(workers)
        .thread_name(|idx| format!("trust-cg-global-{idx}"))
        .build_global();
    Ok(())
}

/// Resolve a compatibility worker cap through the shared typed contract.
///
/// This helper is only for work-complete, order-stable lanes. Search lanes must
/// carry an identity-bound search policy instead. A malformed or zero
/// `TRUST_CG_MAX_PARALLELISM` is returned as an explicit budget error.
pub fn artifact_neutral_parallelism_limit(
    default_limit: NonZeroUsize,
) -> Result<NonZeroUsize, ResourceBudgetError> {
    Ok(capture_executor_budget(
        default_limit,
        NonZeroUsize::MIN,
        HostResourceSnapshot::capture_cpu_only(),
    )?
    .cpu_slots())
}

/// Resolve a large-stack worker cap through the shared memory-aware contract.
///
/// Unlike [`artifact_neutral_parallelism_limit`], this captures host memory and
/// ensures `slots * 32 MiB` does not exceed known available memory. A frontend
/// can impose a lower lane-specific `hard_limit` without re-parsing ambient
/// controls.
pub fn artifact_neutral_large_stack_slot_limit(
    default_limit: NonZeroUsize,
    hard_limit: NonZeroUsize,
) -> Result<NonZeroUsize, ResourceBudgetError> {
    let host = HostResourceSnapshot::capture();
    let resolved = capture_executor_budget(default_limit, default_limit, host)?.large_stack_slots();
    Ok(resolved.min(hard_limit))
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
    let limit = configured_input_byte_limit()?;
    let file = std::fs::File::open(path).map_err(|err| format!("I/O error: {err}"))?;
    let len = file
        .metadata()
        .map_err(|err| format!("I/O error: {err}"))?
        .len();
    check_input_len(path, len, limit)?;

    read_stream_bounded(file, path, limit)
}

fn read_stream_bounded(reader: impl Read, path: &Path, limit: u64) -> Result<Vec<u8>, String> {
    // Metadata is only an early rejection: files can grow after it is read,
    // and virtual files may report zero length. Bound the read itself, with
    // one extra byte to distinguish an exact-limit input from a larger one.
    let mut bytes = Vec::new();
    reader
        .take(limit.saturating_add(1))
        .read_to_end(&mut bytes)
        .map_err(|err| format!("I/O error: {err}"))?;
    check_input_len(path, bytes.len() as u64, limit)?;
    Ok(bytes)
}

pub(crate) fn read_utf8_bounded(path: &Path) -> Result<String, String> {
    let bytes = read_file_bounded(path)?;
    String::from_utf8(bytes).map_err(|err| format!("I/O error: {err}"))
}

fn capture_executor_budget(
    default_cpu_slots: NonZeroUsize,
    default_large_stack_slots: NonZeroUsize,
    host: HostResourceSnapshot,
) -> Result<ArtifactNeutralExecutorBudget, ResourceBudgetError> {
    let defaults = ArtifactNeutralExecutorDefaults::new(
        default_cpu_slots,
        default_large_stack_slots,
        // Construct the fixed positive reservation directly in its nonzero
        // domain, so no runtime validation or panic branch is necessary.
        NonZeroUsize::MIN.saturating_add(PROOF_VERIFIER_STACK_BYTES - 1),
    );
    ArtifactNeutralExecutorBudget::capture_for_host(defaults, host)
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
    .get()
}

fn default_parallelism() -> NonZeroUsize {
    NonZeroUsize::MIN.saturating_add(DEFAULT_MAX_PARALLELISM - 1)
}

fn memory_adaptive_parallelism_default_for_host(host: HostResourceSnapshot) -> NonZeroUsize {
    let available_parallelism = host.available_parallelism();
    let Some(mem) = host.available_memory_bytes().map(std::num::NonZeroU64::get) else {
        // A failed or unsupported memory probe still has to respect the CPU
        // ceiling. Linux and macOS provide probes through the shared leaf.
        return default_parallelism().min(available_parallelism);
    };
    let by_memory = (mem / PARALLELISM_MEMORY_BUDGET_PER_WORKER) as usize;
    NonZeroUsize::new(by_memory)
        .map_or(default_parallelism(), |slots| {
            slots.max(default_parallelism())
        })
        .min(available_parallelism)
}

fn configured_input_byte_limit() -> Result<u64, String> {
    match trust_cg_process_env::var(TRUST_CG_MAX_INPUT_BYTES_ENV) {
        Ok(raw) => parse_input_byte_limit(Some(&raw)),
        Err(std::env::VarError::NotPresent) => parse_input_byte_limit(None),
        Err(error) => Err(format!("invalid {TRUST_CG_MAX_INPUT_BYTES_ENV}: {error}")),
    }
}

fn parse_input_byte_limit(raw: Option<&str>) -> Result<u64, String> {
    let Some(raw) = raw else {
        return Ok(DEFAULT_MAX_INPUT_BYTES);
    };
    raw.trim().parse::<u64>().ok().filter(|value| *value > 0).ok_or_else(|| {
        format!("invalid {TRUST_CG_MAX_INPUT_BYTES_ENV}: expected a positive byte count, got {raw:?}")
    })
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

    /// This file's fixtures are hand-built and carry no codegen license
    /// (`body_gate: None`), which trust-cg REFUSES by default (roadmap WS7.5,
    /// decision gate DG-73). Its compiles state `Permit` explicitly, so none of
    /// them passes because it was silently refused.
    fn permit_unlicensed() -> crate::CodegenLicensePolicy {
        crate::CodegenLicensePolicy::default().with_unlicensed(crate::UnlicensedBodyPolicy::Permit)
    }
    use std::path::Path;

    #[test]
    fn all_executor_boundaries_reject_invalid_controls_even_for_serial_work() {
        for value in ["0", "malformed", "-1"] {
            trust_cg_process_env::with_env_overrides(
                &[(TRUST_CG_MAX_PARALLELISM_ENV, value)],
                || {
                    for count in [0, 1, 64] {
                        assert!(worker_count_for_items(count).is_err());
                        assert!(try_worker_count_for_items(count).is_err());
                        assert!(verification_worker_count_for_items(count).is_err());
                    }
                    assert!(artifact_neutral_parallelism_limit(NonZeroUsize::MIN).is_err());
                    assert!(
                        artifact_neutral_large_stack_slot_limit(
                            NonZeroUsize::MIN,
                            NonZeroUsize::MIN
                        )
                        .is_err()
                    );
                    assert!(bound_global_rayon_pool().is_err());
                    assert!(admit_compilation_budget().is_err());
                },
            );
        }
    }

    #[test]
    fn compiler_and_raw_jit_reject_invalid_budget_before_work() {
        trust_cg_process_env::with_env_overrides(&[(TRUST_CG_MAX_PARALLELISM_ENV, "0")], || {
            let module = trust_ir::Module::new("invalid-budget");
            for parallel in [false, true] {
                let compiler = crate::Compiler::new(crate::CompilerConfig {
                    parallel,
                    ..Default::default()
                })
                .with_codegen_license(permit_unlicensed());
                assert!(matches!(
                    compiler.compile(&module),
                    Err(crate::CompileError::ResourceBudget(_))
                ));
            }
            let jit = crate::jit::JitCompiler::new(Default::default());
            assert!(matches!(
                jit.compile_raw(&[], &Default::default()),
                Err(crate::jit::JitError::ResourceBudget(_))
            ));
        });
    }

    /// A host-memory reading below one verifier stack narrows the budget to
    /// one slot instead of refusing the compile: the reading is momentary, so
    /// a refusal would make a valid compile's outcome nondeterministic.
    #[test]
    fn low_memory_reading_keeps_one_verifier_stack_slot() {
        trust_cg_process_env::with_env_overrides_removed(&[TRUST_CG_MAX_PARALLELISM_ENV], || {
            let host = HostResourceSnapshot::new(NonZeroUsize::MIN, std::num::NonZeroU64::new(1));
            let budget = capture_executor_budget(NonZeroUsize::MIN, NonZeroUsize::MIN, host)
                .expect("a low memory reading does not refuse the budget");
            assert_eq!(budget.large_stack_slots().get(), 1);
        });
    }

    #[test]
    fn parallelism_limit_defaults_to_bounded_host_cap() {
        trust_cg_process_env::with_env_overrides_removed(&[TRUST_CG_MAX_PARALLELISM_ENV], || {
            let host = HostResourceSnapshot::new(NonZeroUsize::new(64).unwrap(), None);
            let budget =
                capture_executor_budget(default_parallelism(), NonZeroUsize::MIN, host).unwrap();
            assert_eq!(budget.cpu_slots().get(), DEFAULT_MAX_PARALLELISM);
        });
    }

    #[test]
    fn worker_count_disables_parallelism_below_two_workers() {
        trust_cg_process_env::with_env_overrides_removed(&[TRUST_CG_MAX_PARALLELISM_ENV], || {
            assert_eq!(worker_count_for_items(0).unwrap(), None);
            assert_eq!(worker_count_for_items(1).unwrap(), None);
            // Work-aware width: a handful of items stays SERIAL rather than
            // spawning a thread per item. An ordinary crate's CGU is this size, and
            // the full-width fanout measured 8% more CPU for no wall gain there.
            assert_eq!(
                worker_count_for_items(2).unwrap(),
                None,
                "2 items must not fan out"
            );
            assert_eq!(
                worker_count_for_items(9).unwrap(),
                None,
                "corpus-sized CGU stays serial"
            );
            assert_eq!(
                worker_count_for_items(31).unwrap(),
                None,
                "under 2 workers' worth of items"
            );
            // Genuinely large modules still fan out, bounded by items/16.
            assert!(
                worker_count_for_items(32).unwrap().is_some_and(|w| w >= 2),
                "32 items is two workers' worth"
            );
            assert!(
                worker_count_for_items(129)
                    .unwrap()
                    .is_some_and(|w| (2..=8).contains(&w)),
                "129 items yields at most items/16 workers"
            );
        });
    }

    /// The x86-64 encode default width grows by one worker per
    /// [`X86_ENCODE_DEFAULT_ITEMS_PER_WORKER`] functions past the first two; a
    /// configured limit and the shared policy keep the
    /// [`MIN_ITEMS_PER_WORKER`] bound alone.
    #[test]
    fn x86_encode_default_width_is_work_bounded_and_the_shared_policy_is_not() {
        for (items, shared_width, encode_default_width) in [
            (31, None, None),
            (32, Some(2), Some(2)),
            (129, Some(8), Some(2)),
            (299, Some(18), Some(2)),
            (400, Some(24), Some(4)),
            (2400, Some(24), Some(24)),
        ] {
            let shared = worker_count_for_items_with_limit(items, 24);
            assert_eq!(shared, shared_width, "shared width for {items} items");
            assert_eq!(
                x86_encode_width(items, shared, false),
                encode_default_width,
                "x86 encode default width for {items} items"
            );
            assert_eq!(
                x86_encode_width(items, shared, true),
                shared_width,
                "x86 encode configured width for {items} items"
            );
        }
        let narrow_host = worker_count_for_items_with_limit(400, 2);
        assert_eq!(x86_encode_width(400, narrow_host, false), Some(2));
        assert_eq!(x86_encode_width(400, None, false), None);
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
        assert_eq!(
            parse_input_byte_limit(None).unwrap(),
            DEFAULT_MAX_INPUT_BYTES
        );
        assert_eq!(parse_input_byte_limit(Some("1024")).unwrap(), 1024);
        for raw in ["0", "bad", "", "-1", "18446744073709551616"] {
            assert!(
                parse_input_byte_limit(Some(raw))
                    .unwrap_err()
                    .contains(TRUST_CG_MAX_INPUT_BYTES_ENV)
            );
        }
    }

    #[test]
    fn input_read_stops_after_limit_plus_one_bytes() {
        let mut stream = std::io::Cursor::new(vec![0; 1024]);
        let error = read_stream_bounded(&mut stream, Path::new("growing.tmbc"), 10).unwrap_err();
        assert_eq!(stream.position(), 11);
        assert!(error.contains("input limit of 10 bytes"));
        assert_eq!(
            read_stream_bounded(&b"1234567890"[..], Path::new("exact.tmbc"), 10).unwrap(),
            b"1234567890"
        );
    }

    #[test]
    fn input_byte_limit_honors_scoped_environment_overrides() {
        trust_cg_process_env::with_env_overrides(&[(TRUST_CG_MAX_INPUT_BYTES_ENV, "17")], || {
            assert_eq!(configured_input_byte_limit().unwrap(), 17);
        });
    }

    #[test]
    fn oversized_input_error_names_override_env() {
        let error = check_input_len(Path::new("huge.tmbc"), 11, 10).unwrap_err();
        assert!(error.contains("huge.tmbc"));
        assert!(error.contains(TRUST_CG_MAX_INPUT_BYTES_ENV));
    }
}
