// trust-cg-codegen/resource_limits.rs - Shared host resource limits
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Shared host resource limits for Trust Codegen-owned compilation paths.

use std::path::Path;

/// Environment variable controlling the maximum Rayon worker count used by
/// Trust Codegen-owned compilation fanout.
pub const TRUST_CG_MAX_PARALLELISM_ENV: &str = "TRUST_CG_MAX_PARALLELISM";

/// Environment variable controlling the maximum input file size accepted by
/// the trust_ir loader before reading the whole module into memory.
pub const TRUST_CG_MAX_INPUT_BYTES_ENV: &str = "TRUST_CG_MAX_INPUT_BYTES";

/// Floor for the regalloc+encode fanout when host memory cannot be determined.
///
/// This is the historical fixed cap. It is now a FLOOR rather than the value:
/// see [`memory_adaptive_parallelism_default`].
const DEFAULT_MAX_PARALLELISM: usize = 2;

/// Memory budgeted per concurrent regalloc+encode worker.
///
/// The fanout's peak footprint is dominated by one in-flight function's
/// liveness + interference + encode buffers. 1 GiB per worker is deliberately
/// generous: the point is to stay safe on small hosts, not to squeeze the last
/// worker out of a large one.
const PARALLELISM_MEMORY_BUDGET_PER_WORKER: u64 = 1024 * 1024 * 1024;

const DEFAULT_MAX_INPUT_BYTES: u64 = 512 * 1024 * 1024;

/// Effective Rayon worker count for a parallel operation over `item_count`
/// independent work items.
#[must_use]
pub fn worker_count_for_items(item_count: usize) -> Option<usize> {
    if item_count < 2 {
        return None;
    }
    let workers = configured_parallelism_limit().min(item_count);
    (workers >= 2).then_some(workers)
}

/// Effective Rayon worker count for the per-function PROOF-CERTIFICATE lane
/// (CT-7).
///
/// Unlike [`worker_count_for_items`] — whose conservative default cap of
/// [`DEFAULT_MAX_PARALLELISM`] bounds the memory-hungry regalloc+encode
/// fanout — the certificate lane is pure read-only CPU work over the shared
/// `&'static` verifier (small per-worker footprint, no I/O), and it is the
/// dominant proofs-on compile-time cost. Its default cap is therefore the
/// host's available parallelism. An EXPLICIT `TRUST_CG_MAX_PARALLELISM`
/// still bounds this lane exactly like every other fanout (the operator's
/// stated limit wins). Worker count never affects output: the cert lane
/// collects into a function-ordered vector, so the bundle is byte-identical
/// at any width (`test_x86_parallel_and_serial_multi_function_byte_identical`).
#[must_use]
pub fn verification_worker_count_for_items(item_count: usize) -> Option<usize> {
    if item_count < 2 {
        return None;
    }
    let available = std::thread::available_parallelism().map_or(1, usize::from);
    let cap = match std::env::var(TRUST_CG_MAX_PARALLELISM_ENV)
        .ok()
        .as_deref()
        .and_then(|value| value.trim().parse::<usize>().ok())
        .filter(|value| *value > 0)
    {
        Some(explicit) => explicit.min(available).max(1),
        None => available,
    };
    let workers = cap.min(item_count);
    (workers >= 2).then_some(workers)
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
    let available = std::thread::available_parallelism().map_or(1, usize::from);
    parse_parallelism_limit_with_default(
        std::env::var(TRUST_CG_MAX_PARALLELISM_ENV).ok().as_deref(),
        available,
        memory_adaptive_parallelism_default(available),
    )
}

/// Host-available memory in bytes, or `None` when it cannot be determined.
///
/// Uses `MemAvailable` (not `MemFree`): it is the kernel's own estimate of what
/// is obtainable without swapping, which is exactly the question here.
fn host_available_memory_bytes() -> Option<u64> {
    #[cfg(target_os = "linux")]
    {
        let meminfo = std::fs::read_to_string("/proc/meminfo").ok()?;
        for line in meminfo.lines() {
            if let Some(rest) = line.strip_prefix("MemAvailable:") {
                let kib: u64 = rest.split_whitespace().next()?.parse().ok()?;
                return Some(kib.saturating_mul(1024));
            }
        }
        None
    }
    #[cfg(not(target_os = "linux"))]
    {
        None
    }
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
/// `TRUST_CG_MAX_PARALLELISM` still wins (see
/// [`parse_parallelism_limit_with_default`]).
///
/// Worker count never affects output — the fanout collects into a
/// function-ordered vector, so artifacts are byte-identical at any width.
#[must_use]
fn memory_adaptive_parallelism_default(available_parallelism: usize) -> usize {
    let Some(mem) = host_available_memory_bytes() else {
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

/// Historical fixed-default resolution, retained so the pre-adaptive contract
/// stays pinned by tests. Production resolves through
/// [`parse_parallelism_limit_with_default`] with a host-adaptive default.
#[cfg(test)]
fn parse_parallelism_limit(raw: Option<&str>, available: usize) -> usize {
    parse_parallelism_limit_with_default(raw, available, DEFAULT_MAX_PARALLELISM)
}

/// Resolve the fanout width: an explicit operator limit always wins; otherwise
/// `default_limit` (host-adaptive in production) applies. Both are clamped to
/// host parallelism and to at least one worker.
fn parse_parallelism_limit_with_default(
    raw: Option<&str>,
    available: usize,
    default_limit: usize,
) -> usize {
    let available = available.max(1);
    let configured = raw
        .and_then(|value| value.trim().parse::<usize>().ok())
        .filter(|value| *value > 0)
        .unwrap_or(default_limit);
    configured.min(available).max(1)
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
        assert_eq!(parse_parallelism_limit(None, 64), DEFAULT_MAX_PARALLELISM);
        assert_eq!(parse_parallelism_limit(Some("999"), 4), 4);
        assert_eq!(parse_parallelism_limit(Some("1"), 64), 1);
        assert_eq!(
            parse_parallelism_limit(Some("bad"), 64),
            DEFAULT_MAX_PARALLELISM
        );
        assert_eq!(
            parse_parallelism_limit(Some("0"), 64),
            DEFAULT_MAX_PARALLELISM
        );
    }

    #[test]
    fn worker_count_disables_parallelism_below_two_workers() {
        assert_eq!(worker_count_for_items(0), None);
        assert_eq!(worker_count_for_items(1), None);
    }

    /// An explicit operator limit ALWAYS wins over the host-adaptive default —
    /// including when it is lower. A machine-derived default must never be able
    /// to exceed a stated limit.
    #[test]
    fn explicit_parallelism_limit_overrides_adaptive_default() {
        assert_eq!(parse_parallelism_limit_with_default(Some("3"), 64, 32), 3);
        assert_eq!(parse_parallelism_limit_with_default(Some("1"), 64, 32), 1);
        // Explicit above host parallelism still clamps to the host.
        assert_eq!(parse_parallelism_limit_with_default(Some("999"), 8, 2), 8);
        // No explicit limit -> the adaptive default, clamped to the host.
        assert_eq!(parse_parallelism_limit_with_default(None, 64, 12), 12);
        assert_eq!(parse_parallelism_limit_with_default(None, 4, 12), 4);
        // Invalid/zero explicit values fall back to the adaptive default.
        assert_eq!(parse_parallelism_limit_with_default(Some("bad"), 64, 9), 9);
        assert_eq!(parse_parallelism_limit_with_default(Some("0"), 64, 9), 9);
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
        let Some(mem) = host_available_memory_bytes() else {
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
