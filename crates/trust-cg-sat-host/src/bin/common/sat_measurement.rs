// Shared measurement lifecycle for the SAT benchmark drivers.
// Timings are observations, not proof or eligible performance headlines by themselves.

use std::sync::atomic::Ordering;
use std::time::{Duration, Instant};
use trust_cg_sat_host::propagate::{
    JIT_ANALYZE_DRIVEN, JIT_ANALYZE_DRIVER_CLAUSE_AGREEMENTS, JIT_ANALYZE_DRIVER_FORCE,
    JIT_ANALYZE_DRIVER_NATIVE_SKIPS, JIT_DIVERGENCE_COUNT, JIT_INIT_COUNT, JIT_PRIMARY_RETURNS,
    PRIMARY_JIT_MODE, PROPAGATE_CALL_COUNT, SHADOW_MODE,
};
use trust_cg_sat_host::sys;

pub type AnyError = Box<dyn std::error::Error + Send + Sync + 'static>;

pub fn bench_err(message: impl Into<String>) -> AnyError {
    message.into().into()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolveMode {
    Native,
    Shadow,
    Primary { analyze_driver: bool },
}

/// The benchmark drivers pin the watched-literal provider. Keep its optional
/// disk tier out of memory-only measurements, restoring the caller's setting.
pub struct DiskBackingGuard(bool);

impl DiskBackingGuard {
    pub fn enter(enabled: bool) -> Self {
        use trust_cg_jit_matrix::jit_compile_cache::JIT_BCP_WATCHED_LITERAL_CACHE;
        JIT_BCP_WATCHED_LITERAL_CACHE.with(|cache| {
            let mut cache = cache.borrow_mut();
            let previous = cache.disk_backed();
            cache.set_disk_backed(enabled);
            Self(previous)
        })
    }
}

impl Drop for DiskBackingGuard {
    fn drop(&mut self) {
        use trust_cg_jit_matrix::jit_compile_cache::JIT_BCP_WATCHED_LITERAL_CACHE;
        JIT_BCP_WATCHED_LITERAL_CACHE.with(|cache| cache.borrow_mut().set_disk_backed(self.0));
    }
}

pub fn require_memory_primed() -> Result<(), AnyError> {
    use trust_cg_jit_matrix::jit_compile_cache::JIT_BCP_WATCHED_LITERAL_CACHE;
    if JIT_BCP_WATCHED_LITERAL_CACHE.with(|cache| cache.borrow().is_empty()) {
        return Err(bench_err(
            "memory priming produced no provider; refusing a memory-primed row",
        ));
    }
    Ok(())
}

/// One benchmark-owned directory, selected only for this executable's disk
/// section. This driver runs sequentially and must not overlap root overrides.
/// Clear operations target the owned directory, never a resolved user cache.
pub struct DiskCacheWorkspace {
    directory: tempfile::TempDir,
}

impl DiskCacheWorkspace {
    pub fn new() -> Result<Self, AnyError> {
        use trust_cg_jit_matrix::jit_disk_cache::{
            disk_lookup, disk_store, set_disk_cache_root_for_tests,
        };
        let workspace = Self {
            directory: tempfile::Builder::new()
                .prefix("trust-cg-sat-bench-")
                .tempdir()?,
        };
        // The IR-text disk cache is used only below a directory no other
        // user can write (`0777 & !umask` otherwise); the I/O control below
        // fails on one it ignores.
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            std::fs::set_permissions(
                workspace.directory.path(),
                std::fs::Permissions::from_mode(0o700),
            )?;
        }
        set_disk_cache_root_for_tests(Some(workspace.directory.path().to_path_buf()));
        workspace.require_selected()?;
        // Exercise the actual cache I/O and ambient-policy gates before
        // labeling anything disk-primed. This is not a solver/proof control.
        disk_store(0, "benchmark-io-control", "benchmark cache I/O control");
        if disk_lookup(0, "benchmark-io-control").as_deref() != Some("benchmark cache I/O control")
        {
            return Err(bench_err(
                "isolated disk-cache control failed; cache policy or I/O is unavailable",
            ));
        }
        workspace.clear()?;
        Ok(workspace)
    }

    fn require_selected(&self) -> Result<(), AnyError> {
        if trust_cg_jit_matrix::jit_disk_cache::disk_cache_dir().as_deref()
            != Some(self.directory.path())
        {
            return Err(bench_err(
                "benchmark disk-cache root changed; refusing cache access",
            ));
        }
        Ok(())
    }

    pub fn clear(&self) -> Result<(), AnyError> {
        self.require_selected()?;
        for entry in std::fs::read_dir(self.directory.path())? {
            // No recursion or ambient path resolution: these are files in
            // the TempDir this benchmark created and exclusively owns.
            std::fs::remove_file(entry?.path())?;
        }
        Ok(())
    }

    pub fn require_primed(&self) -> Result<(), AnyError> {
        self.require_selected()?;
        if trust_cg_jit_matrix::jit_disk_cache::disk_cache_file_count() == 0 {
            return Err(bench_err(
                "disk priming produced no cache artifact; refusing a disk-primed row",
            ));
        }
        Ok(())
    }
}

impl Drop for DiskCacheWorkspace {
    fn drop(&mut self) {
        use trust_cg_jit_matrix::jit_disk_cache::{disk_cache_dir, set_disk_cache_root_for_tests};
        if disk_cache_dir().as_deref() == Some(self.directory.path()) {
            set_disk_cache_root_for_tests(None);
        }
        // TempDir removes only the benchmark-owned artifacts.
    }
}

/// Telemetry snapshot harvested across one measurement lane. The counters are process-global so callers diff before/after
/// to attribute the JIT firing behaviour to the just-completed
/// fixture. See `propagate.rs` for the canonical definitions.
#[derive(Default, Clone, Copy, Debug)]
pub struct SolveTelemetry {
    pub propagate_calls: u64,
    pub jit_inits: u64,
    pub jit_primary_events: u64,
    pub jit_divergences: u64,
    pub jit_analyze_driven: u64,
    pub jit_clause_shortcuts: u64,
    pub jit_reserved_native_skips: u64,
}

fn snapshot_telemetry() -> SolveTelemetry {
    SolveTelemetry {
        propagate_calls: PROPAGATE_CALL_COUNT.load(Ordering::SeqCst),
        jit_inits: JIT_INIT_COUNT.load(Ordering::SeqCst),
        jit_primary_events: JIT_PRIMARY_RETURNS.load(Ordering::SeqCst),
        jit_divergences: JIT_DIVERGENCE_COUNT.load(Ordering::SeqCst),
        jit_analyze_driven: JIT_ANALYZE_DRIVEN.load(Ordering::SeqCst),
        jit_clause_shortcuts: JIT_ANALYZE_DRIVER_CLAUSE_AGREEMENTS.load(Ordering::SeqCst),
        jit_reserved_native_skips: JIT_ANALYZE_DRIVER_NATIVE_SKIPS.load(Ordering::SeqCst),
    }
}

fn exact_count_delta(name: &str, before: u64, after: u64) -> Result<u64, AnyError> {
    if after == u64::MAX {
        return Err(bench_err(format!(
            "{name} saturated; an exact benchmark rate is unavailable"
        )));
    }
    after.checked_sub(before).ok_or_else(|| {
        bench_err(format!(
            "{name} regressed during measurement: {before} -> {after}"
        ))
    })
}

fn telemetry_delta(
    before: &SolveTelemetry,
    after: &SolveTelemetry,
) -> Result<SolveTelemetry, AnyError> {
    Ok(SolveTelemetry {
        propagate_calls: exact_count_delta(
            "propagate calls",
            before.propagate_calls,
            after.propagate_calls,
        )?,
        jit_inits: exact_count_delta("JIT initializations", before.jit_inits, after.jit_inits)?,
        jit_primary_events: exact_count_delta(
            "primary events",
            before.jit_primary_events,
            after.jit_primary_events,
        )?,
        jit_divergences: exact_count_delta(
            "divergences",
            before.jit_divergences,
            after.jit_divergences,
        )?,
        jit_analyze_driven: exact_count_delta(
            "analyze-driver events",
            before.jit_analyze_driven,
            after.jit_analyze_driven,
        )?,
        jit_clause_shortcuts: exact_count_delta(
            "clause shortcuts",
            before.jit_clause_shortcuts,
            after.jit_clause_shortcuts,
        )?,
        jit_reserved_native_skips: exact_count_delta(
            "reserved native skips",
            before.jit_reserved_native_skips,
            after.jit_reserved_native_skips,
        )?,
    })
}

/// This executable measures one lane at a time. Restore process-global modes
/// on success, workload error, or unwind; controls must serialize their use.
struct ModeGuard {
    primary: bool,
    shadow: bool,
    force: bool,
}

impl ModeGuard {
    fn enter(mode: SolveMode) -> Self {
        let (primary, shadow, force) = match mode {
            SolveMode::Native => (false, false, false),
            SolveMode::Shadow => (false, true, false),
            SolveMode::Primary { analyze_driver } => (true, false, analyze_driver),
        };
        Self {
            primary: PRIMARY_JIT_MODE.swap(primary, Ordering::SeqCst),
            shadow: SHADOW_MODE.swap(shadow, Ordering::SeqCst),
            force: JIT_ANALYZE_DRIVER_FORCE.swap(force, Ordering::SeqCst),
        }
    }
}

impl Drop for ModeGuard {
    fn drop(&mut self) {
        JIT_ANALYZE_DRIVER_FORCE.store(self.force, Ordering::SeqCst);
        SHADOW_MODE.store(self.shadow, Ordering::SeqCst);
        PRIMARY_JIT_MODE.store(self.primary, Ordering::SeqCst);
    }
}

pub fn require_matching_verdict(label: &str, expected: i32, actual: i32) -> Result<(), AnyError> {
    if !matches!(actual, sys::SAT | sys::UNSAT) || actual != expected {
        return Err(bench_err(format!(
            "rc mismatch on {label}: expected={expected} actual={actual}"
        )));
    }
    Ok(())
}

/// Shared measurement boundary. Only workload preparation and execution are
/// injected for controls; mode selection, timing, and telemetry are the same
/// code used by every solve lane in both benchmark drivers.
pub fn measure(
    mode: SolveMode,
    repetitions: usize,
    warmup: bool,
    mut prepare: impl FnMut() -> Result<(), AnyError>,
    mut solve: impl FnMut() -> Result<i32, AnyError>,
) -> Result<(Vec<Duration>, i32, SolveTelemetry), AnyError> {
    if repetitions == 0 {
        return Err(bench_err(
            "solve measurement requires at least one repetition",
        ));
    }
    let _modes = ModeGuard::enter(mode);
    let mut expected_rc = None;
    if warmup {
        prepare()?;
        let rc = solve()?;
        require_matching_verdict("solve warmup", rc, rc)?;
        expected_rc = Some(rc);
    }
    // Timing and telemetry both exclude warmup. Per-solve denominators below
    // are exactly `repetitions`, not `repetitions + warmup`.
    let before = snapshot_telemetry();
    let mut samples = Vec::with_capacity(repetitions);
    for _ in 0..repetitions {
        prepare()?;
        let t0 = Instant::now();
        let rc = solve()?;
        let elapsed = t0.elapsed();
        require_matching_verdict("solve repetition", expected_rc.unwrap_or(rc), rc)?;
        expected_rc = Some(rc);
        samples.push(elapsed);
    }
    let after = snapshot_telemetry();
    let rc = expected_rc.ok_or_else(|| bench_err("solve measurement produced no verdict"))?;
    Ok((samples, rc, telemetry_delta(&before, &after)?))
}

/// Primary-lane adapter for infallible cache preparation.
pub fn measure_primary_jit(
    force: bool,
    repetitions: usize,
    warmup: bool,
    mut prepare: impl FnMut(),
    solve: impl FnMut() -> Result<i32, AnyError>,
) -> Result<(Vec<Duration>, i32, SolveTelemetry), AnyError> {
    measure(
        SolveMode::Primary {
            analyze_driver: force,
        },
        repetitions,
        warmup,
        || {
            prepare();
            Ok(())
        },
        solve,
    )
}

#[cfg(test)]
pub(crate) mod test_support {
    pub static MODE_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
}

#[cfg(test)]
mod measurement_tests {
    use super::test_support::MODE_LOCK;
    use super::*;
    use std::cell::Cell;

    // Keep independent cleanup even when a deliberately armed control panics.
    struct RestoreModes(bool, bool, bool);

    impl RestoreModes {
        fn set(primary: bool, shadow: bool, force: bool) -> Self {
            Self(
                PRIMARY_JIT_MODE.swap(primary, Ordering::SeqCst),
                SHADOW_MODE.swap(shadow, Ordering::SeqCst),
                JIT_ANALYZE_DRIVER_FORCE.swap(force, Ordering::SeqCst),
            )
        }
    }

    impl Drop for RestoreModes {
        fn drop(&mut self) {
            PRIMARY_JIT_MODE.store(self.0, Ordering::SeqCst);
            SHADOW_MODE.store(self.1, Ordering::SeqCst);
            JIT_ANALYZE_DRIVER_FORCE.store(self.2, Ordering::SeqCst);
        }
    }

    fn modes() -> (bool, bool, bool) {
        (
            PRIMARY_JIT_MODE.load(Ordering::SeqCst),
            SHADOW_MODE.load(Ordering::SeqCst),
            JIT_ANALYZE_DRIVER_FORCE.load(Ordering::SeqCst),
        )
    }

    const SOLVE_MODES: [SolveMode; 4] = [
        SolveMode::Native,
        SolveMode::Shadow,
        SolveMode::Primary {
            analyze_driver: false,
        },
        SolveMode::Primary {
            analyze_driver: true,
        },
    ];

    #[test]
    fn every_lane_selects_and_restores_modes_from_every_ambient_combination() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        for bits in 0..8 {
            let initial = (bits & 1 != 0, bits & 2 != 0, bits & 4 != 0);
            let _restore = RestoreModes::set(initial.0, initial.1, initial.2);
            for mode in SOLVE_MODES {
                let expected = match mode {
                    SolveMode::Native => (false, false, false),
                    SolveMode::Shadow => (false, true, false),
                    SolveMode::Primary { analyze_driver } => (true, false, analyze_driver),
                };
                for warmup in [false, true] {
                    let (samples, rc, _) = measure(
                        mode,
                        2,
                        warmup,
                        || Ok(()),
                        || {
                            assert_eq!(modes(), expected);
                            Ok(sys::SAT)
                        },
                    )
                    .unwrap();
                    assert_eq!(samples.len(), 2);
                    assert_eq!(rc, sys::SAT);
                    assert_eq!(modes(), initial);
                }
            }
        }
    }

    #[test]
    fn preparation_failure_never_executes_a_sample_or_leaks_modes() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(true, true, true);
        for mode in SOLVE_MODES {
            for warmup in [false, true] {
                let calls = Cell::new(0);
                let result = measure(
                    mode,
                    2,
                    warmup,
                    || Err(bench_err("injected cache-preparation error")),
                    || {
                        calls.set(calls.get() + 1);
                        Ok(sys::SAT)
                    },
                );
                assert!(result.is_err());
                assert_eq!(calls.get(), 0);
                assert_eq!(modes(), (true, true, true));
            }
        }
    }

    #[test]
    fn every_lane_rejects_a_disagreeing_or_invalid_repetition() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(true, true, true);
        for mode in SOLVE_MODES {
            for bad in [sys::UNSAT, 2, -1] {
                for warmup in [false, true] {
                    let mut outcomes = [sys::SAT, bad, sys::SAT].into_iter();
                    assert!(
                        measure(
                            mode,
                            3,
                            warmup,
                            || Ok(()),
                            || Ok(outcomes.next().unwrap_or(sys::SAT))
                        )
                        .is_err()
                    );
                    assert_eq!(modes(), (true, true, true));
                }
            }
        }
    }

    #[test]
    fn telemetry_regression_returns_an_error_instead_of_wrapping_or_panicking() {
        let before = SolveTelemetry {
            propagate_calls: 2,
            ..Default::default()
        };
        let after = SolveTelemetry {
            propagate_calls: 1,
            ..Default::default()
        };
        assert!(telemetry_delta(&before, &after).is_err());
    }

    #[test]
    fn saturated_telemetry_cannot_be_published_as_an_exact_rate() {
        let before = SolveTelemetry {
            jit_primary_events: u64::MAX - 1,
            ..Default::default()
        };
        let after = SolveTelemetry {
            jit_primary_events: u64::MAX,
            ..Default::default()
        };
        assert!(telemetry_delta(&before, &after).is_err());
    }

    #[test]
    fn disk_backing_setting_is_restored_after_nested_scopes_and_unwind() {
        use trust_cg_jit_matrix::jit_compile_cache::JIT_BCP_WATCHED_LITERAL_CACHE;
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let initial = JIT_BCP_WATCHED_LITERAL_CACHE.with(|c| c.borrow().disk_backed());
        let result = std::panic::catch_unwind(|| {
            let _outer = DiskBackingGuard::enter(false);
            {
                let _inner = DiskBackingGuard::enter(true);
                assert!(JIT_BCP_WATCHED_LITERAL_CACHE.with(|c| c.borrow().disk_backed()));
            }
            assert!(!JIT_BCP_WATCHED_LITERAL_CACHE.with(|c| c.borrow().disk_backed()));
            panic!("injected disk-policy unwind");
        });
        assert!(result.is_err());
        assert_eq!(
            JIT_BCP_WATCHED_LITERAL_CACHE.with(|c| c.borrow().disk_backed()),
            initial
        );
    }

    #[test]
    fn isolated_disk_controls_require_real_io_and_a_priming_artifact() {
        use trust_cg_jit_matrix::jit_disk_cache::{disk_lookup, disk_store};
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let workspace = DiskCacheWorkspace::new().unwrap();
        let owned = workspace.directory.path().to_path_buf();
        assert!(workspace.require_primed().is_err());
        disk_store(7, "test-priming", "control payload");
        assert_eq!(
            disk_lookup(7, "test-priming").as_deref(),
            Some("control payload")
        );
        workspace.require_primed().unwrap();
        workspace.clear().unwrap();
        assert!(workspace.require_primed().is_err());
        drop(workspace);
        assert!(!owned.exists());
    }

    #[test]
    fn changed_disk_root_cannot_redirect_owned_cache_cleanup() {
        use trust_cg_jit_matrix::jit_disk_cache::set_disk_cache_root_for_tests;
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let workspace = DiskCacheWorkspace::new().unwrap();
        let foreign = tempfile::tempdir().unwrap();
        let sentinel = foreign.path().join("preserve.trust_ir");
        std::fs::write(&sentinel, b"preserve this unrelated cache").unwrap();
        set_disk_cache_root_for_tests(Some(foreign.path().to_path_buf()));
        assert!(workspace.clear().is_err());
        assert!(workspace.require_primed().is_err());
        drop(workspace);
        set_disk_cache_root_for_tests(None);
        assert_eq!(
            std::fs::read(sentinel).unwrap(),
            b"preserve this unrelated cache"
        );
    }

    #[test]
    fn selected_modes_are_distinct_and_restored() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(false, false, true);
        for force in [false, true] {
            let result = measure_primary_jit(
                force,
                2,
                true,
                || {},
                || {
                    assert_eq!(modes(), (true, false, force));
                    Ok(sys::SAT)
                },
            );
            assert!(result.is_ok());
            assert_eq!(modes(), (false, false, true));
        }
    }

    #[test]
    fn warmup_is_excluded_from_measured_telemetry() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(false, false, true);
        for warmup in [false, true] {
            let prepares = Cell::new(0);
            let solves = Cell::new(0);
            let (samples, rc, telemetry) = measure_primary_jit(
                true,
                2,
                warmup,
                || prepares.set(prepares.get() + 1),
                || {
                    solves.set(solves.get() + 1);
                    PROPAGATE_CALL_COUNT.fetch_add(1, Ordering::SeqCst);
                    JIT_PRIMARY_RETURNS.fetch_add(1, Ordering::SeqCst);
                    Ok(sys::SAT)
                },
            )
            .unwrap();
            assert_eq!(solves.get(), 2 + usize::from(warmup));
            assert_eq!(prepares.get(), solves.get());
            assert_eq!(samples.len(), 2);
            assert_eq!(rc, sys::SAT);
            assert_eq!(telemetry.propagate_calls, 2);
            assert_eq!(telemetry.jit_primary_events, 2);
        }
    }

    #[test]
    fn workload_errors_restore_modes_including_shadow() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(false, true, false);
        for warmup in [false, true] {
            let result = measure_primary_jit(
                true,
                2,
                warmup,
                || {},
                || Err(bench_err("injected workload error")),
            );
            assert!(result.is_err());
            assert_eq!(modes(), (false, true, false));
        }
    }

    #[test]
    fn primary_measurement_disables_shadow_and_restores_prior_primary() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(true, true, false);
        measure_primary_jit(
            true,
            1,
            false,
            || {},
            || {
                assert_eq!(modes(), (true, false, true));
                Ok(sys::SAT)
            },
        )
        .unwrap();
        assert_eq!(modes(), (true, true, false));
    }

    #[test]
    fn inconsistent_verdicts_are_not_hidden_by_the_final_repetition() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(false, false, true);
        for warmup in [false, true] {
            let mut outcomes = [sys::SAT, sys::UNSAT, sys::SAT].into_iter();
            let result = measure_primary_jit(
                true,
                3,
                warmup,
                || {},
                || Ok(outcomes.next().unwrap_or(sys::SAT)),
            );
            assert!(
                result.is_err(),
                "a later matching verdict cannot erase a mismatch"
            );
        }
    }

    #[test]
    fn zero_repetitions_cannot_publish_a_measurement() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(false, false, true);
        assert!(measure_primary_jit(true, 0, false, || {}, || Ok(sys::SAT)).is_err());
    }

    #[test]
    fn invalid_or_disagreeing_verdicts_reject_both_primary_columns() {
        for label in ["root-only vs native", "analyze-driver vs native"] {
            for expected in [sys::SAT, sys::UNSAT] {
                assert!(require_matching_verdict(label, expected, expected).is_ok());
                assert!(require_matching_verdict(label, expected, 1 - expected).is_err());
            }
            assert!(require_matching_verdict(label, 2, 2).is_err());
        }
    }

    #[test]
    fn workload_unwind_restores_modes() {
        let _lock = MODE_LOCK.lock().unwrap_or_else(|e| e.into_inner());
        let _restore = RestoreModes::set(false, true, false);
        for warmup in [false, true] {
            let result = std::panic::catch_unwind(|| {
                let _ = measure_primary_jit(
                    true,
                    1,
                    warmup,
                    || {},
                    || {
                        panic!("injected measurement unwind");
                    },
                );
            });
            assert!(result.is_err());
            assert_eq!(modes(), (false, true, false));
        }
    }
}
