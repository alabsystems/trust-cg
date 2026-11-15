// trust-cg-regalloc - Register allocation for Trust Codegen
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Deterministic work counts for the unit tests that bound cost growth
//! (ledger row L14-P6).
//!
//! The routines that replaced a quadratic scan charge one unit per element
//! they examine, and so do the primitive probes the replaced scans were built
//! from ([`crate::liveness::LiveInterval::is_live_at`] and
//! [`crate::liveness::LiveInterval::overlaps`]) and the scans kept as
//! fallbacks. A unit test measures a routine at 1x, 4x and 16x input and bounds
//! each 4x step; routing a caller back through the per-point scan multiplies
//! the charge by the input size and fails that bound. This is a regression
//! test of cost growth, not a complexity proof.
//!
//! Outside `cfg(test)` [`charge`] compiles to nothing.

#[cfg(test)]
thread_local! {
    static UNITS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Record `units` elements examined on this thread (tests only).
#[inline(always)]
pub(crate) fn charge(units: usize) {
    #[cfg(test)]
    UNITS.with(|total| total.set(total.get().saturating_add(units as u64)));
    #[cfg(not(test))]
    let _ = units;
}

/// Run `f` and return its result with the units it charged on this thread.
#[cfg(test)]
pub(crate) fn measure<R>(f: impl FnOnce() -> R) -> (R, u64) {
    let before = UNITS.with(std::cell::Cell::get);
    let result = f();
    (result, UNITS.with(std::cell::Cell::get) - before)
}

/// The largest growth of a work count across one 4x input step. Linear or
/// `n log n` growth stays near 4x; a quadratic scan approaches 16x.
#[cfg(test)]
pub(crate) const MAX_STEP_RATIO: f64 = 5.0;

/// Measure `work(size)` at `base`, `4 * base` and `16 * base` and assert that
/// no 4x step multiplies it by more than [`MAX_STEP_RATIO`].
#[cfg(test)]
pub(crate) fn assert_near_linear(probe: &str, base: usize, mut work: impl FnMut(usize) -> u64) {
    let sizes = [base, 4 * base, 16 * base];
    let counts: Vec<u64> = sizes.iter().map(|&size| work(size)).collect();
    for step in 0..2 {
        let (small, large) = (counts[step], counts[step + 1]);
        assert!(
            small > 0,
            "{probe}: no work charged at size {}",
            sizes[step]
        );
        let ratio = large as f64 / small as f64;
        assert!(
            ratio <= MAX_STEP_RATIO,
            "{probe}: work grew x{ratio:.2} from size {} to {} ({small} -> {large} units); \
             a 4x larger input may cost at most x{MAX_STEP_RATIO}",
            sizes[step],
            sizes[step + 1]
        );
    }
}
