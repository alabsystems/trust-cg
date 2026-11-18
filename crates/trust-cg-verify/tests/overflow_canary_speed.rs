// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//
//! Direct timing of the x86-64 signed-multiply-overflow model canary's check.
//!
//! `trust-cg-codegen`'s `validate_x86_overflow_expansion_canary` runs exactly
//! `OverflowExpansionValidator::signed_mul("x86-overflow-expand", 8,
//! DivisionFreeWideMul, X86_64).validate()` once per process
//! (OD-X86-OVERFLOW-CANARY-UNCONDITIONAL-20261112). That call is not memoized
//! below the codegen `OnceLock`, so each call here repeats the whole check:
//! obligation construction, tape compilation and the 65,536-tuple exhaustive
//! sweep.
//!
//! The timing test is `#[ignore]`d: it measures, it does not gate. Run it in a
//! release build:
//!
//! ```sh
//! scripts/trust_cargo.sh test --release --locked -p trust-cg-verify \
//!     --test overflow_canary_speed -- --ignored --nocapture
//! ```
//!
//! The verdict assertion runs in every mode, so a timing taken from a build in
//! which the canary does not verify is never printed.

use std::time::Instant;
use trust_cg_verify::pass_validators::{
    OverflowExpansion, OverflowExpansionValidator, PassValidation, PassValidator, TargetArch,
};

fn canary() -> OverflowExpansionValidator {
    OverflowExpansionValidator::signed_mul(
        "x86-overflow-expand",
        8,
        OverflowExpansion::DivisionFreeWideMul,
        TargetArch::X86_64,
    )
}

#[test]
fn canary_validator_verifies() {
    assert!(
        matches!(canary().validate(), PassValidation::Verified { .. }),
        "the fixed overflow canary must verify"
    );
}

#[test]
#[ignore = "timing measurement; run explicitly with --ignored --nocapture"]
fn overflow_canary_check_time() {
    const ITERATIONS: usize = 41;
    let mut samples_us: Vec<f64> = Vec::with_capacity(ITERATIONS);
    for _ in 0..ITERATIONS {
        let start = Instant::now();
        let verdict = canary().validate();
        let elapsed = start.elapsed();
        assert!(
            matches!(verdict, PassValidation::Verified { .. }),
            "the fixed overflow canary must verify, got {verdict:?}"
        );
        samples_us.push(elapsed.as_secs_f64() * 1e6);
    }
    let first = samples_us[0];
    let mut sorted = samples_us.clone();
    sorted.sort_by(f64::total_cmp);
    let median = sorted[ITERATIONS / 2];
    let min = sorted[0];
    let max = sorted[ITERATIONS - 1];
    println!(
        "overflow-canary-check: iterations={ITERATIONS} first_us={first:.1} \
         median_us={median:.1} min_us={min:.1} max_us={max:.1}"
    );
}
