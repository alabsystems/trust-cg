// Regression tests for layout-sensitive kernel fixture selection.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

#[path = "../fixture_toolchain.rs"]
mod fixture_toolchain;

use fixture_toolchain::{FixtureToolchain, classify_fixture_toolchain};

#[test]
fn exact_rust_1_95_identity_selects_frozen_fixture() {
    assert_eq!(
        classify_fixture_toolchain("rustc 1.95.0 (59807616e 2026-04-14)\n"),
        FixtureToolchain::Rust195
    );
}

#[test]
fn pinned_rust_1_97_selects_regenerated_fixture() {
    assert_eq!(
        classify_fixture_toolchain("rustc 1.97.1 (8bab26f4f 2026-07-14)\n"),
        FixtureToolchain::Current
    );
}

#[test]
fn exact_trust_compiler_selects_regenerated_fixture() {
    assert_eq!(
        classify_fixture_toolchain("rustc 1.96.0-dev (94d61d9b6 2026-06-15)"),
        FixtureToolchain::Current
    );
}

#[test]
fn uncertified_compilers_are_unsupported() {
    for version in [
        "rustc 1.99.0-nightly (012345678 2026-07-22)",
        "rustc 1.99.0-dev (012345678 2026-07-22)",
        "rustc 1.98.0 (012345678 2026-08-01)",
    ] {
        assert_eq!(
            classify_fixture_toolchain(version),
            FixtureToolchain::Unsupported,
            "accepted {version}"
        );
    }
}

#[test]
fn missing_or_malformed_compiler_output_fails_closed() {
    for version in ["", "rustc", "1.95.0", "rustc 1.95.0"] {
        assert_eq!(
            classify_fixture_toolchain(version),
            FixtureToolchain::Unsupported,
            "accepted {version:?}"
        );
    }
}
