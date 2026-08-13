// Exact compiler predicate for layout-sensitive kernel JIT fixtures.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

pub(crate) const RUST_1_95_FIXTURE_COMPILER: &str = "rustc 1.95.0 (59807616e 2026-04-14)";
pub(crate) const RUST_1_97_FIXTURE_COMPILER: &str = "rustc 1.97.1 (8bab26f4f 2026-07-14)";
pub(crate) const TRUST_FIXTURE_COMPILER: &str = "rustc 1.96.0-dev (94d61d9b6 2026-06-15)";

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FixtureToolchain {
    Rust195,
    Current,
    Unsupported,
}

pub(crate) fn classify_fixture_toolchain(rustc_version: &str) -> FixtureToolchain {
    match rustc_version.trim() {
        RUST_1_95_FIXTURE_COMPILER => FixtureToolchain::Rust195,
        RUST_1_97_FIXTURE_COMPILER | TRUST_FIXTURE_COMPILER => FixtureToolchain::Current,
        _ => FixtureToolchain::Unsupported,
    }
}
