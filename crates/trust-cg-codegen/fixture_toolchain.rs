// Exact compiler predicate for layout-sensitive kernel JIT fixtures.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

pub(crate) const RUST_1_95_FIXTURE_COMPILER: &str = "rustc 1.95.0 (59807616e 2026-04-14)";
pub(crate) const RUST_1_97_FIXTURE_COMPILER: &str = "rustc 1.97.1 (8bab26f4f 2026-07-14)";
pub(crate) const TRUST_FIXTURE_COMPILER: &str = "rustc 1.96.0-dev (94d61d9b6 2026-06-15)";
/// The installed Trust compiler the root workspace builds with
/// (`rust-toolchain.toml` `channel = "trust"`; owner directive 2026-09-28).
/// Qualified for the EXISTING current fixtures, not regenerated ones: all 118
/// tests of the eleven layout-gated targets (the 52 release capstones among
/// them) pass under it, each in its own process
/// (`reports/perf/2026-09-28-trust-321aaeda7-fixture-qualification/`). A
/// Trust update must re-run that qualification before it is added here.
pub(crate) const TRUST_321AAEDA7_FIXTURE_COMPILER: &str =
    "rustc 1.99.0-dev (321aaeda7 2026-09-17) (trustc 0.1.0)";

/// Exact compiler and target qualified for Linux kernel fixtures. Individual
/// targets select regenerated inputs or their qualified existing corpus.
pub(crate) fn has_ae9_linux_kernel_fixtures(rustc_version: &str, target: &str) -> bool {
    rustc_version.trim() == "rustc 1.99.0-dev (ae9c2c1da 2026-09-21) (trustc 0.1.0)"
        && target == "aarch64-unknown-linux-gnu"
}

/// Exact compiler and target pairs qualified to run the current kernel fixture
/// corpus unchanged: the `*.trust.tir` closures and the inline fixtures that
/// [`FixtureToolchain::Current`] selects. A pair is added only after every
/// case of every kernel-JIT target passed in its own process on it. Nothing
/// is regenerated, and the legacy selector below does not change. The Darwin
/// 450403669 build passed 118 of 118 cases
/// (`reports/perf/2026-09-28-trust-450403669-fixture-qualification/`), as did the
/// C6 build through the maintained complete-inventory runner
/// (`reports/perf/2026-10-28-trust-c6d3ebc20-fixture-qualification/`). The D460
/// build also passed the unchanged 118-case inventory
/// (`reports/perf/2026-10-29-trust-d460ce139-fixture-qualification/`).
/// The 29ebb build passed that same complete isolated inventory
/// (`reports/perf/2026-11-06-trust-29ebb403d-fixture-qualification/`).
const QUALIFIED_CURRENT_KERNEL_FIXTURES: &[(&str, &str)] = &[
    // All 118 unchanged cases passed; see the 2026-11-06 29ebb qualification report.
    (
        "rustc 1.101.0-dev (29ebb403d 2026-10-28) (trustc 0.12.0+g29ebb403d)",
        "aarch64-apple-darwin",
    ),
    (
        "rustc 1.99.0-dev (450403669 2026-09-24) (trustc 0.10.0+g450403669)",
        "aarch64-apple-darwin",
    ),
    (
        "rustc 1.101.0-dev (c6d3ebc20 2026-10-27) (trustc 0.11.0+gc6d3ebc20)",
        "aarch64-apple-darwin",
    ),
    (
        "rustc 1.101.0-dev (d460ce139 2026-10-28) (trustc 0.12.0+gd460ce139)",
        "aarch64-apple-darwin",
    ),
];

/// Whether this exact compiler and target qualified the current corpus.
pub(crate) fn qualifies_current_kernel_fixtures(rustc_version: &str, target: &str) -> bool {
    QUALIFIED_CURRENT_KERNEL_FIXTURES
        .iter()
        .any(|&(compiler, qualified_target)| {
            rustc_version.trim() == compiler && target == qualified_target
        })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum FixtureToolchain {
    Rust195,
    Current,
    Unsupported,
}

pub(crate) fn classify_fixture_toolchain(rustc_version: &str) -> FixtureToolchain {
    match rustc_version.trim() {
        RUST_1_95_FIXTURE_COMPILER => FixtureToolchain::Rust195,
        RUST_1_97_FIXTURE_COMPILER | TRUST_FIXTURE_COMPILER | TRUST_321AAEDA7_FIXTURE_COMPILER => {
            FixtureToolchain::Current
        }
        _ => FixtureToolchain::Unsupported,
    }
}

/// The layout cfg `build.rs` emits for the kernel-JIT fixture targets.
///
/// Order matters. A compiler the legacy selector or an exact
/// [`qualifies_current_kernel_fixtures`] pair certifies selects its corpus
/// whether or not a lint driver is in front of it, so a qualified compiler is
/// never demoted to the lint-only cfg. Only an uncertified compiler under a
/// lint driver gets `kernel_fixture_layout_lint_only`; any other compiler
/// gets `kernel_fixture_layout_unknown`, whose targets stop at their
/// `compile_error!`.
pub(crate) fn kernel_fixture_layout_cfg(
    rustc_version: &str,
    target: &str,
    lint_driver: bool,
) -> &'static str {
    match classify_fixture_toolchain(rustc_version) {
        FixtureToolchain::Rust195 => "kernel_fixture_layout_matches",
        FixtureToolchain::Current => "kernel_fixture_layout_current",
        FixtureToolchain::Unsupported
            if qualifies_current_kernel_fixtures(rustc_version, target) =>
        {
            "kernel_fixture_layout_current"
        }
        FixtureToolchain::Unsupported if lint_driver => "kernel_fixture_layout_lint_only",
        FixtureToolchain::Unsupported => "kernel_fixture_layout_unknown",
    }
}

/// Whether the compiler driver for this build is a LINT driver.
///
/// A lint driver (`clippy-driver`, `tippy-driver`) type-checks and emits
/// metadata; it produces no runnable test binary, so it cannot execute a
/// frozen `repr(Rust)` layout fixture. That is what makes it safe to compile
/// the layout-sensitive integration targets under an UNCERTIFIED compiler for
/// the purpose of linting them — and only for that purpose.
///
/// Cargo names the driver in `RUSTC_WORKSPACE_WRAPPER` (`cargo clippy`,
/// `tippy`); `RUSTC_WRAPPER` is checked too because a wrapper set there would
/// reach the same rustc invocations. A plain `cargo build`/`test` sets
/// neither, which is what keeps the ordinary path fail-closed.
///
/// The check is on the executable's FILE STEM, not a substring of the path: a
/// checkout that merely lives under a directory called `clippy-driver` must
/// not be mistaken for a lint run.
pub(crate) fn lint_driver_from(wrappers: impl IntoIterator<Item = Option<String>>) -> bool {
    wrappers.into_iter().flatten().any(|value| {
        matches!(
            std::path::Path::new(&value)
                .file_stem()
                .and_then(|stem| stem.to_str()),
            Some("clippy-driver" | "tippy-driver")
        )
    })
}
