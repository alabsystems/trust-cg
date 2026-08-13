// trust-cg-codegen build script.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Emits `cfg(kernel_fixture_layout_matches)` only when the building rustc is
//! the exact stable release used to generate the frozen kernel fixtures.
//!
//! A family of kernel-verification e2e tests JIT-compiles a FROZEN trust-ir
//! snapshot (`include_str!("*.tir")`) that bakes the `repr(Rust)` layout of the
//! un-`repr`-annotated kernel types (Option/Result niches, enum discriminants,
//! field offsets) as literal constants. Those constants match the toolchain the
//! fixtures were generated under — stable 1.95 — and are compared against a
//! reference the test toolchain compiles fresh. Later stable releases and
//! rustc-master (the self-hosted `trustc` / nightly) reassigned those niches,
//! so selecting the frozen-old-layout JIT input with a different compiler can
//! corrupt the differential's values before the comparison. That is a stale-
//! fixture artifact, not a trust-cg backend defect. Every affected test in the
//! current tree has a regenerated fixture for the pinned Rust 1.97 release and
//! the exact Trust compiler that generated it. An unrecognized compiler makes
//! those integration targets fail at compile time instead of running either
//! fixture.
//!
//! The gate is identity-based, not channel-based. Treating every stable
//! compiler as layout-compatible was unsound: the repository's pinned Rust
//! 1.97.1 already differs from 1.95.0.

use std::process::Command;

mod fixture_toolchain;

fn main() {
    println!("cargo::rustc-check-cfg=cfg(kernel_fixture_layout_matches)");
    println!("cargo::rustc-check-cfg=cfg(kernel_fixture_layout_current)");
    println!("cargo::rustc-check-cfg=cfg(kernel_fixture_layout_unknown)");

    let rustc = std::env::var_os("RUSTC").unwrap_or_else(|| "rustc".into());
    let version = Command::new(&rustc)
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
        .unwrap_or_default();

    // Fail closed in the layout-sensitive integration targets. Ordinary
    // library builds remain available on an unknown compiler, but those tests
    // carry a compile_error rather than executing an incompatible repr(Rust)
    // fixture. The current fixture is certified for the release compiler and
    // the exact Trust compiler that generated it.
    match fixture_toolchain::classify_fixture_toolchain(&version) {
        fixture_toolchain::FixtureToolchain::Rust195 => {
            println!("cargo::rustc-cfg=kernel_fixture_layout_matches");
        }
        fixture_toolchain::FixtureToolchain::Current => {
            println!("cargo::rustc-cfg=kernel_fixture_layout_current");
        }
        fixture_toolchain::FixtureToolchain::Unsupported => {
            println!("cargo::rustc-cfg=kernel_fixture_layout_unknown");
        }
    }

    // Only the compiler identity can change the answer.
    println!("cargo::rerun-if-env-changed=RUSTC");
}
