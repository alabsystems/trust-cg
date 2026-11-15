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
//! current tree has a regenerated fixture for Rust 1.97.1 and the exact Trust
//! compiler that generated it, and the installed Trust compiler the workspace
//! now builds with is qualified for those same fixtures by running every
//! layout-gated test under it (`fixture_toolchain.rs`). An unrecognized compiler makes
//! those integration targets fail at compile time instead of running either
//! fixture. Ten targets also select separately generated ae9 Linux fixtures;
//! frontend roundtrip qualifies its existing inputs on that exact compiler and
//! target. Each integration target opts into this qualification explicitly.
//! A later exact compiler and target pair may also run the current corpus
//! unchanged once every kernel-JIT case has passed on it
//! (`qualifies_current_kernel_fixtures`).
//!
//! The gate is identity-based, not channel-based. Treating every stable
//! compiler as layout-compatible was unsound: Rust 1.97.1 already differs from
//! 1.95.0, and every Trust update must be qualified again before it is added.

use std::process::Command;

mod fixture_toolchain;

fn main() {
    println!("cargo::rustc-check-cfg=cfg(kernel_fixture_layout_matches)");
    println!("cargo::rustc-check-cfg=cfg(kernel_fixture_layout_current)");
    println!("cargo::rustc-check-cfg=cfg(kernel_fixture_layout_unknown)");
    println!("cargo::rustc-check-cfg=cfg(kernel_fixture_ae9_linux)");
    println!("cargo::rustc-check-cfg=cfg(kernel_fixture_layout_lint_only)");

    // Cargo names a lint driver in RUSTC_WORKSPACE_WRAPPER (`cargo clippy`,
    // `tippy`); a plain build sets neither wrapper, measured.
    let lint_driver = fixture_toolchain::lint_driver_from([
        std::env::var("RUSTC_WORKSPACE_WRAPPER").ok(),
        std::env::var("RUSTC_WRAPPER").ok(),
    ]);

    // Cargo (targo) always names the compiler for a build script.
    let rustc = std::env::var_os("RUSTC").expect("RUSTC is set by cargo for build scripts");
    let version = Command::new(&rustc)
        .arg("--version")
        .output()
        .ok()
        .filter(|o| o.status.success())
        .map(|o| String::from_utf8_lossy(&o.stdout).into_owned())
        .unwrap_or_default();

    let target = std::env::var("TARGET").unwrap_or_default();
    if fixture_toolchain::has_ae9_linux_kernel_fixtures(&version, &target) {
        println!("cargo::rustc-cfg=kernel_fixture_ae9_linux");
    }

    // Fail closed in the layout-sensitive integration targets. Ordinary
    // library builds remain available on an unknown compiler, but those tests
    // carry a compile_error rather than executing an incompatible repr(Rust)
    // fixture. The current fixture is certified for the release compiler and
    // the exact Trust compiler that generated it.
    //
    // LINT-ONLY (`kernel_fixture_layout_lint_only`). A lint driver
    // type-checks and emits metadata; it links no test binary, so it cannot
    // EXECUTE a frozen repr(Rust) layout fixture. Compiling these targets
    // under it is what lets the lint gate see them at all — before this,
    // eleven integration targets were simply unlintable on any compiler but
    // the certified ones, and the gate reported them NOT LINTED rather than
    // pretending they were covered.
    //
    // This does NOT widen the execution guard by one compiler. The targets
    // pair this cfg with a runtime refusal at their JIT entry, so a fixture
    // cannot run even if a lint driver were pressed into service as a codegen
    // wrapper. A certified or exactly qualified compiler is never demoted to
    // it (`fixture_toolchain::kernel_fixture_layout_cfg`).
    println!(
        "cargo::rustc-cfg={}",
        fixture_toolchain::kernel_fixture_layout_cfg(&version, &target, lint_driver)
    );

    // The compiler identity, the target ABI (the Linux kernel fixtures depend
    // on it), and whether a lint driver is in front of the compiler are the
    // only inputs that can change the answer.
    println!("cargo::rerun-if-env-changed=RUSTC");
    println!("cargo::rerun-if-env-changed=TARGET");
    println!("cargo::rerun-if-env-changed=RUSTC_WORKSPACE_WRAPPER");
    println!("cargo::rerun-if-env-changed=RUSTC_WRAPPER");
}
