//! Positive-evidence markers for the Darwin AArch64 bridge runner.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! libtest reports `ok` for a test that returned early exactly as it does for
//! one that checked its claim. Every test that
//! `scripts/check_darwin_aarch64_bridge.py` requires therefore calls [`record`]
//! at the point its claim has been asserted, and the runner credits a passed
//! test only when that test's own captured output carries a marker naming it.
//! A passed test without its marker fails the runner; it is never a pass.
//!
//! The marker says what was checked and whether the backend compiles behind it
//! ran with proof certificates (`certs=on`, the default lane) or with the
//! backend's `no-proof-certs` knob (`certs=off`, a proofs-off diagnostic). It
//! is testing-evidence bookkeeping, not a proof claim.
#![allow(dead_code)]

/// The line prefix the runner parses.
pub const MARKER: &str = "TCG_DARWIN_BRIDGE_POSITIVE";

/// What a test established before it recorded its marker.
#[derive(Clone, Copy, Debug)]
pub enum Evidence {
    /// A backend-built executable was linked, run, and its result checked.
    NativeRun,
    /// A backend compile (and link, where the test links) succeeded and its
    /// output was checked; nothing was run.
    Compiled,
    /// The backend refused the program with the diagnostic the test names.
    ExpectedRefusal,
    /// A compile-verdict corpus met its committed floor; nothing was run.
    CompileVerdict,
    /// A compile's counted fixed cost stayed within its bound; nothing was run.
    FixedCost,
    /// A pure unit check of test-side parsing; no backend compile.
    UnitCheck,
}

impl Evidence {
    fn label(self) -> &'static str {
        match self {
            Evidence::NativeRun => "native-run",
            Evidence::Compiled => "compiled",
            Evidence::ExpectedRefusal => "expected-refusal",
            Evidence::CompileVerdict => "compile-verdict",
            Evidence::FixedCost => "fixed-cost",
            Evidence::UnitCheck => "unit-check",
        }
    }
}

/// Whether the backend compiles behind the evidence carried proof certificates.
#[derive(Clone, Copy, Debug)]
pub enum Certs {
    /// The default lane: proof certificates required.
    On,
    /// The backend's `no-proof-certs` knob: a proofs-off diagnostic.
    Off,
    /// No backend compile is involved.
    None,
}

impl Certs {
    fn label(self) -> &'static str {
        match self {
            Certs::On => "on",
            Certs::Off => "off",
            Certs::None => "none",
        }
    }
}

/// Print this test's marker. libtest names each test's thread after the test,
/// with any `--test-threads` value, so the marker names the test that asserted
/// the claim; the runner also attributes it to that test's captured output.
pub fn record(evidence: Evidence, certs: Certs) {
    let thread = std::thread::current();
    let test = thread.name().unwrap_or("<unnamed>");
    println!(
        "{MARKER} kind={} certs={} test={test}",
        evidence.label(),
        certs.label()
    );
}
