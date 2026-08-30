// trust-cg-codegen/tests/common/skip.rs - the one loud test-skip line
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! The single loud line an integration test prints before it returns early
//! because an EXTERNAL authority it needs is absent (the host architecture,
//! a C compiler). `SKIP <test>: <reason>` on stderr, grep-able; the caller
//! keeps its own `return`, so which tests skip, and when, is unchanged.

use std::process::Command;

/// Print the uniform skip line.
pub fn skip_test(test: &str, reason: &str) {
    eprintln!("SKIP {test}: {reason}");
}

/// The aarch64 link-and-run gate: `true` when the host is aarch64 AND `cc`
/// answers `--version`; otherwise prints the skip line naming the missing
/// authority and returns `false` so the caller can `return`.
pub fn aarch64_linkrun_or_skip(test: &str) -> bool {
    if !cfg!(target_arch = "aarch64") {
        skip_test(
            test,
            "aarch64-only link-and-run e2e on a non-aarch64 host (run on an aarch64 host to run)",
        );
        return false;
    }
    let has_cc = Command::new("cc")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    if !has_cc {
        skip_test(test, "no C compiler on PATH (install cc to run)");
        return false;
    }
    true
}
