// trust-cg-lift - boundary enforcement
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! ENFORCES that `trust-cg-lift` stays out of every production/gate path.
//!
//! # Why this is a test and not a comment
//!
//! `trust-cg-lift` is reachable only as a `dev-dependency` of
//! `trust-cg-codegen`. Dev-dependencies do not propagate, so no shipped binary,
//! output gate, or emitted artifact can contain this crate's decoder. That is a
//! genuinely load-bearing fact — it is the reason a decoder hole here is an
//! ORACLE-fidelity problem rather than a shipped-soundness problem.
//!
//! But it was, until this file existed, an INCIDENTAL fact: nothing stopped a
//! future edit from adding a normal `[dependencies]` edge and silently promoting
//! this decoder into the trusted path. `trust-cg-codegen/src/decode_check.rs`
//! already documents the intent to do exactly that ("ENC-5 (aarch64, AS lane)
//! instantiates the SAME trait against the fixed-width A64 decoder in
//! `trust-cg-lift`'s disasm surface — a clean seam, no plumbing change").
//!
//! Promoting this crate is allowed. Promoting it SILENTLY is not. This test
//! turns the boundary into something a change has to walk through deliberately.

use std::path::{Path, PathBuf};
use std::process::Command;

/// The crate under enforcement.
const CRATE: &str = "trust-cg-lift";

fn workspace_root() -> PathBuf {
    // `crates/trust-cg-lift` -> workspace root.
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("workspace root above crates/<crate>")
        .to_path_buf()
}

/// Run `cargo tree -i CRATE -e <edges>` and return the lines naming a package.
///
/// `cargo tree -i` prints the queried crate first, then its reverse
/// dependencies over the selected edge kinds. Cargo computes the edge kinds, so
/// this test does not re-implement dependency resolution.
fn reverse_deps(edges: &str) -> Vec<String> {
    let out = Command::new(env!("CARGO"))
        .args([
            "tree", "--invert", CRATE, "--edges", edges, "--prefix", "none",
        ])
        .current_dir(workspace_root())
        .output()
        .unwrap_or_else(|e| panic!("run cargo tree -e {edges}: {e}"));
    assert!(
        out.status.success(),
        "cargo tree -e {edges} failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8(out.stdout).expect("cargo tree output is utf-8");
    stdout
        .lines()
        .map(str::trim)
        .filter(|l| !l.is_empty())
        .map(|l| l.split_whitespace().next().unwrap_or(l).to_string())
        // Drop the queried crate itself; keep only its dependents.
        .filter(|name| name != CRATE)
        .collect()
}

/// The decoder must not be reachable over any edge that ends up in a built
/// artifact. `normal` and `build` both propagate; `dev` does not.
#[test]
fn trust_cg_lift_has_no_non_dev_dependents() {
    let dependents = reverse_deps("normal,build");
    assert!(
        dependents.is_empty(),
        "`{CRATE}` has gained a non-dev dependency edge from: {dependents:?}\n\n\
         This crate's AArch64 decoder is a DEVELOPMENT-TIME ORACLE. It is not a \
         trusted component, and its acceptance set has only ever been validated as \
         one. Before promoting it into a production or gate path (e.g. the ENC-5 \
         aarch64 `decode_check` instantiation), you must:\n\
           1. re-run the objdump differential over this decoder and record the \
              GHOST/MISMATCH counts at the promoting commit;\n\
           2. state what the gate now trusts it for, in \
              `src/disasm/aarch64.rs`'s module docs;\n\
           3. relax this test deliberately, with that rationale.\n\
         Refusing to decode is always acceptable; being silently promoted is not."
    );
}

/// Guard against the above passing VACUOUSLY.
///
/// If the crate were renamed, orphaned, or dropped from the workspace, `cargo
/// tree --invert` would report no dependents and the real assertion would pass
/// while checking nothing. Pin the dev edge that is supposed to exist.
#[test]
fn trust_cg_lift_is_still_reachable_as_a_dev_dependency() {
    let dependents = reverse_deps("dev");
    assert!(
        dependents.iter().any(|d| d == "trust-cg-codegen"),
        "expected `trust-cg-codegen` to depend on `{CRATE}` as a dev-dependency, but \
         cargo tree reports dependents {dependents:?}. If that edge really is gone, \
         this crate has no consumer and both tests here are vacuous — delete them \
         together with the crate, do not weaken them."
    );
}
