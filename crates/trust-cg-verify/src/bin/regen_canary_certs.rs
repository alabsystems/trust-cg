// trust-cg-verify/bin/regen_canary_certs.rs - Canary CERT-SKIP cert regen tool
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Offline builder for the repo-committed canary DRAT certificates
//! (`verdict_db/canary_certs/*.lratcert`), consumed by the per-compile
//! CERT-SKIP tier (`trust_cg_verify::canary_cert`).
//!
//! For each certifiable canary obligation (currently: the popcnt SWAR
//! width-32 canary — the ~16 s/process live solve) this tool:
//!
//!  1. re-proves the obligation `unsat` with a LIVE run of the real `ay`
//!     (bit-blasting the exact per-compile SMT2 bytes to a DIMACS CNF),
//!  2. has ay emit a DRAT refutation of that CNF,
//!  3. trims the proof to its optimized core (`drat-trim -O -l`), and
//!  4. INDEPENDENTLY re-checks the trimmed proof with the vendored
//!     `drat-trim` before writing anything.
//!
//! Writes NOTHING for an obligation that does not prove + independently
//! check. After regenerating, rebuild (the certs are embedded via
//! `include_str!`) and commit the new `.lratcert` files; regen both artifacts
//! together with `regen_verdict_db` when the solver changes.
//!
//! Run on a QUIET machine: the recorded SMT2 embeds the pinned 30 s solver
//! budget, and the offline solve must fit it.
//!
//! Usage (from the repo):
//!
//! ```text
//! cargo run --release -p trust-cg-verify --bin regen_canary_certs [out-dir]
//! ```

use std::path::PathBuf;

fn main() {
    // Default output: the committed cert dir inside this crate's source tree.
    let default_out = concat!(env!("CARGO_MANIFEST_DIR"), "/verdict_db/canary_certs");
    let out_dir: PathBuf = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(default_out));

    eprintln!(
        "regen_canary_certs: proving + certifying the canary obligations with a live solver..."
    );
    let started = std::time::Instant::now();
    match trust_cg_verify::canary_cert::regen_canary_certs(&out_dir) {
        Ok(report) => {
            eprintln!(
                "regen_canary_certs: OK in {:.1}s — {} cert(s) written to {}",
                started.elapsed().as_secs_f64(),
                report.certs.len(),
                out_dir.display(),
            );
            eprintln!("  solver: {}", report.solver_path);
            eprintln!("  solver-sha256: {}", report.solver_identity);
            for (name, len) in &report.certs {
                eprintln!("  cert: {name} ({len} bytes)");
            }
            eprintln!(
                "regen_canary_certs: rebuild trust-cg-verify (certs are embedded via \
                 include_str!) and commit the new .lratcert file(s)"
            );
        }
        Err(e) => {
            eprintln!("regen_canary_certs: FAILED — nothing committed: {e}");
            std::process::exit(1);
        }
    }
}
