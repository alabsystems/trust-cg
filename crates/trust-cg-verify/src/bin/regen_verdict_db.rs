// trust-cg-verify/bin/regen_verdict_db.rs - Tier-0 verdict DB regen tool (PROOF-3)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Offline builder for the repo-committed tier-0 verdict DB.
//!
//! Re-proves every fixed, program-independent seed obligation (the popcnt
//! SWAR width-32 canary + the four guard-carrier expansion canaries at
//! widths 32/64) with a LIVE run of the real `ay` solver, and rewrites
//! `crates/trust-cg-verify/verdict_db/tier0.vdb` deterministically. Writes
//! NOTHING unless every seed discharges `Verified`. See
//! `verdict_db/README.md` for the trust story and
//! `trust_cg_verify::verdict_db::regen_tier0_db` for the mechanism.
//!
//! Usage (from the repo):
//!
//! ```text
//! cargo run --release -p trust-cg-verify --bin regen_verdict_db [out-path]
//! ```

use std::path::PathBuf;

fn main() {
    // Default output: the committed DB inside this crate's source tree.
    let default_out = concat!(env!("CARGO_MANIFEST_DIR"), "/verdict_db/tier0.vdb");
    let out_path: PathBuf = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(default_out));

    eprintln!("regen_verdict_db: re-proving tier-0 seed obligations with a live solver...");
    let started = std::time::Instant::now();
    match trust_cg_verify::verdict_db::regen_tier0_db(&out_path) {
        Ok(report) => {
            eprintln!(
                "regen_verdict_db: OK in {:.1}s — {} row(s) written to {} \
                 ({} seed, {} registry, {} reconstruction)",
                started.elapsed().as_secs_f64(),
                report.entries.len(),
                out_path.display(),
                report.seed_rows,
                report.db_rows,
                report.recon_rows,
            );
            eprintln!("  solver: {}", report.solver_path);
            eprintln!("  solver-sha256: {}", report.solver_identity);
            eprintln!(
                "  solver-version: {}",
                report.solver_version.as_deref().unwrap_or("(undetected)")
            );
            eprintln!(
                "  exemptions: {} (written to {})",
                report.exemptions.len(),
                report.exemptions_path.display()
            );
            for e in &report.exemptions {
                eprintln!("    exempt [{}] {}: {}", e.reason, e.category, e.name);
            }
            eprintln!(
                "regen_verdict_db: rebuild trust-cg-verify (the DB is embedded via include_str!) \
                 and commit the updated tier0.vdb + exemptions.txt"
            );
        }
        Err(e) => {
            eprintln!("regen_verdict_db: FAILED (nothing was written unless stated): {e}");
            std::process::exit(1);
        }
    }
}
