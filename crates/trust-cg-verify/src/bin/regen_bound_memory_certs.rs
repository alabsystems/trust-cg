// trust-cg-verify/bin/regen_bound_memory_certs.rs - bound-memory form certificate regen tool
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Offline builder for the committed bound-memory form certificates
//! (`verdict_db/bound_memory_certs/*.lratcert.zst` and `manifest.v1`),
//! consumed by `trust_cg_verify::bound_memory_authority`.
//!
//! For every distinct exact query of a pair (`STP`/`LDP`) or scalar
//! (`LDR`/`STR`) form theorem the tool reuses a query-bound existing payload
//! that the current checker replays, or has the admitted AY producer
//! bit-blast the exact query to CNF and emit a DRAT refutation, trims it with
//! `drat-trim -l` and re-checks the trimmed proof with the vendored,
//! independent `drat-trim`. A query that yields no checker-accepted
//! certificate is reported and gets no file (its rows stay unverified).
//!
//! Usage (from the repo):
//!
//! ```text
//! scripts/trust_cargo.sh run --release -p trust-cg-verify \
//!     --bin regen_bound_memory_certs -- [out-dir] [--jobs N] [--only SUBSTRING]
//! ```
//!
//! With no `out-dir` the committed directory is regenerated; rebuild
//! afterwards (the manifest is embedded; the bodies are read from the source
//! tree) and commit every `.lratcert.zst` and `manifest.v1`. `--only` measures
//! a subset and refuses the committed directory. Set
//! `TCG_BOUND_MEMORY_REGEN_ALL=1` to force fresh AY production for every query.
//!
//! `--set atomic` regenerates the separate atomic-memory set instead
//! (`verdict_db/atomic_memory_certs/`, the 48 single-instruction atomic form
//! theorems of `trust_cg_verify::aarch64_atomic_forms`), with the same
//! protocol and its own manifest and host qualifications.
//! `--set neon` regenerates the NEON structure-memory set
//! (`verdict_db/neon_memory_certs/`, the 14 `LD1`/`ST1` post-index form
//! theorems of `trust_cg_verify::aarch64_neon_structure_forms`) the same way.
//!
//! Run on another host, over an unchanged corpus, this is how that host's
//! checker is QUALIFIED: every committed payload is replayed with its checker
//! bytes, the existing authorizations are kept and that host's
//! `(target, checker SHA-256)` is added. Until then the library's
//! `bound_memory_set_binds_the_exact_runtime_checker_bytes` is red there and
//! every bound-memory row is an uncredited checker-identity miss.

use std::path::PathBuf;

fn main() {
    #[derive(Clone, Copy, PartialEq)]
    enum Set {
        Bound,
        Atomic,
        Neon,
    }
    let mut out_dir: Option<PathBuf> = None;
    let mut set = Set::Bound;
    let mut jobs = 4usize;
    let mut only: Option<String> = None;
    let mut args = std::env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--set" => match args.next().as_deref() {
                Some("bound") => set = Set::Bound,
                Some("atomic") => set = Set::Atomic,
                Some("neon") => set = Set::Neon,
                other => {
                    eprintln!("--set requires `bound`, `atomic` or `neon`, got {other:?}");
                    std::process::exit(2);
                }
            },
            "--jobs" => {
                jobs = args
                    .next()
                    .and_then(|value| value.parse().ok())
                    .filter(|value| *value > 0)
                    .unwrap_or_else(|| {
                        eprintln!("--jobs requires a positive integer");
                        std::process::exit(2);
                    });
            }
            "--only" => {
                only = Some(args.next().unwrap_or_else(|| {
                    eprintln!("--only requires a substring of a certificate filename");
                    std::process::exit(2);
                }));
            }
            other if other.starts_with('-') => {
                eprintln!("unknown argument {other:?}");
                std::process::exit(2);
            }
            other => out_dir = Some(PathBuf::from(other)),
        }
    }
    let out_dir = out_dir.unwrap_or_else(|| {
        PathBuf::from(match set {
            Set::Atomic => concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/verdict_db/atomic_memory_certs"
            ),
            Set::Neon => concat!(env!("CARGO_MANIFEST_DIR"), "/verdict_db/neon_memory_certs"),
            Set::Bound => concat!(env!("CARGO_MANIFEST_DIR"), "/verdict_db/bound_memory_certs"),
        })
    });
    let started = std::time::Instant::now();
    let regen = match set {
        Set::Atomic => trust_cg_verify::canary_cert::regen_atomic_memory_certs,
        Set::Neon => trust_cg_verify::canary_cert::regen_neon_memory_certs,
        Set::Bound => trust_cg_verify::canary_cert::regen_bound_memory_certs,
    };
    let report = match regen(&out_dir, jobs, only.as_deref()) {
        Ok(report) => report,
        Err(error) => {
            eprintln!("regen_bound_memory_certs: FAILED: {error}");
            std::process::exit(1);
        }
    };
    println!("elapsed_s\t{:.1}", started.elapsed().as_secs_f64());
    println!("solver\t{}\t{}", report.solver_path, report.solver_identity);
    println!("solver_admission\t{}", report.solver_admission);
    println!(
        "checker\t{}\t{}",
        report.checker_target, report.checker_identity
    );
    for label in &report.checkers {
        println!("manifest_checker\t{label}");
    }
    println!("file\tforms\toutcome\tcnf_bytes\tdrat_bytes\tcert_bytes\tmillis\treused");
    let mut certified = 0usize;
    let mut forms_certified = 0usize;
    let mut forms_total = 0usize;
    for row in &report.rows {
        forms_total += row.forms.len();
        let (outcome, cnf, drat, cert) = match &row.outcome {
            Ok((cnf, drat, cert)) => {
                certified += 1;
                forms_certified += row.forms.len();
                ("ok".to_string(), *cnf, *drat, *cert)
            }
            Err(error) => (
                format!("NO CERTIFICATE: {}", error.replace(['\t', '\n'], " ")),
                0,
                0,
                0,
            ),
        };
        println!(
            "{}\t{}\t{outcome}\t{cnf}\t{drat}\t{cert}\t{}\t{}",
            row.file,
            row.forms.join(" | "),
            row.millis,
            row.reused
        );
    }
    println!(
        "queries\t{}\tcertified\t{certified}\tforms\t{forms_total}\tforms_certified\t{forms_certified}",
        report.rows.len()
    );
    println!("published\t{}\t{}", report.published, out_dir.display());
}
