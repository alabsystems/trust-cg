// trust-cg-drat-trim - Vendored drat-trim DRAT proof checker.
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Purpose
// -------
// Ship Marijn Heule's `drat-trim` (MIT) as a standalone executable
// built at compile time into `OUT_DIR`, and expose its on-disk path so
// callers do not need a system-installed `drat-trim` on PATH.
//
// Usage
// -----
//
// ```no_run
// use std::process::Command;
// use trust_cg_drat_trim::drat_trim_executable_path;
//
// let out = Command::new(drat_trim_executable_path())
//     .arg("instance.cnf")
//     .arg("proof.drat")
//     .output()
//     .expect("invoke drat-trim");
// assert!(out.status.success());
// ```
//
// Provenance is recorded in `build.rs`.

use std::path::{Path, PathBuf};
use std::sync::OnceLock;

/// Absolute path to the `drat-trim` executable that was compiled by
/// this crate's `build.rs` into `OUT_DIR`.
///
/// The path is computed once and cached. Returns a borrowed `Path` so
/// callers can pass it directly to `std::process::Command::new(...)`.
pub fn drat_trim_executable_path() -> &'static Path {
    static CACHED: OnceLock<PathBuf> = OnceLock::new();
    CACHED
        .get_or_init(|| {
            // `DRAT_TRIM_BUILT_EXE` is set by `build.rs` via
            // `cargo:rustc-env=...`, so `env!` resolves at compile time
            // to the absolute OUT_DIR path. We turn it into a `PathBuf`
            // for the cache. (Deliberately outside the `TCG_`/`TRUST_CG_`
            // namespaces: trustc rejects those in its process environment
            // as untracked codegen controls.)
            PathBuf::from(env!("DRAT_TRIM_BUILT_EXE"))
        })
        .as_path()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::io::Write;
    use std::process::Command;
    use tempfile::NamedTempFile;

    #[test]
    fn executable_exists_and_is_runnable() {
        let exe = drat_trim_executable_path();
        let meta = fs::metadata(exe).expect("drat-trim binary exists in OUT_DIR");
        assert!(meta.is_file(), "drat-trim path is not a regular file");
        // Invoking with no arguments: upstream drat-trim prints a usage
        // banner and exits non-zero. We accept either "ran at all" (got
        // an Output) and either exit status, because some upstream
        // revisions return 0 on the banner. The point of this smoke
        // test is to prove the build produced an actually-executable
        // binary, not to pin down its CLI surface.
        let out = Command::new(exe)
            .output()
            .expect("spawn drat-trim subprocess");
        assert!(
            !out.stdout.is_empty() || !out.stderr.is_empty(),
            "drat-trim produced no output at all; suspicious",
        );
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn executable_has_required_content_derived_macho_uuid() {
        let out = Command::new("otool")
            .arg("-l")
            .arg(drat_trim_executable_path())
            .output()
            .expect("run otool over vendored checker");
        assert!(out.status.success(), "otool must inspect vendored checker");
        let load_commands = String::from_utf8_lossy(&out.stdout);
        assert!(
            load_commands
                .lines()
                .any(|line| line.trim() == "cmd LC_UUID"),
            "linker-signed checker must retain the content-derived Mach-O UUID required by dyld"
        );
    }

    /// End-to-end: hand drat-trim a trivially-unsatisfiable CNF and an
    /// empty (just the empty clause) DRAT proof, and require
    /// acceptance.
    ///
    /// The CNF `(x) ∧ (¬x)` is UNSAT by unit propagation. The minimal
    /// DRAT proof that resolves to the empty clause is the single line
    /// `0` (a clause with zero literals), which is the standard way to
    /// terminate a DRAT trace.
    #[test]
    fn accepts_trivial_unsat_proof() {
        let mut cnf = NamedTempFile::new().expect("tmp cnf");
        writeln!(cnf, "p cnf 1 2").unwrap();
        writeln!(cnf, "1 0").unwrap();
        writeln!(cnf, "-1 0").unwrap();
        cnf.flush().unwrap();

        let mut drat = NamedTempFile::new().expect("tmp drat");
        writeln!(drat, "0").unwrap();
        drat.flush().unwrap();

        let out = Command::new(drat_trim_executable_path())
            .arg(cnf.path())
            .arg(drat.path())
            .output()
            .expect("invoke drat-trim");
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        assert!(
            out.status.success(),
            "drat-trim should accept the trivial proof.\nstdout: {}\nstderr: {}",
            stdout,
            stderr
        );
        assert!(
            stdout.contains("VERIFIED") || stdout.contains("s VERIFIED"),
            "drat-trim output missing VERIFIED banner.\nstdout: {}\nstderr: {}",
            stdout,
            stderr
        );
    }
}
