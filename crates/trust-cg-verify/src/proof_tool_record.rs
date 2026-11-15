//! The proof tools this process actually ran, for a gate's identity record.
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//! Copyright 2026 Andrew Yates | License: Apache-2.0
//!
//! A gate that reports "these proofs were checked by Clean X" must name the
//! checker that RAN, not a file it expected to run: discovery may skip the
//! toolchain's `bin/clean` for the aterm package, an override may name another
//! file, and an overlay build pins a third. So the record is written where the
//! tools run. With [`PROOF_IDENTITY_OUT_ENV`] naming a file, this process
//! appends one JSON line (schema [`SCHEMA`]) the first time it runs each
//! distinct tool:
//!
//! * `clean`: where a checker checks a proof
//!   (`obligation_cert_store::carcara_verify_with_expected_checker_with_env`),
//!   with the SHA-256 the run was bound to before and after it. The control
//!   probe of discovery is not a proof check and is not recorded.
//! * `ay`: where the admitted AY is started (`PinnedAy`'s one launcher), with its
//!   admitted digest and identity line.
//!
//! Each line also names the overlay manifest this crate was built from, if
//! any. The variable carries the `TRUST_CG_` prefix, so `scripts/trust_cargo.sh`
//! hands it to test executables and never to the compiler. Recording is
//! best-effort output: a write failure is reported once on stderr and never
//! changes a verdict.

use std::collections::HashSet;
use std::io::Write;
use std::path::Path;
use std::sync::{Mutex, OnceLock};

/// The file the records are appended to.
pub const PROOF_IDENTITY_OUT_ENV: &str = "TRUST_CG_PROOF_IDENTITY_OUT";

/// Schema of one line.
pub const SCHEMA: &str = "trust-cg.proof-tool-use.v1";

/// Which proof tool ran.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ProofTool {
    /// The Alethe proof checker (Clean with Carcara).
    Clean,
    /// The dependency-closed CIC checker linked into the actual verifier.
    #[cfg(feature = "original-i128-cic")]
    CleanCic,
    /// The solver that produced the proof.
    Ay,
}

impl ProofTool {
    fn as_str(self) -> &'static str {
        match self {
            Self::Clean => "clean",
            #[cfg(feature = "original-i128-cic")]
            Self::CleanCic => "clean-cic",
            Self::Ay => "ay",
        }
    }
}

/// Record that `tool` at `path` with `sha256` ran (once per process per
/// distinct triple), when [`PROOF_IDENTITY_OUT_ENV`] is set.
pub(crate) fn note(tool: ProofTool, path: &Path, sha256: &str, identity: Option<&str>) {
    let Some(out) = trust_cg_process_env::var_os(PROOF_IDENTITY_OUT_ENV) else {
        return;
    };
    if out.is_empty() {
        return;
    }
    static SEEN: OnceLock<Mutex<HashSet<(ProofTool, String, String)>>> = OnceLock::new();
    let first = SEEN
        .get_or_init(|| Mutex::new(HashSet::new()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .insert((tool, path.display().to_string(), sha256.to_owned()));
    if !first {
        return;
    }
    let overlay = crate::ay_identity::ToolchainAyRecord::recorded()
        .overlay()
        .map(|overlay| overlay.manifest_sha256().to_owned());
    let line = record_line(tool, path, sha256, identity, overlay.as_deref());
    if let Err(error) = append_line(Path::new(&out), &line) {
        static WARNED: OnceLock<()> = OnceLock::new();
        WARNED.get_or_init(|| {
            eprintln!(
                "[trust-cg] cannot append the proof-tool record to {} ({error}); the gate's \
                 identity record will be incomplete",
                Path::new(&out).display()
            );
        });
    }
}

/// One JSON line (no trailing newline).
fn record_line(
    tool: ProofTool,
    path: &Path,
    sha256: &str,
    identity: Option<&str>,
    overlay_manifest_sha256: Option<&str>,
) -> String {
    serde_json::json!({
        "schema": SCHEMA,
        "role": tool.as_str(),
        "path": path.display().to_string(),
        "sha256": sha256,
        "identity": identity,
        "toolchain_overlay_manifest_sha256": overlay_manifest_sha256,
        "pid": std::process::id(),
    })
    .to_string()
}

/// Append `line` and a newline in ONE write, so concurrent processes
/// appending to the same file (`O_APPEND`) never interleave inside a line.
fn append_line(path: &Path, line: &str) -> std::io::Result<()> {
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)?;
    file.write_all(format!("{line}\n").as_bytes())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_record_line_names_the_tool_that_ran() {
        let line = record_line(
            ProofTool::Clean,
            Path::new("/opt/store/clean/8606/bin/clean"),
            &"c".repeat(64),
            None,
            Some(&"d".repeat(64)),
        );
        let value: serde_json::Value = serde_json::from_str(&line).unwrap();
        assert_eq!(value["schema"], SCHEMA);
        assert_eq!(value["role"], "clean");
        assert_eq!(value["path"], "/opt/store/clean/8606/bin/clean");
        assert_eq!(value["sha256"], "c".repeat(64));
        assert_eq!(value["identity"], serde_json::Value::Null);
        assert_eq!(value["toolchain_overlay_manifest_sha256"], "d".repeat(64));
        assert!(!line.contains('\n'));
    }

    #[test]
    fn note_appends_each_distinct_tool_once() {
        let dir = tempfile::tempdir().unwrap();
        let out = dir.path().join("identity.jsonl");
        let checker = dir.path().join("checker-for-note-test");
        trust_cg_process_env::with_env_overrides(
            &[(PROOF_IDENTITY_OUT_ENV, out.to_str().unwrap())],
            || {
                note(ProofTool::Clean, &checker, &"1".repeat(64), None);
                note(ProofTool::Clean, &checker, &"1".repeat(64), None);
                note(ProofTool::Clean, &checker, &"2".repeat(64), None);
                note(ProofTool::Ay, &checker, &"1".repeat(64), Some("ay 0.0.0"));
            },
        );
        let text = std::fs::read_to_string(&out).unwrap();
        let rows: Vec<serde_json::Value> = text
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        let summary: Vec<(String, String)> = rows
            .iter()
            .map(|row| {
                (
                    row["role"].as_str().unwrap().to_owned(),
                    row["sha256"].as_str().unwrap().to_owned(),
                )
            })
            .collect();
        assert_eq!(
            summary,
            [
                ("clean".to_owned(), "1".repeat(64)),
                ("clean".to_owned(), "2".repeat(64)),
                ("ay".to_owned(), "1".repeat(64)),
            ]
        );
        assert_eq!(rows[2]["identity"], "ay 0.0.0");
    }
}
