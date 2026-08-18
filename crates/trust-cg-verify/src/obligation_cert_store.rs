// trust-cg-verify - machine-local, Carcara-rechecked Alethe obligation cert store
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! A machine-local, independently-re-checked ALETHE certificate store — the
//! sound generalization of the fixed [`crate::canary_cert`] DRAT tier.
//!
//! # What it is
//!
//! `canary_cert` embeds a HAND-PICKED set of repo-committed DRAT certificates
//! (popcnt, the shift-reconstruction family, `Icmp_EQ_I32`) and, on the solve
//! funnel's hot path, credits a "skip the live solve" verdict ONLY when the
//! vendored `drat-trim` independently re-derives the empty clause here and now.
//! It is sound but does not scale: every new obligation class is a manual
//! regen + a committed cert.
//!
//! This store lifts that pattern to ANY obligation, machine-locally:
//!  * on a MISS it live-solves as usual, then (off the hot path) re-runs the
//!    solver with Alethe proof emission, has an INDEPENDENT checker (Carcara,
//!    via `clean cert verify-external`) confirm the proof BEFORE writing it, and
//!    atomically persists `<store>/<verdict_key>.alethecert`;
//!  * on a later HIT for the same obligation (same SMT2 bytes, same solver
//!    binary) it credits the verdict ONLY after Carcara re-checks the stored
//!    Alethe proof against the CURRENT SMT2, in this process.
//!
//! # Why a hit is SOUND (stronger than the live solve it replaces)
//!
//! A hit does not trust the stored bytes. It re-derives the same three teeth as
//! `canary_cert`, with tooth 3 swapped for Carcara:
//!  1. **key membership** — the caller derived `verdict_key` in-process from the
//!     resolved solver's bytes-hash and the exact SMT2 bytes;
//!  2. **binding** — the cert's recorded `solver_identity` equals the resolved
//!     solver's identity AND its `smt2_sha256` equals the SHA-256 of the SMT2
//!     being discharged NOW (so a cert can never be served for a different
//!     query or under a different solver);
//!  3. **independent re-check** — Carcara (a kernel-adjacent Alethe checker,
//!     NOT the ay solver that produced the proof) verifies that the stored
//!     Alethe proof refutes THIS SMT2, now, in this process.
//!
//! Because Carcara independently checks the refutation, a hit rests on
//! independent evidence that the obligation is UNSAT — it is strictly stronger
//! than crediting the ay solver's live verdict, and it shrinks the trusted base
//! (the DRAT tier leaves the SMT2->CNF bit-blast inside ay's TCB; the Alethe
//! proof is checked at the SMT level). Any miss / binding mismatch / tamper /
//! absent-checker / non-"fully verified" result falls through to the live solve
//! below — never a weaker or wrong verdict.
//!
//! Gated OFF by default: the store is inert unless `TCG_PROOF_CERT_STORE` names
//! a directory. `TCG_PROOF_CERT_STORE_DEBUG=1` traces consume/mint decisions.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

use sha2::{Digest, Sha256};

/// Certificate schema tag, first line of every stored `.alethecert`.
const ALETHE_CERT_SCHEMA: &str = "tcg-alethe-cert-v1";

/// Store directory from `TCG_PROOF_CERT_STORE`, or `None` (tier disabled).
fn store_dir() -> Option<PathBuf> {
    std::env::var_os("TCG_PROOF_CERT_STORE").map(PathBuf::from)
}

fn debug_enabled() -> bool {
    std::env::var_os("TCG_PROOF_CERT_STORE_DEBUG").is_some()
}

macro_rules! trace {
    ($($a:tt)*) => {
        if debug_enabled() {
            eprintln!("[alethe-cert-store] {}", format!($($a)*));
        }
    };
}

/// A stored, independently-checkable Alethe certificate.
#[derive(Clone, Debug)]
struct AletheCert {
    /// Content identity (SHA-256 hex) of the solver binary that produced the
    /// proof; must equal the resolved solver's identity to be consulted.
    solver_identity: String,
    /// SHA-256 hex of the SMT2 problem the proof refutes; binds the cert to an
    /// exact query.
    smt2_sha256: String,
    /// Diagnostic obligation name (not authority).
    obligation_name: String,
    /// The SMT-LIB2 problem text (persisted so the recheck is self-contained).
    smt2: String,
    /// The Alethe proof text (`ay solve --proof-format alethe`).
    alethe_proof: String,
}

impl AletheCert {
    /// Serialize to the strict length-framed text format. Each variable-length
    /// section is preceded by a `bytes:<n>` line so a truncated / concatenated
    /// file can never be silently mis-parsed.
    fn serialize(&self) -> String {
        let mut out = String::new();
        out.push_str(ALETHE_CERT_SCHEMA);
        out.push('\n');
        out.push_str(&format!("solver-sha256:{}\n", self.solver_identity));
        out.push_str(&format!("smt2-sha256:{}\n", self.smt2_sha256));
        out.push_str(&format!("obligation:{}\n", self.obligation_name));
        out.push_str(&format!("smt2-bytes:{}\n", self.smt2.len()));
        out.push_str(&self.smt2);
        out.push('\n');
        out.push_str(&format!("proof-bytes:{}\n", self.alethe_proof.len()));
        out.push_str(&self.alethe_proof);
        out.push('\n');
        out
    }

    /// Parse the length-framed format. Returns `None` (a miss, fail-closed) on
    /// ANY malformation — a bad entry never reaches the checker.
    fn parse(text: &str) -> Option<AletheCert> {
        let mut lines = text.split_inclusive('\n');
        if lines.next()?.trim_end() != ALETHE_CERT_SCHEMA {
            return None;
        }
        let solver_identity = header_value(lines.next()?, "solver-sha256:")?;
        let smt2_sha256 = header_value(lines.next()?, "smt2-sha256:")?;
        let obligation_name = header_value(lines.next()?, "obligation:")?;
        // The remaining text is `smt2-bytes:<n>\n<n bytes>\nproof-bytes:<n>\n<n bytes>\n`.
        // Re-split from the raw remainder to honor exact byte counts.
        let consumed = ALETHE_CERT_SCHEMA
            .len()
            .checked_add(1)?
            .checked_add(header_line_len(text, "solver-sha256:")?)?
            .checked_add(header_line_len_after(text, "smt2-sha256:")?)?
            .checked_add(header_line_len_after(text, "obligation:")?)?;
        let rest = text.get(consumed..)?;
        let smt2 = read_framed(rest, "smt2-bytes:")?;
        let after_smt2 = consumed.checked_add(framed_span("smt2-bytes:", &smt2)?)?;
        let rest2 = text.get(after_smt2..)?;
        let alethe_proof = read_framed(rest2, "proof-bytes:")?;
        let after_proof = after_smt2.checked_add(framed_span("proof-bytes:", &alethe_proof)?)?;
        if after_proof != text.len() {
            return None;
        }
        Some(AletheCert {
            solver_identity,
            smt2_sha256,
            obligation_name,
            smt2,
            alethe_proof,
        })
    }
}

fn header_value(line: &str, prefix: &str) -> Option<String> {
    line.trim_end_matches('\n')
        .strip_prefix(prefix)
        .map(|s| s.to_string())
}

fn header_line_len(text: &str, prefix: &str) -> Option<usize> {
    // Length (incl. newline) of the header line at the current position.
    let start = text.find(prefix)?;
    let nl = text[start..].find('\n')? + 1;
    Some(nl)
}

fn header_line_len_after(text: &str, prefix: &str) -> Option<usize> {
    header_line_len(text, prefix)
}

/// Read a `<prefix><n>\n<n bytes>\n` framed section from the START of `rest`.
fn read_framed(rest: &str, prefix: &str) -> Option<String> {
    let line_end = rest.find('\n')?;
    let n: usize = rest.get(..line_end)?.strip_prefix(prefix)?.parse().ok()?;
    let body_start = line_end + 1;
    let body_end = body_start.checked_add(n)?;
    let body = rest.get(body_start..body_end)?;
    // The framed body must be followed by exactly a newline.
    if rest.as_bytes().get(body_end) != Some(&b'\n') {
        return None;
    }
    Some(body.to_string())
}

/// Byte span consumed by a framed section (`<prefix><n>\n<body>\n`).
fn framed_span(prefix: &str, body: &str) -> Option<usize> {
    prefix
        .len()
        .checked_add(body.len().to_string().len())?
        .checked_add(1)?
        .checked_add(body.len())?
        .checked_add(1)
}

fn sha256_hex(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    format!("{:x}", h.finalize())
}

fn cert_path(dir: &Path, verdict_key: &str) -> PathBuf {
    // verdict_key is a hex SHA-256 (safe filename). Guard defensively anyway.
    let safe: String = verdict_key
        .chars()
        .filter(|c| c.is_ascii_alphanumeric() || *c == '-' || *c == '_')
        .collect();
    dir.join(format!("{safe}.alethecert"))
}

/// Per-process consume memo (verdict_key -> honored?), mirroring canary_cert.
fn consume_memo() -> &'static Mutex<HashMap<String, bool>> {
    static MEMO: OnceLock<Mutex<HashMap<String, bool>>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Resolve the Carcara/Clean external checker. `TCG_CLEAN_CHECKER` overrides
/// the default `~/Clean/target/release/clean`. `None` (absent) => never skip.
pub(crate) fn clean_checker_path() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("TCG_CLEAN_CHECKER") {
        let pb = PathBuf::from(p);
        return pb.is_file().then_some(pb);
    }
    let home = std::env::var_os("HOME")?;
    let pb = PathBuf::from(home).join("Clean/target/release/clean");
    pb.is_file().then_some(pb)
}

/// CONSUME (hot path): does a stored Alethe cert back `verdict_key`, and does
/// Carcara independently re-check its proof against the CURRENT SMT2, now?
///
/// `true` => skip the live solve (independently proven UNSAT). `false` => fall
/// through to the live solver — never a verdict of its own.
pub(crate) fn alethe_cert_skip_verified(verdict_key: &str, solver_path: &str, smt2: &str) -> bool {
    let Some(dir) = store_dir() else {
        return false;
    };
    // Regen / recording must always observe genuine live runs.
    if crate::verdict_db::recording_active() {
        return false;
    }
    if let Some(hit) = consume_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .get(verdict_key)
        .copied()
    {
        return hit;
    }
    let hit = consume_verified_in(&dir, verdict_key, solver_path, smt2, clean_checker_path());
    consume_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .insert(verdict_key.to_string(), hit);
    hit
}

/// Core of the consume path over explicit inputs (no memo / no env), so the
/// soundness tests can drive forged / tampered / mismatched stores.
fn consume_verified_in(
    dir: &Path,
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    checker: Option<PathBuf>,
) -> bool {
    let path = cert_path(dir, verdict_key);
    let Ok(text) = std::fs::read_to_string(&path) else {
        return false; // tooth 1: no cert for this key
    };
    let Some(cert) = AletheCert::parse(&text) else {
        trace!("{verdict_key}: malformed cert, declining");
        return false;
    };
    // Tooth 2: binding. Solver identity + exact SMT2 bytes.
    let Some(identity) = crate::ay_bridge::solver_identity_hash(solver_path) else {
        return false;
    };
    if identity != cert.solver_identity {
        trace!("{verdict_key}: solver identity mismatch, declining");
        return false;
    }
    if sha256_hex(smt2.as_bytes()) != cert.smt2_sha256 {
        trace!("{verdict_key}: smt2 hash mismatch, declining");
        return false;
    }
    // Defense in depth: the persisted SMT2 must itself hash to the recorded
    // value (a tampered `smt2` section can never reach the checker as the
    // problem while masquerading as this obligation).
    if sha256_hex(cert.smt2.as_bytes()) != cert.smt2_sha256 {
        trace!("{verdict_key}: stored smt2 self-hash mismatch, declining");
        return false;
    }
    // Tooth 3: independent Carcara re-check against the CURRENT smt2.
    let Some(checker) = checker else {
        trace!("{verdict_key}: no Carcara checker available, declining (fail-safe)");
        return false;
    };
    let ok = carcara_verify(&checker, smt2, &cert.alethe_proof);
    trace!(
        "{verdict_key}: obligation={:?} carcara_verified={ok}",
        cert.obligation_name
    );
    ok
}

/// The Carcara/Clean external cert JSON (the 2026-07-15 `verify-external`
/// contract): `{"type":"alethe_certificate","version":"1.0","problem":<smt2>,
/// "proof":<alethe>}`. Returns true iff the checker reports a full, hole-free
/// verification.
pub(crate) fn carcara_verify(checker: &Path, smt2: &str, alethe_proof: &str) -> bool {
    let Ok(dir) = tempfile::tempdir() else {
        return false;
    };
    let cert_json = dir.path().join("cert.json");
    let json = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": smt2,
        "proof": alethe_proof,
    });
    if std::fs::write(&cert_json, serde_json::to_vec(&json).unwrap_or_default()).is_err() {
        return false;
    }
    let Ok(out) = Command::new(checker)
        .arg("cert")
        .arg("verify-external")
        .arg(&cert_json)
        // Clean's verbose Alethe lane emits the proof-completeness status.
        // The non-verbose `... verification: PASSED` line alone does not
        // distinguish a fully checked proof from a future weaker success mode.
        .arg("--verbose")
        .output()
    else {
        return false;
    };
    if debug_enabled() {
        eprintln!(
            "[alethe-cert-store] checker={} status={} stdout={} stderr={}",
            checker.display(),
            out.status,
            String::from_utf8_lossy(&out.stdout).trim(),
            String::from_utf8_lossy(&out.stderr).trim(),
        );
    }
    if !out.status.success() {
        return false;
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    clean_alethe_stdout_is_fully_verified(&stdout)
}

/// Parse the stable `clean cert verify-external --verbose` success contract.
///
/// Authority must not rest on a loose substring such as `"passed"`: a batch
/// summary, diagnostic, or mixed success/failure transcript can contain that
/// word without establishing that this Alethe proof was checked completely.
/// Require all three exact, line-oriented claims emitted by Clean's Alethe
/// verifier and reject any transcript that also reports failure, holes, or an
/// incomplete proof. Process success is checked by [`carcara_verify`] before
/// this parser is called.
fn clean_alethe_stdout_is_fully_verified(stdout: &str) -> bool {
    let lines: Vec<String> = stdout
        .lines()
        .map(|line| line.trim().to_ascii_lowercase())
        .collect();

    let has_pass = lines
        .iter()
        .any(|line| line == "external certificate verification: passed");
    let has_alethe_type = lines.iter().any(|line| line == "type: alethe smt proof");
    let has_full_status = lines
        .iter()
        .any(|line| line == "proof status: fully verified");
    let has_rejection = lines.iter().any(|line| {
        line.contains("failed") || line.contains("holey") || line.contains("incomplete")
    });

    has_pass && has_alethe_type && has_full_status && !has_rejection
}

/// MINT-ON-MISS (off the hot path, opt-in): after a live UNSAT for `smt2`,
/// re-run the solver with Alethe proof emission, have Carcara confirm the proof
/// BEFORE writing, and atomically persist the cert. Never mints unchecked;
/// no-ops while recording, when the store is disabled, or on any failure.
pub(crate) fn mint_alethe_cert(
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    obligation_name: &str,
) {
    let Some(dir) = store_dir() else {
        return;
    };
    if crate::verdict_db::recording_active() {
        return;
    }
    let path = cert_path(&dir, verdict_key);
    if path.exists() {
        return; // already minted
    }
    let Some(checker) = clean_checker_path() else {
        trace!("{verdict_key}: mint skipped (no Carcara checker to pre-verify)");
        return;
    };
    let ok = mint_into(
        &dir,
        verdict_key,
        solver_path,
        smt2,
        obligation_name,
        &checker,
    );
    if ok {
        trace!("{verdict_key}: minted Carcara-verified cert for {obligation_name:?}");
    }
}

/// Mint core over explicit paths (no env / no store-gate), so the end-to-end
/// integration test can drive the real ay->Carcara->write cycle. Returns
/// whether a cert was written. NEVER writes a cert Carcara did not verify.
fn mint_into(
    dir: &Path,
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    obligation_name: &str,
    checker: &Path,
) -> bool {
    let path = cert_path(dir, verdict_key);
    if path.exists() {
        return false;
    }
    let Some(identity) = crate::ay_bridge::solver_identity_hash(solver_path) else {
        return false;
    };
    let Ok(work) = tempfile::tempdir() else {
        return false;
    };
    // 1. Emit an Alethe proof for this SMT2 (UNSAT refutation).
    let smt2_path = work.path().join("problem.smt2");
    let proof_path = work.path().join("proof.alethe");
    if std::fs::write(&smt2_path, smt2).is_err() {
        return false;
    }
    let Ok(out) = Command::new(solver_path)
        .arg("solve")
        .arg(&smt2_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("alethe")
        .output()
    else {
        return false;
    };
    let stdout = String::from_utf8_lossy(&out.stdout).to_lowercase();
    if !stdout.contains("unsat") {
        trace!("{verdict_key}: mint skipped (solver did not report unsat)");
        return false;
    }
    let Ok(alethe_proof) = std::fs::read_to_string(&proof_path) else {
        return false;
    };
    if alethe_proof.trim().is_empty() {
        return false;
    }
    // 2. Carcara MUST confirm the proof before we ever persist it.
    if !carcara_verify(checker, smt2, &alethe_proof) {
        trace!("{verdict_key}: mint REFUSED (Carcara did not verify the fresh proof)");
        return false;
    }
    let cert = AletheCert {
        solver_identity: identity,
        smt2_sha256: sha256_hex(smt2.as_bytes()),
        obligation_name: obligation_name.to_string(),
        smt2: smt2.to_string(),
        alethe_proof,
    };
    // 3. Atomic write (tempfile in the store dir + rename).
    if std::fs::create_dir_all(dir).is_err() {
        return false;
    }
    let tmp = dir.join(format!(".{verdict_key}.tmp"));
    if std::fs::write(&tmp, cert.serialize()).is_err() {
        return false;
    }
    if std::fs::rename(&tmp, &path).is_err() {
        let _ = std::fs::remove_file(&tmp);
        return false;
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    fn write_cert(dir: &Path, key: &str, cert: &AletheCert) {
        std::fs::write(cert_path(dir, key), cert.serialize()).unwrap();
    }

    fn sample(smt2: &str, proof: &str, solver_id: &str) -> AletheCert {
        AletheCert {
            solver_identity: solver_id.to_string(),
            smt2_sha256: sha256_hex(smt2.as_bytes()),
            obligation_name: "test_ob".to_string(),
            smt2: smt2.to_string(),
            alethe_proof: proof.to_string(),
        }
    }

    #[test]
    fn serialize_roundtrips_through_parse() {
        let c = sample(
            "(assert false)\n(check-sat)",
            "(step t1 (cl) :rule false)",
            "abcd",
        );
        let text = c.serialize();
        let p = AletheCert::parse(&text).expect("parses");
        assert_eq!(p.solver_identity, c.solver_identity);
        assert_eq!(p.smt2_sha256, c.smt2_sha256);
        assert_eq!(p.obligation_name, c.obligation_name);
        assert_eq!(p.smt2, c.smt2);
        assert_eq!(p.alethe_proof, c.alethe_proof);
    }

    #[test]
    fn parse_rejects_wrong_schema() {
        assert!(AletheCert::parse("not-a-cert\nsolver-sha256:x\n").is_none());
    }

    #[test]
    fn parse_rejects_truncated_framed_body() {
        let c = sample("(assert false)", "proofbody", "id");
        let mut text = c.serialize();
        text.truncate(text.len() - 3); // chop the proof body
        assert!(AletheCert::parse(&text).is_none());
    }

    #[test]
    fn parse_rejects_trailing_bytes() {
        let c = sample("(assert false)", "proofbody", "id");
        let mut text = c.serialize();
        text.push_str("another-certificate-or-junk\n");
        assert!(AletheCert::parse(&text).is_none());
    }

    #[test]
    fn parse_rejects_overflowing_frame_length() {
        let c = sample("(assert false)", "proofbody", "id");
        let text = c.serialize().replacen(
            &format!("smt2-bytes:{}", c.smt2.len()),
            &format!("smt2-bytes:{}0", usize::MAX),
            1,
        );
        assert!(AletheCert::parse(&text).is_none());
    }

    #[test]
    fn consume_declines_missing_key() {
        let dir = tempfile::tempdir().unwrap();
        // No cert written, no checker: must decline.
        assert!(!consume_verified_in(
            dir.path(),
            "deadbeef",
            "/nonexistent/solver",
            "smt",
            None
        ));
    }

    #[test]
    fn consume_declines_smt2_hash_mismatch() {
        // A cert whose smt2_sha256 is for a DIFFERENT problem than presented.
        let dir = tempfile::tempdir().unwrap();
        // Fake a readable "solver" so identity resolves; use this file itself.
        let solver = dir.path().join("solverbin");
        std::fs::write(&solver, b"solver-bytes").unwrap();
        let id = crate::ay_bridge::solver_identity_hash(solver.to_str().unwrap()).unwrap();
        let mut c = sample("(assert PROBLEM_A)", "proof", &id);
        c.smt2 = "(assert PROBLEM_A)".to_string();
        c.smt2_sha256 = sha256_hex(c.smt2.as_bytes());
        write_cert(dir.path(), "k1", &c);
        // Present a DIFFERENT smt2: binding tooth-2 must fail before any checker.
        let checker = Some(PathBuf::from("/bin/echo")); // would "succeed" — but we must not reach it
        assert!(!consume_verified_in(
            dir.path(),
            "k1",
            solver.to_str().unwrap(),
            "(assert PROBLEM_B)",
            checker
        ));
    }

    #[test]
    fn consume_declines_solver_identity_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let solver = dir.path().join("solverbin");
        std::fs::write(&solver, b"solver-bytes").unwrap();
        let smt2 = "(assert false)";
        // Cert names a DIFFERENT solver identity than the resolved one.
        let c = sample(smt2, "proof", "some-other-solver-identity");
        write_cert(dir.path(), "k2", &c);
        let checker = Some(PathBuf::from("/bin/echo"));
        assert!(!consume_verified_in(
            dir.path(),
            "k2",
            solver.to_str().unwrap(),
            smt2,
            checker
        ));
    }

    /// END-TO-END with the REAL ay + Carcara binaries: mint a cert for a
    /// known-unsat QF_BV obligation, then prove the four soundness properties
    /// on the CONSUME path against that real cert. This external-tool campaign
    /// requires explicit binary paths; the Clean binary must be built with its
    /// `carcara-verify` feature:
    ///
    /// ```text
    /// TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1 \
    /// AY_SOLVER_PATH=/path/to/ay TCG_CLEAN_CHECKER=/path/to/clean-with-carcara-verify \
    /// cargo test -p trust-cg-verify --lib \
    ///     end_to_end_mint_then_consume_real_binaries
    /// ```
    #[test]
    fn end_to_end_mint_then_consume_real_binaries() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_EXTERNAL_CERT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "external certificate campaign not requested; \
                 set TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1 with explicit \
                 AY_SOLVER_PATH and TCG_CLEAN_CHECKER paths to run"
            );
            return;
        }

        let ay = PathBuf::from(
            std::env::var_os("AY_SOLVER_PATH")
                .expect("AY_SOLVER_PATH must name the exact AY binary under test"),
        );
        let checker = PathBuf::from(
            std::env::var_os("TCG_CLEAN_CHECKER")
                .expect("TCG_CLEAN_CHECKER must name the exact Clean checker under test"),
        );
        assert!(
            ay.is_file(),
            "AY_SOLVER_PATH is not a file: {}",
            ay.display()
        );
        assert!(
            checker.is_file(),
            "TCG_CLEAN_CHECKER is not a file: {}",
            checker.display()
        );
        let ay = ay
            .to_str()
            .expect("AY_SOLVER_PATH must be valid UTF-8 for subprocess invocation");

        // Keep this canary inside QF_BV while making the contradiction direct.
        // The test is authority for certificate transport, binding, and the
        // independent checker—not for AY's rewrite-proof coverage. In
        // particular, `not (= x x)` currently exercises an unsupported Alethe
        // rewrite hole and correctly downgrades AY's result to `unknown`, so it
        // cannot serve as a certificate-pipeline canary.
        let smt2 = "(set-logic QF_BV)\n(assert false)\n(check-sat)\n";
        let dir = tempfile::tempdir().unwrap();
        let key = "e2e_false_qfbv";

        // MINT: real ay emits Alethe; Carcara pre-verifies; cert is written.
        let minted = mint_into(dir.path(), key, ay, smt2, "false_qfbv", &checker);
        assert!(
            minted,
            "mint should succeed for a real unsat + verifiable proof"
        );
        assert!(cert_path(dir.path(), key).exists(), "cert file written");

        // CONSUME (happy path): binding + independent Carcara re-check => hit.
        assert!(
            consume_verified_in(dir.path(), key, ay, smt2, Some(checker.clone())),
            "a freshly minted, Carcara-verifiable cert must be honored"
        );

        // ADVERSARIAL 1 — tampered proof: Carcara must reject => no skip.
        {
            let text = std::fs::read_to_string(cert_path(dir.path(), key)).unwrap();
            let cert = AletheCert::parse(&text).unwrap();
            let mut bad = cert.clone();
            bad.alethe_proof = "(malformed".to_string();
            std::fs::write(cert_path(dir.path(), "tampered"), bad.serialize()).unwrap();
            assert!(
                !consume_verified_in(dir.path(), "tampered", ay, smt2, Some(checker.clone())),
                "a proof Carcara cannot re-check must NOT be honored"
            );
        }

        // ADVERSARIAL 2 — wrong SMT2 presented: binding tooth-2 rejects before
        // any checker (even a real verifiable proof for a DIFFERENT problem).
        assert!(
            !consume_verified_in(
                dir.path(),
                key,
                ay,
                "(set-logic QF_BV)\n(declare-const y (_ BitVec 8))\n(assert (= y y))\n(check-sat)\n",
                Some(checker.clone())
            ),
            "a cert must never be served for a different query"
        );

        // ADVERSARIAL 3 — no checker: fail-safe decline even with a valid cert.
        assert!(
            !consume_verified_in(dir.path(), key, ay, smt2, None),
            "absent Carcara checker must fail closed"
        );
    }

    #[test]
    fn consume_declines_when_no_checker() {
        // Binding all correct, but no Carcara checker => fail-safe decline.
        let dir = tempfile::tempdir().unwrap();
        let solver = dir.path().join("solverbin");
        std::fs::write(&solver, b"solver-bytes").unwrap();
        let id = crate::ay_bridge::solver_identity_hash(solver.to_str().unwrap()).unwrap();
        let smt2 = "(assert false)";
        let c = sample(smt2, "proof", &id);
        write_cert(dir.path(), "k3", &c);
        assert!(!consume_verified_in(
            dir.path(),
            "k3",
            solver.to_str().unwrap(),
            smt2,
            None
        ));
    }

    #[test]
    fn clean_alethe_success_parser_requires_the_exact_full_verification_contract() {
        let genuine = "External certificate verification: PASSED\n\
                       Type: Alethe SMT proof\n\
                       Problem bytes: 12, proof bytes: 34\n\
                       Proof status: fully verified\n\
                       Verified in 0.001000s\n";
        assert!(clean_alethe_stdout_is_fully_verified(genuine));

        // A broad `contains(\"passed\")` check would incorrectly accept this
        // unrelated aggregate transcript.
        assert!(!clean_alethe_stdout_is_fully_verified(
            "Batch verification complete: 1/2 passed, 1 failed\n"
        ));
        assert!(!clean_alethe_stdout_is_fully_verified(
            "External certificate verification: PASSED\nType: Alethe SMT proof\n"
        ));
        assert!(!clean_alethe_stdout_is_fully_verified(
            "External certificate verification: PASSED\n\
             Type: Alethe SMT proof\n\
             Proof status: fully verified\n\
             External certificate verification: FAILED\n"
        ));
    }
}
