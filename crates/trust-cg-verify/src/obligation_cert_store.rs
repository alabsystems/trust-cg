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
//!    binary) it credits the verdict ONLY after the byte-identical external
//!    Clean/Carcara checker recorded at mint re-checks the stored Alethe proof
//!    against the CURRENT SMT2, in this process.
//!
//! # Why a hit is SOUND (stronger than the live solve it replaces)
//!
//! A hit does not trust the stored bytes. It re-derives the same three teeth as
//! `canary_cert`, with tooth 3 swapped for Carcara:
//!  1. **key membership** — the caller derived `verdict_key` in-process from the
//!     resolved solver's bytes-hash and the exact SMT2 bytes;
//!  2. **binding** — the cert's recorded producer AY identity equals the
//!     resolved solver identity, its `smt2_sha256` equals the exact query being
//!     discharged, and its external Clean checker SHA equals the executable
//!     replaying it now;
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
//! # Why the checker is CAPABILITY-PROBED, not just located
//!
//! Fail-closed is only half a safety property: it keeps wrong answers out, but
//! it cannot tell "this proof is bad" from "this binary cannot check proofs".
//! Both arrive here as `false`. A `clean` built without the `carcara-verify`
//! cargo feature answers EVERY Alethe request with "carcara-verify feature
//! required for tier 1 verification" — a content-INDEPENDENT refusal — and on
//! this box that silently cost 22 of 54 compile-gate outcomes with not one line
//! of output, because trust-cg accepted any file at the checker path on a bare
//! `is_file()` and read each refusal as a failed proof.
//!
//! So [`clean_checker_path`] proves the external checker's capability before
//! returning it: once per path per process (~10ms) it verifies a known-good
//! CONTROL proof. A checker that cannot verify that cannot verify anything, is
//! reported ABSENT rather than consulted, and produces one loud, self-
//! explaining diagnostic naming the build line that fixes it.
//!
//! Gated OFF by default: the store is inert unless `TCG_PROOF_CERT_STORE` names
//! a directory. `TCG_PROOF_CERT_STORE_DEBUG=1` traces consume/mint decisions.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};

use sha2::{Digest, Sha256};

/// Certificate schema tag, first line of every stored `.alethecert`.
const ALETHE_CERT_SCHEMA: &str = "tcg-alethe-cert-v2";

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
    producer_ay_identity: String,
    /// Content identity of the independent external Clean/Carcara executable
    /// that accepted this proof when the certificate was minted. This is a C0
    /// checker role, distinct from the C1 `clean-kernel` Rust dependency.
    external_clean_checker_identity: String,
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
        out.push_str(&format!(
            "producer-ay-sha256:{}\n",
            self.producer_ay_identity
        ));
        out.push_str(&format!(
            "external-clean-checker-sha256:{}\n",
            self.external_clean_checker_identity
        ));
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
        let producer_ay_identity = header_value(lines.next()?, "producer-ay-sha256:")?;
        let external_clean_checker_identity =
            header_value(lines.next()?, "external-clean-checker-sha256:")?;
        let smt2_sha256 = header_value(lines.next()?, "smt2-sha256:")?;
        let obligation_name = header_value(lines.next()?, "obligation:")?;
        for digest in [
            &producer_ay_identity,
            &external_clean_checker_identity,
            &smt2_sha256,
        ] {
            if digest.len() != 64
                || !digest
                    .bytes()
                    .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
            {
                return None;
            }
        }
        // The remaining text is `smt2-bytes:<n>\n<n bytes>\nproof-bytes:<n>\n<n bytes>\n`.
        // Re-split from the raw remainder to honor exact byte counts.
        let consumed = ALETHE_CERT_SCHEMA
            .len()
            .checked_add(1)?
            .checked_add(header_line_len(text, "producer-ay-sha256:")?)?
            .checked_add(header_line_len_after(
                text,
                "external-clean-checker-sha256:",
            )?)?
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
            producer_ay_identity,
            external_clean_checker_identity,
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

/// Per-process positive replay memo. The key binds the caller's verdict key,
/// exact producer/query identities, complete certificate bytes, and exact
/// checker executable bytes. Negative outcomes are never memoized: a cert
/// minted or repaired later in the same process must remain consumable.
fn consume_memo() -> &'static Mutex<HashMap<String, bool>> {
    static MEMO: OnceLock<Mutex<HashMap<String, bool>>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

fn consume_memo_key(
    verdict_key: &str,
    solver_identity: &str,
    smt2: &str,
    cert_text: &str,
    checker_identity: &str,
) -> String {
    format!(
        "{verdict_key}:{solver_identity}:{}:{}:{checker_identity}",
        sha256_hex(smt2.as_bytes()),
        sha256_hex(cert_text.as_bytes()),
    )
}

/// The build line that produces a checker able to verify Alethe proofs.
/// Quoted verbatim in the unusable-checker diagnostic, so an operator who sees
/// the failure never has to go find out what to do about it.
pub(crate) const CLEAN_CHECKER_BUILD_LINE: &str =
    "cargo build --locked --release -p clean --features carcara-verify";

/// The known-good CONTROL pair used to probe a resolved checker: a two-clause
/// propositional contradiction (`p` and `not p`) and its one-step Alethe
/// resolution refutation. Any checker with a working Alethe lane accepts this;
/// no checker can accept it "by accident", because acceptance is reported
/// through the same `Proof status: fully verified` contract
/// [`clean_alethe_stdout_is_fully_verified`] requires of real obligations.
const CHECKER_PROBE_SMT2: &str =
    "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n";
const CHECKER_PROBE_ALETHE: &str =
    "(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule resolution :premises (t1 t0))\n";

/// Stable substring Clean emits when its binary was built without the
/// `carcara-verify` cargo feature (`VerifyError::CarcaraNotEnabled`).
const CARCARA_FEATURE_MARKER: &str = "carcara-verify feature required";
/// Stable substring Clean emits when built without `clean-elab/ay-smt`, the
/// outer of the two gates in series on the Alethe lane.
const AY_SMT_FEATURE_MARKER: &str = "ay-smt feature required";

/// Why a checker that EXISTS on disk still cannot be used as proof authority.
///
/// The distinction this type draws is the whole point of the probe: a checker
/// that refuses every proof content-INDEPENDENTLY is not a strict checker, it
/// is a broken one, and consulting it produces the same `false` as a genuine
/// refutation failure while meaning something completely different.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum CheckerDefect {
    /// Built without `carcara-verify`: answers EVERY Alethe request with
    /// "carcara-verify feature required for tier 1 verification", whatever the
    /// proof says. This is the failure this probe exists for.
    CarcaraFeatureMissing,
    /// Built without `ay-smt`: the Alethe lane is absent one level further out.
    AySmtFeatureMissing,
    /// Ran, but did not verify the control proof. Either not `clean`, too old
    /// to speak the `verify-external` contract, or otherwise broken.
    ControlProofRejected(String),
    /// Could not be executed at all (not executable, bad architecture, ...).
    NotRunnable(String),
}

impl CheckerDefect {
    /// One-line reason, suitable for embedding in an `AYResult::Unknown`.
    fn reason(&self) -> String {
        match self {
            Self::CarcaraFeatureMissing => format!(
                "it was built WITHOUT the `carcara-verify` cargo feature, so it rejects every \
                 Alethe proof regardless of validity; rebuild with `{CLEAN_CHECKER_BUILD_LINE}`"
            ),
            Self::AySmtFeatureMissing => format!(
                "it was built WITHOUT the `ay-smt` cargo feature, so it has no Alethe lane at \
                 all; rebuild with `{CLEAN_CHECKER_BUILD_LINE}`"
            ),
            Self::ControlProofRejected(detail) => format!(
                "it did not verify a known-good control proof, so it cannot be trusted to \
                 verify real ones (transcript: {detail})"
            ),
            Self::NotRunnable(detail) => format!("it could not be executed ({detail})"),
        }
    }
}

/// Resolve the independent C0 checker path WITHOUT probing it. The explicit
/// role-named variable takes precedence; `TCG_CLEAN_CHECKER` remains a legacy
/// compatibility alias. Neither variable names the C1 dependency Clean role.
fn resolve_clean_checker_path() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("TCG_EXTERNAL_CLEAN_CHECKER")
        .or_else(|| std::env::var_os("TCG_CLEAN_CHECKER"))
    {
        let pb = PathBuf::from(p);
        return pb.is_file().then_some(pb);
    }
    let home = std::env::var_os("HOME")?;
    let pb = PathBuf::from(home).join("Clean/target/release/clean");
    pb.is_file().then_some(pb)
}

/// Per-process capability memo keyed by path AND executable content identity.
/// Replacing a binary at an unchanged path cannot inherit the old verdict.
fn checker_capability_memo() -> &'static Mutex<HashMap<(PathBuf, String), Result<(), CheckerDefect>>>
{
    static MEMO: OnceLock<Mutex<HashMap<(PathBuf, String), Result<(), CheckerDefect>>>> =
        OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Can this checker verify ANY Alethe proof? Probes once per path+bytes per process
/// (~10ms) and warns loudly, exactly once, when the answer is no.
fn clean_checker_capability(path: &Path) -> Result<String, CheckerDefect> {
    let identity = crate::lrat_cert::checker_binary_sha256(path).ok_or_else(|| {
        CheckerDefect::NotRunnable("could not read/hash checker executable".to_string())
    })?;
    let key = (path.to_path_buf(), identity.clone());
    if let Some(verdict) = checker_capability_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .get(&key)
        .cloned()
    {
        return verdict.map(|()| identity);
    }
    let verdict = probe_clean_checker(path);
    let after = crate::lrat_cert::checker_binary_sha256(path);
    let verdict = if after.as_deref() == Some(identity.as_str()) {
        verdict
    } else {
        Err(CheckerDefect::NotRunnable(
            "checker executable identity changed during capability probe".to_string(),
        ))
    };
    let mut memo = checker_capability_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner());
    // Another thread may have raced us here; only the inserting thread warns,
    // so the diagnostic stays a single block however many threads probe.
    if !memo.contains_key(&key) {
        if let Err(defect) = &verdict {
            warn_checker_unusable(path, defect);
        }
        memo.insert(key, verdict.clone());
    }
    verdict.map(|()| identity)
}

/// The loud, self-explaining diagnostic. Deliberately NOT gated behind
/// `TCG_PROOF_CERT_STORE_DEBUG`: a provisioned-but-incapable checker silently
/// cost this repo 22 of 54 compile-gate outcomes, and silence is exactly the
/// property being fixed. Absence of a checker stays quiet (not having Clean
/// installed is a legitimate configuration); a checker that is PRESENT and
/// CANNOT WORK is always a misconfiguration worth a line of stderr.
fn warn_checker_unusable(path: &Path, defect: &CheckerDefect) {
    eprintln!(
        "\n\
         [trust-cg] INDEPENDENT PROOF CHECKER UNUSABLE — verification is DEGRADED\n\
         \x20 checker: {}\n\
         \x20 problem: {}\n\
         \x20 effect:  trust-cg is treating this checker as ABSENT rather than believing its\n\
         \x20          answers. Solver UNSAT verdicts can no longer be promoted to Verified,\n\
         \x20          and the Alethe certificate store will neither mint nor honor certs.\n\
         \x20 fix:     {}\n\
         \x20          (or point TCG_EXTERNAL_CLEAN_CHECKER at a binary built that way)\n",
        path.display(),
        defect.reason(),
        CLEAN_CHECKER_BUILD_LINE,
    );
}

/// Run the control pair through the checker and classify what came back.
fn probe_clean_checker(path: &Path) -> Result<(), CheckerDefect> {
    let Some(out) = run_clean_verify_external(path, CHECKER_PROBE_SMT2, CHECKER_PROBE_ALETHE)
    else {
        return Err(CheckerDefect::NotRunnable(
            "could not spawn the checker or stage its certificate".to_string(),
        ));
    };
    classify_probe_output(
        out.status.success(),
        &String::from_utf8_lossy(&out.stdout),
        &String::from_utf8_lossy(&out.stderr),
    )
}

/// Pure classifier over a probe transcript, so the mapping from Clean's actual
/// bytes to a defect is unit-testable without a subprocess.
fn classify_probe_output(
    status_success: bool,
    stdout: &str,
    stderr: &str,
) -> Result<(), CheckerDefect> {
    if status_success && clean_alethe_stdout_is_fully_verified(stdout) {
        return Ok(());
    }
    let transcript = format!("{stdout}\n{stderr}");
    if transcript.contains(CARCARA_FEATURE_MARKER) {
        return Err(CheckerDefect::CarcaraFeatureMissing);
    }
    if transcript.contains(AY_SMT_FEATURE_MARKER) {
        return Err(CheckerDefect::AySmtFeatureMissing);
    }
    let detail: String = transcript
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join(" | ");
    let detail = if detail.len() > 300 {
        format!("{}...", &detail[..300])
    } else if detail.is_empty() {
        "<no output>".to_string()
    } else {
        detail
    };
    Err(CheckerDefect::ControlProofRejected(detail))
}

/// Resolve the C0 Carcara/Clean external checker AND confirm it can actually
/// verify a proof. `None` => never skip, never promote — the checker is absent
/// or is one whose answers carry no information.
pub(crate) fn clean_checker_path() -> Option<PathBuf> {
    let pb = resolve_clean_checker_path()?;
    clean_checker_capability(&pb).ok().map(|_| pb)
}

fn clean_checker_path_and_identity() -> Option<(PathBuf, String)> {
    let path = resolve_clean_checker_path()?;
    let identity = clean_checker_capability(&path).ok()?;
    Some((path, identity))
}

/// Why no checker is available, for callers that must report WHY a proof could
/// not be promoted. `None` when a usable checker IS available.
///
/// This exists to keep two opposite situations from sharing one message:
/// "checked and refused" (the proof is bad — investigate the proof) versus
/// "cannot check at all" (the toolchain is misprovisioned — fix the build).
pub(crate) fn clean_checker_unavailable_reason() -> Option<String> {
    let Some(pb) = resolve_clean_checker_path() else {
        return Some(format!(
            "no external Clean/Carcara checker is installed at \
             $TCG_EXTERNAL_CLEAN_CHECKER (legacy $TCG_CLEAN_CHECKER) or \
             ~/Clean/target/release/clean (build one with `{CLEAN_CHECKER_BUILD_LINE}`)"
        ));
    };
    match clean_checker_capability(&pb) {
        Ok(_) => None,
        Err(defect) => Some(format!("{} is unusable: {}", pb.display(), defect.reason())),
    }
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
    let Some(checker) = clean_checker_path_and_identity() else {
        return false;
    };
    let path = cert_path(&dir, verdict_key);
    let Ok(cert_text) = std::fs::read_to_string(&path) else {
        return false;
    };
    let Some(solver_identity) = crate::ay_bridge::solver_identity_hash(solver_path) else {
        return false;
    };
    let memo_key = consume_memo_key(verdict_key, &solver_identity, smt2, &cert_text, &checker.1);
    if let Some(hit) = consume_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .get(&memo_key)
        .copied()
    {
        return hit;
    }
    let hit = consume_verified_text(&cert_text, verdict_key, solver_path, smt2, Some(checker));
    if hit {
        consume_memo()
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .insert(memo_key, true);
    }
    hit
}

/// Core of the consume path over explicit inputs (no memo / no env), so the
/// soundness tests can drive forged / tampered / mismatched stores.
#[cfg(test)]
fn consume_verified_in(
    dir: &Path,
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    checker: Option<(PathBuf, String)>,
) -> bool {
    let path = cert_path(dir, verdict_key);
    let Ok(text) = std::fs::read_to_string(&path) else {
        return false; // tooth 1: no cert for this key
    };
    consume_verified_text(&text, verdict_key, solver_path, smt2, checker)
}

fn consume_verified_text(
    text: &str,
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    checker: Option<(PathBuf, String)>,
) -> bool {
    let Some(cert) = AletheCert::parse(&text) else {
        trace!("{verdict_key}: malformed cert, declining");
        return false;
    };
    // Tooth 2: binding. Solver identity + exact SMT2 bytes.
    let Some(identity) = crate::ay_bridge::solver_identity_hash(solver_path) else {
        return false;
    };
    if crate::ay_bridge::verdict_cache_key_v2(&identity, smt2) != verdict_key {
        trace!("{verdict_key}: caller key does not derive from producer+query, declining");
        return false;
    }
    if identity != cert.producer_ay_identity {
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
    if cert.smt2.as_bytes() != smt2.as_bytes() {
        trace!("{verdict_key}: stored smt2 bytes differ from current query, declining");
        return false;
    }
    // Tooth 3: independent Carcara re-check against the CURRENT smt2.
    let Some((checker, checker_identity)) = checker else {
        trace!("{verdict_key}: no Carcara checker available, declining (fail-safe)");
        return false;
    };
    if checker_identity != cert.external_clean_checker_identity {
        trace!("{verdict_key}: external checker identity mismatch, declining");
        return false;
    }
    let ok =
        carcara_verify_with_expected_checker(&checker, &checker_identity, smt2, &cert.alethe_proof);
    trace!(
        "{verdict_key}: obligation={:?} carcara_verified={ok}",
        cert.obligation_name
    );
    ok
}

/// Stage the Carcara/Clean external cert JSON (the 2026-07-15 `verify-external`
/// contract): `{"type":"alethe_certificate","version":"1.0","problem":<smt2>,
/// "proof":<alethe>}` and run the checker over it. `None` when the request
/// could not be made at all (staging or spawn failed) — distinct from a
/// request the checker answered negatively.
fn run_clean_verify_external(
    checker: &Path,
    smt2: &str,
    alethe_proof: &str,
) -> Option<std::process::Output> {
    let dir = tempfile::tempdir().ok()?;
    let cert_json = dir.path().join("cert.json");
    let json = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": smt2,
        "proof": alethe_proof,
    });
    std::fs::write(&cert_json, serde_json::to_vec(&json).ok()?).ok()?;
    Command::new(checker)
        .arg("cert")
        .arg("verify-external")
        .arg(&cert_json)
        // Clean's verbose Alethe lane emits the proof-completeness status.
        // The non-verbose `... verification: PASSED` line alone does not
        // distinguish a fully checked proof from a future weaker success mode.
        .arg("--verbose")
        .output()
        .ok()
}

/// Returns true iff the checker reports a full, hole-free verification of this
/// exact proof. Callers must obtain `checker` from [`clean_checker_path`], so
/// a `false` here always means "this proof was checked and refused", never
/// "this binary refuses everything".
pub(crate) fn carcara_verify(checker: &Path, smt2: &str, alethe_proof: &str) -> bool {
    // Re-establish capability for the exact bytes about to perform this replay.
    // `clean_checker_path()` and this call are separated by ordinary caller
    // work, so a path-only handoff would otherwise admit a replacement binary
    // without probing it. The capability memo is keyed by path+SHA and the
    // replay hashes those same bytes before and after execution.
    let Ok(identity) = clean_checker_capability(checker) else {
        return false;
    };
    carcara_verify_with_expected_checker(checker, &identity, smt2, alethe_proof)
}

fn carcara_verify_with_expected_checker(
    checker: &Path,
    expected_checker_sha256: &str,
    smt2: &str,
    alethe_proof: &str,
) -> bool {
    if crate::lrat_cert::checker_binary_sha256(checker).as_deref() != Some(expected_checker_sha256)
    {
        return false;
    }
    let Some(out) = run_clean_verify_external(checker, smt2, alethe_proof) else {
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
    if !out.status.success()
        || crate::lrat_cert::checker_binary_sha256(checker).as_deref()
            != Some(expected_checker_sha256)
    {
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

/// Accept exactly one successful SMT-LIB `unsat` verdict from AY.
///
/// A substring check is not a protocol check: diagnostics such as "proof for
/// unsat was not produced" contain the same bytes, and a failed process can
/// still have written partial stdout. Certificate minting therefore requires a
/// successful child, one standalone `unsat` line, no competing verdict, and no
/// SMT-LIB error row.
fn ay_stdout_is_exact_unsat(status_success: bool, stdout: &str) -> bool {
    if !status_success
        || stdout
            .lines()
            .any(|line| line.trim_start().starts_with("(error"))
    {
        return false;
    }
    let verdicts: Vec<&str> = stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect();
    verdicts == ["unsat"]
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
    let Some((checker, checker_identity)) = clean_checker_path_and_identity() else {
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
        &checker_identity,
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
    expected_checker_identity: &str,
) -> bool {
    let path = cert_path(dir, verdict_key);
    if path.exists() {
        return false;
    }
    let Some(identity) = crate::ay_bridge::solver_identity_hash(solver_path) else {
        return false;
    };
    if crate::ay_bridge::verdict_cache_key_v2(&identity, smt2) != verdict_key {
        trace!("{verdict_key}: mint skipped (key does not derive from producer+query)");
        return false;
    }
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
    let stdout = String::from_utf8_lossy(&out.stdout);
    if !ay_stdout_is_exact_unsat(out.status.success(), &stdout) {
        trace!(
            "{verdict_key}: mint skipped (solver did not return one exact successful unsat verdict)"
        );
        return false;
    }
    let Ok(alethe_proof) = std::fs::read_to_string(&proof_path) else {
        return false;
    };
    if alethe_proof.trim().is_empty() {
        return false;
    }
    if crate::ay_bridge::solver_identity_hash(solver_path).as_deref() != Some(identity.as_str()) {
        trace!("{verdict_key}: mint skipped (AY producer bytes changed during proof emission)");
        return false;
    }
    // 2. Carcara MUST confirm the proof before we ever persist it.
    if !carcara_verify_with_expected_checker(
        checker,
        expected_checker_identity,
        smt2,
        &alethe_proof,
    ) {
        trace!("{verdict_key}: mint REFUSED (Carcara did not verify the fresh proof)");
        return false;
    }
    let cert = AletheCert {
        producer_ay_identity: identity,
        external_clean_checker_identity: expected_checker_identity.to_string(),
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

    /// VERBATIM `clean cert verify-external <control> --verbose` stdout from a
    /// `clean` built WITHOUT `carcara-verify` (exit 1). Captured on this box
    /// 2026-08-17 from the binary that silently voided 22 of 54 compile-gate
    /// outcomes. If Clean ever changes this text, the test that reads it fails
    /// LOUDLY rather than the probe quietly misclassifying the build again.
    const TRANSCRIPT_NO_CARCARA_STDOUT: &str = "External certificate verification: FAILED\n  \
        Type: Alethe SMT proof\n  Error: proof_verification_failed: carcara-verify feature \
        required for tier 1 verification\n  Time: 0.000031s\n";
    const TRANSCRIPT_NO_CARCARA_STDERR: &str = "Error: proof_verification_failed: carcara-verify feature required for tier 1 \
         verification\n";

    /// VERBATIM stdout from the same command on a `--features carcara-verify`
    /// build (exit 0), same control certificate.
    const TRANSCRIPT_CAPABLE_STDOUT: &str = "External certificate verification: PASSED\n  \
        Type: Alethe SMT proof\n  Problem bytes: 81, proof bytes: 84\n  Proof status: fully \
        verified\n  Verified in 0.000230s\n";

    fn write_cert(dir: &Path, key: &str, cert: &AletheCert) {
        std::fs::write(cert_path(dir, key), cert.serialize()).unwrap();
    }

    #[test]
    fn probe_accepts_a_checker_that_verifies_the_control_proof() {
        assert_eq!(
            classify_probe_output(true, TRANSCRIPT_CAPABLE_STDOUT, ""),
            Ok(())
        );
    }

    #[test]
    fn probe_names_the_missing_carcara_feature_rather_than_blaming_the_proof() {
        // THE REGRESSION UNDER TEST. This transcript is a content-INDEPENDENT
        // refusal: the checker did not evaluate the proof, it declined to have
        // an Alethe lane. It must never be reported as a rejected proof.
        assert_eq!(
            classify_probe_output(
                false,
                TRANSCRIPT_NO_CARCARA_STDOUT,
                TRANSCRIPT_NO_CARCARA_STDERR
            ),
            Err(CheckerDefect::CarcaraFeatureMissing)
        );
    }

    #[test]
    fn probe_diagnostic_quotes_the_build_line_that_fixes_it() {
        let reason = CheckerDefect::CarcaraFeatureMissing.reason();
        assert!(
            reason.contains(CLEAN_CHECKER_BUILD_LINE),
            "the missing-feature reason must be actionable, got: {reason}"
        );
        assert!(
            reason.contains("regardless of validity"),
            "the reason must say the refusal is content-independent, got: {reason}"
        );
    }

    #[test]
    fn probe_names_the_missing_ay_smt_feature_separately() {
        // The outer of the two gates in series produces a different message,
        // and a different rebuild conversation.
        assert_eq!(
            classify_probe_output(
                false,
                "External certificate verification: FAILED\n",
                "Error: verifier_not_available: ay-smt feature required for Alethe proof \
                 verification\n"
            ),
            Err(CheckerDefect::AySmtFeatureMissing)
        );
    }

    #[test]
    fn probe_rejects_a_binary_that_is_not_the_clean_checker() {
        // A wrong-but-runnable binary at the checker path used to be trusted
        // on a bare `is_file()`.
        let verdict = classify_probe_output(false, "", "error: unrecognized subcommand 'cert'\n");
        match verdict {
            Err(CheckerDefect::ControlProofRejected(detail)) => {
                assert!(
                    detail.contains("unrecognized subcommand"),
                    "detail: {detail}"
                );
            }
            other => panic!("expected ControlProofRejected, got {other:?}"),
        }
    }

    #[test]
    fn probe_rejects_a_silent_success_that_does_not_claim_full_verification() {
        // Exit 0 alone is not capability: the probe demands the same
        // `Proof status: fully verified` contract real obligations must meet,
        // so a future weaker success mode cannot silently pass the gate.
        assert!(matches!(
            classify_probe_output(true, "External certificate verification: PASSED\n", ""),
            Err(CheckerDefect::ControlProofRejected(_))
        ));
    }

    /// Stage an executable stub at `dir/clean` that replays a fixed
    /// transcript, so the resolve -> probe -> verdict path can be driven end to
    /// end without a 124 MB checker build.
    #[cfg(unix)]
    fn fake_checker(dir: &Path, stdout: &str, stderr: &str, code: i32) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = dir.join("clean");
        std::fs::write(
            &path,
            format!(
                "#!/bin/sh\nprintf '%s' {}\nprintf '%s' {} >&2\nexit {code}\n",
                shell_single_quote(stdout),
                shell_single_quote(stderr),
            ),
        )
        .unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        path
    }

    #[cfg(unix)]
    fn shell_single_quote(s: &str) -> String {
        format!("'{}'", s.replace('\'', r"'\''"))
    }

    #[cfg(unix)]
    #[test]
    fn incapable_checker_is_reported_absent_end_to_end() {
        let dir = tempfile::tempdir().unwrap();
        let checker = fake_checker(
            dir.path(),
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        // The binary EXISTS and RUNS — the old `is_file()` gate admitted it.
        assert!(checker.is_file());
        assert!(matches!(
            clean_checker_capability(&checker),
            Err(CheckerDefect::CarcaraFeatureMissing)
        ));
        // ...and a second call is served from the memo, so the loud diagnostic
        // is printed once per process, not once per obligation.
        assert!(matches!(
            clean_checker_capability(&checker),
            Err(CheckerDefect::CarcaraFeatureMissing)
        ));
    }

    #[cfg(unix)]
    #[test]
    fn capable_checker_passes_the_probe_end_to_end() {
        let dir = tempfile::tempdir().unwrap();
        let checker = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        assert!(clean_checker_capability(&checker).is_ok());
    }

    #[cfg(unix)]
    #[test]
    fn checker_replacement_at_same_path_cannot_inherit_capability() {
        let dir = tempfile::tempdir().unwrap();
        let checker = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let first_identity = clean_checker_capability(&checker).expect("capable checker");
        let replaced = fake_checker(
            dir.path(),
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        assert_eq!(checker, replaced);
        assert_ne!(
            crate::lrat_cert::checker_binary_sha256(&replaced).as_deref(),
            Some(first_identity.as_str())
        );
        assert!(matches!(
            clean_checker_capability(&replaced),
            Err(CheckerDefect::CarcaraFeatureMissing)
        ));
    }

    #[test]
    fn control_pair_is_a_real_refutation_not_a_placeholder() {
        // Guards against the probe degenerating into a liveness check: the
        // control must be an actual contradiction with an actual resolution
        // step, or a checker could "pass" it without doing any proof checking.
        assert!(CHECKER_PROBE_SMT2.contains("(assert p)"));
        assert!(CHECKER_PROBE_SMT2.contains("(assert (not p))"));
        assert!(CHECKER_PROBE_ALETHE.contains(":rule resolution"));
        assert!(
            CHECKER_PROBE_ALETHE.contains("(cl)"),
            "must derive the empty clause"
        );
    }

    #[test]
    fn ay_mint_requires_one_exact_successful_unsat_verdict() {
        assert!(ay_stdout_is_exact_unsat(true, "unsat\n"));
        assert!(ay_stdout_is_exact_unsat(
            true,
            "producer diagnostic\nunsat\nproof written\n"
        ));
        for (status, stdout) in [
            (false, "unsat\n"),
            (true, "solver could not produce an unsat proof\n"),
            (true, "unknown\n"),
            (true, "sat\n"),
            (true, "unsat\nsat\n"),
            (true, "unsat\nunsat\n"),
            (true, "(error \"proof emission failed\")\nunsat\n"),
        ] {
            assert!(
                !ay_stdout_is_exact_unsat(status, stdout),
                "must reject status={status} stdout={stdout:?}"
            );
        }
    }

    fn sample(smt2: &str, proof: &str, solver_id: &str) -> AletheCert {
        AletheCert {
            producer_ay_identity: solver_id.to_string(),
            external_clean_checker_identity: "55".repeat(32),
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
            &"aa".repeat(32),
        );
        let text = c.serialize();
        let p = AletheCert::parse(&text).expect("parses");
        assert_eq!(p.producer_ay_identity, c.producer_ay_identity);
        assert_eq!(
            p.external_clean_checker_identity,
            c.external_clean_checker_identity
        );
        assert_eq!(p.smt2_sha256, c.smt2_sha256);
        assert_eq!(p.obligation_name, c.obligation_name);
        assert_eq!(p.smt2, c.smt2);
        assert_eq!(p.alethe_proof, c.alethe_proof);
    }

    #[test]
    fn positive_replay_memo_binds_query_cert_producer_and_checker_bytes() {
        let make = |verdict: &str, producer: &str, smt2: &str, cert: &str, checker: &str| {
            consume_memo_key(verdict, producer, smt2, cert, checker)
        };
        let producer = "11".repeat(32);
        let checker = "22".repeat(32);
        let base = make(
            "verdict-a",
            &producer,
            "(assert false)",
            "certificate bytes",
            &checker,
        );
        for mutant in [
            make(
                "verdict-b",
                &producer,
                "(assert false)",
                "certificate bytes",
                &checker,
            ),
            make(
                "verdict-a",
                &"33".repeat(32),
                "(assert false)",
                "certificate bytes",
                &checker,
            ),
            make(
                "verdict-a",
                &producer,
                "(assert true)",
                "certificate bytes",
                &checker,
            ),
            make(
                "verdict-a",
                &producer,
                "(assert false)",
                "mutated certificate bytes",
                &checker,
            ),
            make(
                "verdict-a",
                &producer,
                "(assert false)",
                "certificate bytes",
                &"44".repeat(32),
            ),
        ] {
            assert_ne!(base, mutant);
        }
    }

    #[test]
    fn parse_rejects_wrong_schema() {
        assert!(AletheCert::parse("not-a-cert\nsolver-sha256:x\n").is_none());
        assert!(AletheCert::parse("tcg-alethe-cert-v1\nsolver-sha256:x\n").is_none());
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
        let presented = "(assert PROBLEM_B)";
        let key = crate::ay_bridge::verdict_cache_key_v2(&id, presented);
        write_cert(dir.path(), &key, &c);
        // Present a DIFFERENT smt2: binding tooth-2 must fail before any checker.
        let checker = Some((PathBuf::from("/bin/echo"), "55".repeat(32)));
        assert!(!consume_verified_in(
            dir.path(),
            &key,
            solver.to_str().unwrap(),
            presented,
            checker
        ));
    }

    #[test]
    fn consume_declines_solver_identity_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let solver = dir.path().join("solverbin");
        std::fs::write(&solver, b"solver-bytes").unwrap();
        let smt2 = "(assert false)";
        let actual_id = crate::ay_bridge::solver_identity_hash(solver.to_str().unwrap()).unwrap();
        let key = crate::ay_bridge::verdict_cache_key_v2(&actual_id, smt2);
        // Cert names a DIFFERENT solver identity than the resolved one.
        let c = sample(smt2, "proof", &"66".repeat(32));
        write_cert(dir.path(), &key, &c);
        let checker = Some((PathBuf::from("/bin/echo"), "55".repeat(32)));
        assert!(!consume_verified_in(
            dir.path(),
            &key,
            solver.to_str().unwrap(),
            smt2,
            checker
        ));
    }

    #[test]
    fn consume_declines_external_checker_identity_mismatch() {
        let dir = tempfile::tempdir().unwrap();
        let solver = dir.path().join("solverbin");
        std::fs::write(&solver, b"solver-bytes").unwrap();
        let solver_id = crate::ay_bridge::solver_identity_hash(solver.to_str().unwrap()).unwrap();
        let smt2 = "(assert false)";
        let key = crate::ay_bridge::verdict_cache_key_v2(&solver_id, smt2);
        let cert = sample(smt2, "proof", &solver_id);
        write_cert(dir.path(), &key, &cert);
        assert!(!consume_verified_in(
            dir.path(),
            &key,
            solver.to_str().unwrap(),
            smt2,
            Some((PathBuf::from("/bin/echo"), "77".repeat(32))),
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
    /// AY_SOLVER_PATH=/path/to/ay \
    /// TCG_EXTERNAL_CLEAN_CHECKER=/path/to/clean-with-carcara-verify \
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
                 AY_SOLVER_PATH and TCG_EXTERNAL_CLEAN_CHECKER paths to run"
            );
            return;
        }

        let ay = PathBuf::from(
            std::env::var_os("AY_SOLVER_PATH")
                .expect("AY_SOLVER_PATH must name the exact AY binary under test"),
        );
        let checker = PathBuf::from(
            std::env::var_os("TCG_EXTERNAL_CLEAN_CHECKER")
                .or_else(|| std::env::var_os("TCG_CLEAN_CHECKER"))
                .expect("TCG_EXTERNAL_CLEAN_CHECKER must name the exact checker under test"),
        );
        assert!(
            ay.is_file(),
            "AY_SOLVER_PATH is not a file: {}",
            ay.display()
        );
        assert!(
            checker.is_file(),
            "TCG_EXTERNAL_CLEAN_CHECKER is not a file: {}",
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
        let producer_identity = crate::ay_bridge::solver_identity_hash(ay).unwrap();
        let key = crate::ay_bridge::verdict_cache_key_v2(&producer_identity, smt2);
        let checker_identity = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();

        // MINT: real ay emits Alethe; Carcara pre-verifies; cert is written.
        let minted = mint_into(
            dir.path(),
            &key,
            ay,
            smt2,
            "false_qfbv",
            &checker,
            &checker_identity,
        );
        assert!(
            minted,
            "mint should succeed for a real unsat + verifiable proof"
        );
        assert!(cert_path(dir.path(), &key).exists(), "cert file written");

        // CONSUME (happy path): binding + independent Carcara re-check => hit.
        assert!(
            consume_verified_in(
                dir.path(),
                &key,
                ay,
                smt2,
                Some((checker.clone(), checker_identity.clone()))
            ),
            "a freshly minted, Carcara-verifiable cert must be honored"
        );

        // ADVERSARIAL 1 — tampered proof: Carcara must reject => no skip.
        {
            let path = cert_path(dir.path(), &key);
            let text = std::fs::read_to_string(&path).unwrap();
            let cert = AletheCert::parse(&text).unwrap();
            let mut bad = cert.clone();
            bad.alethe_proof = "(malformed".to_string();
            std::fs::write(&path, bad.serialize()).unwrap();
            assert!(
                !consume_verified_in(
                    dir.path(),
                    &key,
                    ay,
                    smt2,
                    Some((checker.clone(), checker_identity.clone()))
                ),
                "a proof Carcara cannot re-check must NOT be honored"
            );
            std::fs::write(path, text).unwrap();
        }

        // ADVERSARIAL 2 — wrong SMT2 presented: binding tooth-2 rejects before
        // any checker (even a real verifiable proof for a DIFFERENT problem).
        assert!(
            !consume_verified_in(
                dir.path(),
                &key,
                ay,
                "(set-logic QF_BV)\n(declare-const y (_ BitVec 8))\n(assert (= y y))\n(check-sat)\n",
                Some((checker.clone(), checker_identity.clone()))
            ),
            "a cert must never be served for a different query"
        );

        // ADVERSARIAL 3 — no checker: fail-safe decline even with a valid cert.
        assert!(
            !consume_verified_in(dir.path(), &key, ay, smt2, None),
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
        let key = crate::ay_bridge::verdict_cache_key_v2(&id, smt2);
        let c = sample(smt2, "proof", &id);
        write_cert(dir.path(), &key, &c);
        assert!(!consume_verified_in(
            dir.path(),
            &key,
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
