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
//!  * on a MISS it live-solves with AY, checks the exact emitted proof with
//!    Carcara via `clean cert verify-external` (the owning Trust toolchain's
//!    `clean`, else aterm's package; see `default_clean_checker_candidates`),
//!    and persists that same proof. Optional minting can derive/check another proof if no entry exists;
//!    both paths run synchronously and publish without replacing another entry;
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
//! A `clean` built without the `carcara-verify`
//! cargo feature answers EVERY Alethe request with "carcara-verify feature
//! required for tier 1 verification" — a content-INDEPENDENT refusal that a
//! file-existence check cannot distinguish from a capable binary.
//!
//! So checker discovery verifies a known-good CONTROL proof before admitting a
//! candidate. A complete rejection of that control means this binary is not
//! admitted as authority, and the diagnostic names the aterm package to repair.
//! Timeout/I/O failures are transient and do not poison capability memos. The frequently
//! polled [`clean_checker_path`] API caches only a positive scheduling hint;
//! every authority-bearing path uses [`clean_checker_path_and_identity_with_env`] and
//! re-binds the current executable bytes before and after actual replay.
//! AY configuration supplies a per-subprocess deadline for authority probes
//! and AY runs; zero is unlimited. A Clean check of a proof (the store's
//! re-check, the mint's check) runs under the checker's own deadline instead
//! ([`proof_check_timeout_ms`], ruling OD-223), never less than that solve
//! budget and never unbounded. Scheduling hints use the effective default.
//! This does not bound whole-query time, staging, hashing or OS calls.
//!
//! ON by default (since 88f8a7d1). `store_dir` resolves, in order:
//! `TCG_NO_CERT_STORE` or the global `TCG_NO_PROOF_CACHE` set => the tier is
//! OFF; else `TCG_PROOF_CERT_STORE` names an explicit directory; else the
//! per-box default `$XDG_CACHE_HOME/trust-cg/alethe-certs`, falling back to
//! `$HOME/.cache/trust-cg/alethe-certs` (only absolute values, by the one
//! user-cache rule `private_fs::user_cache_base`). Even with a directory, consume and
//! mint are inert while verdict-DB recording is active and whenever no
//! capable Carcara checker resolves. `TCG_PROOF_CERT_STORE_DEBUG=1` traces
//! consume/mint decisions.

use std::collections::{HashMap, HashSet, VecDeque};
use std::io::{self, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Mutex, OnceLock};
use std::time::Duration;

use crate::subprocess::{self, RunError};
use sha2::{Digest, Sha256};
use trust_cg_process_env::SanitizedChildEnv;

/// Same per-subprocess policy as AY: zero is unlimited, not an immediate expiry.
fn process_timeout(timeout_ms: u64) -> Option<Duration> {
    (timeout_ms != 0).then_some(Duration::from_millis(timeout_ms))
}

/// The default deadline, in milliseconds, of one Clean check of an AY Alethe
/// proof (ruling OD-223): 180 s of wall-clock time, separate from the AY solve
/// budget the check follows. The proof check is not the solve: on the Darwin
/// x86-64 qualification host AY 13556 answers `u64::leading_zeros`' body query
/// `unsat` in 7.6-8.0 s while Clean 5f09e36c needs 41-53 s of CPU time to
/// re-check its ~11 MB Alethe proof (51 s at load 8.8), so under the 30 s
/// solve budget that every check used to share the proof was never credited.
/// 180 s is 3.4 times that worst measured check. It changes completeness and
/// compile time only: Clean accepts the exact proof or nothing is credited.
pub(crate) const PROOF_CHECK_DEADLINE_MS: u64 = 180_000;

/// Overrides [`PROOF_CHECK_DEADLINE_MS`] with a positive number of
/// milliseconds of at most [`PROOF_CHECK_DEADLINE_CAP_MS`] (offline replays
/// and the deadline controls); anything else is ignored. A request freezes it
/// with the rest of its replay policy (`function_request::POLICY_KEYS`). It
/// does not reach a rustc-bridge compile, whose trustc refuses `TCG_*`
/// variables: there the default applies.
pub(crate) const PROOF_CHECK_TIMEOUT_ENV: &str = "TCG_CLEAN_CHECK_TIMEOUT_MS";

/// The largest checker deadline [`PROOF_CHECK_TIMEOUT_ENV`] may name (one
/// hour): the check is always bounded.
pub(crate) const PROOF_CHECK_DEADLINE_CAP_MS: u64 = 3_600_000;

/// The deadline of one Clean check of an AY Alethe proof that follows a solve
/// budgeted `solve_timeout_ms` (OD-223): the checker's own deadline
/// ([`PROOF_CHECK_DEADLINE_MS`], or [`PROOF_CHECK_TIMEOUT_ENV`]), never less
/// than the solve budget (a check never gets less time than before the
/// ruling), and never unbounded: a solve budget of zero ("no deadline") still
/// gives the check its own finite deadline. Every Clean check of a proof takes
/// it: the fresh replay's check of the proof AY just emitted, the certificate
/// store's re-check of a stored proof (and its prefetch), the mint's check,
/// and the check of a composed closed-definition proof. The checker's
/// capability probe of its control proof keeps the solve budget: it checks no
/// query's proof.
pub(crate) fn proof_check_timeout_ms(solve_timeout_ms: u64) -> u64 {
    let checker = trust_cg_process_env::var(PROOF_CHECK_TIMEOUT_ENV)
        .ok()
        .and_then(|value| value.trim().parse::<u64>().ok())
        .filter(|ms| (1..=PROOF_CHECK_DEADLINE_CAP_MS).contains(ms))
        .unwrap_or(PROOF_CHECK_DEADLINE_MS);
    checker.max(solve_timeout_ms)
}

/// Certificate schema tag, first line of every stored `.alethecert`.
const ALETHE_CERT_SCHEMA: &str = "tcg-alethe-cert-v2";

/// Store directory for per-box Alethe certs.
///
/// Resolution order: `TCG_NO_CERT_STORE` or the global proof-reuse kill switch
/// `TCG_NO_PROOF_CACHE` disables the tier entirely; `TCG_PROOF_CERT_STORE`
/// names an explicit directory; otherwise the per-box default
/// `<user cache>/trust-cg/alethe-certs`, the user cache by the one rule every
/// trust-cg cache root is resolved by
/// (`trust_cg_process_env::private_fs::user_cache_base`: an absolute
/// `$XDG_CACHE_HOME`, else an absolute `$HOME/.cache`; an empty or relative
/// value is ignored, never read against the working directory).
/// `None` when no location is resolvable — the tier is fail-closed-inert.
///
/// The default is safe to leave on everywhere: cert filenames are
/// `verdict_cache_key_v2(solver-bytes-sha256, smt2)`, so entries from
/// different solver builds (or test fixtures) can never collide, and the
/// consume path re-validates every binding and re-runs the independent
/// checker before memoizing a hit. Reuse of that positive replay is bound to
/// the current query, certificate bytes, producer and checker identities.
fn store_dir() -> Option<PathBuf> {
    store_dir_from(
        trust_cg_process_env::var_os("TCG_NO_CERT_STORE").is_some(),
        trust_cg_process_env::var_os("TCG_NO_PROOF_CACHE").is_some(),
        trust_cg_process_env::var_os("TCG_PROOF_CERT_STORE").map(PathBuf::from),
        trust_cg_process_env::var_os("XDG_CACHE_HOME"),
        trust_cg_process_env::var_os("HOME"),
    )
}

/// Freeze this store's resolution against one child snapshot: an explicit
/// relative `TCG_PROOF_CERT_STORE` names a path in its working directory; the
/// per-box default is absolute already.
pub(crate) fn captured_store_dir(child_env: &SanitizedChildEnv) -> Option<PathBuf> {
    child_env.anchor_path(&store_dir()?)
}

/// The per-box tier of the source-bound negative memo: its own namespace
/// ([`crate::source_bound_negative_memo::STORE_NAMESPACE`]) inside this store,
/// under the same resolution and kill switches (`None` when the store is off).
/// Its entries withhold credit only; they are never read as certificates.
pub(crate) fn negative_memo_dir() -> Option<PathBuf> {
    Some(store_dir()?.join(crate::source_bound_negative_memo::STORE_NAMESPACE))
}

/// The store that holds the replay-prefetch hints
/// ([`crate::cert_replay_prefetch`]), under the same resolution and kill
/// switches (`None` when the store is off). Hints name certificates to replay
/// early; they are never read as certificates or verdicts.
pub(crate) fn replay_hint_dir() -> Option<PathBuf> {
    store_dir()
}

/// Env-free core of [`store_dir`], so the resolution order is testable
/// without process-global environment races.
fn store_dir_from(
    no_cert_store: bool,
    no_proof_cache: bool,
    explicit: Option<PathBuf>,
    xdg_cache_home: Option<std::ffi::OsString>,
    home: Option<std::ffi::OsString>,
) -> Option<PathBuf> {
    if no_cert_store || no_proof_cache {
        return None;
    }
    if let Some(dir) = explicit {
        return Some(dir);
    }
    trust_cg_process_env::private_fs::user_cache_base(xdg_cache_home.as_deref(), home.as_deref())
        .ok()
        .map(|base| base.join("trust-cg").join("alethe-certs"))
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
const CONSUME_MEMO_CAPACITY: usize = 4_096;

#[derive(Default)]
struct ConsumeMemo {
    entries: HashSet<[u8; 32]>,
    insertion_order: VecDeque<[u8; 32]>,
    /// Memo keys whose replay is running now. A second request for the same
    /// key (the replay prefetch and the compile asking for one certificate at
    /// once) waits for that replay instead of starting another checker; it
    /// then finds the entry, or replays itself if the first replay failed.
    in_flight: HashSet<[u8; 32]>,
}

impl ConsumeMemo {
    fn contains(&self, key: &[u8; 32]) -> bool {
        self.entries.contains(key)
    }

    fn insert(&mut self, key: [u8; 32]) {
        if !self.entries.insert(key) {
            return;
        }
        self.insertion_order.push_back(key);
        while self.entries.len() > CONSUME_MEMO_CAPACITY {
            if let Some(evicted) = self.insertion_order.pop_front() {
                self.entries.remove(&evicted);
            }
        }
    }
}

/// Forget the in-process positive replay memo, as a new process starts.
#[cfg(test)]
pub(crate) fn forget_consume_memo_for_test() {
    *consume_memo().lock().unwrap_or_else(|p| p.into_inner()) = ConsumeMemo::default();
}

fn consume_memo() -> &'static Mutex<ConsumeMemo> {
    static MEMO: OnceLock<Mutex<ConsumeMemo>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(ConsumeMemo::default()))
}

/// Signalled whenever a replay in [`ConsumeMemo::in_flight`] finishes.
fn consume_memo_settled() -> &'static std::sync::Condvar {
    static SETTLED: std::sync::Condvar = std::sync::Condvar::new();
    &SETTLED
}

/// Claims `memo_key` for one replay. Dropping it, also on unwind, releases
/// the claim and wakes every waiter, so a panicking replay never strands one.
struct ReplayClaim {
    memo_key: [u8; 32],
    hit: bool,
}

impl Drop for ReplayClaim {
    fn drop(&mut self) {
        let mut memo = consume_memo().lock().unwrap_or_else(|p| p.into_inner());
        memo.in_flight.remove(&self.memo_key);
        if self.hit {
            memo.insert(self.memo_key);
        }
        drop(memo);
        consume_memo_settled().notify_all();
    }
}

/// `Ok(())` when `memo_key` already holds a positive replay; otherwise wait
/// for any replay of it in flight and, if that leaves no entry, claim it.
fn memo_hit_or_claim(memo_key: [u8; 32]) -> Result<(), ReplayClaim> {
    let mut memo = consume_memo().lock().unwrap_or_else(|p| p.into_inner());
    loop {
        if memo.contains(&memo_key) {
            return Ok(());
        }
        if memo.in_flight.insert(memo_key) {
            return Err(ReplayClaim {
                memo_key,
                hit: false,
            });
        }
        memo = consume_memo_settled()
            .wait(memo)
            .unwrap_or_else(|p| p.into_inner());
    }
}

fn consume_memo_key(
    verdict_key: &str,
    solver_identity: &str,
    smt2: &str,
    cert_text: &str,
    positive_reuse_context_id: &[u8; 32],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(b"trust-cg.alethe-consume-memo.v2\0");
    for (label, value) in [
        (b"verdict-key".as_slice(), verdict_key.as_bytes()),
        (b"solver-sha256".as_slice(), solver_identity.as_bytes()),
        (b"smt2".as_slice(), smt2.as_bytes()),
        (b"certificate".as_slice(), cert_text.as_bytes()),
        (
            b"positive-reuse-context".as_slice(),
            positive_reuse_context_id.as_slice(),
        ),
    ] {
        hasher.update((label.len() as u64).to_be_bytes());
        hasher.update(label);
        hasher.update((value.len() as u64).to_be_bytes());
        hasher.update(value);
    }
    hasher.finalize().into()
}

/// Product repair belongs to the toolchain and aterm's package channel, not a
/// sibling checkout.
const CLEAN_CHECKER_PACKAGE_HINT: &str = "the Trust toolchain's `bin/clean`, or else the aterm-managed Clean package (check `aterm pkg doctor` and `aterm pkg which clean`), must include carcara-verify";

/// [`CLEAN_CHECKER_PACKAGE_HINT`]'s subject, for a defect other than the
/// missing `carcara-verify` feature.
const CLEAN_CHECKER_PACKAGE_LOCATION: &str = "the Trust toolchain's `bin/clean`, or else the aterm-managed Clean package (check `aterm pkg doctor` and `aterm pkg which clean`),";

/// The script that assembles (and reassembles) an overlay toolchain.
const OVERLAY_ASSEMBLER: &str = "scripts/assemble_trust_overlay.py";

/// What an OVERLAY build's missing `bin/clean` needs: it never considers the
/// aterm package or an override, so only reassembling the overlay helps.
const CLEAN_CHECKER_OVERLAY_HINT: &str = "this trust-cg was built from an overlay toolchain, which uses only the overlay's own `bin/clean` (never the aterm-managed Clean package or a TCG_EXTERNAL_CLEAN_CHECKER override): reassemble the overlay (scripts/assemble_trust_overlay.py) with a Clean built with carcara-verify, then rebuild";

/// What repairs `defect`, found in a checker that `explicit` named (or that
/// default discovery found) under this build's policy: the DEGRADED banner's
/// `fix:` line and the tail of the unavailable reason.
///
/// It names the defect that was found, not the policy's generic repair: an
/// override with other bytes (a wrapper script, a copy, another build) is
/// repaired by unsetting it, an overlay `bin/clean` replaced after assembly by
/// restoring or reassembling it (its build features are not in question), and
/// only a checker without a feature by a Clean built with that feature. A
/// timed-out control probe is not a defect of the checker's build, so it gets
/// no build repair.
///
/// Always ONE line: it is embedded, once per failing candidate, in the
/// unavailable reason that `AYResult::Unknown` carries. The banner adds its
/// own development-only line ([`warn_checker_unusable`]).
fn checker_repair_hint(
    defect: &CheckerDefect,
    overlay: bool,
    explicit: Option<&CheckerOverride>,
) -> String {
    let needed = match defect {
        CheckerDefect::CarcaraFeatureMissing => "a Clean built with the `carcara-verify` feature",
        CheckerDefect::AySmtFeatureMissing => "a Clean built with the `ay-smt` feature",
        _ => "a Clean whose `cert verify-external` verifies the control proof",
    };
    match (defect, explicit) {
        (CheckerDefect::TimedOut(_), _) => String::from(
            "a timed-out control probe is not a defect of the checker's build; retry with a \
             larger solver budget or under less machine load",
        ),
        (CheckerDefect::NotTheOverlayChecker { expected, .. }, explicit) if expected.is_empty() => {
            format!(
                "this trust-cg was built from an overlay toolchain whose overlay.json was \
                 refused, so it accepts no checker{}: reassemble the overlay \
                 ({OVERLAY_ASSEMBLER}), then rebuild trust-cg",
                explicit
                    .map(|override_| format!(" (${} cannot change that)", override_.variable))
                    .unwrap_or_default()
            )
        }
        (CheckerDefect::NotTheOverlayChecker { expected, .. }, Some(override_)) => format!(
            "unset ${}: this trust-cg was built from an overlay toolchain and accepts only the \
             Clean its overlay.json names (sha256 {expected}), so a checker with other bytes \
             (a wrapper, a copy, another build) is refused; without the override the \
             overlay's own `bin/clean` is used (if ${} names that `bin/clean` itself, it was \
             replaced after assembly: restore it or reassemble the overlay \
             ({OVERLAY_ASSEMBLER}), then rebuild trust-cg)",
            override_.variable, override_.variable
        ),
        (CheckerDefect::NotTheOverlayChecker { expected, .. }, None) => format!(
            "the overlay's `bin/clean` no longer has the bytes its overlay.json names (sha256 \
             {expected}): it was replaced after assembly, so restore it or reassemble the \
             overlay ({OVERLAY_ASSEMBLER}), then rebuild trust-cg"
        ),
        (_, Some(override_)) if overlay => format!(
            "unset ${}: this trust-cg was built from an overlay toolchain and checks proofs \
             only with the overlay's own `bin/clean`, so an override can never supply {needed}",
            override_.variable
        ),
        (_, Some(override_)) => format!(
            "point ${} at {needed}, or unset it to use default discovery \
             ({CLEAN_CHECKER_PACKAGE_HINT})",
            override_.variable
        ),
        (_, None) if overlay => format!(
            "the overlay's own `bin/clean` is the only checker this build uses (never the \
             aterm-managed Clean package or an override): reassemble the overlay \
             ({OVERLAY_ASSEMBLER}) with {needed}, then rebuild trust-cg"
        ),
        (CheckerDefect::CarcaraFeatureMissing, None) => CLEAN_CHECKER_PACKAGE_HINT.to_owned(),
        (_, None) => format!("{CLEAN_CHECKER_PACKAGE_LOCATION} must be {needed}"),
    }
}

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
    /// The control did not finish within this request's budget. Not a cached
    /// defect in the executable, and not evidence that the proof is invalid.
    TimedOut(String),
    /// Capable, but not the checker the overlay toolchain that built this
    /// crate names (`ToolchainAyRecord::pinned_clean_sha256`).
    NotTheOverlayChecker {
        /// The overlay manifest's Clean digest (empty: the manifest was refused).
        expected: String,
        /// This file's digest.
        found: String,
    },
}

impl CheckerDefect {
    /// One-line reason, suitable for embedding in an `AYResult::Unknown`.
    fn reason(&self) -> String {
        match self {
            Self::CarcaraFeatureMissing => String::from(
                "it was built WITHOUT the `carcara-verify` cargo feature, so it rejects every \
                 Alethe proof regardless of validity",
            ),
            Self::AySmtFeatureMissing => String::from(
                "it was built WITHOUT the `ay-smt` cargo feature, so it has no Alethe lane at all",
            ),
            Self::ControlProofRejected(detail) => format!(
                "it did not verify a known-good control proof, so it cannot be trusted to \
                 verify real ones (transcript: {detail})"
            ),
            Self::NotRunnable(detail) => format!("it could not be executed ({detail})"),
            Self::TimedOut(detail) => format!("its control-proof probe timed out ({detail})"),
            Self::NotTheOverlayChecker { expected, found } if expected.is_empty() => format!(
                "trust-cg was built from an overlay toolchain whose manifest was refused, so it \
                 accepts no proof checker (this file's sha256 is {found}); reassemble the overlay"
            ),
            Self::NotTheOverlayChecker { expected, found } => format!(
                "trust-cg was built from an overlay toolchain whose overlay.json names the Clean \
                 with sha256 {expected}, but this file's sha256 is {found}; an overlay build \
                 never falls back to another checker"
            ),
        }
    }

    fn cacheable(&self) -> bool {
        matches!(
            self,
            Self::CarcaraFeatureMissing
                | Self::AySmtFeatureMissing
                | Self::ControlProofRejected(_)
                | Self::NotTheOverlayChecker { .. }
        )
    }
}

#[derive(Clone, Debug)]
pub(crate) enum CheckerResolutionError {
    Timeout,
    Unavailable(String),
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CheckerOverride {
    variable: &'static str,
    path: PathBuf,
}

#[derive(Clone, Debug)]
struct CheckerDiscovery {
    selected: Option<(PathBuf, String)>,
    /// Logical extension-less candidates, in the exact order considered.
    candidates: Vec<PathBuf>,
    /// Existing candidates that ran but failed the control-proof probe.
    unusable: Vec<(PathBuf, CheckerDefect)>,
    explicit: Option<CheckerOverride>,
    /// Discovered under an overlay build's pin ([`CheckerPolicy`]).
    overlay: bool,
}

/// The explicit role-named variable takes precedence; `TCG_CLEAN_CHECKER`
/// remains a legacy compatibility alias. An explicit value is authoritative:
/// a missing or incapable override does not silently fall through to a
/// different checker. Neither variable names the C1 dependency Clean role.
fn clean_checker_override() -> Option<CheckerOverride> {
    if let Some(path) = trust_cg_process_env::var_os("TCG_EXTERNAL_CLEAN_CHECKER") {
        return Some(CheckerOverride {
            variable: "TCG_EXTERNAL_CLEAN_CHECKER",
            path: PathBuf::from(path),
        });
    }
    trust_cg_process_env::var_os("TCG_CLEAN_CHECKER").map(|path| CheckerOverride {
        variable: "TCG_CLEAN_CHECKER",
        path: PathBuf::from(path),
    })
}

/// What a build accepts as its proof checker: the default candidates, in
/// order, and for an overlay build the one digest it accepts.
#[derive(Clone, Debug, PartialEq, Eq)]
struct CheckerPolicy {
    /// `None`: ordinary discovery. `Some(digest)`: an overlay build, which
    /// accepts only the checker with these bytes (`Some("")`, a refused
    /// manifest, accepts none). See `ToolchainAyRecord::pinned_clean_sha256`.
    pin: Option<String>,
    candidates: Vec<PathBuf>,
}

impl CheckerPolicy {
    fn overlay(&self) -> bool {
        self.pin.is_some()
    }
}

/// The Trust toolchain ships its own `clean`, and aterm also ships one as a
/// separately versioned package. Default discovery considers at most two
/// candidates, in order:
///
///  1. the `clean` of the OWNING Trust toolchain
///     ([`owning_toolchain_clean_checker_candidate_from`]): the toolchain whose
///     `bin/ay` [`crate::ay_identity`] admits as the solver, then
///  2. aterm's managed package (`store/clean/current/bin/clean`), for a
///     toolchain that ships no capable checker.
///
/// Neither is trusted for being found. Each is capability-probed against the
/// control proof and bound by its executable SHA-256 exactly like any other
/// checker. A candidate that fails the probe is skipped; it is reported with
/// the loud DEGRADED banner only when no default candidate is capable, and
/// otherwise with a one-line notice naming the checker used instead
/// ([`report_unusable_checkers`]). Do not silently substitute an arbitrary PATH
/// command or a developer's sibling build: any other development checker still
/// requires an explicit override, and an explicit override never falls back to
/// either.
///
/// The toolchain comes FIRST because a checker must read the proofs of the AY
/// it is paired with, and the toolchain ships the two as one sealed pair. The
/// package is versioned on its own. Measured 2026-09-27 (TRUSTCG-06): the
/// toolchain AY (ay 0.27.0, commit 3211f7fc7, Trust 450403669e) justifies
/// bit-vector ring identities with `poly_simp`; the managed package
/// (`store/clean/8606`) passes the control proof but rejects those steps
/// ("terms are not equal after arithmetic normalization: '(bvadd S A)' and
/// '(bvadd A S)'"), which production reads as a WORKING checker rejecting the
/// proof. The toolchain's own `clean` fully verifies the same proofs.
///
/// Stored certificates bind the checker digest that minted them, so a box
/// whose certificates were minted by the package checker re-solves them once:
/// a binding mismatch is a miss, never a weaker verdict.
///
/// A crate built from an OVERLAY toolchain has exactly one candidate, the
/// owning toolchain's `clean`, and accepts it only with the digest the overlay
/// manifest names ([`checker_policy_for`]): the overlay replaced the pack's AY,
/// and a checker that fails the probe must stop verification loudly, not be
/// swapped for the package checker (measured: an overlay whose `bin/clean`
/// lacked `carcara-verify` silently verified with `store/clean/8606`).
///
/// This is the policy of THIS build: [`checker_policy_for`] over the record
/// `build.rs` made, this process's executable, and aterm's package. Every
/// production discovery takes its candidates and pin from here.
fn checker_policy() -> CheckerPolicy {
    checker_policy_for(
        crate::ay_identity::ToolchainAyRecord::recorded(),
        std::env::current_exe().ok().as_deref(),
        || crate::aterm_toolchain::packaged_tool_path(crate::aterm_toolchain::ProofTool::Clean),
    )
}

/// The checker policy a toolchain record implies. An overlay record pins its
/// manifest's Clean digest and drops the package from the candidates, so the
/// owning toolchain's `bin/clean` is the only default; the package lookup is
/// not even made.
fn checker_policy_for(
    record: &crate::ay_identity::ToolchainAyRecord,
    running_executable: Option<&Path>,
    packaged: impl FnOnce() -> Option<PathBuf>,
) -> CheckerPolicy {
    let pin = record.pinned_clean_sha256().map(str::to_owned);
    let toolchain =
        owning_toolchain_clean_checker_candidate_from(running_executable, record.build_sysroot());
    let packaged = if pin.is_some() { None } else { packaged() };
    CheckerPolicy {
        pin,
        candidates: default_clean_checker_candidates_from(toolchain, packaged),
    }
}

#[cfg(test)]
fn default_clean_checker_candidates() -> Vec<PathBuf> {
    checker_policy().candidates
}

/// Refuse a capable checker that is not the overlay's (see
/// [`CheckerPolicy::pin`]).
fn overlay_pin_defect(pin: Option<&str>, identity: &str) -> Option<CheckerDefect> {
    let expected = pin?;
    (expected != identity).then(|| CheckerDefect::NotTheOverlayChecker {
        expected: expected.to_owned(),
        found: identity.to_owned(),
    })
}

/// Order and de-duplicate the default candidates (env-free, unit-testable).
fn default_clean_checker_candidates_from(
    toolchain: Option<PathBuf>,
    packaged: Option<PathBuf>,
) -> Vec<PathBuf> {
    let mut candidates: Vec<PathBuf> = toolchain.into_iter().collect();
    if let Some(packaged) = packaged
        && !candidates.contains(&packaged)
    {
        candidates.push(packaged);
    }
    candidates
}

/// The `clean` of the Trust toolchain that owns this code, named by the same
/// rule [`crate::ay_identity`] names the solver by: the Trust sysroot of the
/// compiler HOSTING this process when there is one
/// ([`trust_sysroot_clean_checker_candidate_for`]), otherwise the sysroot of
/// the compiler that BUILT this crate, as `build.rs` recorded it.
///
/// Without the second leg, a process no compiler hosts (this crate's tests,
/// `trust-cg` itself, examples) had no toolchain checker at all and could only
/// ever reach aterm's package, whatever toolchain built it and whatever AY that
/// toolchain ships.
#[cfg(test)]
fn owning_toolchain_clean_checker_candidate() -> Option<PathBuf> {
    owning_toolchain_clean_checker_candidate_from(
        std::env::current_exe().ok().as_deref(),
        crate::ay_identity::ToolchainAyRecord::recorded().build_sysroot(),
    )
}

/// Env-free core of [`owning_toolchain_clean_checker_candidate`].
fn owning_toolchain_clean_checker_candidate_from(
    running_executable: Option<&Path>,
    build_sysroot: &Path,
) -> Option<PathBuf> {
    running_executable
        .and_then(trust_sysroot_clean_checker_candidate_for)
        .or_else(|| trust_sysroot_clean_checker_candidate_in(build_sysroot))
}

/// `<sysroot>/bin/clean` when `sysroot` is an absolute Trust sysroot (it has
/// `lib/rustlib` and a `bin/trustc`). The build record is a path the building
/// compiler printed, not something the environment can steer; an empty
/// (unrecorded) or relative path would resolve against the working directory,
/// so it names nothing.
fn trust_sysroot_clean_checker_candidate_in(sysroot: &Path) -> Option<PathBuf> {
    if !sysroot.is_absolute() || !sysroot.join("lib").join("rustlib").is_dir() {
        return None;
    }
    let bin = sysroot.join("bin");
    bin.join(format!("trustc{}", std::env::consts::EXE_SUFFIX))
        .is_file()
        .then(|| bin.join("clean"))
}

/// The `clean` shipped in the same Trust sysroot as `executable`, if
/// `executable` lives in one.
///
/// A Trust sysroot is recognised structurally, the way rustc finds its own:
/// the CANONICAL executable sits in `<sysroot>/bin`, that directory also holds
/// `trustc`, and `<sysroot>/lib/rustlib` exists. Every in-process host of this
/// crate (`trustc`/`rustc` and the other drivers linking `rustc_interface`)
/// lives there. The location comes from the process image, never from an
/// environment variable, so a request-scoped environment cannot steer it, and
/// symlinks are resolved first, so a link to the compiler cannot adopt the
/// `clean` beside the LINK. An upstream Rust sysroot (no `trustc`), a cargo
/// `target/*/deps` directory, and a `bin` without `lib/rustlib` are rejected.
///
/// Why this may be a default at all: this `clean` is shipped by the same
/// toolchain artifact as the compiler performing the verification, so anyone
/// able to replace it can replace that compiler. Consulting it adds no
/// principal to the trusted base; the control probe and the digest binding
/// still decide whether its bytes are ever used.
fn trust_sysroot_clean_checker_candidate_for(executable: &Path) -> Option<PathBuf> {
    let executable = executable.canonicalize().ok()?;
    let bin = executable.parent()?;
    if bin.file_name()? != "bin" {
        return None;
    }
    trust_sysroot_clean_checker_candidate_in(bin.parent()?)
}

fn existing_checker_file(candidate: &Path) -> Option<PathBuf> {
    if candidate.is_file() {
        return Some(candidate.to_path_buf());
    }
    // The documented source-tree layouts use an extension-less executable.
    // Native Windows cargo builds produce `clean.exe`, however, so admit that
    // exact sibling just as AY's file-based discovery does.
    #[cfg(windows)]
    if candidate.extension().is_none() {
        let with_exe = candidate.with_extension("exe");
        if with_exe.is_file() {
            return Some(with_exe);
        }
    }
    None
}

/// Per-process capability memo keyed by path AND executable content identity.
/// Replacing a binary at an unchanged path cannot inherit the old verdict.
type CheckerCapabilityKey = (PathBuf, String, [u8; 32]);

const CHECKER_CAPABILITY_MEMO_CAPACITY: usize = 64;

#[derive(Default)]
struct CheckerCapabilityMemo {
    entries: HashMap<CheckerCapabilityKey, Result<(), CheckerDefect>>,
    insertion_order: VecDeque<CheckerCapabilityKey>,
}

fn checker_capability_memo() -> &'static Mutex<CheckerCapabilityMemo> {
    static MEMO: OnceLock<Mutex<CheckerCapabilityMemo>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(CheckerCapabilityMemo::default()))
}

/// Per-process control-proof VERDICT memo keyed by path, executable STAT
/// METADATA and child environment.
///
/// Separate from [`checker_capability_memo`], which is keyed by the
/// executable's CONTENT digest, because the two memos answer two different
/// questions at two different prices:
///
///  * AUTHORITY ("which bytes am I about to trust") needs the content digest
///    and is worth a full read of the executable.
///  * AVAILABILITY ("is a usable checker present at all") needs no identity.
///    The scheduling hint, [`clean_checker_path`], throws the identity away.
///
/// Keeping these roles separate avoids content hashing for scheduling. The
/// VERDICT stored here is shared by both lanes: it is a property of the bytes
/// a file state names, so the capability lane takes a verdict recorded here
/// for the identical state and environment in place of running the control
/// proof again ([`recorded_probe_verdict`]). That reuse is proof-relevant (it
/// can select the checker a certificate binds); the capability lane still
/// binds the digest of the current bytes to every capable answer, and
/// `TCG_PARANOID_FILE_HASH` refuses the reuse.
type CheckerAvailabilityMemo =
    Mutex<HashMap<(PathBuf, String, [u8; 32]), Result<(), CheckerDefect>>>;

fn checker_availability_memo() -> &'static CheckerAvailabilityMemo {
    static MEMO: OnceLock<CheckerAvailabilityMemo> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Can this checker verify the control proof? Memoize completed outcomes by
/// path+bytes and warn once per stable defect. Timeout, I/O and mid-probe
/// replacement remain retryable. A capable answer always carries the digest
/// of the executable's current bytes; scheduling hints cannot substitute for
/// this authority-bound check. The control proof itself runs at most once per
/// file state and child environment ([`recorded_probe_verdict`]).
#[cfg(test)]
fn clean_checker_capability(path: &Path, timeout_ms: u64) -> Result<String, CheckerDefect> {
    clean_checker_capability_with_env(path, &SanitizedChildEnv::capture_verifier(), timeout_ms)
}

fn clean_checker_capability_with_env(
    path: &Path,
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> Result<String, CheckerDefect> {
    clean_checker_capability_observed(path, child_env, timeout_ms, || {})
}

/// [`clean_checker_capability_with_env`] with `between_state_and_digest` run
/// after the file state is read and before the content digest is taken. The
/// production caller passes a no-op; a test uses it to replace the checker in
/// exactly the window the post-digest state recheck guards.
fn clean_checker_capability_observed(
    path: &Path,
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
    between_state_and_digest: impl FnOnce(),
) -> Result<String, CheckerDefect> {
    let env_digest = child_env.digest();
    // The file state this call starts from. A control-proof verdict already
    // recorded for exactly this state (by the availability probe, or by an
    // earlier capability probe) is the verdict a new probe would reach; see
    // [`recorded_probe_verdict`].
    let state = crate::lrat_cert::file_metadata_identity(path);
    let recorded = state
        .as_deref()
        .filter(|_| !crate::lrat_cert::paranoid_file_hash())
        .and_then(|state| recorded_probe_verdict(path, state, &env_digest));
    // A STABLE defect needs no content digest: a defective candidate is never
    // selected, so nothing would ever be bound to its bytes. Only the digest
    // is skipped; the verdict is the one the probe returned for this state.
    if let Some(Err(defect)) = recorded {
        return Err(defect);
    }
    between_state_and_digest();
    let identity = crate::lrat_cert::checker_binary_sha256(path).ok_or_else(|| {
        CheckerDefect::NotRunnable("could not read/hash checker executable".to_string())
    })?;
    let key = (path.to_path_buf(), identity.clone(), env_digest);
    if let Some(verdict) = checker_capability_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .entries
        .get(&key)
        .cloned()
    {
        return verdict.map(|()| identity);
    }
    // A capable verdict recorded for the state the digest was just taken in
    // binds to exactly these bytes: the file state is the same before and
    // after the digest, and the probe that recorded it saw that same state
    // before and after it ran. That is the strength of the probe below, whose
    // before/after digest compare is itself keyed by the same file state
    // (`checker_binary_sha256` memoizes on it).
    let verdict = match recorded {
        Some(Ok(())) if crate::lrat_cert::file_metadata_identity(path) == state => Ok(()),
        _ => {
            let verdict = probe_clean_checker_with_env(path, child_env, timeout_ms);
            let after = crate::lrat_cert::checker_binary_sha256(path);
            let after_state = crate::lrat_cert::file_metadata_identity(path);
            if after.as_deref() == Some(identity.as_str()) {
                // Share the outcome with the availability lane when the file
                // state held across the probe (the rule that lane applies).
                if let Some(state) = state.as_deref()
                    && after_state.as_deref() == Some(state)
                {
                    record_probe_verdict(path, state, env_digest, &verdict);
                }
                verdict
            } else {
                Err(CheckerDefect::NotRunnable(
                    "checker executable identity changed during capability probe".to_string(),
                ))
            }
        }
    };
    if let Err(defect) = &verdict
        && !defect.cacheable()
    {
        trace!("{}: {}", path.display(), defect.reason());
        return verdict.map(|()| identity);
    }
    let mut memo = checker_capability_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner());
    // Another thread may have raced us here. Use the stored result so all
    // racers observe one verdict. Discovery, which knows whether another
    // candidate was selected, reports a defect ([`report_unusable_checkers`]).
    if let Some(stored) = memo.entries.get(&key) {
        return stored.clone().map(|()| identity);
    }
    if memo.entries.len() == CHECKER_CAPABILITY_MEMO_CAPACITY
        && let Some(evicted) = memo.insertion_order.pop_front()
    {
        memo.entries.remove(&evicted);
    }
    memo.insertion_order.push_back(key.clone());
    memo.entries.insert(key, verdict.clone());
    verdict.map(|()| identity)
}

/// Is a USABLE checker present at `path`? Same probe as
/// [`clean_checker_capability`], memoized on file METADATA instead of content,
/// and returning no identity at all.
///
/// # What a recorded verdict is trusted for
///
/// The memo is process-local and never persisted. A verdict recorded here
/// answers two questions:
///
///  * AVAILABILITY, for the scheduling hint. A false negative only makes the
///    hint unavailable; a false positive sends the caller into the solver
///    lane, whose authority capture
///    ([`clean_checker_path_and_identity_with_env`]) selects again and binds
///    the selected checker's FULL CONTENT DIGEST before anything is credited.
///  * CAPABILITY, on that authority capture. It takes a verdict recorded here
///    for the identical file state and child environment in place of its own
///    control-proof run ([`recorded_probe_verdict`]), so this verdict CAN
///    decide which checker a certificate binds. Its strength is the
///    file-state assumption the capability lane's before/after digest compare
///    already rested on (that compare is memoized on the same stat tuple).
///    The digest bound to the answer is still that of the current bytes;
///    every promotion, stored-cert consume and replay still binds to
///    `checker_binary_sha256` bytes; and `TCG_PARANOID_FILE_HASH` refuses the
///    reuse and probes again.
///
/// The before/after metadata compare mirrors the capability path's before/after
/// hash compare, so a binary swapped mid-probe is rejected rather than
/// memoized under the identity it no longer has.
fn clean_checker_available(path: &Path, timeout_ms: u64) -> Result<(), CheckerDefect> {
    let child_env = SanitizedChildEnv::capture_verifier();
    let identity = crate::lrat_cert::file_metadata_identity(path).ok_or_else(|| {
        CheckerDefect::NotRunnable("could not stat checker executable".to_string())
    })?;
    let key = (path.to_path_buf(), identity.clone(), child_env.digest());
    if let Some(verdict) = checker_availability_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .get(&key)
        .cloned()
    {
        return verdict;
    }
    let verdict = probe_clean_checker_with_env(path, &child_env, timeout_ms);
    let after = crate::lrat_cert::file_metadata_identity(path);
    let verdict = if after.as_deref() == Some(identity.as_str()) {
        verdict
    } else {
        Err(CheckerDefect::NotRunnable(
            "checker executable metadata changed during availability probe".to_string(),
        ))
    };
    if let Err(defect) = &verdict
        && !defect.cacheable()
    {
        trace!("{}: {}", path.display(), defect.reason());
        return verdict;
    }
    let mut memo = checker_availability_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner());
    // Same racer discipline as the capability memo: all racers observe the one
    // stored result, and discovery reports a defect.
    memo.entry(key).or_insert(verdict).clone()
}

/// The control-proof verdict already recorded for `path` in exactly the file
/// state `state` ([`crate::lrat_cert::file_metadata_identity`]) under the
/// child environment `env_digest`, if any.
///
/// Both probe lanes record here only a verdict whose probe saw the same file
/// state before and after it ran, and only a completed one (capable, or a
/// stable defect; never a timeout or an I/O failure). A later probe of the
/// same state would therefore run the same bytes on the same control pair.
/// The state includes the inode, size, mtime and ctime, and any change to the
/// file moves ctime, which only root can set back — the same assumption the
/// content-digest memo ([`crate::lrat_cert::checker_binary_sha256`]) and the
/// capability lane's before/after compare already rest on.
///
/// The capability lane binds a reused capable verdict only if the file state
/// is still `state` after it took the content digest, so a checker replaced
/// between the state read and the digest is probed, not bound to the old
/// verdict. A verdict is never reused under another child environment.
///
/// Reusing it removes a duplicate `clean` process per candidate per compile:
/// the scheduling hint probes every default candidate at backend `init`, and
/// the authority capture used to probe each of them again.
fn recorded_probe_verdict(
    path: &Path,
    state: &str,
    env_digest: &[u8; 32],
) -> Option<Result<(), CheckerDefect>> {
    checker_availability_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .get(&(path.to_path_buf(), state.to_owned(), *env_digest))
        .cloned()
}

/// Record a completed capability-probe verdict for the availability lane.
/// Only a capable verdict or a stable defect is recorded; the caller has
/// checked that the file state held across the probe. An existing entry wins
/// (the availability lane's racer discipline).
fn record_probe_verdict(
    path: &Path,
    state: &str,
    env_digest: [u8; 32],
    verdict: &Result<(), CheckerDefect>,
) {
    if let Err(defect) = verdict
        && !defect.cacheable()
    {
        return;
    }
    checker_availability_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .entry((path.to_path_buf(), state.to_owned(), env_digest))
        .or_insert_with(|| verdict.clone());
}

/// How discovery reports a candidate that failed the control-proof probe.
#[derive(Clone, Debug, PartialEq, Eq)]
enum UnusableCheckerReport {
    /// Nothing capable was selected, so `Verified` is unreachable: the loud
    /// DEGRADED banner ([`warn_checker_unusable`]).
    Degraded,
    /// Discovery went on to select this checker: a one-line notice
    /// ([`note_checker_skipped`]). The DEGRADED banner's "Solver UNSAT verdicts
    /// can no longer be promoted" would be false here.
    SkippedFor(PathBuf),
}

/// Decide how each unusable candidate of one discovery is reported. Only
/// stable defects are reported: a timeout or an I/O failure is retryable, is
/// traced by the probe, and says nothing lasting about the executable.
fn unusable_checker_reports<'a>(
    unusable: &'a [(PathBuf, CheckerDefect)],
    selected: Option<&Path>,
) -> Vec<(&'a Path, &'a CheckerDefect, UnusableCheckerReport)> {
    unusable
        .iter()
        .filter(|(_, defect)| defect.cacheable())
        .map(|(path, defect)| {
            let report = match selected {
                Some(selected) => UnusableCheckerReport::SkippedFor(selected.to_path_buf()),
                None => UnusableCheckerReport::Degraded,
            };
            (path.as_path(), defect, report)
        })
        .collect()
}

/// Report the unusable candidates of one discovery (see
/// [`unusable_checker_reports`]). Each message prints once per process.
fn report_unusable_checkers(
    unusable: &[(PathBuf, CheckerDefect)],
    selected: Option<&Path>,
    overlay: bool,
    explicit: Option<&CheckerOverride>,
) {
    for (path, defect, report) in unusable_checker_reports(unusable, selected) {
        match report {
            UnusableCheckerReport::Degraded => {
                warn_checker_unusable(path, defect, overlay, explicit);
            }
            UnusableCheckerReport::SkippedFor(selected) => {
                note_checker_skipped(path, defect, &selected);
            }
        }
    }
}

/// A default candidate failed the probe but a later one is capable: say which
/// checker was skipped, why, and which one is used, once per process.
fn note_checker_skipped(path: &Path, defect: &CheckerDefect, selected: &Path) {
    static NOTED: OnceLock<Mutex<HashSet<(PathBuf, String, PathBuf)>>> = OnceLock::new();
    let first = NOTED
        .get_or_init(|| Mutex::new(HashSet::new()))
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .insert((path.to_path_buf(), defect.reason(), selected.to_path_buf()));
    if first {
        eprintln!(
            "[trust-cg] proof checker {} skipped ({}); using {}",
            path.display(),
            defect.reason(),
            selected.display(),
        );
    }
}

/// Stable capability defects in a provisioned checker must be visible, not
/// mistaken for invalid user proofs. Missing packages are explained by the
/// authority path; transient process failures are returned without this
/// package-repair warning.
fn warn_checker_unusable(
    path: &Path,
    defect: &CheckerDefect,
    overlay: bool,
    explicit: Option<&CheckerOverride>,
) {
    // There are TWO discoveries over the same probe (metadata-keyed
    // availability, content-keyed capability), so without this the same
    // misconfiguration would print the block twice on the exact path that
    // matters: an unusable checker makes `clean_checker_path` warn, then
    // `clean_checker_unavailable_reason` re-asks via the capability discovery
    // and warns again. The stated property is ONE loud block per problem per
    // process; keep it that way.
    static WARNED: OnceLock<Mutex<std::collections::HashSet<(PathBuf, String)>>> = OnceLock::new();
    let first = WARNED
        .get_or_init(|| Mutex::new(std::collections::HashSet::new()))
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .insert((path.to_path_buf(), defect.reason()));
    if !first {
        return;
    }
    eprintln!(
        "\n\
         [trust-cg] INDEPENDENT PROOF CHECKER UNUSABLE — verification is DEGRADED\n\
         \x20 checker: {}\n\
         \x20 problem: {}\n\
         \x20 effect:  trust-cg is treating this checker as ABSENT rather than believing its\n\
         \x20          answers. Solver UNSAT verdicts can no longer be promoted to Verified,\n\
         \x20          and the Alethe certificate store will neither mint nor honor certs.\n\
         \x20 fix:     {}\n{}",
        path.display(),
        defect.reason(),
        checker_repair_hint(defect, overlay, explicit),
        if overlay || explicit.is_some() {
            ""
        } else {
            "\x20          (development only: select a capable binary with \
             TCG_EXTERNAL_CLEAN_CHECKER)\n"
        },
    );
}

/// Run the control pair through the checker and classify what came back.
fn probe_clean_checker_with_env(
    path: &Path,
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> Result<(), CheckerDefect> {
    crate::process_cost::note_checker_probe();
    let out = run_clean_verify_external_with_env(
        path,
        CHECKER_PROBE_SMT2,
        CHECKER_PROBE_ALETHE,
        child_env,
        timeout_ms,
    );
    crate::process_cost::mark("checker_probe_done");
    let out = out.map_err(|error| match error {
        RunError::Timeout(_) => CheckerDefect::TimedOut(error.to_string()),
        RunError::Io { .. } => CheckerDefect::NotRunnable(error.to_string()),
    })?;
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
        format!("{}...", &detail[..detail.floor_char_boundary(300)])
    } else if detail.is_empty() {
        "<no output>".to_string()
    } else {
        detail
    };
    Err(CheckerDefect::ControlProofRejected(detail))
}

/// Select the first capable default checker, or probe only the explicit
/// override when one was supplied, under an ordinary (unpinned) policy. This
/// core takes all path inputs directly so search order and precedence can be
/// tested without mutating process-global environment variables.
#[cfg(test)]
fn discover_clean_checker_from(
    explicit: Option<CheckerOverride>,
    default_candidates: Vec<PathBuf>,
    timeout_ms: u64,
) -> CheckerDiscovery {
    discover_clean_checker_from_with_env(
        explicit,
        CheckerPolicy {
            pin: None,
            candidates: default_candidates,
        },
        &SanitizedChildEnv::capture_verifier(),
        timeout_ms,
    )
}

/// Discovery under `policy`: an explicit override replaces its candidates but
/// never its pin, so an overlay build refuses an override with other bytes.
fn discover_clean_checker_from_with_env(
    explicit: Option<CheckerOverride>,
    policy: CheckerPolicy,
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> CheckerDiscovery {
    let overlay = policy.overlay();
    let pin = policy.pin;
    let candidates = explicit
        .as_ref()
        .map(|override_| vec![override_.path.clone()])
        .unwrap_or(policy.candidates);
    let mut unusable = Vec::new();
    let mut selected = None;

    for logical_candidate in &candidates {
        let anchored = child_env.anchor_path(logical_candidate);
        let logical_candidate = anchored.as_ref().unwrap_or(logical_candidate);
        let Some(path) = existing_checker_file(logical_candidate) else {
            continue;
        };
        match clean_checker_capability_with_env(&path, child_env, timeout_ms) {
            Ok(identity) => match overlay_pin_defect(pin.as_deref(), &identity) {
                None => {
                    selected = Some((path, identity));
                    break;
                }
                Some(defect) => unusable.push((path, defect)),
            },
            Err(defect) => unusable.push((path, defect)),
        }
    }
    report_unusable_checkers(
        &unusable,
        selected.as_ref().map(|(path, _)| path.as_path()),
        overlay,
        explicit.as_ref(),
    );

    CheckerDiscovery {
        selected,
        candidates,
        unusable,
        explicit,
        overlay,
    }
}

fn discover_clean_checker(timeout_ms: u64) -> CheckerDiscovery {
    discover_clean_checker_from_with_env(
        clean_checker_override(),
        checker_policy(),
        &SanitizedChildEnv::capture_verifier(),
        timeout_ms,
    )
}

/// Select the first checker that passes the metadata-keyed availability probe,
/// or probe only the explicit override when one was supplied. The SELECTION is
/// a scheduling decision: the authority path below selects again and binds the
/// executable's full content digest. The control-proof verdicts recorded on
/// the way are reused by that path for the identical file state and child
/// environment ([`clean_checker_available`]).
fn discover_available_checker_path_from(
    explicit: Option<CheckerOverride>,
    default_candidates: Vec<PathBuf>,
    overlay: bool,
) -> Option<PathBuf> {
    let candidates = explicit
        .as_ref()
        .map(|override_| vec![override_.path.clone()])
        .unwrap_or(default_candidates);
    let mut unusable = Vec::new();
    let mut selected = None;
    for logical_candidate in candidates {
        let Some(path) = existing_checker_file(&logical_candidate) else {
            continue;
        };
        match clean_checker_available(&path, crate::ay_bridge::AYConfig::default().timeout_ms) {
            Ok(()) => {
                selected = Some(path);
                break;
            }
            Err(defect) => unusable.push((path, defect)),
        }
    }
    report_unusable_checkers(&unusable, selected.as_deref(), overlay, explicit.as_ref());
    selected
}

/// Positive-only scheduling-hint memo. The key is the complete ordered search
/// configuration (an explicit override is a one-element list). A hit may be
/// stale after an executable is replaced, so it MUST NOT authorize a proof;
/// it only avoids re-hashing a large checker on repeated "is the solver lane
/// worth scheduling?" polls. Every authority-bearing caller goes through
/// [`clean_checker_path_and_identity_with_env`] and hashes/probes the current bytes.
fn checker_path_hint_memo() -> &'static Mutex<HashMap<Vec<PathBuf>, PathBuf>> {
    static MEMO: OnceLock<Mutex<HashMap<Vec<PathBuf>, PathBuf>>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

fn clean_checker_path_hint_from(
    explicit: Option<CheckerOverride>,
    default_candidates: Vec<PathBuf>,
    overlay: bool,
) -> Option<PathBuf> {
    let key = explicit
        .as_ref()
        .map(|override_| vec![override_.path.clone()])
        .unwrap_or_else(|| default_candidates.clone());
    let selected = if let Some(path) = checker_path_hint_memo()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .get(&key)
        .cloned()
    {
        path
    } else {
        let selected = discover_available_checker_path_from(explicit, default_candidates, overlay)?;
        checker_path_hint_memo()
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
            .entry(key)
            .or_insert_with(|| selected.clone());
        selected
    };
    Some(selected)
}

/// Return a capability-probed path as a cheap scheduling hint. `None` means no
/// usable checker was found now. `Some` is deliberately NOT proof authority: a
/// positive hint can become stale if the executable is replaced. Proof replay
/// and promotion must resolve [`clean_checker_path_and_identity_with_env`] and retain
/// its before/after executable-identity checks.
pub(crate) fn clean_checker_path() -> Option<PathBuf> {
    let policy = checker_policy();
    let overlay = policy.overlay();
    let path = clean_checker_path_hint_from(clean_checker_override(), policy.candidates, overlay)?;
    warm_clean_checker_identity(&path);
    Some(path)
}

/// Start an opportunistic identity hash on a detached thread, at most once per
/// process. It cannot authorize a proof or replace the authority path's current
/// executable-identity checks, and has no subprocess to supervise.
fn warm_clean_checker_identity(path: &Path) {
    static STARTED: OnceLock<()> = OnceLock::new();
    let path = path.to_path_buf();
    STARTED.get_or_init(move || {
        let _ = std::thread::Builder::new()
            .name("trust-cg-checker-identity-warm".to_string())
            .spawn(move || {
                let _ = crate::lrat_cert::checker_binary_sha256(&path);
            });
    });
}

/// Resolve a currently capable checker and bind its exact executable identity.
/// It does not take the scheduling hint's selection: it walks the candidates
/// again and binds the selected checker's current content digest. It does
/// reuse a control-proof verdict the hint recorded for the identical file
/// state and child environment ([`recorded_probe_verdict`]) unless
/// `TCG_PARANOID_FILE_HASH` is set. Paranoid mode still permits a capability
/// memo hit keyed by the freshly computed content digest and child environment;
/// it does not require rerunning an already checked identical control proof.
/// It is the only discovery API that
/// authority-bearing certificate replay/mint paths may use.
#[cfg(test)]
pub(crate) fn clean_checker_path_and_identity(
    timeout_ms: u64,
) -> Result<(PathBuf, String), CheckerResolutionError> {
    resolve_checker_discovery(discover_clean_checker(timeout_ms))
}

pub(crate) fn clean_checker_path_and_identity_with_env(
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> Result<(PathBuf, String), CheckerResolutionError> {
    resolve_checker_discovery(discover_clean_checker_from_with_env(
        clean_checker_override(),
        checker_policy(),
        child_env,
        timeout_ms,
    ))
}

fn resolve_checker_discovery(
    discovery: CheckerDiscovery,
) -> Result<(PathBuf, String), CheckerResolutionError> {
    if let Some(selected) = discovery.selected {
        return Ok(selected);
    }
    if discovery
        .unusable
        .iter()
        .any(|(_, defect)| matches!(defect, CheckerDefect::TimedOut(_)))
    {
        return Err(CheckerResolutionError::Timeout);
    }
    Err(CheckerResolutionError::Unavailable(
        clean_checker_unavailable_reason_from(discovery)
            .unwrap_or_else(|| "no usable checker".to_string()),
    ))
}

/// The proof checker this build resolves now, as `(path, sha256)`, or why none
/// resolves: the discovery the certificate authority path runs, under this
/// build's [`checker_policy`] and the process environment (including
/// `TCG_EXTERNAL_CLEAN_CHECKER`). For reports and tests; the authority path
/// resolves again for every proof it checks.
pub fn resolve_proof_checker() -> Result<(PathBuf, String), String> {
    resolve_proof_checker_under(checker_policy())
}

/// [`resolve_proof_checker`] under `policy` in place of this build's.
fn resolve_proof_checker_under(policy: CheckerPolicy) -> Result<(PathBuf, String), String> {
    resolve_checker_discovery(discover_clean_checker_from_with_env(
        clean_checker_override(),
        policy,
        &SanitizedChildEnv::capture_verifier(),
        crate::ay_bridge::AYConfig::default().timeout_ms,
    ))
    .map_err(|error| match error {
        CheckerResolutionError::Timeout => "the proof checker's control probe timed out".into(),
        CheckerResolutionError::Unavailable(reason) => reason,
    })
}

/// [`resolve_proof_checker`] as an overlay build whose manifest names the
/// Clean with sha256 `pin` resolves it, on a build of any kind: for tests of
/// a caller that must refuse what such a build's authority refuses. The
/// override variables select the candidate, as in production; with neither
/// set there is none.
#[cfg(test)]
pub(crate) fn resolve_proof_checker_pinned_for_tests(
    pin: &str,
) -> Result<(PathBuf, String), String> {
    resolve_proof_checker_under(CheckerPolicy {
        pin: Some(pin.to_owned()),
        candidates: Vec::new(),
    })
}

/// A stub at `dir/clean` that passes the control-proof probe, for tests that
/// need a capable checker without a checker build.
#[cfg(all(test, unix))]
pub(crate) fn capable_checker_stub_for_tests(dir: &Path) -> PathBuf {
    tests::fake_checker(dir, tests::TRANSCRIPT_CAPABLE_STDOUT, "", 0)
}

/// Why no checker is available, for callers that must report WHY a proof could
/// not be promoted. `None` when a usable checker IS available.
///
/// This exists to keep two opposite situations from sharing one message:
/// "checked and refused" (the proof is bad — investigate the proof) versus
/// "cannot check at all" (the toolchain is misprovisioned — fix the build).
pub(crate) fn clean_checker_unavailable_reason() -> Option<String> {
    clean_checker_unavailable_reason_from(discover_clean_checker(
        crate::ay_bridge::AYConfig::default().timeout_ms,
    ))
}

/// Env-free diagnostic core paired with [`discover_clean_checker_from`].
fn clean_checker_unavailable_reason_from(discovery: CheckerDiscovery) -> Option<String> {
    if discovery.selected.is_some() {
        return None;
    }

    if let Some(override_) = discovery.explicit {
        if let Some((path, defect)) = discovery.unusable.first() {
            return Some(format!(
                "${} explicitly selects {}, but that checker is unusable: {}; explicit checker \
                 overrides do not fall back to auto-discovery; {}",
                override_.variable,
                path.display(),
                defect.reason(),
                checker_repair_hint(defect, discovery.overlay, Some(&override_)),
            ));
        }
        let path = if override_.path.as_os_str().is_empty() {
            "<empty path>".to_string()
        } else {
            override_.path.display().to_string()
        };
        return Some(format!(
            "${} explicitly selects {path}, but that path is not a checker file; explicit \
             checker overrides do not fall back to auto-discovery",
            override_.variable,
        ));
    }

    if !discovery.unusable.is_empty() {
        let detail = discovery
            .unusable
            .iter()
            .map(|(path, defect)| {
                format!(
                    "{} ({}; {})",
                    path.display(),
                    defect.reason(),
                    checker_repair_hint(defect, discovery.overlay, None)
                )
            })
            .collect::<Vec<_>>()
            .join("; ");
        return Some(format!(
            "no usable external Clean/Carcara checker was found; installed default candidate(s) \
             failed the control-proof probe: {detail}"
        ));
    }
    if discovery.overlay {
        let searched = discovery
            .candidates
            .iter()
            .map(|path| path.display().to_string())
            .collect::<Vec<_>>()
            .join(", ");
        return Some(format!(
            "no proof checker file at the overlay toolchain's {}; \
             {CLEAN_CHECKER_OVERLAY_HINT}",
            if searched.is_empty() {
                "bin/clean (the build recorded no Trust sysroot)".to_owned()
            } else {
                searched
            }
        ));
    }

    let searched = if discovery.candidates.is_empty() {
        "the owning Trust toolchain's sysroot (the hosting or the building compiler's), aterm \
         package prefixes on PATH, and the platform-default package store"
            .to_string()
    } else {
        discovery
            .candidates
            .iter()
            .map(|path| path.display().to_string())
            .collect::<Vec<_>>()
            .join(", ")
    };
    Some(format!(
        "no Trust-toolchain or aterm-managed Clean proof checker is installed; searched {searched}; \
         {CLEAN_CHECKER_PACKAGE_HINT}. For toolchain development only, set \
         $TCG_EXTERNAL_CLEAN_CHECKER (legacy $TCG_CLEAN_CHECKER) explicitly"
    ))
}

/// CONSUME (hot path): does a stored Alethe cert back `verdict_key`, and does
/// Carcara independently re-check its proof against the CURRENT SMT2, now?
///
/// `true` => skip the live solve (independently proven UNSAT). `false` => fall
/// through to the live solver — never a verdict of its own.
pub(crate) fn alethe_cert_skip_verified_with_authority(
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    authority: &crate::verification_authority::VerificationAuthority,
    timeout_ms: u64,
) -> bool {
    let Some(dir) = store_dir() else {
        return false;
    };
    // Regen / recording must always observe genuine live runs.
    if crate::verdict_db::recording_active() {
        return false;
    }
    let path = cert_path(&dir, verdict_key);
    let Ok(cert_text) = std::fs::read_to_string(&path) else {
        return false;
    };
    let hit = replay_cert_text(
        &cert_text,
        verdict_key,
        solver_path,
        smt2,
        authority,
        timeout_ms,
    );
    if hit {
        crate::cert_replay_prefetch::note_used(verdict_key);
    }
    hit
}

/// PREFETCH ([`crate::cert_replay_prefetch`]): replay the stored certificate
/// named `verdict_key` against its own SMT2 now, so that a later
/// [`alethe_cert_skip_verified_with_authority`] for the same exact query,
/// certificate bytes and authority finds the positive replay memo entry. It is
/// the consume path's replay with the query taken from the certificate:
/// `consume_verified_text` still requires the key to derive from the admitted
/// AY's identity and those bytes, and the recorded checker to re-check the
/// proof completely. Returns whether that replay succeeded; nothing else is
/// recorded, and a failure caches nothing.
pub(crate) fn prefetch_stored_cert(
    verdict_key: &str,
    authority: &crate::verification_authority::VerificationAuthority,
    timeout_ms: u64,
) -> bool {
    let Some(dir) = store_dir() else {
        return false;
    };
    if crate::verdict_db::recording_active() {
        return false;
    }
    let path = cert_path(&dir, verdict_key);
    let Ok(cert_text) = std::fs::read_to_string(&path) else {
        return false;
    };
    let Some(cert) = AletheCert::parse(&cert_text) else {
        trace!("{verdict_key}: prefetch: malformed cert, declining");
        return false;
    };
    replay_cert_text(
        &cert_text,
        verdict_key,
        authority.solver_path_text(),
        &cert.smt2,
        authority,
        timeout_ms,
    )
}

/// The replay both entry points share: the positive memo, a single in-flight
/// replay per memo key, then the full consume check.
fn replay_cert_text(
    cert_text: &str,
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    authority: &crate::verification_authority::VerificationAuthority,
    timeout_ms: u64,
) -> bool {
    let Some(checker) = authority.checker() else {
        return false;
    };
    let Some(positive_reuse_context_id) = authority.positive_reuse_context_id() else {
        return false;
    };
    replay_cert_text_with(
        cert_text,
        verdict_key,
        solver_path,
        smt2,
        (checker.path().to_path_buf(), checker.sha256().to_owned()),
        &positive_reuse_context_id,
        authority.child_env(),
        timeout_ms,
    )
}

/// [`replay_cert_text`] over an explicit checker, reuse context and child
/// environment (the authority's), so tests can drive the memo and the
/// in-flight registry with a stub checker.
#[allow(clippy::too_many_arguments)]
fn replay_cert_text_with(
    cert_text: &str,
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    checker: (PathBuf, String),
    positive_reuse_context_id: &[u8; 32],
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> bool {
    let Some(solver_identity) = crate::ay_bridge::solver_identity_hash(solver_path) else {
        return false;
    };
    let memo_key = consume_memo_key(
        verdict_key,
        &solver_identity,
        smt2,
        cert_text,
        positive_reuse_context_id,
    );
    let mut claim = match memo_hit_or_claim(memo_key) {
        Ok(()) => return true,
        Err(claim) => claim,
    };
    crate::process_cost::mark("cert_replay_begin");
    crate::process_cost::note_certificate_replay();
    let hit = consume_verified_text(
        cert_text,
        verdict_key,
        solver_path,
        smt2,
        Some(checker),
        child_env,
        timeout_ms,
    );
    crate::process_cost::mark("cert_replay_end");
    claim.hit = hit;
    drop(claim);
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
    let child_env = SanitizedChildEnv::capture_verifier();
    consume_verified_text(
        &text,
        verdict_key,
        solver_path,
        smt2,
        checker,
        &child_env,
        crate::ay_bridge::AYConfig::default().timeout_ms,
    )
}

fn consume_verified_text(
    text: &str,
    verdict_key: &str,
    solver_path: &str,
    smt2: &str,
    checker: Option<(PathBuf, String)>,
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> bool {
    let Some(cert) = AletheCert::parse(text) else {
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
    // The re-check runs under the checker's own deadline (OD-223), not the
    // solve budget `timeout_ms` names: a stored proof Clean needs longer than
    // the solve to re-check is still credited from the store.
    let ok = carcara_verify_with_expected_checker_with_env(
        &checker,
        &checker_identity,
        smt2,
        &cert.alethe_proof,
        child_env,
        proof_check_timeout_ms(timeout_ms),
    )
    .unwrap_or_else(|error| {
        trace!("{verdict_key}: replay failed: {error}");
        if crate::diag::solve_trace_enabled() {
            eprintln!(
                "TCG_SOLVE_TRACE cert_store_recheck_failed obligation={:?} proof_bytes={} {error}",
                cert.obligation_name,
                cert.alethe_proof.len(),
            );
        }
        false
    });
    trace!(
        "{verdict_key}: obligation={:?} carcara_verified={ok}",
        cert.obligation_name
    );
    ok
}

/// Stage the Carcara/Clean external cert JSON (the 2026-07-15 `verify-external`
/// contract): `{"type":"alethe_certificate","version":"1.0","problem":<smt2>,
/// "proof":<alethe>}` and capture the complete checker response under
/// `timeout_ms` (zero: unlimited, the per-process policy; a proof check passes
/// the checker's own deadline). Staging/I/O errors and timeouts remain distinct
/// from a complete response that rejects the proof.
fn run_clean_verify_external_with_env(
    checker: &Path,
    smt2: &str,
    alethe_proof: &str,
    child_env: &SanitizedChildEnv,
    timeout_ms: u64,
) -> Result<std::process::Output, RunError> {
    let stage_error = |source| RunError::Io {
        operation: "stage Clean certificate",
        source,
        cleanup: None,
    };
    let dir = tempfile::tempdir().map_err(stage_error)?;
    let cert_json = dir.path().join("cert.json");
    let json = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": smt2,
        "proof": alethe_proof,
    });
    let json = serde_json::to_vec(&json).map_err(|error| stage_error(io::Error::other(error)))?;
    std::fs::write(&cert_json, json).map_err(stage_error)?;
    let mut command = clean_verify_external_command(checker, &cert_json);
    child_env.apply_to_command(&mut command);
    subprocess::run(&mut command, process_timeout(timeout_ms))
}

/// The independent checker's arguments for one staged certificate. Clean's
/// verbose Alethe lane emits the proof-completeness status; the non-verbose
/// `... verification: PASSED` line alone does not distinguish a fully checked
/// proof from a future weaker success mode. Also rendered into the
/// source-bound negative memo's replay protocol.
pub(crate) fn clean_verify_external_args(cert_json: &Path) -> Vec<std::ffi::OsString> {
    vec![
        "cert".into(),
        "verify-external".into(),
        cert_json.as_os_str().to_owned(),
        "--verbose".into(),
    ]
}

/// The independent checker command for one staged certificate.
pub(crate) fn clean_verify_external_command(checker: &Path, cert_json: &Path) -> Command {
    let mut command = Command::new(checker);
    command.args(clean_verify_external_args(cert_json));
    command
}

/// Returns true iff the checker reports a full, hole-free verification of this
/// exact proof. [`clean_checker_path`] is only a scheduling hint and may become
/// stale, so this function re-establishes capability for the current bytes. A
/// `false` can therefore mean either replacement/unavailability or rejection;
/// authority-bearing production callers retain the richer identity-bound API.
#[cfg(test)]
pub(crate) fn carcara_verify(checker: &Path, smt2: &str, alethe_proof: &str) -> bool {
    // Re-establish capability for the exact bytes about to perform this replay.
    // `clean_checker_path()` and this call are separated by ordinary caller
    // work, so a path-only handoff would otherwise admit a replacement binary
    // without probing it. The capability memo is keyed by path+SHA and the
    // replay hashes those same bytes before and after execution.
    let timeout_ms = crate::ay_bridge::AYConfig::default().timeout_ms;
    let child_env = SanitizedChildEnv::capture_verifier();
    let Ok(identity) = clean_checker_capability_with_env(checker, &child_env, timeout_ms) else {
        return false;
    };
    carcara_verify_with_expected_checker_with_env(
        checker,
        &identity,
        smt2,
        alethe_proof,
        &child_env,
        timeout_ms,
    )
    .unwrap_or(false)
}

#[cfg(test)]
pub(crate) fn carcara_verify_with_expected_checker(
    checker: &Path,
    expected_checker_sha256: &str,
    smt2: &str,
    alethe_proof: &str,
    timeout_ms: u64,
) -> Result<bool, RunError> {
    carcara_verify_with_expected_checker_with_env(
        checker,
        expected_checker_sha256,
        smt2,
        alethe_proof,
        &SanitizedChildEnv::capture_verifier(),
        timeout_ms,
    )
}

/// One Clean check of `alethe_proof` against `smt2` by the checker whose bytes
/// hash to `expected_checker_sha256`, under `check_timeout_ms` (a proof
/// check's callers pass [`proof_check_timeout_ms`] of their solve budget, the
/// checker's own deadline). `Ok(true)` only for a complete, hole-free
/// verification by those bytes; `Err(RunError::Timeout)` when the deadline
/// expired, with the process group's CPU time under it.
pub(crate) fn carcara_verify_with_expected_checker_with_env(
    checker: &Path,
    expected_checker_sha256: &str,
    smt2: &str,
    alethe_proof: &str,
    child_env: &SanitizedChildEnv,
    check_timeout_ms: u64,
) -> Result<bool, RunError> {
    if crate::lrat_cert::checker_binary_sha256(checker).as_deref() != Some(expected_checker_sha256)
    {
        return Ok(false);
    }
    let out = run_clean_verify_external_with_env(
        checker,
        smt2,
        alethe_proof,
        child_env,
        check_timeout_ms,
    )?;
    if debug_enabled() {
        eprintln!(
            "[alethe-cert-store] checker={} status={} stdout={} stderr={}",
            checker.display(),
            out.status,
            String::from_utf8_lossy(&out.stdout).trim(),
            String::from_utf8_lossy(&out.stderr).trim(),
        );
    }
    let bound_after = crate::lrat_cert::checker_binary_sha256(checker).as_deref()
        == Some(expected_checker_sha256);
    if bound_after {
        // These bytes checked a proof (whatever the verdict): the gate's
        // identity record names them, not the file discovery expected.
        crate::proof_tool_record::note(
            crate::proof_tool_record::ProofTool::Clean,
            checker,
            expected_checker_sha256,
            None,
        );
    }
    if !out.status.success() || !bound_after {
        return Ok(false);
    }
    let stdout = String::from_utf8_lossy(&out.stdout);
    Ok(clean_alethe_stdout_is_fully_verified(&stdout))
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

/// Persist a proof the CURRENT process just Carcara-verified against `smt2`,
/// so the next identical compile on this box can skip the live derivation.
///
/// Unlike [`mint_alethe_cert_with_authority`] this never re-runs the solver: the proof in
/// hand is the one the independent checker accepted moments ago, and the
/// consume path re-validates every binding (and re-runs the checker) on every
/// hit — a bad write can only ever cost a cache miss, never an acceptance.
pub(crate) fn persist_verified_alethe(
    solver_path: &str,
    smt2: &str,
    obligation_name: &str,
    alethe_proof: &str,
    external_clean_checker_identity: &str,
) {
    let Some(dir) = store_dir() else {
        return;
    };
    if crate::verdict_db::recording_active() {
        return;
    }
    persist_verified_alethe_into(
        &dir,
        solver_path,
        smt2,
        obligation_name,
        alethe_proof,
        external_clean_checker_identity,
    );
}

/// Env-free core of [`persist_verified_alethe`] (no store gate, no recording
/// gate), so tests can drive the write path against explicit directories.
/// Returns whether a cert was written.
fn persist_verified_alethe_into(
    dir: &Path,
    solver_path: &str,
    smt2: &str,
    obligation_name: &str,
    alethe_proof: &str,
    external_clean_checker_identity: &str,
) -> bool {
    let Some(identity) = crate::ay_bridge::solver_identity_hash(solver_path) else {
        return false;
    };
    let verdict_key = crate::ay_bridge::verdict_cache_key_v2(&identity, smt2);
    let path = cert_path(dir, &verdict_key);
    if path.exists() {
        return false;
    }
    let cert = AletheCert {
        producer_ay_identity: identity,
        external_clean_checker_identity: external_clean_checker_identity.to_string(),
        smt2_sha256: sha256_hex(smt2.as_bytes()),
        obligation_name: obligation_name.to_string(),
        smt2: smt2.to_string(),
        alethe_proof: alethe_proof.to_string(),
    };
    if !publish_cert(dir, &path, &cert) {
        return false;
    }
    trace!("{verdict_key}: persisted promotion-time cert for {obligation_name:?}");
    crate::cert_replay_prefetch::note_used(&verdict_key);
    true
}

/// Synchronous, optional mint-on-miss. Re-run AY, check its exact proof with
/// the identity-bound aterm checker, then publish without clobbering an entry.
/// AY runs under the caller's solve budget and the check under the checker's
/// own deadline ([`proof_check_timeout_ms`]); failure does not publish a cert.
pub(crate) fn mint_alethe_cert_with_authority(
    verdict_key: &str,
    smt2: &str,
    obligation_name: &str,
    authority: &crate::verification_authority::VerificationAuthority,
    timeout_ms: u64,
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
    let Some(checker) = authority.checker() else {
        trace!("{verdict_key}: mint skipped (no Carcara checker to pre-verify)");
        return;
    };
    let ok = mint_into_with_env(
        &MintRequest {
            dir: &dir,
            verdict_key,
            solver: authority.solver(),
            smt2,
            obligation_name,
            checker: checker.path(),
            expected_checker_identity: checker.sha256(),
            timeout_ms,
        },
        authority.child_env(),
    );
    if ok {
        trace!("{verdict_key}: minted Carcara-verified cert for {obligation_name:?}");
        crate::cert_replay_prefetch::note_used(verdict_key);
    }
}

/// The inputs of ONE mint: the store to publish into, the verdict the cert is
/// bound to, the producer to re-run, and the checker identity that must confirm
/// the fresh proof. Grouped so the mint entry points name the same request.
struct MintRequest<'a> {
    dir: &'a Path,
    verdict_key: &'a str,
    solver: &'a crate::ay_identity::PinnedAy,
    smt2: &'a str,
    obligation_name: &'a str,
    checker: &'a Path,
    expected_checker_identity: &'a str,
    timeout_ms: u64,
}

/// Mint core over explicit paths (no env / no store-gate), so the end-to-end
/// integration test can drive the real ay->Carcara->write cycle. Returns
/// whether a cert was written. NEVER writes a cert Carcara did not verify.
#[cfg(test)]
fn mint_into(request: &MintRequest<'_>) -> bool {
    mint_into_with_env(request, &SanitizedChildEnv::capture_verifier())
}

fn mint_into_with_env(request: &MintRequest<'_>, child_env: &SanitizedChildEnv) -> bool {
    let &MintRequest {
        dir,
        verdict_key,
        solver,
        smt2,
        obligation_name,
        checker,
        expected_checker_identity,
        timeout_ms,
    } = request;
    let path = cert_path(dir, verdict_key);
    if path.exists() {
        return false;
    }
    // The producer is an admitted AY: its identity is the digest it was
    // admitted with, valid while the file is unchanged.
    if solver.revalidate().is_err() {
        trace!("{verdict_key}: mint skipped (the admitted AY changed on disk)");
        return false;
    }
    let identity = solver.sha256().to_owned();
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
    let Ok(mut command) = solver.command() else {
        trace!("{verdict_key}: mint skipped (the admitted AY changed on disk)");
        return false;
    };
    command
        .arg("solve")
        .arg(&smt2_path)
        .arg("--proof")
        .arg(&proof_path)
        .arg("--proof-format")
        .arg("alethe");
    child_env.apply_to_command(&mut command);
    let out = match subprocess::run(&mut command, process_timeout(timeout_ms)) {
        Ok(out) => out,
        Err(error) => {
            trace!("{verdict_key}: AY certificate emission failed: {error}");
            return false;
        }
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
    if solver.revalidate().is_err() {
        trace!("{verdict_key}: mint skipped (AY producer bytes changed during proof emission)");
        return false;
    }
    // 2. Carcara MUST confirm the proof before we ever persist it, under the
    // checker's own deadline (OD-223); the solve above had `timeout_ms`.
    if !carcara_verify_with_expected_checker_with_env(
        checker,
        expected_checker_identity,
        smt2,
        &alethe_proof,
        child_env,
        proof_check_timeout_ms(timeout_ms),
    )
    .unwrap_or_else(|error| {
        trace!("{verdict_key}: mint replay failed: {error}");
        false
    }) {
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
    // 3. Publish only the fully staged, independently checked certificate.
    publish_cert(dir, &path, &cert)
}

/// Each publisher owns a newly created staging file, including same-process
/// threads. Publish without replacing an existing entry or following a shared
/// predictable staging path. This is not a durability guarantee: some platforms
/// may leave a second hard link after publication/crash; replay always rechecks
/// the certificate. The store directory must not be attacker-controlled.
fn publish_cert(dir: &Path, path: &Path, cert: &AletheCert) -> bool {
    // Under the user cache this is `<cache>/trust-cg/alethe-certs`: every
    // directory created is `0700` whatever the umask, so the shared
    // `trust-cg` root it may create never refuses the AY private copy.
    if trust_cg_process_env::private_fs::create_private_dir_all(dir).is_err() {
        return false;
    }
    let Ok(mut tmp) = tempfile::NamedTempFile::new_in(dir) else {
        return false;
    };
    if tmp.write_all(cert.serialize().as_bytes()).is_err() {
        return false;
    }
    tmp.persist_noclobber(path).is_ok()
}

#[cfg(all(test, unix))]
#[path = "obligation_cert_store_process_tests.rs"]
mod process_tests;

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
    pub(super) const TRANSCRIPT_CAPABLE_STDOUT: &str = "External certificate verification: PASSED\n  \
        Type: Alethe SMT proof\n  Problem bytes: 81, proof bytes: 84\n  Proof status: fully \
        verified\n  Verified in 0.000230s\n";

    fn write_cert(dir: &Path, key: &str, cert: &AletheCert) {
        std::fs::write(cert_path(dir, key), cert.serialize()).unwrap();
    }

    #[test]
    fn cert_store_regression_unicode_probe_diagnostic_is_bounded_without_panicking() {
        let transcript = format!("{}é{}", "a".repeat(299), "x".repeat(40));
        let Err(CheckerDefect::ControlProofRejected(detail)) =
            classify_probe_output(false, &transcript, "")
        else {
            panic!("the control must be rejected with a diagnostic");
        };
        assert_eq!(detail, format!("{}...", "a".repeat(299)));
    }

    #[cfg(unix)]
    #[test]
    fn cert_store_regression_persistence_does_not_follow_shared_staging_symlinks() {
        let dir = tempfile::tempdir().unwrap();
        let solver = dir.path().join("solver");
        std::fs::write(&solver, "producer bytes").unwrap();
        let solver = solver.to_str().unwrap();
        let identity = crate::ay_bridge::solver_identity_hash(solver).unwrap();
        let smt2 = "(assert false)";
        let key = crate::ay_bridge::verdict_cache_key_v2(&identity, smt2);
        let sentinel = dir.path().join("unrelated-file");
        std::fs::write(&sentinel, "must not change").unwrap();
        let shared = dir
            .path()
            .join(format!(".{key}.{}.tmp", std::process::id()));
        std::os::unix::fs::symlink(&sentinel, &shared).unwrap();
        assert!(persist_verified_alethe_into(
            dir.path(),
            solver,
            smt2,
            "control",
            "proof",
            &"55".repeat(32)
        ));
        assert_eq!(
            std::fs::read_to_string(&sentinel).unwrap(),
            "must not change"
        );
        assert!(
            !std::fs::symlink_metadata(cert_path(dir.path(), &key))
                .unwrap()
                .file_type()
                .is_symlink()
        );
        assert!(
            shared.is_symlink(),
            "unowned staging debris must be untouched"
        );
    }

    #[test]
    fn cert_store_regression_concurrent_publishers_cannot_replace_or_mix_entries() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("entry.alethecert");
        let barrier = std::sync::Barrier::new(16);
        let winners = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..16)
                .map(|index| {
                    let barrier = &barrier;
                    let path = &path;
                    let dir = dir.path();
                    scope.spawn(move || {
                        let cert = sample(
                            "(assert false)",
                            &format!("{index}").repeat(131072),
                            &"44".repeat(32),
                        );
                        barrier.wait();
                        publish_cert(dir, path, &cert).then(|| cert.serialize())
                    })
                })
                .collect();
            handles
                .into_iter()
                .filter_map(|handle| handle.join().unwrap())
                .collect::<Vec<_>>()
        });
        assert_eq!(
            winners.len(),
            1,
            "publication is no-clobber even for racing threads"
        );
        assert_eq!(std::fs::read_to_string(&path).unwrap(), winners[0]);
        assert_eq!(std::fs::read_dir(dir.path()).unwrap().count(), 1);
        let cert = sample("(assert false)", "later entry", &"44".repeat(32));
        assert!(!publish_cert(dir.path(), &path, &cert));
        assert_eq!(std::fs::read_to_string(&path).unwrap(), winners[0]);
        let occupied = dir.path().join("occupied");
        std::fs::create_dir(&occupied).unwrap();
        assert!(!publish_cert(dir.path(), &occupied, &cert));
        assert_eq!(
            std::fs::read_dir(dir.path()).unwrap().count(),
            2,
            "failed publisher cleans its own staging file"
        );
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
    fn probe_diagnostic_names_the_aterm_package_capability_defect() {
        let reason = CheckerDefect::CarcaraFeatureMissing.reason();
        let repair = checker_repair_hint(&CheckerDefect::CarcaraFeatureMissing, false, None);
        assert!(
            repair.contains(CLEAN_CHECKER_PACKAGE_HINT),
            "the missing-feature repair must be actionable, got: {repair}"
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
    pub(super) fn fake_checker(dir: &Path, stdout: &str, stderr: &str, code: i32) -> PathBuf {
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
    pub(super) fn shell_single_quote(s: &str) -> String {
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
            clean_checker_capability(&checker, 30_000),
            Err(CheckerDefect::CarcaraFeatureMissing)
        ));
        // ...and a second call is served from the memo, so the loud diagnostic
        // is printed once per process, not once per obligation.
        assert!(matches!(
            clean_checker_capability(&checker, 30_000),
            Err(CheckerDefect::CarcaraFeatureMissing)
        ));
    }

    #[cfg(unix)]
    #[test]
    fn capable_checker_passes_the_probe_end_to_end() {
        let dir = tempfile::tempdir().unwrap();
        let checker = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        assert!(clean_checker_capability(&checker, 30_000).is_ok());
    }

    // -----------------------------------------------------------------------
    // The AVAILABILITY lane: same probe, metadata-keyed, no content digest.
    // -----------------------------------------------------------------------

    #[cfg(unix)]
    #[test]
    fn availability_probe_answers_the_same_question_as_capability() {
        let dir = tempfile::tempdir().unwrap();
        let capable = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        assert!(clean_checker_available(&capable, 30_000).is_ok());
        // ...and a second call is served from the metadata memo.
        assert!(clean_checker_available(&capable, 30_000).is_ok());

        let broken_dir = tempfile::tempdir().unwrap();
        let broken = fake_checker(
            broken_dir.path(),
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        assert!(matches!(
            clean_checker_available(&broken, 30_000),
            Err(CheckerDefect::CarcaraFeatureMissing)
        ));

        assert!(matches!(
            clean_checker_available(&dir.path().join("absent"), 30_000),
            Err(CheckerDefect::NotRunnable(_))
        ));
    }

    /// Stage a checker that REPLACES ITSELF while the probe is running, by
    /// rename (the ordinary way a rebuilt binary lands). The running `sh`
    /// keeps its open fd, so the transcript is still emitted — but the
    /// after-probe metadata no longer matches the before-probe metadata.
    #[cfg(unix)]
    fn self_replacing_checker(dir: &Path, stdout: &str) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = dir.join("clean");
        std::fs::write(
            &path,
            format!(
                "#!/bin/sh\nprintf '%s' {}\ncp \"$0\" \"$0.new\"\nprintf '\\n# swapped\\n' >> \
                 \"$0.new\"\nmv \"$0.new\" \"$0\"\nexit 0\n",
                shell_single_quote(stdout),
            ),
        )
        .unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        path
    }

    #[cfg(unix)]
    #[test]
    fn availability_memo_rejects_a_binary_swapped_mid_probe() {
        // The metadata-keyed memo must have the same tooth as the content-keyed
        // one: a checker replaced WHILE its own probe runs must be reported
        // unusable, not memoized as capable under the identity it no longer
        // has. Mirrors the capability path's before/after hash compare.
        let dir = tempfile::tempdir().unwrap();
        let checker = self_replacing_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT);
        let before = crate::lrat_cert::file_metadata_identity(&checker).unwrap();

        let verdict = clean_checker_available(&checker, 30_000);

        let after = crate::lrat_cert::file_metadata_identity(&checker).unwrap();
        assert_ne!(
            before, after,
            "the stub must actually replace itself, or this test is vacuous"
        );
        match verdict {
            Err(CheckerDefect::NotRunnable(detail)) => {
                assert!(
                    detail.contains("metadata changed"),
                    "rejected for the wrong reason: {detail}"
                );
            }
            other => panic!("a mid-probe replacement must be rejected, got {other:?}"),
        }
        // Nothing was memoized under the pre-swap identity as capable: asking
        // again about those exact (now gone) bytes must not answer Ok.
        assert!(
            checker_availability_memo()
                .lock()
                .unwrap_or_else(|p| p.into_inner())
                .get(&(
                    checker.clone(),
                    before,
                    SanitizedChildEnv::capture_verifier().digest()
                ))
                .is_none_or(|v| v.is_err())
        );
    }

    #[cfg(unix)]
    #[test]
    fn availability_probe_never_streams_the_checkers_bytes() {
        // The whole point of the change: the availability question must be
        // ANSWERABLE without a content read. Pin it on `clean_checker_available`
        // itself — `clean_checker_path` additionally kicks the off-critical-path
        // identity warm, whose whole job is to hash, so counting there would
        // measure the wrong thing.
        let dir = tempfile::tempdir().unwrap();
        let checker = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let before = crate::lrat_cert::file_hash_computation_count(&checker);
        assert!(clean_checker_available(&checker, 30_000).is_ok());
        assert_eq!(
            crate::lrat_cert::file_hash_computation_count(&checker),
            before,
            "the availability probe must not stream the checker's bytes"
        );
    }

    #[cfg(unix)]
    #[test]
    fn clean_checker_path_resolves_a_capable_checker_end_to_end() {
        let dir = tempfile::tempdir().unwrap();
        let checker = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let resolved = trust_cg_process_env::with_env_overrides(
            &[(
                "TCG_EXTERNAL_CLEAN_CHECKER",
                checker.to_str().expect("utf-8 temp path"),
            )],
            clean_checker_path,
        );
        assert_eq!(resolved.as_deref(), Some(checker.as_path()));
    }

    #[cfg(unix)]
    #[test]
    fn authority_lane_still_returns_a_full_content_digest() {
        // The guard against silently downgrading proof authority to metadata:
        // `clean_checker_path_and_identity` is what binds stored certificates
        // to the bytes that replay them, and it must still be a 64-char
        // lowercase-hex SHA-256 of the executable's CONTENT.
        let dir = tempfile::tempdir().unwrap();
        let checker = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        // An ordinary build's record: an overlay build's would pin its own
        // Clean and refuse this fixture.
        let (path, identity) = crate::ay_identity::test_fixtures::with_ordinary_record(|| {
            trust_cg_process_env::with_env_overrides(
                &[(
                    "TCG_EXTERNAL_CLEAN_CHECKER",
                    checker.to_str().expect("utf-8 temp path"),
                )],
                || clean_checker_path_and_identity(30_000),
            )
        })
        .expect("a capable checker resolves on the authority lane");

        assert_eq!(path, checker);
        assert_eq!(identity.len(), 64, "not a SHA-256: {identity}");
        assert!(
            identity
                .chars()
                .all(|c| c.is_ascii_digit() || ('a'..='f').contains(&c)),
            "not lowercase hex: {identity}"
        );
        assert_eq!(
            Some(identity.as_str()),
            crate::lrat_cert::checker_binary_sha256(&checker).as_deref(),
            "the authority identity must be the content digest of these bytes"
        );
        assert_ne!(
            Some(identity.as_str()),
            crate::lrat_cert::file_metadata_identity(&checker).as_deref(),
            "the authority identity must not be the metadata identity"
        );
    }

    #[cfg(unix)]
    #[test]
    fn default_checker_discovery_uses_the_managed_binary_not_sibling_builds() {
        let directory = tempfile::tempdir().unwrap();
        let prefix = directory.path().join("aterm/pkg");
        let managed_dir = prefix.join("store/clean/current/bin");
        let sibling_dir = directory.path().join("clean/target/release");
        std::fs::create_dir_all(&managed_dir).unwrap();
        std::fs::create_dir_all(&sibling_dir).unwrap();
        let managed = fake_checker(
            &managed_dir,
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        fake_checker(&sibling_dir, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        trust_cg_process_env::with_env_overrides(
            &[
                ("PATH", prefix.join("bin").to_str().unwrap()),
                ("HOME", directory.path().to_str().unwrap()),
            ],
            || {
                // The owning toolchain's checker (named by the build record in
                // this harness, not by PATH or HOME) leads; the package is the
                // only environment-derived candidate; the sibling is never one.
                // The policy of an ordinary (non-overlay) build of this crate,
                // wherever the harness itself was built.
                let recorded = crate::ay_identity::ToolchainAyRecord::recorded();
                let ordinary = crate::ay_identity::ToolchainAyRecord::new(
                    recorded.build_sysroot().to_path_buf(),
                    Err("fixture".into()),
                );
                let candidates =
                    checker_policy_for(&ordinary, std::env::current_exe().ok().as_deref(), || {
                        crate::aterm_toolchain::packaged_tool_path(
                            crate::aterm_toolchain::ProofTool::Clean,
                        )
                    })
                    .candidates;
                let toolchain = owning_toolchain_clean_checker_candidate();
                let expected: Vec<PathBuf> = toolchain
                    .iter()
                    .cloned()
                    .chain([managed.canonicalize().unwrap()])
                    .collect();
                assert_eq!(candidates, expected);
                assert!(
                    !candidates.iter().any(|path| path.starts_with(&sibling_dir)),
                    "{candidates:?}"
                );
                let package_only: Vec<PathBuf> = candidates
                    .into_iter()
                    .filter(|path| Some(path) != toolchain.as_ref())
                    .collect();
                let discovery = discover_clean_checker_from(None, package_only, 30_000);
                assert!(
                    discovery.selected.is_none(),
                    "a broken package must not be hidden by a sibling build"
                );
                assert_eq!(discovery.unusable.len(), 1);
            },
        );
    }

    /// Lay out `<root>/<name>` as a (possibly incomplete) Trust sysroot.
    #[cfg(unix)]
    fn fake_trust_sysroot(root: &Path, name: &str, trustc: bool, rustlib: bool) -> PathBuf {
        let sysroot = root.join(name);
        std::fs::create_dir_all(sysroot.join("bin")).unwrap();
        if rustlib {
            std::fs::create_dir_all(sysroot.join("lib/rustlib")).unwrap();
        }
        if trustc {
            std::fs::write(sysroot.join("bin/trustc"), b"compiler").unwrap();
        }
        std::fs::write(sysroot.join("bin/tippy-driver"), b"driver").unwrap();
        sysroot.canonicalize().unwrap()
    }

    #[cfg(unix)]
    #[test]
    fn sysroot_checker_candidate_is_the_clean_beside_the_running_trust_compiler() {
        let dir = tempfile::tempdir().unwrap();
        let trust = fake_trust_sysroot(dir.path(), "trust", true, true);
        for executable in ["trustc", "tippy-driver"] {
            assert_eq!(
                trust_sysroot_clean_checker_candidate_for(&trust.join("bin").join(executable)),
                Some(trust.join("bin/clean")),
                "{executable} runs from a Trust sysroot"
            );
        }

        let upstream = fake_trust_sysroot(dir.path(), "upstream", false, true);
        assert_eq!(
            trust_sysroot_clean_checker_candidate_for(&upstream.join("bin/tippy-driver")),
            None,
            "an upstream Rust sysroot (no trustc) ships no Trust checker"
        );
        let bare = fake_trust_sysroot(dir.path(), "bare", true, false);
        assert_eq!(
            trust_sysroot_clean_checker_candidate_for(&bare.join("bin/trustc")),
            None,
            "a generic bin directory without lib/rustlib is not a sysroot"
        );

        let deps = dir.path().join("target/debug/deps");
        std::fs::create_dir_all(&deps).unwrap();
        std::fs::create_dir_all(dir.path().join("target/debug/lib/rustlib")).unwrap();
        for name in ["trustc", "clean", "trust_cg_verify-0123456789abcdef"] {
            std::fs::write(deps.join(name), b"cargo artifact").unwrap();
        }
        assert_eq!(
            trust_sysroot_clean_checker_candidate_for(
                &deps.join("trust_cg_verify-0123456789abcdef")
            ),
            None,
            "a cargo deps directory is not a sysroot bin directory"
        );
        assert_eq!(
            trust_sysroot_clean_checker_candidate_for(&trust.join("bin/not-installed")),
            None,
            "an executable that does not exist resolves no sysroot"
        );
    }

    #[cfg(unix)]
    #[test]
    fn sysroot_checker_candidate_follows_the_executable_not_a_link_to_it() {
        let dir = tempfile::tempdir().unwrap();
        let trust = fake_trust_sysroot(dir.path(), "trust", true, true);
        let decoy = fake_trust_sysroot(dir.path(), "decoy", false, true);
        std::fs::write(decoy.join("bin/clean"), b"decoy checker").unwrap();
        std::os::unix::fs::symlink(trust.join("bin/trustc"), decoy.join("bin/trustc")).unwrap();
        assert_eq!(
            trust_sysroot_clean_checker_candidate_for(&decoy.join("bin/trustc")),
            Some(trust.join("bin/clean")),
            "the checker beside the LINK must never be adopted"
        );
    }

    #[test]
    fn default_candidates_try_the_toolchain_before_the_package_and_never_twice() {
        let toolchain = PathBuf::from("/toolchain/bin/clean");
        let package = PathBuf::from("/pkg/store/clean/current/bin/clean");
        assert_eq!(
            default_clean_checker_candidates_from(Some(toolchain.clone()), Some(package.clone())),
            [toolchain.clone(), package.clone()]
        );
        assert_eq!(
            default_clean_checker_candidates_from(None, Some(package.clone())),
            [package]
        );
        assert_eq!(
            default_clean_checker_candidates_from(Some(toolchain.clone()), None),
            std::slice::from_ref(&toolchain)
        );
        assert_eq!(
            default_clean_checker_candidates_from(Some(toolchain.clone()), Some(toolchain.clone())),
            [toolchain]
        );
        assert!(default_clean_checker_candidates_from(None, None).is_empty());
    }

    /// REGRESSION PIN for TRUSTCG-06: a process no compiler hosts (this test
    /// harness) resolved no toolchain checker at all, so the managed package
    /// (`store/clean/8606`, measured 2026-09-27) checked the proofs of the
    /// toolchain AY (ay 0.27.0, 3211f7fc7) and rejected its bit-vector
    /// `poly_simp` steps. The first default checker must be the `clean` of the
    /// toolchain that built this crate, the one whose `bin/ay` is admitted.
    #[test]
    fn unhosted_process_checks_with_the_building_toolchains_clean_first() {
        let build_sysroot = crate::ay_identity::ToolchainAyRecord::recorded().build_sysroot();
        let candidates = default_clean_checker_candidates();
        let is_trust_sysroot = build_sysroot.is_absolute()
            && build_sysroot.join("lib").join("rustlib").is_dir()
            && build_sysroot
                .join("bin")
                .join(format!("trustc{}", std::env::consts::EXE_SUFFIX))
                .is_file();
        if is_trust_sysroot {
            assert_eq!(
                candidates.first(),
                Some(&build_sysroot.join("bin").join("clean")),
                "the building Trust toolchain's checker must lead: {candidates:?}"
            );
        } else {
            // A stock-toolchain build records no Trust sysroot and names no
            // toolchain checker; only the package can remain.
            assert!(
                candidates.len() <= 1,
                "{} is not a Trust sysroot: {candidates:?}",
                build_sysroot.display()
            );
        }
    }

    #[cfg(unix)]
    #[test]
    fn owning_toolchain_checker_is_the_hosting_compilers_else_the_building_compilers() {
        let dir = tempfile::tempdir().unwrap();
        let hosting = fake_trust_sysroot(dir.path(), "hosting", true, true);
        let building = fake_trust_sysroot(dir.path(), "building", true, true);
        let stock = fake_trust_sysroot(dir.path(), "stock", false, true);
        let deps = dir.path().join("target/debug/deps");
        std::fs::create_dir_all(&deps).unwrap();
        let test_binary = deps.join("trust_cg_verify-0123456789abcdef");
        std::fs::write(&test_binary, b"cargo artifact").unwrap();

        assert_eq!(
            owning_toolchain_clean_checker_candidate_from(
                Some(&hosting.join("bin/trustc")),
                &building
            ),
            Some(hosting.join("bin/clean")),
            "a hosting Trust compiler owns the process"
        );
        for running in [Some(test_binary.as_path()), None] {
            assert_eq!(
                owning_toolchain_clean_checker_candidate_from(running, &building),
                Some(building.join("bin/clean")),
                "with no hosting compiler, the building compiler owns the code ({running:?})"
            );
        }
        assert_eq!(
            owning_toolchain_clean_checker_candidate_from(Some(&test_binary), &stock),
            None,
            "a stock build sysroot ships no Trust checker"
        );
        for unrecorded in [PathBuf::new(), PathBuf::from("building")] {
            assert_eq!(
                owning_toolchain_clean_checker_candidate_from(Some(&test_binary), &unrecorded),
                None,
                "an empty or relative record ({unrecorded:?}) must not resolve against the \
                 working directory"
            );
        }
    }

    #[test]
    fn a_skipped_default_checker_is_noted_and_only_an_empty_route_is_degraded() {
        let toolchain = PathBuf::from("/toolchain/bin/clean");
        let package = PathBuf::from("/pkg/store/clean/current/bin/clean");
        let unusable = [
            (toolchain.clone(), CheckerDefect::CarcaraFeatureMissing),
            (
                PathBuf::from("/slow/bin/clean"),
                CheckerDefect::TimedOut("deadline".to_string()),
            ),
            (
                PathBuf::from("/odd/bin/clean"),
                CheckerDefect::NotRunnable("exec format error".to_string()),
            ),
        ];
        assert_eq!(
            unusable_checker_reports(&unusable, Some(&package)),
            [(
                toolchain.as_path(),
                &CheckerDefect::CarcaraFeatureMissing,
                UnusableCheckerReport::SkippedFor(package.clone())
            )],
            "a capable later checker makes a skipped one a notice, and transient defects are \
             not reported as a property of the executable"
        );
        assert_eq!(
            unusable_checker_reports(&unusable, None),
            [(
                toolchain.as_path(),
                &CheckerDefect::CarcaraFeatureMissing,
                UnusableCheckerReport::Degraded
            )]
        );
    }

    /// Stage `path` as a checker stub that appends one line to `<path>.calls`
    /// per run and replays a fixed transcript.
    #[cfg(unix)]
    fn counting_checker(path: &Path, stdout: &str, stderr: &str, code: i32) {
        use std::os::unix::fs::PermissionsExt;
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(
            path,
            format!(
                "#!/bin/sh\nprintf 'probe\\n' >> \"$0.calls\"\nprintf '%s' {}\nprintf '%s' {} >&2\nexit {code}\n",
                shell_single_quote(stdout),
                shell_single_quote(stderr),
            ),
        )
        .unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    #[cfg(unix)]
    fn checker_runs(path: &Path) -> usize {
        let mut calls = path.as_os_str().to_owned();
        calls.push(".calls");
        std::fs::read_to_string(PathBuf::from(calls)).map_or(0, |text| text.lines().count())
    }

    #[cfg(unix)]
    #[test]
    fn toolchain_checker_leads_and_the_package_is_a_probed_digest_bound_fallback() {
        let dir = tempfile::tempdir().unwrap();
        let trust = fake_trust_sysroot(dir.path(), "trust", true, true);
        let toolchain_clean = trust.join("bin/clean");
        let candidate = trust_sysroot_clean_checker_candidate_for(&trust.join("bin/trustc"))
            .expect("fake sysroot must resolve its checker");
        assert_eq!(candidate, toolchain_clean);
        let package = dir.path().join("pkg/store/clean/current/bin/clean");

        // A capable toolchain checker wins, and the package is never even run.
        counting_checker(&toolchain_clean, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        counting_checker(&package, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let discovery = discover_clean_checker_from(
            None,
            default_clean_checker_candidates_from(Some(candidate.clone()), Some(package.clone())),
            30_000,
        );
        assert_eq!(
            discovery.selected.as_ref().map(|(path, _)| path),
            Some(&toolchain_clean)
        );
        assert_eq!(
            checker_runs(&package),
            0,
            "the package must not be probed behind a capable toolchain checker"
        );

        // A toolchain checker built without carcara-verify (every Trust
        // sysroot `clean` measured through 2026-09-15) falls back to the
        // package, which is itself probed and bound by the digest of its own
        // bytes; the toolchain defect stays on the record.
        counting_checker(
            &toolchain_clean,
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        let discovery = discover_clean_checker_from(
            None,
            default_clean_checker_candidates_from(Some(candidate.clone()), Some(package.clone())),
            30_000,
        );
        let (selected, identity) = discovery
            .selected
            .clone()
            .expect("a capable package must be selected behind an incapable toolchain checker");
        assert_eq!(selected, package);
        assert_eq!(
            Some(identity.as_str()),
            crate::lrat_cert::checker_binary_sha256(&package).as_deref(),
            "the fallback's authority identity is the content digest of its own bytes"
        );
        assert_eq!(
            discovery.unusable,
            [(
                toolchain_clean.clone(),
                CheckerDefect::CarcaraFeatureMissing
            )]
        );
        assert_eq!(checker_runs(&package), 1);

        // With no package, an incapable toolchain checker is NOT a checker.
        let discovery = discover_clean_checker_from(
            None,
            default_clean_checker_candidates_from(Some(candidate.clone()), None),
            30_000,
        );
        assert!(discovery.selected.is_none());
        assert_eq!(
            discovery.unusable,
            [(
                toolchain_clean.clone(),
                CheckerDefect::CarcaraFeatureMissing
            )]
        );
        let reason = clean_checker_unavailable_reason_from(discovery)
            .expect("an incapable toolchain checker must explain the unavailable route");
        assert!(
            reason.contains(&toolchain_clean.display().to_string()),
            "{reason}"
        );
        assert!(
            reason.contains("failed the control-proof probe"),
            "{reason}"
        );

        // An explicit override stays authoritative: nothing falls back to
        // either default checker behind it, capable or not.
        counting_checker(&toolchain_clean, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let before = (checker_runs(&toolchain_clean), checker_runs(&package));
        let discovery = discover_clean_checker_from(
            Some(CheckerOverride {
                variable: "TCG_EXTERNAL_CLEAN_CHECKER",
                path: dir.path().join("missing-clean"),
            }),
            default_clean_checker_candidates_from(Some(candidate), Some(package.clone())),
            30_000,
        );
        assert!(discovery.selected.is_none());
        assert_eq!(
            (checker_runs(&toolchain_clean), checker_runs(&package)),
            before
        );
    }

    /// Fixed-cost bound on checker discovery (L14-P5). A compile asks twice:
    /// the scheduling hint at backend `init` ([`clean_checker_path`]), then
    /// the authority capture of every verification request
    /// ([`clean_checker_path_and_identity_with_env`]). On the Trust 9192 host
    /// (toolchain `clean` without carcara-verify, package `clean` capable)
    /// that was measured at FOUR `clean` processes and TWO executable digests
    /// (108 MB and 116 MB) per compile, the second pair on the critical path
    /// of every warm compile. The bound: one control-proof process per
    /// candidate per file state, and a content digest only of the checker
    /// that is selected.
    #[cfg(unix)]
    #[test]
    fn a_compile_probes_each_checker_once_and_digests_only_the_selected_one() {
        let dir = tempfile::tempdir().unwrap();
        let toolchain = dir.path().join("trust/bin/clean");
        let package = dir.path().join("pkg/store/clean/current/bin/clean");
        counting_checker(
            &toolchain,
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        counting_checker(&package, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let candidates =
            default_clean_checker_candidates_from(Some(toolchain.clone()), Some(package.clone()));
        let digests = |path: &Path| crate::lrat_cert::file_hash_computation_count(path);

        // Backend init: the scheduling hint probes both candidates, digests none.
        assert_eq!(
            clean_checker_path_hint_from(None, candidates.clone(), false),
            Some(package.clone())
        );
        assert_eq!((checker_runs(&toolchain), checker_runs(&package)), (1, 1));
        assert_eq!((digests(&toolchain), digests(&package)), (0, 0));

        // Every authority capture of the compile: no further process, the
        // incapable candidate is never digested, the selected one once, and
        // the authority identity is still the digest of its current bytes.
        for _ in 0..3 {
            let discovery = discover_clean_checker_from(None, candidates.clone(), 30_000);
            let (selected, identity) = discovery.selected.clone().expect("capable package");
            assert_eq!(selected, package);
            assert_eq!(
                Some(identity.as_str()),
                crate::lrat_cert::checker_binary_sha256(&package).as_deref()
            );
            assert_eq!(
                discovery.unusable,
                [(toolchain.clone(), CheckerDefect::CarcaraFeatureMissing)]
            );
        }
        assert_eq!((checker_runs(&toolchain), checker_runs(&package)), (1, 1));
        assert_eq!((digests(&toolchain), digests(&package)), (0, 1));

        // The reuse is per file state: a checker replaced at the same path is
        // probed again, and its new verdict is the one reported.
        counting_checker(
            &package,
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        let discovery = discover_clean_checker_from(None, candidates.clone(), 30_000);
        assert!(discovery.selected.is_none());
        assert_eq!(checker_runs(&package), 2);
        assert!(
            discovery
                .unusable
                .contains(&(package.clone(), CheckerDefect::CarcaraFeatureMissing))
        );
    }

    /// The same bound in the other order (an authority capture before any
    /// scheduling hint, as a library user without a backend `init` does).
    #[cfg(unix)]
    #[test]
    fn an_authority_probe_answers_the_later_availability_question() {
        let dir = tempfile::tempdir().unwrap();
        let checker = dir.path().join("clean");
        counting_checker(&checker, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        assert!(clean_checker_capability(&checker, 30_000).is_ok());
        assert_eq!(checker_runs(&checker), 1);
        assert!(clean_checker_available(&checker, 30_000).is_ok());
        assert_eq!(
            checker_runs(&checker),
            1,
            "the availability lane must reuse the verdict for the same file state"
        );
    }

    /// `TCG_PARANOID_FILE_HASH` refuses the file-state-keyed shortcut on the
    /// authority lane. It reruns a scheduling-only control proof, but may reuse
    /// a capability verdict keyed by a freshly computed content digest.
    #[cfg(unix)]
    #[test]
    fn paranoid_file_hash_reprobes_on_the_authority_lane() {
        let dir = tempfile::tempdir().unwrap();
        let checker = dir.path().join("clean");
        counting_checker(&checker, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        assert!(clean_checker_available(&checker, 30_000).is_ok());
        assert_eq!(checker_runs(&checker), 1);
        let verdict =
            trust_cg_process_env::with_env_overrides(&[("TCG_PARANOID_FILE_HASH", "1")], || {
                clean_checker_capability(&checker, 30_000)
            });
        assert!(verdict.is_ok());
        assert_eq!(checker_runs(&checker), 2);
        let digests_before = crate::lrat_cert::file_hash_computation_count(&checker);
        let repeated =
            trust_cg_process_env::with_env_overrides(&[("TCG_PARANOID_FILE_HASH", "1")], || {
                clean_checker_capability(&checker, 30_000)
            });
        assert_eq!(repeated, verdict);
        assert_eq!(
            checker_runs(&checker),
            2,
            "content-bound verdict is reusable"
        );
        assert!(
            crate::lrat_cert::file_hash_computation_count(&checker) > digests_before,
            "paranoid capability reuse must still read the executable bytes"
        );
    }

    #[cfg(unix)]
    fn script_checker(path: &Path, body: &str) {
        use std::os::unix::fs::PermissionsExt;
        std::fs::write(
            path,
            format!("#!/bin/sh\nprintf 'probe\\n' >> \"$0.calls\"\n{body}"),
        )
        .unwrap();
        std::fs::set_permissions(path, std::fs::Permissions::from_mode(0o755)).unwrap();
    }

    /// The race the post-digest state recheck closes: a checker replaced after
    /// the capability lane read its file state and before it took the content
    /// digest. The verdict recorded for the OLD state must not be bound to the
    /// NEW bytes; the replacement is probed and its own verdict reported.
    #[cfg(unix)]
    #[test]
    fn a_checker_replaced_before_the_digest_is_probed_not_bound_to_the_old_verdict() {
        let dir = tempfile::tempdir().unwrap();
        let checker = dir.path().join("clean");
        counting_checker(&checker, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        assert!(clean_checker_available(&checker, 30_000).is_ok());
        assert_eq!(checker_runs(&checker), 1);

        let staged = dir.path().join("clean.next");
        let verdict = clean_checker_capability_observed(
            &checker,
            &SanitizedChildEnv::capture_verifier(),
            30_000,
            || {
                // A new inode renamed over the path: a new file state.
                counting_checker(
                    &staged,
                    TRANSCRIPT_NO_CARCARA_STDOUT,
                    TRANSCRIPT_NO_CARCARA_STDERR,
                    1,
                );
                std::fs::rename(&staged, &checker).unwrap();
            },
        );
        assert_eq!(verdict, Err(CheckerDefect::CarcaraFeatureMissing));
        assert_eq!(
            checker_runs(&checker),
            2,
            "the replacement must be probed, not bound to the verdict for the old state"
        );
    }

    /// The capability lane shares a verdict with the availability lane only
    /// when the file state held across its probe (the rule the availability
    /// lane applies). This checker is capable, but it moves its own metadata
    /// while it runs (same bytes), so nothing is recorded for the state the
    /// probe started from.
    #[cfg(unix)]
    #[test]
    fn a_capability_probe_whose_checker_state_moved_records_nothing() {
        let dir = tempfile::tempdir().unwrap();
        let checker = dir.path().join("clean");
        script_checker(
            &checker,
            &format!(
                "touch \"$0\"\nprintf '%s' {}\n",
                shell_single_quote(TRANSCRIPT_CAPABLE_STDOUT)
            ),
        );
        let child_env = SanitizedChildEnv::capture_verifier();
        let before = crate::lrat_cert::file_metadata_identity(&checker).unwrap();
        let identity = clean_checker_capability_with_env(&checker, &child_env, 30_000)
            .expect("same bytes before and after the probe");
        assert_eq!(
            Some(identity.as_str()),
            crate::lrat_cert::checker_binary_sha256(&checker).as_deref()
        );
        assert_eq!(checker_runs(&checker), 1);
        assert_ne!(
            crate::lrat_cert::file_metadata_identity(&checker).as_deref(),
            Some(before.as_str()),
            "the fixture must move the file state during the probe"
        );
        assert!(recorded_probe_verdict(&checker, &before, &child_env.digest()).is_none());
    }

    /// A verdict is reused only under the child environment it was reached in:
    /// a checker's answer can depend on what it inherits. This one is capable
    /// unless `RAYON_NUM_THREADS` (an inherited resource control) is 7.
    #[cfg(unix)]
    #[test]
    fn a_verdict_recorded_under_one_child_environment_is_not_reused_under_another() {
        let dir = tempfile::tempdir().unwrap();
        let checker = dir.path().join("clean");
        script_checker(
            &checker,
            &format!(
                "if [ \"$RAYON_NUM_THREADS\" = 7 ]; then printf '%s' {}; printf '%s' {} >&2; \
                 exit 1; fi\nprintf '%s' {}\n",
                shell_single_quote(TRANSCRIPT_NO_CARCARA_STDOUT),
                shell_single_quote(TRANSCRIPT_NO_CARCARA_STDERR),
                shell_single_quote(TRANSCRIPT_CAPABLE_STDOUT)
            ),
        );
        let recorded_env =
            trust_cg_process_env::with_env_overrides(&[("RAYON_NUM_THREADS", "1")], || {
                assert!(clean_checker_available(&checker, 30_000).is_ok());
                SanitizedChildEnv::capture_verifier()
            });
        assert_eq!(checker_runs(&checker), 1);
        let other_env = trust_cg_process_env::with_env_overrides(
            &[("RAYON_NUM_THREADS", "7")],
            SanitizedChildEnv::capture_verifier,
        );
        assert_ne!(recorded_env.digest(), other_env.digest());
        assert_eq!(
            clean_checker_capability_with_env(&checker, &other_env, 30_000),
            Err(CheckerDefect::CarcaraFeatureMissing)
        );
        assert_eq!(checker_runs(&checker), 2);
        // Under the environment it was recorded in, the verdict is reused.
        assert!(clean_checker_capability_with_env(&checker, &recorded_env, 30_000).is_ok());
        assert_eq!(checker_runs(&checker), 2);
    }

    #[cfg(unix)]
    #[test]
    fn default_discovery_skips_incapable_checker_and_selects_next_capable_one() {
        let dir = tempfile::tempdir().unwrap();
        let incapable_dir = dir.path().join("trust-checker");
        let capable_dir = dir.path().join("standalone-checker");
        std::fs::create_dir_all(&incapable_dir).unwrap();
        std::fs::create_dir_all(&capable_dir).unwrap();
        let incapable = fake_checker(
            &incapable_dir,
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        let capable = fake_checker(&capable_dir, TRANSCRIPT_CAPABLE_STDOUT, "", 0);

        let discovery =
            discover_clean_checker_from(None, vec![incapable.clone(), capable.clone()], 30_000);
        assert_eq!(
            discovery.selected.as_ref().map(|(path, _)| path),
            Some(&capable)
        );
        assert_eq!(discovery.unusable.len(), 1);
        assert_eq!(discovery.unusable[0].0, incapable);
        assert_eq!(
            discovery.unusable[0].1,
            CheckerDefect::CarcaraFeatureMissing
        );
        assert_eq!(clean_checker_unavailable_reason_from(discovery), None);
    }

    #[cfg(unix)]
    #[test]
    fn explicit_incapable_checker_suppresses_default_fallback_and_is_diagnosed() {
        let dir = tempfile::tempdir().unwrap();
        let explicit_dir = dir.path().join("explicit-checker");
        let default_dir = dir.path().join("default-checker");
        std::fs::create_dir_all(&explicit_dir).unwrap();
        std::fs::create_dir_all(&default_dir).unwrap();
        let explicit = fake_checker(
            &explicit_dir,
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        let capable_default = fake_checker(&default_dir, TRANSCRIPT_CAPABLE_STDOUT, "", 0);

        let discovery = discover_clean_checker_from(
            Some(CheckerOverride {
                variable: "TCG_EXTERNAL_CLEAN_CHECKER",
                path: explicit.clone(),
            }),
            vec![capable_default],
            30_000,
        );
        assert!(discovery.selected.is_none());
        assert_eq!(discovery.candidates, [explicit]);
        assert_eq!(discovery.unusable.len(), 1);
        let reason = clean_checker_unavailable_reason_from(discovery)
            .expect("the explicit incapable checker must explain the unavailable route");
        assert!(reason.contains("$TCG_EXTERNAL_CLEAN_CHECKER explicitly selects"));
        assert!(reason.contains("explicit checker overrides do not fall back"));
        assert!(reason.contains(CLEAN_CHECKER_PACKAGE_HINT));
    }

    /// An overlay build accepts only the Clean its manifest names: a capable
    /// checker with other bytes is refused, never selected, and the package
    /// checker is not even a candidate. Driven through [`checker_policy_for`],
    /// the function production's [`checker_policy`] applies to this build's
    /// own record, over overlay and ordinary fixture records.
    #[cfg(unix)]
    #[test]
    fn overlay_build_accepts_only_the_manifest_checker_and_never_falls_back() {
        use crate::ay_identity::{ToolchainAyRecord, ToolchainOverlay};
        let dir = tempfile::tempdir().unwrap();
        let sysroot = fake_trust_sysroot(dir.path(), "overlay", true, true);
        let package_dir = dir.path().join("package");
        std::fs::create_dir_all(&package_dir).unwrap();
        let overlay_clean = fake_checker(&sysroot.join("bin"), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let package = fake_checker(
            &package_dir,
            &format!("{TRANSCRIPT_CAPABLE_STDOUT}\n"),
            "",
            0,
        );
        let overlay_sha = crate::lrat_cert::checker_binary_sha256(&overlay_clean).unwrap();
        let package_sha = crate::lrat_cert::checker_binary_sha256(&package).unwrap();
        assert_ne!(overlay_sha, package_sha);
        let manifest =
            ToolchainOverlay::new(&"a".repeat(64), &overlay_sha, &"b".repeat(40)).unwrap();
        let overlay_record =
            ToolchainAyRecord::new_overlay(sysroot.clone(), Err("fixture".into()), Some(manifest));
        let env = SanitizedChildEnv::capture_verifier();

        let package_asked = std::cell::Cell::new(false);
        let policy = checker_policy_for(&overlay_record, None, || {
            package_asked.set(true);
            Some(package.clone())
        });
        assert!(
            !package_asked.get(),
            "an overlay build must not even look up the package"
        );
        assert_eq!(
            policy,
            CheckerPolicy {
                pin: Some(overlay_sha.clone()),
                candidates: vec![overlay_clean.clone()],
            }
        );
        let discovery = discover_clean_checker_from_with_env(None, policy.clone(), &env, 30_000);
        assert_eq!(
            discovery.selected,
            Some((overlay_clean.clone(), overlay_sha.clone()))
        );

        // An explicit override is held to the same pin.
        let discovery = discover_clean_checker_from_with_env(
            Some(CheckerOverride {
                variable: "TCG_EXTERNAL_CLEAN_CHECKER",
                path: package.clone(),
            }),
            policy.clone(),
            &env,
            30_000,
        );
        assert!(discovery.selected.is_none());
        assert_eq!(
            discovery.unusable,
            [(
                package.clone(),
                CheckerDefect::NotTheOverlayChecker {
                    expected: overlay_sha.clone(),
                    found: package_sha.clone(),
                }
            )]
        );

        // The overlay's checker replaced by other (capable) bytes: refused,
        // and nothing else is tried.
        let replaced = std::fs::read(&package).unwrap();
        std::fs::write(&overlay_clean, &replaced).unwrap();
        let policy = checker_policy_for(&overlay_record, None, || Some(package.clone()));
        let discovery = discover_clean_checker_from_with_env(None, policy, &env, 30_000);
        assert!(discovery.selected.is_none());
        assert_eq!(
            discovery.unusable,
            [(
                overlay_clean.clone(),
                CheckerDefect::NotTheOverlayChecker {
                    expected: overlay_sha.clone(),
                    found: package_sha.clone(),
                }
            )]
        );
        let reason = clean_checker_unavailable_reason_from(discovery).unwrap();
        assert!(reason.contains("never falls back"), "{reason}");
        assert!(reason.contains("replaced after assembly"), "{reason}");
        assert!(reason.contains(OVERLAY_ASSEMBLER), "{reason}");
        assert!(!reason.contains(CLEAN_CHECKER_PACKAGE_HINT), "{reason}");
        assert!(!reason.contains("carcara-verify"), "{reason}");

        // The sysroot's checker without carcara-verify: the overlay build
        // stops, while the same sysroot recorded as an ORDINARY toolchain
        // falls back to the capable package. The overlay record is what
        // forbids the fallback (measured before the pin: an overlay whose
        // bin/clean lacked carcara-verify verified with store/clean/8606).
        fake_checker(
            &sysroot.join("bin"),
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        let policy = checker_policy_for(&overlay_record, None, || Some(package.clone()));
        let discovery = discover_clean_checker_from_with_env(None, policy, &env, 30_000);
        assert!(discovery.selected.is_none());
        assert_eq!(
            discovery.unusable,
            [(overlay_clean.clone(), CheckerDefect::CarcaraFeatureMissing)]
        );
        let ordinary = ToolchainAyRecord::new(sysroot.clone(), Err("fixture".into()));
        let policy = checker_policy_for(&ordinary, None, || Some(package.clone()));
        assert_eq!(policy.pin, None);
        assert_eq!(
            policy.candidates,
            vec![overlay_clean.clone(), package.clone()]
        );
        let discovery = discover_clean_checker_from_with_env(None, policy, &env, 30_000);
        assert_eq!(
            discovery.selected,
            Some((package.clone(), package_sha.clone()))
        );

        // A refused manifest pins the empty digest, which nothing matches,
        // not even the capable checker the manifest was assembled with.
        fake_checker(&sysroot.join("bin"), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let refused = ToolchainAyRecord::new_overlay(sysroot.clone(), Err("fixture".into()), None);
        let policy = checker_policy_for(&refused, None, || Some(package.clone()));
        assert_eq!(policy.pin.as_deref(), Some(""));
        let discovery = discover_clean_checker_from_with_env(None, policy, &env, 30_000);
        assert!(discovery.selected.is_none());
        let reason = clean_checker_unavailable_reason_from(discovery).unwrap();
        assert!(reason.contains("manifest was refused"), "{reason}");
    }

    /// The authority path applies the checker pin of THIS build's record: in
    /// an ordinary build the record pins nothing, so a fixture overlay record
    /// stands in for it ([`crate::ay_identity::test_fixtures::with_recorded`])
    /// and the production discovery (`checker_policy()` inside
    /// [`clean_checker_path_and_identity_with_env`], [`resolve_proof_checker`]
    /// and [`clean_checker_unavailable_reason`]) runs unchanged. Dropping the
    /// pin there (reviewer mutant M2: `CheckerPolicy { pin: None,
    /// ..checker_policy() }`) selects the override below and fails this test;
    /// the overlay integration test catches it only in an overlay build.
    #[cfg(unix)]
    #[test]
    fn the_authority_path_applies_the_recorded_overlay_pin() {
        use crate::ay_identity::test_fixtures::with_recorded;
        use crate::ay_identity::{ToolchainAyRecord, ToolchainOverlay};
        const OVERRIDES: [&str; 2] = ["TCG_EXTERNAL_CLEAN_CHECKER", "TCG_CLEAN_CHECKER"];
        let dir = tempfile::tempdir().unwrap();
        let sysroot = fake_trust_sysroot(dir.path(), "overlay-authority", true, true);
        let own = fake_checker(&sysroot.join("bin"), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let wrapper_dir = dir.path().join("wrapper");
        std::fs::create_dir_all(&wrapper_dir).unwrap();
        // Capable, but other bytes: what a wrapper around the overlay's Clean is.
        let wrapper = fake_checker(
            &wrapper_dir,
            &format!("{TRANSCRIPT_CAPABLE_STDOUT}\n\n"),
            "",
            0,
        );
        let wrapper_text = wrapper.to_str().unwrap();
        let own_sha = crate::lrat_cert::checker_binary_sha256(&own).unwrap();
        let wrapper_sha = crate::lrat_cert::checker_binary_sha256(&wrapper).unwrap();
        assert_ne!(own_sha, wrapper_sha);
        let manifest = ToolchainOverlay::new(&"a".repeat(64), &own_sha, &"b".repeat(40)).unwrap();
        let overlay_record =
            ToolchainAyRecord::new_overlay(sysroot.clone(), Err("fixture".into()), Some(manifest));
        let env = SanitizedChildEnv::capture_verifier();
        let authority = || clean_checker_path_and_identity_with_env(&env, 30_000);
        let refusal = |result: Result<(PathBuf, String), CheckerResolutionError>| match result {
            Err(CheckerResolutionError::Unavailable(reason)) => reason,
            other => panic!("an overlay build must refuse this checker, got {other:?}"),
        };

        trust_cg_process_env::with_env_overrides_removed(&OVERRIDES, || {
            with_recorded(overlay_record.clone(), || {
                assert_eq!(checker_policy().pin.as_deref(), Some(own_sha.as_str()));
                assert_eq!(
                    authority().ok(),
                    Some((own.clone(), own_sha.clone())),
                    "the overlay's own bin/clean is the checker"
                );
                assert_eq!(resolve_proof_checker(), Ok((own.clone(), own_sha.clone())));
                assert_eq!(clean_checker_unavailable_reason(), None);

                for variable in OVERRIDES {
                    trust_cg_process_env::with_env_overrides(&[(variable, wrapper_text)], || {
                        let reason = refusal(authority());
                        assert!(reason.contains("never falls back"), "{variable}: {reason}");
                        assert!(reason.contains(&own_sha), "{variable}: {reason}");
                        assert!(
                            reason.contains(&format!("unset ${variable}")),
                            "{variable}: {reason}"
                        );
                        assert_eq!(resolve_proof_checker(), Err(reason.clone()));
                        assert_eq!(clean_checker_unavailable_reason(), Some(reason));
                    });
                }

                // The overlay's own file replaced by the wrapper's bytes:
                // refused, and nothing else is tried.
                std::fs::copy(&wrapper, &own).unwrap();
                let reason = refusal(authority());
                assert!(reason.contains("replaced after assembly"), "{reason}");
                assert!(!reason.contains("carcara-verify"), "{reason}");
            });
        });

        // The same checker under an ORDINARY record: nothing is pinned, and
        // the capable override is the checker. The record decides.
        let ordinary = ToolchainAyRecord::new(sysroot, Err("fixture".into()));
        trust_cg_process_env::with_env_overrides_removed(&OVERRIDES, || {
            with_recorded(ordinary, || {
                assert_eq!(checker_policy().pin, None);
                trust_cg_process_env::with_env_overrides(
                    &[("TCG_EXTERNAL_CLEAN_CHECKER", wrapper_text)],
                    || {
                        assert_eq!(
                            authority().ok(),
                            Some((wrapper.clone(), wrapper_sha.clone()))
                        )
                    },
                );
            });
        });
    }

    /// The gate's identity record names the checker that CHECKED a proof,
    /// written where the check runs (`carcara_verify_with_expected_checker_with_env`),
    /// whatever the verdict, and never a checker whose bytes were not the
    /// ones bound. Disabling that `note` call (reviewer mutant M1) fails this.
    #[cfg(unix)]
    #[test]
    fn a_proof_check_records_the_checker_that_ran() {
        use crate::proof_tool_record::{PROOF_IDENTITY_OUT_ENV, SCHEMA};
        let dir = tempfile::tempdir().unwrap();
        let accepting_dir = dir.path().join("accepting");
        let rejecting_dir = dir.path().join("rejecting");
        std::fs::create_dir_all(&accepting_dir).unwrap();
        std::fs::create_dir_all(&rejecting_dir).unwrap();
        let accepting = fake_checker(&accepting_dir, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let rejecting = fake_checker(
            &rejecting_dir,
            "External certificate verification: FAILED\n",
            "",
            1,
        );
        let accepting_sha = crate::lrat_cert::checker_binary_sha256(&accepting).unwrap();
        let rejecting_sha = crate::lrat_cert::checker_binary_sha256(&rejecting).unwrap();
        let out = dir.path().join("identity.jsonl");
        let env = SanitizedChildEnv::capture_verifier();
        let check = |checker: &Path, sha: &str| {
            carcara_verify_with_expected_checker_with_env(
                checker,
                sha,
                CHECKER_PROBE_SMT2,
                CHECKER_PROBE_ALETHE,
                &env,
                30_000,
            )
            .unwrap()
        };

        trust_cg_process_env::with_env_overrides_removed(&[PROOF_IDENTITY_OUT_ENV], || {
            assert!(check(&accepting, &accepting_sha));
        });
        assert!(!out.exists(), "nothing is recorded without the variable");
        trust_cg_process_env::with_env_overrides(
            &[(PROOF_IDENTITY_OUT_ENV, out.to_str().unwrap())],
            || {
                assert!(check(&accepting, &accepting_sha));
                assert!(check(&accepting, &accepting_sha));
                assert!(!check(&rejecting, &rejecting_sha));
                // Bound to other bytes: refused before it runs, not recorded.
                assert!(!check(&rejecting, &accepting_sha));
            },
        );

        let overlay_manifest = crate::ay_identity::ToolchainAyRecord::recorded()
            .overlay()
            .map(|overlay| overlay.manifest_sha256().to_owned());
        let rows: Vec<serde_json::Value> = std::fs::read_to_string(&out)
            .unwrap()
            .lines()
            .map(|line| serde_json::from_str(line).unwrap())
            .collect();
        let expected = [(&accepting, &accepting_sha), (&rejecting, &rejecting_sha)];
        assert_eq!(rows.len(), expected.len(), "{rows:?}");
        for (row, (path, sha)) in rows.iter().zip(expected) {
            assert_eq!(row["schema"], SCHEMA);
            assert_eq!(row["role"], "clean");
            assert_eq!(row["path"], path.display().to_string());
            assert_eq!(row["sha256"], sha.as_str());
            assert_eq!(row["pid"], std::process::id());
            assert_eq!(
                row["toolchain_overlay_manifest_sha256"],
                serde_json::json!(overlay_manifest)
            );
        }
    }

    /// An ORDINARY build's unavailable reason (embedded in `AYResult::Unknown`
    /// and in the proof-toolchain unavailable reason) is one line, and each
    /// failing default candidate's repair names the defect THAT candidate
    /// has. Measured regression: the banner's two-line repair (package text
    /// plus an indented development-only line) was spliced into this reason
    /// once per candidate, and a candidate that rejected the control proof
    /// was told its package "must include carcara-verify".
    #[test]
    fn ordinary_unavailable_reason_is_one_line_and_names_each_candidates_defect() {
        let discovery = |unusable: Vec<(PathBuf, CheckerDefect)>| CheckerDiscovery {
            selected: None,
            candidates: unusable.iter().map(|(path, _)| path.clone()).collect(),
            unusable,
            explicit: None,
            overlay: false,
        };
        let no_carcara = (
            PathBuf::from("/a/clean"),
            CheckerDefect::CarcaraFeatureMissing,
        );
        let no_ay_smt = (
            PathBuf::from("/b/clean"),
            CheckerDefect::AySmtFeatureMissing,
        );
        let rejects = (
            PathBuf::from("/c/clean"),
            CheckerDefect::ControlProofRejected("x".into()),
        );
        let not_runnable = (
            PathBuf::from("/d/clean"),
            CheckerDefect::NotRunnable("exec format error".into()),
        );
        let timed_out = (
            PathBuf::from("/e/clean"),
            CheckerDefect::TimedOut("after 1 ms".into()),
        );

        let all = clean_checker_unavailable_reason_from(discovery(vec![
            no_carcara.clone(),
            no_ay_smt.clone(),
            rejects.clone(),
            not_runnable.clone(),
            timed_out.clone(),
        ]))
        .expect("no candidate was usable");
        assert!(!all.contains('\n'), "the reason must be one line: {all:?}");
        assert!(!all.contains("development only"), "{all}");
        for (path, _) in [&no_carcara, &no_ay_smt, &rejects, &not_runnable, &timed_out] {
            assert!(all.contains(&path.display().to_string()), "{all}");
        }

        let one = |candidate: &(PathBuf, CheckerDefect)| {
            clean_checker_unavailable_reason_from(discovery(vec![candidate.clone()]))
                .expect("the only candidate was unusable")
        };
        let reason = one(&no_carcara);
        assert!(reason.contains(CLEAN_CHECKER_PACKAGE_HINT), "{reason}");
        let reason = one(&no_ay_smt);
        assert!(reason.contains("`ay-smt`"), "{reason}");
        assert!(!reason.contains("carcara-verify"), "{reason}");
        for candidate in [&rejects, &not_runnable] {
            let reason = one(candidate);
            assert!(reason.contains("aterm pkg"), "{reason}");
            assert!(reason.contains("control proof"), "{reason}");
            assert!(!reason.contains("carcara-verify"), "{reason}");
        }
        // A timeout is not a defect of the checker's build: no package repair.
        let reason = one(&timed_out);
        assert!(!reason.contains("carcara-verify"), "{reason}");
        assert!(!reason.contains("aterm pkg"), "{reason}");
    }

    /// The DEGRADED banner's `fix:` line names the repair for the defect that
    /// was found, under the build's policy and the override (if any) that
    /// named the checker. Measured in an overlay gate run: a
    /// TCG_EXTERNAL_CLEAN_CHECKER wrapper refused for its bytes was told to
    /// "reassemble the overlay ... with a Clean built with carcara-verify",
    /// which neither applies nor helps; unsetting the override does.
    #[test]
    fn degraded_banner_repair_names_the_defect_that_was_found() {
        let sha = "e".repeat(64);
        let other = "f".repeat(64);
        let wrong_bytes = CheckerDefect::NotTheOverlayChecker {
            expected: sha.clone(),
            found: other.clone(),
        };
        let refused_manifest = CheckerDefect::NotTheOverlayChecker {
            expected: String::new(),
            found: other.clone(),
        };
        let wrapper = CheckerOverride {
            variable: "TCG_EXTERNAL_CLEAN_CHECKER",
            path: PathBuf::from("/tmp/wrapper/clean"),
        };
        let legacy = CheckerOverride {
            variable: "TCG_CLEAN_CHECKER",
            path: PathBuf::from("/tmp/wrapper/clean"),
        };

        // Overlay build, override with other bytes: unset the override.
        for override_ in [&wrapper, &legacy] {
            let fix = checker_repair_hint(&wrong_bytes, true, Some(override_));
            assert!(
                fix.starts_with(&format!("unset ${}", override_.variable)),
                "{fix}"
            );
            assert!(fix.contains(&sha), "{fix}");
            assert!(!fix.contains("carcara-verify"), "{fix}");
            assert!(!fix.contains("aterm pkg"), "{fix}");
            // The override may name the overlay's own, replaced, bin/clean:
            // then unsetting it does not help, restoring or reassembling does.
            assert!(fix.contains("restore it or reassemble"), "{fix}");
        }
        // Overlay build, an incapable override: unsetting is still the repair,
        // since no override can supply the overlay's own bytes.
        let fix = checker_repair_hint(&CheckerDefect::CarcaraFeatureMissing, true, Some(&wrapper));
        assert!(
            fix.starts_with("unset $TCG_EXTERNAL_CLEAN_CHECKER"),
            "{fix}"
        );

        // Overlay build, its own bin/clean replaced after assembly: restore
        // or reassemble; carcara-verify is not in question.
        let fix = checker_repair_hint(&wrong_bytes, true, None);
        assert!(fix.contains("replaced after assembly"), "{fix}");
        assert!(fix.contains(OVERLAY_ASSEMBLER), "{fix}");
        assert!(fix.contains(&sha), "{fix}");
        assert!(!fix.contains("carcara-verify"), "{fix}");
        assert!(!fix.contains("TCG_EXTERNAL_CLEAN_CHECKER"), "{fix}");

        // A refused manifest accepts nothing: only reassembly helps, and an
        // override cannot change that.
        let fix = checker_repair_hint(&refused_manifest, true, None);
        assert!(fix.contains("was refused"), "{fix}");
        assert!(fix.contains(OVERLAY_ASSEMBLER), "{fix}");
        let fix = checker_repair_hint(&refused_manifest, true, Some(&wrapper));
        assert!(
            fix.contains("$TCG_EXTERNAL_CLEAN_CHECKER cannot change that"),
            "{fix}"
        );

        // Overlay build, its own bin/clean lacks a feature: reassemble with
        // a Clean built with THAT feature.
        let fix = checker_repair_hint(&CheckerDefect::CarcaraFeatureMissing, true, None);
        assert!(fix.contains(OVERLAY_ASSEMBLER), "{fix}");
        assert!(fix.contains("`carcara-verify`"), "{fix}");
        assert!(!fix.contains("aterm pkg"), "{fix}");
        let fix = checker_repair_hint(&CheckerDefect::AySmtFeatureMissing, true, None);
        assert!(
            fix.contains("`ay-smt`") && !fix.contains("carcara"),
            "{fix}"
        );
        let fix = checker_repair_hint(&CheckerDefect::ControlProofRejected("x".into()), true, None);
        assert!(
            fix.contains("verify-external") && !fix.contains("carcara"),
            "{fix}"
        );

        // Ordinary build: the package repair, or the override's own repair.
        // The banner, not this one-line repair, adds the development-only
        // override line.
        let fix = checker_repair_hint(&CheckerDefect::CarcaraFeatureMissing, false, None);
        assert_eq!(fix, CLEAN_CHECKER_PACKAGE_HINT);
        let fix = checker_repair_hint(
            &CheckerDefect::ControlProofRejected("x".into()),
            false,
            None,
        );
        assert!(
            fix.contains("aterm pkg") && fix.contains("verify-external"),
            "{fix}"
        );
        assert!(!fix.contains("carcara"), "{fix}");
        let fix = checker_repair_hint(&CheckerDefect::CarcaraFeatureMissing, false, Some(&legacy));
        assert!(fix.starts_with("point $TCG_CLEAN_CHECKER at"), "{fix}");
        assert!(fix.contains("`carcara-verify`"), "{fix}");

        // Every repair is one line, under every policy and override.
        for defect in [
            CheckerDefect::CarcaraFeatureMissing,
            CheckerDefect::AySmtFeatureMissing,
            CheckerDefect::ControlProofRejected("x".into()),
            CheckerDefect::NotRunnable("x".into()),
            CheckerDefect::TimedOut("x".into()),
            wrong_bytes.clone(),
            refused_manifest.clone(),
        ] {
            for overlay in [false, true] {
                for explicit in [None, Some(&wrapper), Some(&legacy)] {
                    let fix = checker_repair_hint(&defect, overlay, explicit);
                    assert!(
                        !fix.contains('\n'),
                        "{defect:?} {overlay} {explicit:?}: {fix:?}"
                    );
                }
            }
        }
    }

    #[cfg(unix)]
    #[test]
    fn cached_path_hint_cannot_authorize_a_replaced_checker() {
        let dir = tempfile::tempdir().unwrap();
        let checker_dir = dir.path().join("hinted-checker");
        std::fs::create_dir_all(&checker_dir).unwrap();
        let checker = fake_checker(&checker_dir, TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let candidates = vec![checker.clone()];

        assert_eq!(
            clean_checker_path_hint_from(None, candidates.clone(), false),
            Some(checker.clone()),
            "the first hint must perform the metadata-keyed availability probe"
        );

        // Replace the executable at the identical path with an incapable
        // build. The cheap positive hint is intentionally allowed to be stale:
        // its only effect is deciding whether solver work is worth scheduling.
        let replaced = fake_checker(
            &checker_dir,
            TRANSCRIPT_NO_CARCARA_STDOUT,
            TRANSCRIPT_NO_CARCARA_STDERR,
            1,
        );
        assert_eq!(replaced, checker);
        assert_eq!(
            clean_checker_path_hint_from(None, candidates.clone(), false),
            Some(checker.clone()),
            "a hint hit must not re-hash the checker"
        );

        // Authority resolution bypasses that hint, hashes the CURRENT bytes,
        // reruns the control proof, and rejects the replacement.
        let authoritative = discover_clean_checker_from(None, candidates, 30_000);
        assert!(authoritative.selected.is_none());
        assert_eq!(authoritative.unusable.len(), 1);
        assert_eq!(
            authoritative.unusable[0].1,
            CheckerDefect::CarcaraFeatureMissing
        );
    }

    #[cfg(unix)]
    #[test]
    fn checker_replacement_at_same_path_cannot_inherit_capability() {
        let dir = tempfile::tempdir().unwrap();
        let checker = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let first_identity = clean_checker_capability(&checker, 30_000).expect("capable checker");
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
            clean_checker_capability(&replaced, 30_000),
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
    fn store_dir_resolution_order_and_kill_switches() {
        let explicit = Some(PathBuf::from("/explicit/store"));
        let xdg = Some(std::ffi::OsString::from("/xdg-cache"));
        let home = Some(std::ffi::OsString::from("/home/box"));
        let os = |value: &str| Some(std::ffi::OsString::from(value));

        // Either kill switch wins over everything.
        assert_eq!(
            store_dir_from(true, false, explicit.clone(), xdg.clone(), home.clone()),
            None
        );
        assert_eq!(
            store_dir_from(false, true, explicit.clone(), xdg.clone(), home.clone()),
            None
        );
        // Explicit override beats the per-box defaults.
        assert_eq!(
            store_dir_from(false, false, explicit, xdg.clone(), home.clone()),
            Some(PathBuf::from("/explicit/store"))
        );
        // XDG_CACHE_HOME beats HOME.
        assert_eq!(
            store_dir_from(false, false, None, xdg, home.clone()),
            Some(PathBuf::from("/xdg-cache/trust-cg/alethe-certs"))
        );
        // A blank, empty or relative XDG falls through to HOME: the one
        // user-cache rule (`private_fs::user_cache_base`), never the CWD.
        for ignored in ["  ", "", "relative-xdg", " /padded"] {
            assert_eq!(
                store_dir_from(false, false, None, os(ignored), home.clone()),
                Some(PathBuf::from("/home/box/.cache/trust-cg/alethe-certs")),
                "XDG_CACHE_HOME={ignored:?}"
            );
        }
        // A relative or empty HOME names no cache: the tier stays inert.
        for home in ["", "relative-home"] {
            assert_eq!(
                store_dir_from(false, false, None, os("relative-xdg"), os(home)),
                None
            );
        }
        // No location at all: tier stays inert.
        assert_eq!(store_dir_from(false, false, None, None, None), None);
    }

    #[cfg(unix)]
    #[test]
    fn persist_writes_a_cert_the_consume_path_accepts() {
        let dir = tempfile::tempdir().unwrap();
        let store = dir.path().join("store");
        let solver = dir.path().join("solverbin");
        std::fs::write(&solver, b"promotion-fixture-solver").unwrap();
        let smt2 = "(assert false)\n(check-sat)";
        let proof = "(step t1 (cl) :rule false)";
        // The consume replay runs the checker subprocess; a capable-transcript
        // stub stands in for Clean exactly as in the probe tests above.
        let checker = fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0);
        let checker_id = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();

        assert!(persist_verified_alethe_into(
            &store,
            solver.to_str().unwrap(),
            smt2,
            "test:persist-roundtrip",
            proof,
            &checker_id,
        ));
        // Second persist of the same obligation is a no-op (file exists).
        assert!(!persist_verified_alethe_into(
            &store,
            solver.to_str().unwrap(),
            smt2,
            "test:persist-roundtrip",
            proof,
            &checker_id,
        ));

        let id = crate::ay_bridge::solver_identity_hash(solver.to_str().unwrap()).unwrap();
        let key = crate::ay_bridge::verdict_cache_key_v2(&id, smt2);
        assert!(
            cert_path(&store, &key).exists(),
            "filename must be the derived key"
        );
        assert!(consume_verified_in(
            &store,
            &key,
            solver.to_str().unwrap(),
            smt2,
            Some((checker, checker_id)),
        ));
        // A different solver identity must miss the same cert (tooth 2).
        let other = dir.path().join("otherbin");
        std::fs::write(&other, b"different-solver-bytes").unwrap();
        assert!(!consume_verified_in(
            &store,
            &key,
            other.to_str().unwrap(),
            smt2,
            Some((
                fake_checker(dir.path(), TRANSCRIPT_CAPABLE_STDOUT, "", 0),
                "55".repeat(32)
            )),
        ));
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

    /// A stub checker at `dir/clean` that records each run in `dir/clean.calls`,
    /// optionally sleeps, and answers a full verification (or a failure).
    #[cfg(unix)]
    fn replay_checker(dir: &Path, sleep_s: &str, passes: bool) -> PathBuf {
        use std::os::unix::fs::PermissionsExt;
        let path = dir.join("clean");
        let (stdout, code) = if passes {
            (TRANSCRIPT_CAPABLE_STDOUT, 0)
        } else {
            ("External certificate verification: FAILED\n", 1)
        };
        std::fs::write(
            &path,
            format!(
                "#!/bin/sh\nprintf 'run\\n' >> \"$0.calls\"\nsleep {sleep_s}\nprintf '%s' {}\nexit {code}\n",
                shell_single_quote(stdout),
            ),
        )
        .unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        path
    }

    #[cfg(unix)]
    fn replay_checker_runs(checker: &Path) -> usize {
        std::fs::read_to_string(checker.with_file_name("clean.calls"))
            .map(|calls| calls.lines().count())
            .unwrap_or(0)
    }

    /// A stored certificate, its verdict key, the stub checker and a reuse
    /// context of its own (the positive memo is process-wide).
    #[cfg(unix)]
    struct ReplayFixture {
        _dir: tempfile::TempDir,
        solver: String,
        checker: (PathBuf, String),
        cert_text: String,
        smt2: String,
        verdict_key: String,
        context: [u8; 32],
    }

    #[cfg(unix)]
    fn replay_fixture(test: &str, sleep_s: &str, passes: bool) -> ReplayFixture {
        let dir = tempfile::tempdir().unwrap();
        let solver = dir.path().join("solverbin");
        std::fs::write(&solver, format!("solver-bytes {test}")).unwrap();
        let solver = solver.to_str().unwrap().to_owned();
        let id = crate::ay_bridge::solver_identity_hash(&solver).unwrap();
        let checker = replay_checker(dir.path(), sleep_s, passes);
        let checker_sha = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();
        let smt2 = format!("(assert false) ; {test}");
        let mut cert = sample(&smt2, "(step t1 (cl) :rule false)", &id);
        cert.external_clean_checker_identity = checker_sha.clone();
        let verdict_key = crate::ay_bridge::verdict_cache_key_v2(&id, &smt2);
        let context: [u8; 32] = Sha256::digest(format!("replay-fixture:{test}")).into();
        ReplayFixture {
            _dir: dir,
            solver,
            checker: (checker, checker_sha),
            cert_text: cert.serialize(),
            smt2,
            verdict_key,
            context,
        }
    }

    #[cfg(unix)]
    fn replay(fixture: &ReplayFixture, query: &str) -> bool {
        replay_cert_text_with(
            &fixture.cert_text,
            &fixture.verdict_key,
            &fixture.solver,
            query,
            fixture.checker.clone(),
            &fixture.context,
            &SanitizedChildEnv::capture_verifier(),
            30_000,
        )
    }

    /// The prefetch replays a certificate against its own SMT2. The compile's
    /// later replay of the same query is answered from the positive memo (no
    /// second checker run); a different query derives another memo key and is
    /// declined by the consume path's own binding, as without the prefetch.
    #[cfg(unix)]
    #[test]
    fn a_prefetched_replay_answers_only_the_identical_query() {
        let fixture = replay_fixture("identical-query", "0", true);
        let cert = AletheCert::parse(&fixture.cert_text).unwrap();
        assert!(
            replay(&fixture, &cert.smt2),
            "the prefetch replay must pass"
        );
        assert_eq!(replay_checker_runs(&fixture.checker.0), 1);
        assert!(
            replay(&fixture, &fixture.smt2),
            "the compile's query is a memo hit"
        );
        assert_eq!(
            replay_checker_runs(&fixture.checker.0),
            1,
            "no second checker run"
        );
        assert!(
            !replay(&fixture, "(assert true)"),
            "another query must not be credited by the prefetched replay"
        );
        assert_eq!(replay_checker_runs(&fixture.checker.0), 1);
    }

    /// A failed replay records nothing: the next request runs the checker
    /// again.
    #[cfg(unix)]
    #[test]
    fn a_failed_replay_caches_nothing() {
        let fixture = replay_fixture("failed-replay", "0", false);
        assert!(!replay(&fixture, &fixture.smt2));
        assert!(!replay(&fixture, &fixture.smt2));
        assert_eq!(replay_checker_runs(&fixture.checker.0), 2);
    }

    /// Two requests for one certificate at once (the prefetch and the
    /// compile) run one checker: the second waits for the first replay and
    /// takes its memo entry.
    #[cfg(unix)]
    #[test]
    fn concurrent_replays_of_one_certificate_run_one_checker() {
        let fixture = replay_fixture("concurrent-replays", "0.3", true);
        let answers: Vec<bool> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..4)
                .map(|_| scope.spawn(|| replay(&fixture, &fixture.smt2)))
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        assert_eq!(answers, vec![true; 4]);
        assert_eq!(replay_checker_runs(&fixture.checker.0), 1);
    }

    /// When the replay in flight fails, a waiter replays itself rather than
    /// taking a verdict nobody reached.
    #[cfg(unix)]
    #[test]
    fn a_waiter_on_a_failed_replay_replays_itself() {
        let fixture = replay_fixture("waiter-on-failure", "0.3", false);
        let answers: Vec<bool> = std::thread::scope(|scope| {
            let handles: Vec<_> = (0..2)
                .map(|_| scope.spawn(|| replay(&fixture, &fixture.smt2)))
                .collect();
            handles.into_iter().map(|h| h.join().unwrap()).collect()
        });
        assert_eq!(answers, vec![false; 2]);
        assert_eq!(replay_checker_runs(&fixture.checker.0), 2);
    }

    #[test]
    fn positive_replay_memo_binds_query_cert_producer_and_full_authority() {
        let authority = [0xA1; 32];
        let make = |verdict: &str, producer: &str, smt2: &str, cert: &str| {
            consume_memo_key(verdict, producer, smt2, cert, &authority)
        };
        let producer = "11".repeat(32);
        let base = make(
            "verdict-a",
            &producer,
            "(assert false)",
            "certificate bytes",
        );
        for mutant in [
            make(
                "verdict-b",
                &producer,
                "(assert false)",
                "certificate bytes",
            ),
            make(
                "verdict-a",
                &"33".repeat(32),
                "(assert false)",
                "certificate bytes",
            ),
            make("verdict-a", &producer, "(assert true)", "certificate bytes"),
            make(
                "verdict-a",
                &producer,
                "(assert false)",
                "mutated certificate bytes",
            ),
        ] {
            assert_ne!(base, mutant);
        }
        assert_ne!(
            base,
            consume_memo_key(
                "verdict-a",
                &producer,
                "(assert false)",
                "certificate bytes",
                &[0xB2; 32],
            )
        );
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
    /// runs the AY the identity rule admits (`crate::ay_identity`: the build
    /// toolchain's `bin/ay`, or an absolute `AY_SOLVER_PATH` holding those exact
    /// bytes — any other AY is refused and fails the campaign) and an explicit
    /// Clean checker built with its `carcara-verify` feature:
    ///
    /// ```text
    /// TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1 \
    /// TCG_EXTERNAL_CLEAN_CHECKER=/path/to/clean-with-carcara-verify \
    /// scripts/trust_cargo.sh test -p trust-cg-verify --lib \
    ///     end_to_end_mint_then_consume_real_binaries
    /// ```
    #[test]
    fn end_to_end_mint_then_consume_real_binaries() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_EXTERNAL_CERT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "SKIP: external certificate campaign not requested; \
                 set TRUST_CG_RUN_EXTERNAL_CERT_TESTS=1 with an explicit \
                 TCG_EXTERNAL_CLEAN_CHECKER path to run"
            );
            return;
        }

        // The same rule production uses, including its reading of
        // AY_SOLVER_PATH. A requested campaign never skips on a refusal.
        let ay = crate::ay_identity::resolve_for_process().unwrap_or_else(|refusal| {
            panic!("the external certificate campaign requires the admitted AY: {refusal}")
        });
        let checker = PathBuf::from(
            std::env::var_os("TCG_EXTERNAL_CLEAN_CHECKER")
                .or_else(|| std::env::var_os("TCG_CLEAN_CHECKER"))
                .expect("TCG_EXTERNAL_CLEAN_CHECKER must name the exact checker under test"),
        );
        assert!(
            checker.is_file(),
            "TCG_EXTERNAL_CLEAN_CHECKER is not a file: {}",
            checker.display()
        );
        eprintln!("external certificate campaign AY: {}", ay.describe());
        let ay_path = ay.path().to_string_lossy().into_owned();
        let ay_path = ay_path.as_str();

        // Keep this canary inside QF_BV while making the contradiction direct.
        // The test is authority for certificate transport, binding, and the
        // independent checker—not for AY's rewrite-proof coverage. In
        // particular, `not (= x x)` currently exercises an unsupported Alethe
        // rewrite hole and correctly downgrades AY's result to `unknown`, so it
        // cannot serve as a certificate-pipeline canary.
        let smt2 = "(set-logic QF_BV)\n(assert false)\n(check-sat)\n";
        let dir = tempfile::tempdir().unwrap();
        let producer_identity = ay.sha256().to_owned();
        let key = crate::ay_bridge::verdict_cache_key_v2(&producer_identity, smt2);
        let checker_identity = crate::lrat_cert::checker_binary_sha256(&checker).unwrap();

        // MINT: real ay emits Alethe; Carcara pre-verifies; cert is written.
        let minted = mint_into(&MintRequest {
            dir: dir.path(),
            verdict_key: &key,
            solver: &ay,
            smt2,
            obligation_name: "false_qfbv",
            checker: &checker,
            expected_checker_identity: &checker_identity,
            timeout_ms: crate::ay_bridge::AYConfig::default().timeout_ms,
        });
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
                ay_path,
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
                    ay_path,
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
                ay_path,
                "(set-logic QF_BV)\n(declare-const y (_ BitVec 8))\n(assert (= y y))\n(check-sat)\n",
                Some((checker.clone(), checker_identity.clone()))
            ),
            "a cert must never be served for a different query"
        );

        // ADVERSARIAL 3 — no checker: fail-safe decline even with a valid cert.
        assert!(
            !consume_verified_in(dir.path(), &key, ay_path, smt2, None),
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
