// trust-cg-verify/verdict_db.rs - Repo-committed TIER-0 verdict DB (PROOF-3)
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0
//
// Reference: docs/beat-llvm-roadmap-2026-07-01.md §6 WORKSTREAM PROOF, PROOF-3.

//! Repo-committed, content-addressed TIER-0 candidate DB for fixed,
//! program-independent proof obligations (PROOF-3).
//!
//! The DB is embedded from `verdict_db/tier0.vdb` and identifies obligations
//! worth revalidating. A row is never proof authority: the consuming process
//! must obtain a fresh live `unsat` result before crediting `Formal`.
//!
//! # Content correlation, not authentication
//!
//! Rows use [`ay_bridge::verdict_cache_key_v2`]: `SHA-256(domain-tag ||
//! solver-bytes-SHA-256 || SMT2 bytes)`. Re-deriving a key from the query gives
//! strong correlation and corruption detection, but a writable source or cache
//! file can still be forged. A candidate hit can therefore only request live
//! revalidation; it cannot establish a verdict.
//!
//! # Trust story (read `verdict_db/README.md`)
//!
//! The manifest binds the solver bytes that produced the candidate rows and
//! self-disables on a mismatch. Every matching hit is nevertheless re-run with
//! the solver in the current process. Only that live result can be credited.
//! Timeout / CounterExample / Unknown / Error are never persisted.
//!
//! # Fail-closed corruption policy
//!
//! The parser is strict: any malformed header or row disables the tier. Even a
//! well-formed forged candidate cannot mint `Verified`; it still requires a
//! live solver result in this process.

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::{Mutex, OnceLock};

use crate::ay_bridge::{
    AYConfig, AYResult, generate_smt2_query, generate_smt2_query_raw, resolved_solver_path,
    simplifier_alone_proved_unsat, solver_identity_hash, verdict_cache_key_v2,
};
use crate::lowering_proof::{ProofObligation, VerificationConfig};
use crate::proof_database::{ProofCategory, ProofDatabase};
use crate::verify::VerificationStrength;

/// The committed tier-0 DB, embedded at build time. Regenerate with
/// `cargo run -p trust-cg-verify --bin regen_verdict_db` (requires the real
/// `ay` solver; see `verdict_db/README.md`), then rebuild + commit.
const EMBEDDED_TIER0_VDB: &str = include_str!("../verdict_db/tier0.vdb");

/// Schema line every tier-0 DB file must start with.
pub const TIER0_SCHEMA_LINE: &str = "tcg-verdict-db-v1";

/// One verdict row: the obligation's diagnostic name plus the EXACT SMT2
/// bytes the solver returned `unsat` for. The name is informational (regen /
/// diagnostics); the SMT2 bytes are the load-bearing content the lookup key
/// is derived from.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tier0Entry {
    /// Obligation name as reported by the discharge site (diagnostic only).
    pub name: String,
    /// The exact SMT2 query text the recorded solver run proved `unsat`.
    pub smt2: String,
}

/// A parsed tier-0 DB file (manifest header + rows).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Tier0Parsed {
    /// Lowercase-hex SHA-256 of the solver binary that produced every row.
    pub solver_identity: String,
    /// The solver's reported version string at regen time (informational).
    pub solver_version: Option<String>,
    /// Free-text provenance recorded at regen time (informational).
    pub provenance: Option<String>,
    /// The verdict rows.
    pub entries: Vec<Tier0Entry>,
}

/// A tier-0 DB prepared for lookup: the manifest solver identity plus the
/// set of v2 verdict keys derived from each row's SMT2 provenance. Keys are
/// derived (never read) from the file, so a row asserting a key it cannot
/// reproduce from its own SMT2 bytes simply does not exist here.
#[derive(Debug)]
pub(crate) struct Tier0Db {
    solver_identity: String,
    keys: HashSet<String>,
}

impl Tier0Db {
    fn from_parsed(parsed: &Tier0Parsed) -> Self {
        let keys = parsed
            .entries
            .iter()
            .map(|e| verdict_cache_key_v2(&parsed.solver_identity, &e.smt2))
            .collect();
        Tier0Db {
            solver_identity: parsed.solver_identity.clone(),
            keys,
        }
    }
}

/// Parse a tier-0 DB file. STRICT: any malformed construct returns `Err`
/// (which disables the whole tier — fail closed, live discharge). An
/// empty / whitespace-only file parses to `Ok(None)` ("no DB yet"), so the
/// committed placeholder never errors on hosts that have not regenerated.
///
/// Format (`tcg-verdict-db-v1`):
///
/// ```text
/// tcg-verdict-db-v1
/// solver-sha256: <64 lowercase hex>
/// solver-version: <free text>          (optional)
/// provenance: <free text>              (optional)
/// entry <smt2-byte-len> <name>
/// <exactly smt2-byte-len bytes of SMT2>
/// entry ...
/// ```
///
/// Rows are length-framed (SMT2 is multi-line); each SMT2 payload is
/// followed by exactly one `\n` separator.
pub fn parse_tier0_text(text: &str) -> Result<Option<Tier0Parsed>, String> {
    if text.trim().is_empty() {
        return Ok(None);
    }
    let bytes = text.as_bytes();
    let mut pos = 0usize;

    let next_line = |pos: &mut usize| -> Result<String, String> {
        if *pos >= bytes.len() {
            return Err("unexpected end of file".to_string());
        }
        let start = *pos;
        let end = bytes[start..]
            .iter()
            .position(|&b| b == b'\n')
            .map(|i| start + i)
            .ok_or_else(|| "missing trailing newline".to_string())?;
        *pos = end + 1;
        String::from_utf8(bytes[start..end].to_vec()).map_err(|_| "non-UTF8 line".to_string())
    };

    // Header: schema line, then solver-sha256, then optional info lines.
    let schema = next_line(&mut pos)?;
    if schema != TIER0_SCHEMA_LINE {
        return Err(format!(
            "unrecognized schema line {schema:?} (expected {TIER0_SCHEMA_LINE:?})"
        ));
    }
    let identity_line = next_line(&mut pos)?;
    let solver_identity = identity_line
        .strip_prefix("solver-sha256: ")
        .ok_or_else(|| format!("expected 'solver-sha256: <hex>' line, got {identity_line:?}"))?
        .to_string();
    if solver_identity.len() != 64
        || !solver_identity
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
    {
        return Err(format!(
            "solver-sha256 value must be 64 lowercase hex chars, got {solver_identity:?}"
        ));
    }

    let mut solver_version: Option<String> = None;
    let mut provenance: Option<String> = None;
    let mut entries: Vec<Tier0Entry> = Vec::new();

    while pos < bytes.len() {
        let line = next_line(&mut pos)?;
        if let Some(rest) = line.strip_prefix("solver-version: ") {
            if solver_version.is_some() || !entries.is_empty() {
                return Err("duplicate or misplaced solver-version line".to_string());
            }
            solver_version = Some(rest.to_string());
        } else if let Some(rest) = line.strip_prefix("provenance: ") {
            if provenance.is_some() || !entries.is_empty() {
                return Err("duplicate or misplaced provenance line".to_string());
            }
            provenance = Some(rest.to_string());
        } else if let Some(rest) = line.strip_prefix("entry ") {
            let (len_str, name) = rest
                .split_once(' ')
                .ok_or_else(|| format!("malformed entry line {line:?}"))?;
            let len: usize = len_str
                .parse()
                .map_err(|_| format!("malformed entry length in {line:?}"))?;
            if name.is_empty() {
                return Err(format!("empty entry name in {line:?}"));
            }
            let end = pos
                .checked_add(len)
                .filter(|&e| e <= bytes.len())
                .ok_or_else(|| format!("entry {name:?} overruns the file"))?;
            let smt2 = String::from_utf8(bytes[pos..end].to_vec())
                .map_err(|_| format!("entry {name:?} SMT2 is not UTF-8"))?;
            pos = end;
            if pos >= bytes.len() || bytes[pos] != b'\n' {
                return Err(format!("entry {name:?} missing its newline separator"));
            }
            pos += 1;
            entries.push(Tier0Entry {
                name: name.to_string(),
                smt2,
            });
        } else if line.is_empty() {
            // Tolerate blank separator lines between rows only.
            continue;
        } else {
            return Err(format!("unrecognized line {line:?}"));
        }
    }

    Ok(Some(Tier0Parsed {
        solver_identity,
        solver_version,
        provenance,
        entries,
    }))
}

/// Render a tier-0 DB file. Enforces the Verified-only-by-construction row
/// policy at the format level (there is no verdict column that could hold a
/// Timeout) and produces DETERMINISTIC output: rows are sorted and deduped,
/// so regen re-runs are diff-clean when the solver and obligations are
/// unchanged.
pub fn render_tier0_db(
    solver_identity: &str,
    solver_version: Option<&str>,
    provenance: Option<&str>,
    entries: &[Tier0Entry],
) -> Result<String, String> {
    if solver_identity.len() != 64
        || !solver_identity
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
    {
        return Err("solver identity must be 64 lowercase hex chars".to_string());
    }
    let mut sorted: Vec<&Tier0Entry> = entries.iter().collect();
    sorted.sort();
    sorted.dedup();

    let mut out = String::new();
    out.push_str(TIER0_SCHEMA_LINE);
    out.push('\n');
    out.push_str(&format!("solver-sha256: {solver_identity}\n"));
    if let Some(version) = solver_version {
        if version.contains('\n') {
            return Err("solver-version must be a single line".to_string());
        }
        out.push_str(&format!("solver-version: {version}\n"));
    }
    if let Some(prov) = provenance {
        if prov.contains('\n') {
            return Err("provenance must be a single line".to_string());
        }
        out.push_str(&format!("provenance: {prov}\n"));
    }
    for entry in sorted {
        if entry.name.is_empty() || entry.name.contains('\n') {
            return Err(format!("invalid entry name {:?}", entry.name));
        }
        out.push_str(&format!("entry {} {}\n", entry.smt2.len(), entry.name));
        out.push_str(&entry.smt2);
        out.push('\n');
    }
    // Round-trip check: what we wrote must parse back to the same rows, so a
    // renderer bug can never commit a file the loader would misread.
    match parse_tier0_text(&out) {
        Ok(Some(parsed)) => {
            let mut expect: Vec<Tier0Entry> = entries.to_vec();
            expect.sort();
            expect.dedup();
            if parsed.entries != expect {
                return Err("render/parse round-trip mismatch".to_string());
            }
        }
        Ok(None) => {
            if !entries.is_empty() {
                return Err("render/parse round-trip lost all rows".to_string());
            }
        }
        Err(e) => return Err(format!("rendered DB fails to parse: {e}")),
    }
    Ok(out)
}

// ---------------------------------------------------------------------------
// Lookup (the per-compile hot path)
// ---------------------------------------------------------------------------

/// The embedded tier-0 DB, parsed and keyed once per process. `None` when the
/// committed file is empty, unparsable (strict fail-closed), or opted out.
/// The committed DB's recorded solver identity, read from the HEADER ONLY.
///
/// The manifest's `solver-sha256` is the second line of the embedded text, so
/// this needs no body parse and allocates one 64-char string. It exists so the
/// SELF-DISABLE check can run BEFORE [`embedded_tier0`] materializes anything.
///
/// MEASURED (2026-08-07): `embedded_tier0` parses the 6.27 MB `include_str!`
/// and SHA-256s EVERY entry to build its key set — ~9.5 MB of the bridge's
/// ~19 MB compile-memory gap over LLVM — and on a host whose solver does not
/// match the manifest, every byte of that is built and then discarded, because
/// `tier0_candidate_in` only compares identities afterwards. Any host with a
/// locally-built `ay` is in exactly that state.
///
/// `None` when the embedded text is empty or its header is malformed; both
/// cases already disable the tier, and the full parse still runs its strict
/// validation (and still emits the malformed-DB warning) whenever the identity
/// matches.
fn embedded_tier0_identity() -> Option<&'static str> {
    static IDENTITY: OnceLock<Option<String>> = OnceLock::new();
    IDENTITY
        .get_or_init(|| {
            let mut lines = EMBEDDED_TIER0_VDB.lines();
            if lines.next()? != TIER0_SCHEMA_LINE {
                return None;
            }
            let identity = lines.next()?.strip_prefix("solver-sha256: ")?;
            // Same validity rule the full parse applies, so this can never
            // admit an identity the parse would reject.
            if identity.len() != 64
                || !identity
                    .bytes()
                    .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
            {
                return None;
            }
            Some(identity.to_string())
        })
        .as_deref()
}

fn embedded_tier0() -> Option<&'static Tier0Db> {
    static DB: OnceLock<Option<Tier0Db>> = OnceLock::new();
    DB.get_or_init(|| match parse_tier0_text(EMBEDDED_TIER0_VDB) {
        Ok(Some(parsed)) => Some(Tier0Db::from_parsed(&parsed)),
        Ok(None) => None,
        Err(e) => {
            // Fail closed: a corrupt committed DB disables the whole tier
            // (every lookup misses; the live solver runs). Warn once.
            eprintln!(
                "trust-cg-verify::verdict_db: WARNING: committed tier-0 verdict DB is \
                 malformed and has been DISABLED (live solver discharge continues): {e}"
            );
            None
        }
    })
    .as_ref()
}

/// Tier-0 candidate lookup: does the committed DB contain a recorded `unsat`
/// row under `key` for the solver at `solver_path`?
///
/// This is only a hint. Its result must never be promoted to proof authority
/// without a live solver revalidation in the current process. SELF-DISABLE:
/// returns `false` — regardless of the key — unless
/// the resolved solver binary's bytes-hash EQUALS the DB manifest's recorded
/// solver identity. A new/rebuilt/foreign solver therefore invalidates every
/// shipped verdict and falls back to live discharge; stale verdicts are never
/// trusted. Opt out entirely with `TCG_NO_VERDICT_DB=1` (or all verdict reuse
/// with `TCG_NO_PROOF_CACHE=1`, which the caller gates).
fn tier0_candidate_verified(solver_path: &str, key: &str) -> bool {
    if std::env::var_os("TCG_NO_VERDICT_DB").is_some() {
        return false;
    }
    // SELF-DISABLE EARLY. The identity comparison below is the same one
    // `tier0_candidate_in` performs; doing it against the HEADER first means a
    // host whose solver does not match the committed DB never materializes the
    // DB at all. That is ~9.5 MB of parsed text and per-entry SHA-256 keys
    // saved on every such compile — and the rows could not have been used.
    //
    // A matching host is unaffected: it falls through to the full parse exactly
    // as before, including its strict validation.
    // Same short-circuit as the session cache and the cert tier: a `-dirty`
    // solver can never match the committed manifest.
    if crate::ay_bridge::default_solver_reports_dirty_build(solver_path) {
        return false;
    }
    let Some(expected) = embedded_tier0_identity() else {
        return false;
    };
    match solver_identity_hash(solver_path) {
        Some(identity) if identity == expected => {}
        _ => return false,
    }
    let Some(db) = embedded_tier0() else {
        return false;
    };
    tier0_candidate_in(db, solver_path, key)
}

/// Core of [`tier0_candidate_verified`] over an explicit DB. This checks only
/// provenance/key membership; callers cannot treat `true` as a proof verdict.
fn tier0_candidate_in(db: &Tier0Db, solver_path: &str, key: &str) -> bool {
    let Some(identity) = solver_identity_hash(solver_path) else {
        // Unreadable solver binary: identity unknown, never trust tier-0.
        return false;
    };
    if identity != db.solver_identity {
        // SELF-DISABLE: the resolved solver is not the binary that produced
        // the committed verdicts. Fall back to live discharge.
        return false;
    }
    db.keys.contains(key)
}

// ---------------------------------------------------------------------------
// Per-compile tier-0 preference for FIXED registry obligations (PROOF-4 B1)
// ---------------------------------------------------------------------------

/// Fixed, env-independent solver timeout baked into every DB-obligation SMT2
/// query. Pinned (NOT [`crate::ay_bridge::DEFAULT_AY_TIMEOUT_MS`] via the
/// env-sensitive resolver) so the `(set-option :timeout ...)` line — and
/// therefore the derived content key — is byte-identical between the offline
/// regen run and the per-compile lookup regardless of the ambient
/// `TRUST_CG_AY_TIMEOUT_MS`. 30 s is the DEFAULT and the existing seed rows'
/// value; the full-DB gate proves the whole registry at a 10 s budget, so this
/// value only affects which genuinely solver-hard obligations land on the
/// exemption list, never the per-compile cost (no solver runs on the lookup
/// path).
pub(crate) const DB_VERDICT_TIMEOUT_MS: u64 = 30_000;

/// The canonical solver config for DB-obligation verdicts. `solver_path` does
/// NOT affect the emitted SMT2 (only `timeout_ms` + `produce_models` do), so
/// the offline regen (which pins the resolved solver) and the per-compile
/// lookup (`None`) produce byte-identical queries under this config.
pub(crate) fn db_verdict_config() -> AYConfig {
    AYConfig {
        solver_path: None,
        timeout_ms: DB_VERDICT_TIMEOUT_MS,
        produce_models: true,
    }
}

/// The exact SMT2 query bytes a DB obligation's verdict is keyed by. Mirrors
/// EXACTLY what [`crate::ay_bridge::verify_with_ay`] passes to the solver
/// funnel: the `simplifier_alone_proved_unsat` TCB guard routes to the RAW
/// (un-simplified) generator so that the SOLVER — never a local rewrite — is
/// what produced any recorded `unsat`. Regen records these exact bytes; the
/// lookup re-derives them, so a hit means the byte-identical query was proven
/// offline by the recorded solver.
// `pub(crate)` so the ENC-6 LRAT-certificate builder (`crate::lrat_cert`)
// certifies the BYTE-IDENTICAL query a tier-0 row is keyed by — the cert's
// `verdict_key` therefore matches the verdict-DB row it backs.
pub(crate) fn db_obligation_smt2(obligation: &ProofObligation) -> String {
    let config = db_verdict_config();
    if simplifier_alone_proved_unsat(obligation) {
        generate_smt2_query_raw(obligation, &config)
    } else {
        generate_smt2_query(obligation, &config)
    }
}

/// Process-wide resolution of `(solver_path, solver_identity)` for tier-0
/// obligation lookups. Resolved ONCE per process (`find_solver_binary` can
/// spawn `which`; the binary-bytes hash is itself memoized in
/// [`solver_identity_hash`]).
fn tier0_solver() -> Option<&'static (String, String)> {
    static SOLVER: OnceLock<Option<(String, String)>> = OnceLock::new();
    SOLVER
        .get_or_init(|| {
            let path = resolved_solver_path()?;
            let identity = solver_identity_hash(&path)?;
            Some((path, identity))
        })
        .as_ref()
}

/// The process-wide memo for [`tier0_lookup_obligation`], keyed by the FULL
/// obligation content (a lookup can never serve a verdict for different
/// content). Bounded by the number of DISTINCT registry obligations.
fn tier0_obligation_memo() -> &'static Mutex<HashMap<ProofObligation, bool>> {
    static MEMO: OnceLock<Mutex<HashMap<ProofObligation, bool>>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

/// Per-compile tier-0 preference (PROOF-4 B1): does a committed candidate for
/// this fixed obligation revalidate `Verified` with a live solver run in this
/// process?
///
/// The DB is an optimization hint only. A row is attacker-forgeable data, not a
/// certificate; a hit therefore invokes the selected solver on the obligation
/// and credits `Formal` only when that live invocation returns `Verified`.
/// Successful and failed revalidations are memoized by full obligation content
/// for this process. Opt out with `TCG_NO_VERDICT_DB=1` /
/// `TCG_NO_PROOF_CACHE=1`.
pub(crate) fn tier0_lookup_obligation(obligation: &ProofObligation) -> bool {
    if std::env::var_os("TCG_NO_VERDICT_DB").is_some()
        || crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some()
    {
        return false;
    }
    if let Some(hit) = tier0_obligation_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .get(obligation)
        .copied()
    {
        return hit;
    }
    let hit = tier0_lookup_obligation_uncached(obligation);
    tier0_obligation_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .insert(obligation.clone(), hit);
    hit
}

/// Core of [`tier0_lookup_obligation`] (no memo). A candidate hit is always
/// followed by live solver revalidation before returning `true`.
fn tier0_lookup_obligation_uncached(obligation: &ProofObligation) -> bool {
    // BEFORE `tier0_solver()`, which computes the ~320ms content hash: a
    // `-dirty` solver can never match the committed manifest, so this tier is
    // going to decline anyway. Checking here (~10ms, memoized) rather than
    // after keeps the hash off the compile path entirely on a developer box.
    // Decline-only, exactly as in `tier0_candidate_verified` — see
    // `ay_bridge::solver_reports_dirty_build`.
    if let Some(path) = resolved_solver_path()
        && crate::ay_bridge::default_solver_reports_dirty_build(&path)
    {
        return false;
    }
    let Some((path, identity)) = tier0_solver() else {
        return false;
    };
    let smt2 = db_obligation_smt2(obligation);
    let key = verdict_cache_key_v2(identity, &smt2);
    if !tier0_candidate_verified(path, &key) {
        return false;
    }
    revalidate_obligation_with_solver(obligation, path)
}

fn revalidate_obligation_with_solver(obligation: &ProofObligation, solver_path: &str) -> bool {
    let mut config = db_verdict_config();
    config.solver_path = Some(solver_path.to_owned());
    matches!(
        crate::ay_bridge::verify_with_ay(obligation, &config),
        AYResult::Verified
    )
}

/// Test-only: the [`tier0_lookup_obligation_uncached`] derivation against an
/// EXPLICIT DB + solver (so drift between the regen-recording SMT2 and the
/// per-compile lookup SMT2 is caught without a live solver at test time).
#[cfg(test)]
pub(crate) fn tier0_candidate_obligation_in(
    db: &Tier0Db,
    solver_path: &str,
    obligation: &ProofObligation,
) -> bool {
    let Some(identity) = solver_identity_hash(solver_path) else {
        return false;
    };
    let smt2 = db_obligation_smt2(obligation);
    let key = verdict_cache_key_v2(&identity, &smt2);
    tier0_candidate_in(db, solver_path, &key)
}

/// Test-only full consume path over an explicit DB and solver. Unlike the
/// candidate probe above, this returns true only after a live solver result.
#[cfg(test)]
pub(crate) fn tier0_revalidated_obligation_in(
    db: &Tier0Db,
    solver_path: &str,
    obligation: &ProofObligation,
) -> bool {
    if !tier0_candidate_obligation_in(db, solver_path, obligation) {
        return false;
    }
    revalidate_obligation_with_solver(obligation, solver_path)
}

// ---------------------------------------------------------------------------
// Per-compile live-solver fallback for RECONSTRUCTED obligations (PROOF-5 B2)
// ---------------------------------------------------------------------------

/// PROOF-5 B2: is the per-compile LIVE-solver fallback for reconstructed
/// obligations enabled? **Off by default** — the PRIMARY statistical-retirement
/// mechanism is the OFFLINE tier-0 parametric DB (a pure lookup, no solver
/// spawn), which covers the hot integer ALU/shift/neg/not surface. The live
/// fallback spawns a solver per tier-0 MISS, so it is reserved for an explicit
/// STRICT lane and must be OPTED IN with `TCG_RECON_SOLVER_ROUTE=1`; it then
/// additionally requires a usable solver present and the solver lane not
/// disabled via `TCG_REFINE_SOLVER=0`.
///
/// Default posture (this returns `false`): tier-0 lookup credits the covered
/// families `Formal`, and any uncovered family keeps a clearly-labeled
/// `Statistical` fallback — never fail-closed, never a compile-time regression.
/// A solver-ABSENT host always returns `false` (statistical fallback preserved).
pub(crate) fn reconstructed_live_solver_enabled() -> bool {
    // Opt-in only (the hot-path solver spawn is a deliberate strict-lane choice).
    if std::env::var_os("TCG_RECON_SOLVER_ROUTE").is_none_or(|v| v == "0") {
        return false;
    }
    if crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_some() {
        return false;
    }
    // `TCG_REFINE_SOLVER=0` (bridge escape hatch) also disables this lane.
    if crate::env_lock::var_os("TCG_REFINE_SOLVER").is_some_and(|v| v == "0") {
        return false;
    }
    tier0_solver().is_some()
}

/// Bounded per-compile solver budget (ms) for the reconstructed live-solve
/// fallback. Deliberately SHORTER than [`DB_VERDICT_TIMEOUT_MS`] (the offline
/// regen budget): a genuinely solver-hard reconstructed family (e.g. signed
/// div/rem over the INT_MIN/-1 corner) times out quickly and falls back to the
/// statistical posture rather than stalling the compile; the common fast
/// families (LEA effective-address, FP conversions, uncovered ALU widths)
/// discharge in well under a second. Overridable via `TCG_RECON_SOLVER_MS`.
const RECON_LIVE_SOLVE_TIMEOUT_MS: u64 = 5_000;

fn recon_live_solve_config() -> AYConfig {
    let timeout_ms = std::env::var("TCG_RECON_SOLVER_MS")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .unwrap_or(RECON_LIVE_SOLVE_TIMEOUT_MS);
    AYConfig {
        solver_path: None,
        timeout_ms,
        produce_models: true,
    }
}

/// Process-wide memo for [`live_discharge_reconstructed`], keyed by full
/// obligation content — so at most ONE solver spawn per DISTINCT reconstructed
/// obligation per process (repeated instances of the same lowering share the
/// verdict), and a Timeout is not re-attempted within the process.
fn live_recon_memo()
-> &'static Mutex<HashMap<ProofObligation, Option<crate::verify::VerificationResult>>> {
    static MEMO: OnceLock<
        Mutex<HashMap<ProofObligation, Option<crate::verify::VerificationResult>>>,
    > = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

/// PROOF-5 B2: discharge a reconstructed obligation with a LIVE solver run
/// (consulting the dde503a disk cache first via [`crate::ay_bridge::verify_with_ay`]).
///
/// - `Some(Valid)` on `Verified` — SolverProven, credited `Formal`.
/// - `Some(Invalid{..})` on a genuine `CounterExample` — the caller fails CLOSED
///   (the P0 miscompile catch; QF_BV counterexamples are deterministic).
/// - `None` on Timeout/Unknown/Error — INCONCLUSIVE; the caller keeps the
///   statistical fallback (never a nondeterministic reject).
///
/// Never spawns while the regen recorder is armed (the offline builder owns that
/// path). Process-memoized by full obligation content.
pub(crate) fn live_discharge_reconstructed(
    obligation: &ProofObligation,
) -> Option<crate::verify::VerificationResult> {
    // The offline regen drives its own solver runs with the recorder armed;
    // never re-enter the live path from underneath it.
    if recording_active() {
        return None;
    }
    if let Some(hit) = live_recon_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .get(obligation)
        .cloned()
    {
        return hit;
    }
    let verdict = live_discharge_reconstructed_uncached(obligation);
    live_recon_memo()
        .lock()
        .unwrap_or_else(|p| p.into_inner())
        .insert(obligation.clone(), verdict.clone());
    verdict
}

fn live_discharge_reconstructed_uncached(
    obligation: &ProofObligation,
) -> Option<crate::verify::VerificationResult> {
    use crate::verify::VerificationResult;
    match crate::ay_bridge::verify_with_ay(obligation, &recon_live_solve_config()) {
        AYResult::Verified => Some(VerificationResult::Valid),
        AYResult::SolverUnsat => None,
        AYResult::CounterExample(model) => Some(VerificationResult::Invalid {
            counterexample: format!("{model:?}"),
        }),
        AYResult::Timeout | AYResult::Unknown(_) | AYResult::Error(_) => None,
    }
}

// ---------------------------------------------------------------------------
// Regen recorder (the builder path)
// ---------------------------------------------------------------------------

fn recorder() -> &'static Mutex<Option<Vec<Tier0Entry>>> {
    static RECORDER: OnceLock<Mutex<Option<Vec<Tier0Entry>>>> = OnceLock::new();
    RECORDER.get_or_init(|| Mutex::new(None))
}

/// Whether the tier-0 regen recorder is armed. While armed, the CLI solver
/// funnel bypasses BOTH verdict tiers (every discharge is a fresh live solver
/// run) and reports each result to [`record_live_result`].
pub fn recording_active() -> bool {
    recorder()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .is_some()
}

/// Arm the regen recorder (single owner: the regen tool / regen tests).
pub fn record_begin() {
    *recorder()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner()) = Some(Vec::new());
}

/// Disarm the recorder and take everything it captured.
pub fn record_take() -> Vec<Tier0Entry> {
    recorder()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .take()
        .unwrap_or_default()
}

/// Observe one LIVE solver result. ONLY `AYResult::Verified` is ever
/// recorded: Timeout / CounterExample / Unknown / Error results are dropped
/// here — negative or inconclusive verdicts must never become rows in any
/// verdict tier (a Timeout is a scheduling fact, not a proof fact).
pub(crate) fn record_live_result(name: &str, smt2: &str, result: &AYResult) {
    if !matches!(result, AYResult::Verified) {
        return;
    }
    if let Some(entries) = recorder()
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
        .as_mut()
    {
        entries.push(Tier0Entry {
            name: name.to_string(),
            smt2: smt2.to_string(),
        });
    }
}

// ---------------------------------------------------------------------------
// Regen (offline builder — runs the REAL solver)
// ---------------------------------------------------------------------------

/// One registry obligation the real solver did NOT discharge `Verified`
/// offline (a Timeout / Unknown / Error at the pinned budget). Recorded on the
/// committed EXEMPTION LIST (`verdict_db/exemptions.txt`) rather than silently
/// credited: an exempted obligation keeps its (sound, weaker) statistical-sweep
/// discharge on the compile path until solver work or a lane-wise decomposition
/// closes it. A solver COUNTEREXAMPLE is NOT an exemption — it is P0 soundness
/// evidence and aborts regen.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Tier0Exemption {
    /// Short reason tag (`Timeout` / `Unknown` / `Error`).
    pub reason: String,
    /// The obligation's category name (diagnostic grouping).
    pub category: String,
    /// The obligation's diagnostic name.
    pub name: String,
}

/// Report returned by [`regen_tier0_db`].
#[derive(Debug)]
pub struct Tier0RegenReport {
    /// The solver binary whose live runs produced the rows.
    pub solver_path: String,
    /// Its content identity (lowercase-hex SHA-256 of its bytes).
    pub solver_identity: String,
    /// Its reported version string, when detectable.
    pub solver_version: Option<String>,
    /// `(obligation name, SMT2 byte length)` per committed row.
    pub entries: Vec<(String, usize)>,
    /// Number of committed rows sourced from the fixed pass-validator SEEDS
    /// (popcnt + guard-carrier canaries).
    pub seed_rows: usize,
    /// Number of committed rows sourced from the ProofDatabase REGISTRY
    /// (offline-proven >8-bit lowering-pattern obligations, PROOF-4 B1).
    pub db_rows: usize,
    /// Number of committed rows sourced from the CANONICAL (parametric)
    /// RECONSTRUCTION obligations (x86 + aarch64 integer ALU/shift/neg/not; one
    /// row per (family, width) credits the whole width family, PROOF-5 B2).
    pub recon_rows: usize,
    /// Registry/reconstruction obligations the solver did not discharge
    /// `Verified` (recorded on the exemption list, NOT credited).
    pub exemptions: Vec<Tier0Exemption>,
    /// Where the exemption list was written.
    pub exemptions_path: std::path::PathBuf,
}

/// Run every SEED validator through the real solver with the recorder armed
/// and write the resulting tier-0 DB to `out_path`.
///
/// The seeds are the fixed, program-independent, per-process OnceLock canary
/// obligations that today cost a live solver run per cold rustc process:
///
/// - the popcnt SWAR width-32 canary (`trust-cg-codegen` compiler.rs,
///   `validate_x86_popcnt_expansion_canary` — the ~16 s/process one), and
/// - the four Sentinel-S5 guard-carrier expansion canaries at widths 32/64
///   (`x86_64/pipeline.rs` `run_guard_carrier_canary`): Bounds/`AE`,
///   ShiftRange/`AE`, NullIfZero/`E`, DivZero/`E`.
///
/// The `(kind, cond)` pairs mirror the pipeline's `trap_cond` derivations.
/// This duplication is SAFE by construction: a drifted pair either fails
/// regen (the validator refutes a wrong cc — it can never record a wrong-cc
/// `Verified`) or produces a row no compile ever queries (tier-0 miss ⇒ live
/// discharge). It can never mint a verdict for code the pipeline emits.
///
/// Fails (writing NOTHING) unless every seed obligation discharges
/// `Verified` on a live run — a Timeout/Refuted/Unknown seed can never be
/// committed.
pub fn regen_tier0_db(out_path: &Path) -> Result<Tier0RegenReport, String> {
    let solver_path = crate::ay_bridge::resolved_solver_path().ok_or_else(|| {
        "no ay solver binary found (build ~/ay or set AY_SOLVER_PATH)".to_string()
    })?;
    let solver_identity = solver_identity_hash(&solver_path)
        .ok_or_else(|| format!("cannot read/hash solver binary at {solver_path}"))?;
    let solver_version = crate::ay_bridge::solver_version_string(&solver_path);

    // Enumerate the eligible ProofDatabase registry obligations (fixed,
    // program-independent, discharged STATISTICALLY at >8-bit today — the ones
    // the committed DB can turn into a solver-proven lookup). `ProofDatabase::
    // new()` needs a large stack, so build + filter on a dedicated thread.
    let eligible = enumerate_regen_eligible()?;

    // PROOF-5: the finite set of x86 + aarch64 CANONICAL (parametric)
    // RECONSTRUCTION obligations — the integer ALU/shift/neg/not surface, with
    // the immediate FREED so one row covers a whole width family. `ProofDatabase`
    // is not needed here, but reconstruction enumeration touches the same deep
    // encoder stack, so keep it on the large-stack worker for parity.
    let reconstructed = enumerate_reconstruct_regen_obligations()?;

    // Dry-run: enumerate + print, prove NOTHING, write NOTHING.
    if std::env::var_os("TCG_VERDICT_DB_DRYRUN").is_some() {
        print_regen_plan(&eligible);
        eprintln!(
            "regen_verdict_db: {} canonical (parametric) reconstruction obligation(s) \
             (x86 + aarch64 integer ALU/shift/neg/not, both widths)",
            reconstructed.len()
        );
        return Err(format!(
            "dry-run: enumerated {} eligible registry + {} reconstruction obligation(s) \
             (nothing written; unset TCG_VERDICT_DB_DRYRUN to prove + commit)",
            eligible.len(),
            reconstructed.len()
        ));
    }

    record_begin();
    let seed_result = run_seed_validators();
    // The registry + reconstruction phases run WHILE the recorder is armed:
    // every `Verified` funnel result is captured as a tier-0 row; per-obligation
    // exemptions / refutations are tracked from the returned AYResult.
    let db_outcome = prove_registry_obligations(&solver_path, &eligible);
    let recon_outcome = prove_reconstructed_obligations(&solver_path, &reconstructed);
    let recorded = record_take();
    seed_result?;
    let mut exemptions = db_outcome?; // P0 refutation propagates here (nothing written)
    exemptions.extend(recon_outcome?); // P0 refutation propagates here too

    if recorded.is_empty() {
        return Err(
            "no live Verified verdicts were recorded — expected the >8-bit seed + registry \
             obligations to reach the CLI solver funnel"
                .to_string(),
        );
    }

    // Row provenance split (seed / registry / reconstructed) for the report.
    // Seeds are the fixed pass-validator canary names; reconstructed rows carry
    // the RECONSTRUCTED name prefix; everything else is a registry row.
    let seed_rows = recorded
        .iter()
        .filter(|e| is_seed_row_name(&e.name))
        .count();
    let recon_rows = recorded
        .iter()
        .filter(|e| is_reconstructed_row_name(&e.name))
        .count();
    let db_rows = recorded
        .len()
        .saturating_sub(seed_rows)
        .saturating_sub(recon_rows);

    let provenance = std::env::var("TCG_VERDICT_DB_PROVENANCE").ok();
    let text = render_tier0_db(
        &solver_identity,
        solver_version.as_deref(),
        provenance.as_deref(),
        &recorded,
    )?;
    if let Some(parent) = out_path.parent() {
        std::fs::create_dir_all(parent)
            .map_err(|e| format!("cannot create {}: {e}", parent.display()))?;
    }
    std::fs::write(out_path, &text)
        .map_err(|e| format!("cannot write {}: {e}", out_path.display()))?;

    // The committed exemption list lives next to the DB. It is written on EVERY
    // regen (even when empty) so a genuinely-empty list is an explicit,
    // reviewable fact, not an absent file.
    let exemptions_path = out_path
        .parent()
        .unwrap_or_else(|| Path::new("."))
        .join("exemptions.txt");
    let exemptions_text = render_exemptions(
        &solver_identity,
        solver_version.as_deref(),
        provenance.as_deref(),
        &exemptions,
    );
    std::fs::write(&exemptions_path, &exemptions_text)
        .map_err(|e| format!("cannot write {}: {e}", exemptions_path.display()))?;

    let mut entries: Vec<(String, usize)> = recorded
        .iter()
        .map(|e| (e.name.clone(), e.smt2.len()))
        .collect();
    entries.sort();
    entries.dedup();
    Ok(Tier0RegenReport {
        solver_path,
        solver_identity,
        solver_version,
        entries,
        seed_rows,
        db_rows,
        recon_rows,
        exemptions,
        exemptions_path,
    })
}

/// A registry obligation eligible for offline tier-0 proving: fixed content,
/// STATISTICAL discharge strength (>8-bit / >2-input — exhaustive <=8-bit
/// obligations are already a complete proof and never query tier-0), and
/// NON-degenerate (a trivial `X==X` self-equality proves nothing and is never
/// committed as a "solver-proven" row).
struct RegenObligation {
    obligation: ProofObligation,
    category: ProofCategory,
}

/// Build `ProofDatabase::new()` on a large stack and return the eligible
/// registry obligations (see [`RegenObligation`]).
fn enumerate_regen_eligible() -> Result<Vec<RegenObligation>, String> {
    on_large_stack(|| {
        let db = ProofDatabase::new();
        let default_cfg = VerificationConfig::default();
        db.all()
            .iter()
            .filter(|cp| !cp.obligation.is_degenerate())
            .filter(|cp| {
                matches!(
                    VerificationStrength::for_obligation_with_config(&cp.obligation, &default_cfg),
                    VerificationStrength::Statistical { .. }
                )
            })
            .map(|cp| RegenObligation {
                obligation: cp.obligation.clone(),
                category: cp.category,
            })
            .collect()
    })
}

/// Prove each eligible registry obligation with a LIVE run of the real solver
/// (recorder armed → each `Verified` is captured as a tier-0 row). The solver
/// is PINNED to `solver_path` (the manifest binary) so every committed row is
/// genuinely proven by the binary the manifest names. Returns the exemption
/// list (Timeout / Unknown / Error). A solver COUNTEREXAMPLE aborts with a P0
/// error (nothing is written).
fn prove_registry_obligations(
    solver_path: &str,
    eligible: &[RegenObligation],
) -> Result<Vec<Tier0Exemption>, String> {
    let config = AYConfig {
        solver_path: Some(solver_path.to_string()),
        timeout_ms: DB_VERDICT_TIMEOUT_MS,
        produce_models: true,
    };
    let mut exemptions: Vec<Tier0Exemption> = Vec::new();
    let mut refutations: Vec<String> = Vec::new();
    let total = eligible.len();
    for (i, item) in eligible.iter().enumerate() {
        let ob = &item.obligation;
        // verify_with_ay applies the simplifier-unsat TCB guard (the SOLVER,
        // not a local rewrite, produces the recorded `unsat`); db_obligation_smt2
        // mirrors the exact same branch so the lookup key matches.
        let result = crate::ay_bridge::verify_with_ay(ob, &config);
        match result {
            AYResult::Verified => {} // captured by the armed recorder
            AYResult::SolverUnsat => exemptions.push(Tier0Exemption {
                reason: "SolverUnsatUncertified".to_string(),
                category: item.category.name().to_string(),
                name: ob.name.clone(),
            }),
            AYResult::CounterExample(model) => {
                refutations.push(format!("{} :: {model:?}", ob.name));
            }
            AYResult::Timeout => exemptions.push(Tier0Exemption {
                reason: "Timeout".to_string(),
                category: item.category.name().to_string(),
                name: ob.name.clone(),
            }),
            AYResult::Unknown(r) => exemptions.push(Tier0Exemption {
                reason: "Unknown".to_string(),
                category: item.category.name().to_string(),
                name: format!("{} ({r})", ob.name),
            }),
            AYResult::Error(e) => exemptions.push(Tier0Exemption {
                reason: "Error".to_string(),
                category: item.category.name().to_string(),
                name: format!("{} ({e})", ob.name),
            }),
        }
        if (i + 1) % 50 == 0 || i + 1 == total {
            eprintln!(
                "regen_verdict_db: proved {}/{} registry obligation(s) \
                 ({} exemption(s) so far)...",
                i + 1,
                total,
                exemptions.len()
            );
        }
    }

    if !refutations.is_empty() {
        return Err(format!(
            "P0 SOUNDNESS STOP: {} registry obligation(s) were REFUTED (SAT) by the real solver \
             — a committed verdict would have been a MISCOMPILE. NOTHING written. Refuted:\n  {}",
            refutations.len(),
            refutations.join("\n  ")
        ));
    }
    Ok(exemptions)
}

/// Run `f` on a 64 MiB stack (`ProofDatabase::new()` materializes the entire
/// proof registry and overflows the default 8 MiB thread stack).
fn on_large_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> Result<T, String> {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .map_err(|e| format!("cannot spawn regen worker thread: {e}"))?
        .join()
        .map_err(|_| "regen worker thread panicked".to_string())
}

/// PROOF-5: enumerate the x86 + aarch64 CANONICAL (parametric) reconstruction
/// obligations to prove offline into tier-0. Both arch enumerators build
/// synthetic register-operand instances and reconstruct them, so the SMT2 is
/// byte-identical to what the per-compile `canonical_reconstruct_obligation`
/// derives from a real instance. Deduped by full content (a family shared
/// across arches never double-commits a row). Runs on the large stack for
/// parity with the registry phase (the encoder stack is deep).
fn enumerate_reconstruct_regen_obligations() -> Result<Vec<ProofObligation>, String> {
    on_large_stack(|| {
        let mut out = crate::x86_64_function_verifier::enumerate_reconstruct_tier0_obligations();
        out.extend(crate::function_verifier::enumerate_reconstruct_tier0_obligations());
        // Only genuinely-reconstructed obligations belong in tier-0 (defensive:
        // every enumerated form is 32/64-bit and Reconstructed). A commutative
        // ALU form is structurally X==X yet still a real solver proof and the
        // reconstructed-credit rule credits it, so degeneracy is NOT filtered.
        out.retain(|ob| ob.is_reconstructed());
        let mut deduped: Vec<ProofObligation> = Vec::new();
        for ob in out {
            if !deduped.contains(&ob) {
                deduped.push(ob);
            }
        }
        deduped
    })
}

/// PROOF-5: prove each CANONICAL (parametric) reconstruction obligation with a
/// LIVE run of the real solver (recorder armed → each `Verified` becomes a
/// tier-0 row). The solver is PINNED to `solver_path` (the manifest binary).
/// Returns the exemption list (Timeout / Unknown / Error). A solver
/// COUNTEREXAMPLE aborts with a P0 error (nothing is written) — a previously
/// sample-accepted reconstruction coming back solver-REFUTED is a miscompile.
fn prove_reconstructed_obligations(
    solver_path: &str,
    obligations: &[ProofObligation],
) -> Result<Vec<Tier0Exemption>, String> {
    let config = AYConfig {
        solver_path: Some(solver_path.to_string()),
        timeout_ms: DB_VERDICT_TIMEOUT_MS,
        produce_models: true,
    };
    let mut exemptions: Vec<Tier0Exemption> = Vec::new();
    let mut refutations: Vec<String> = Vec::new();
    let total = obligations.len();
    for (i, ob) in obligations.iter().enumerate() {
        match crate::ay_bridge::verify_with_ay(ob, &config) {
            AYResult::Verified => {} // captured by the armed recorder
            AYResult::SolverUnsat => exemptions.push(Tier0Exemption {
                reason: "SolverUnsatUncertified".to_string(),
                category: "Reconstructed".to_string(),
                name: ob.name.clone(),
            }),
            AYResult::CounterExample(model) => {
                refutations.push(format!("{} :: {model:?}", ob.name));
            }
            AYResult::Timeout => exemptions.push(Tier0Exemption {
                reason: "Timeout".to_string(),
                category: "Reconstructed".to_string(),
                name: ob.name.clone(),
            }),
            AYResult::Unknown(r) => exemptions.push(Tier0Exemption {
                reason: "Unknown".to_string(),
                category: "Reconstructed".to_string(),
                name: format!("{} ({r})", ob.name),
            }),
            AYResult::Error(e) => exemptions.push(Tier0Exemption {
                reason: "Error".to_string(),
                category: "Reconstructed".to_string(),
                name: format!("{} ({e})", ob.name),
            }),
        }
        if (i + 1) % 10 == 0 || i + 1 == total {
            eprintln!(
                "regen_verdict_db: proved {}/{} reconstruction obligation(s) \
                 ({} exemption(s) so far)...",
                i + 1,
                total,
                exemptions.len()
            );
        }
    }

    if !refutations.is_empty() {
        return Err(format!(
            "P0 SOUNDNESS STOP: {} reconstruction obligation(s) were REFUTED (SAT) by the real \
             solver — a committed verdict would have been a MISCOMPILE. NOTHING written. \
             Refuted:\n  {}",
            refutations.len(),
            refutations.join("\n  ")
        ));
    }
    Ok(exemptions)
}

/// Diagnostic per-category breakdown of the eligible obligation set (dry-run).
fn print_regen_plan(eligible: &[RegenObligation]) {
    use std::collections::BTreeMap;
    let mut by_cat: BTreeMap<&str, usize> = BTreeMap::new();
    for item in eligible {
        *by_cat.entry(item.category.name()).or_insert(0) += 1;
    }
    eprintln!(
        "regen_verdict_db: {} eligible registry obligation(s) (non-degenerate, Statistical/>8-bit):",
        eligible.len()
    );
    for (cat, n) in by_cat {
        eprintln!("  {cat:30} {n:>4}");
    }
}

/// Names of the fixed pass-validator SEED rows (popcnt + guard-carrier),
/// distinguished from ProofDatabase registry rows for the regen report.
fn is_seed_row_name(name: &str) -> bool {
    name.contains("x86-popcnt-expand") || name.contains("x86-guard-carrier-expand")
}

/// Names of the CANONICAL (parametric) RECONSTRUCTION rows (PROOF-5), which
/// carry the `RECONSTRUCTED` prefix, distinguished from registry rows for the
/// regen report.
fn is_reconstructed_row_name(name: &str) -> bool {
    name.starts_with("RECONSTRUCTED")
}

/// Schema line every exemption-list file starts with.
pub const EXEMPTIONS_SCHEMA_LINE: &str = "tcg-verdict-db-exemptions-v1";

/// Substrings that JUSTIFY a committed exemption: each names a known class of
/// obligation the real `ay` solver is incomplete on at the pinned 30 s budget,
/// so a Timeout there is EXPECTED, NOT a regression. The committed exemption
/// list is checked against this set
/// (`committed_exemptions_are_consistent_and_justified`) so no exemption is
/// silently accepted — an exemption matching none of these fails the test and
/// demands either a decomposition or a justified new marker. Refined from the
/// ACTUAL regen output (2026-07 run, ay 0.11.0): 785/791 eligible registry
/// obligations proved Verified; the 6 timeouts fall into two documented
/// solver-hard classes:
///
/// - **Signed division / remainder over the INT_MIN/-1 overflow corner**
///   (`Sdiv`/`Srem`/`SDIV`): the x86-64 `Sdiv_I32/I64` + `Srem_I32/I64`
///   branchless-guarded IDIV totality proofs and the aarch64 `SDIV …#-1 ≡ NEG`
///   peephole. Full-width (32/64-bit) signed-division equivalence bit-blasts to
///   an expensive circuit and the INT_MIN/-1 total-function reasoning compounds
///   it — a long-documented SMT-hard family in this project (idiv_guard, the
///   i128 SDiv/SRem false-refutation, carrier-051 narrow-div). Kept on the
///   sound statistical-sweep fallback rather than spending unbounded regen time.
/// - **Coroutine-suspend frame-store non-interference** (`CoroSuspend`): the
///   symbolic byte-array (`Array BitVec64 BitVec8`) disjointness proof that the
///   state-slot store preserves the independently-yielded value; array-theory
///   reasoning over symbolic offsets times out at the budget.
pub const EXPECTED_EXEMPTION_MARKERS: &[&str] = &["Sdiv", "Srem", "SDIV", "CoroSuspend"];

/// Render the committed exemption list. Rows are sorted + deduped so regen is
/// diff-clean. Contains NO verdicts — an exemption is precisely the ABSENCE of
/// a committed verdict, recorded explicitly.
pub fn render_exemptions(
    solver_identity: &str,
    solver_version: Option<&str>,
    provenance: Option<&str>,
    exemptions: &[Tier0Exemption],
) -> String {
    let mut sorted: Vec<&Tier0Exemption> = exemptions.iter().collect();
    sorted.sort();
    sorted.dedup();

    let mut out = String::new();
    out.push_str(EXEMPTIONS_SCHEMA_LINE);
    out.push('\n');
    out.push_str(&format!("solver-sha256: {solver_identity}\n"));
    if let Some(v) = solver_version {
        out.push_str(&format!("solver-version: {v}\n"));
    }
    if let Some(p) = provenance {
        out.push_str(&format!("provenance: {p}\n"));
    }
    out.push_str(&format!("count: {}\n", sorted.len()));
    out.push_str(
        "# Registry obligations the real solver did NOT discharge Verified offline at the pinned\n\
         # 30s budget. NOT credited via tier-0 — each keeps the (sound, weaker) statistical-sweep\n\
         # discharge on the compile path until solver work / lane-wise decomposition closes it.\n\
         # Format per row: <reason>\\t<category>\\t<name>\n",
    );
    for e in sorted {
        out.push_str(&format!("{}\t{}\t{}\n", e.reason, e.category, e.name));
    }
    out
}

/// Parse a committed exemption list (see [`render_exemptions`]). Empty /
/// whitespace-only → `Ok(vec![])`. Strict on the schema line.
pub fn parse_exemptions(text: &str) -> Result<Vec<Tier0Exemption>, String> {
    if text.trim().is_empty() {
        return Ok(Vec::new());
    }
    let mut lines = text.lines();
    let schema = lines.next().unwrap_or_default();
    if schema != EXEMPTIONS_SCHEMA_LINE {
        return Err(format!(
            "unrecognized exemptions schema line {schema:?} (expected {EXEMPTIONS_SCHEMA_LINE:?})"
        ));
    }
    let mut out = Vec::new();
    for line in lines {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        if line.starts_with("solver-sha256:")
            || line.starts_with("solver-version:")
            || line.starts_with("provenance:")
            || line.starts_with("count:")
        {
            continue;
        }
        let mut cols = line.splitn(3, '\t');
        let (Some(reason), Some(category), Some(name)) = (cols.next(), cols.next(), cols.next())
        else {
            return Err(format!("malformed exemption row {line:?}"));
        };
        out.push(Tier0Exemption {
            reason: reason.to_string(),
            category: category.to_string(),
            name: name.to_string(),
        });
    }
    Ok(out)
}

/// The seed validators (see [`regen_tier0_db`]). Only >8-bit widths reach the
/// solver (8-bit lanes discharge exhaustively in-process and need no cache).
fn run_seed_validators() -> Result<(), String> {
    use crate::pass_validators::{
        GuardCarrierExpansionValidator, GuardCarrierKind, PassValidation, PassValidator,
        PopcntSwarExpansionValidator,
    };
    use trust_cg_ir::x86_64_ops::X86CondCode;

    let mut failures: Vec<String> = Vec::new();
    let mut run = |validator: &dyn PassValidator| {
        if let PassValidation::Rejected {
            obligation_name,
            reason,
        } = validator.validate()
        {
            failures.push(format!("{obligation_name}: {reason}"));
        }
    };

    // The popcnt SWAR canary at the dominant emitted width (32). Width 64 is
    // deliberately NOT seeded: it exceeds the solver timeout in `validate()`
    // and the compile-path canary never requests it (it is pinned as the
    // full-proof-job test `popcnt_swar_64_emitted_width_genuinely_verifies`).
    run(&PopcntSwarExpansionValidator::x86_generic(
        "x86-popcnt-expand",
        32,
    ));

    // The guard-carrier canaries, mirroring x86_64/pipeline.rs's trap_cond
    // per kind (see regen_tier0_db docs for why drift here is safe).
    for (kind, cond) in [
        (GuardCarrierKind::Bounds, X86CondCode::AE),
        (GuardCarrierKind::ShiftRange, X86CondCode::AE),
        (GuardCarrierKind::NullIfZero, X86CondCode::E),
        (GuardCarrierKind::DivZero, X86CondCode::E),
    ] {
        for width in [32u32, 64] {
            run(&GuardCarrierExpansionValidator::new(
                "x86-guard-carrier-expand",
                kind,
                cond,
                width,
            ));
        }
    }

    if failures.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "seed validator(s) did not discharge Verified on a live run:\n  {}",
            failures.join("\n  ")
        ))
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Recorder tests share one global recorder; serialize them.
    fn recorder_test_lock() -> std::sync::MutexGuard<'static, ()> {
        static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
        LOCK.get_or_init(|| Mutex::new(()))
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    fn temp_dir(tag: &str) -> std::path::PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "tcg_verdict_db_test_{tag}_{}_{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn fake_solver(dir: &Path, bytes: &[u8]) -> (String, String) {
        let path = dir.join(format!("fake_solver_{}", bytes.len()));
        std::fs::write(&path, bytes).unwrap();
        let path = path.to_str().unwrap().to_string();
        let identity = solver_identity_hash(&path).unwrap();
        (path, identity)
    }

    fn db_with(identity: &str, entries: &[Tier0Entry]) -> Tier0Db {
        let text = render_tier0_db(identity, Some("ay test 0.0"), None, entries).unwrap();
        let parsed = parse_tier0_text(&text).unwrap().unwrap();
        Tier0Db::from_parsed(&parsed)
    }

    #[cfg(unix)]
    fn fake_executable_solver(dir: &Path, name: &str, verdict: &str) -> (String, String) {
        use std::os::unix::fs::PermissionsExt;

        let path = dir.join(name);
        std::fs::write(&path, format!("#!/bin/sh\nprintf '%s\\n' '{verdict}'\n")).unwrap();
        let mut permissions = std::fs::metadata(&path).unwrap().permissions();
        permissions.set_mode(0o700);
        std::fs::set_permissions(&path, permissions).unwrap();
        let path = path.to_str().unwrap().to_owned();
        let identity = solver_identity_hash(&path).unwrap();
        (path, identity)
    }

    #[test]
    fn tier0_hit_and_miss() {
        let dir = temp_dir("hit_miss");
        let (solver, identity) = fake_solver(&dir, b"tier0 solver bytes A");
        let smt2 = "(set-logic QF_BV)\n(assert true)\n(check-sat)";
        let db = db_with(
            &identity,
            &[Tier0Entry {
                name: "seed-1".to_string(),
                smt2: smt2.to_string(),
            }],
        );

        // HIT: same solver bytes + byte-identical SMT2.
        let key = verdict_cache_key_v2(&identity, smt2);
        assert!(tier0_candidate_in(&db, &solver, &key));

        // MISS: any different SMT2 (even one byte).
        let other = verdict_cache_key_v2(&identity, "(assert false)");
        assert!(!tier0_candidate_in(&db, &solver, &other));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn cache_hardening_forged_tier0_unsat_row_cannot_override_live_counterexample() {
        use crate::lowering_proof::MachineSideProvenance;
        use crate::smt::SmtExpr;

        let dir = temp_dir("forged_row_revalidation");
        let (solver, identity) = fake_executable_solver(&dir, "sat-solver", "sat");
        let x = SmtExpr::var("x", 8);
        let obligation = ProofObligation {
            machine_side_provenance: MachineSideProvenance::StaticDb,
            name: "forged tier0 candidate".to_owned(),
            trust_ir_expr: x.clone(),
            aarch64_expr: x.bvadd(SmtExpr::bv_const(1, 8)),
            inputs: vec![("x".to_owned(), 8)],
            preconditions: vec![],
            fp_inputs: vec![],
            category: None,
        };
        let db = db_with(
            &identity,
            &[Tier0Entry {
                name: obligation.name.clone(),
                smt2: db_obligation_smt2(&obligation),
            }],
        );

        assert!(
            tier0_candidate_obligation_in(&db, &solver, &obligation),
            "the attacker-controlled row is intentionally a valid candidate"
        );
        assert!(
            !tier0_revalidated_obligation_in(&db, &solver, &obligation),
            "a candidate must not become Formal when the live solver reports SAT"
        );

        let (unsat_solver, unsat_identity) = fake_executable_solver(&dir, "unsat-solver", "unsat");
        let unsat_db = db_with(
            &unsat_identity,
            &[Tier0Entry {
                name: obligation.name.clone(),
                smt2: db_obligation_smt2(&obligation),
            }],
        );
        assert!(
            !tier0_revalidated_obligation_in(&unsat_db, &unsat_solver, &obligation),
            "a forged candidate plus a raw live UNSAT still lacks independently checked proof \
             authority"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn tier0_self_disables_on_solver_hash_mismatch() {
        let dir = temp_dir("self_disable");
        let (solver_a, identity_a) = fake_solver(&dir, b"tier0 solver bytes AA");
        let (solver_b, identity_b) = fake_solver(&dir, b"tier0 solver bytes BBB (a new ay)");
        assert_ne!(identity_a, identity_b);

        let smt2 = "(assert true)";
        let db = db_with(
            &identity_a,
            &[Tier0Entry {
                name: "seed-1".to_string(),
                smt2: smt2.to_string(),
            }],
        );

        // With the recorded solver: hit.
        assert!(tier0_candidate_in(
            &db,
            &solver_a,
            &verdict_cache_key_v2(&identity_a, smt2)
        ));
        // With a DIFFERENT solver binary: the tier self-disables — even a key
        // an attacker computed under the DB's own identity never hits.
        assert!(!tier0_candidate_in(
            &db,
            &solver_b,
            &verdict_cache_key_v2(&identity_b, smt2)
        ));
        assert!(!tier0_candidate_in(
            &db,
            &solver_b,
            &verdict_cache_key_v2(&identity_a, smt2)
        ));
        // With an unreadable solver path: never trust tier-0.
        assert!(!tier0_candidate_in(
            &db,
            "/nonexistent/solver/binary",
            &verdict_cache_key_v2(&identity_a, smt2)
        ));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn tier0_corrupt_rows_fail_closed() {
        let dir = temp_dir("corrupt");
        let (solver, identity) = fake_solver(&dir, b"tier0 solver bytes C");
        let smt2 = "(set-logic QF_BV)\n(assert true)\n(check-sat)";
        let good = render_tier0_db(
            &identity,
            None,
            None,
            &[Tier0Entry {
                name: "seed-1".to_string(),
                smt2: smt2.to_string(),
            }],
        )
        .unwrap();

        // (a) Structural corruption (broken framing / header / garbage) makes
        // the STRICT parser reject the whole file — tier disabled entirely.
        assert!(parse_tier0_text(&good.replace(TIER0_SCHEMA_LINE, "tcg-bogus-db")).is_err());
        assert!(parse_tier0_text(&good.replace("entry ", "entry-")).is_err());
        assert!(parse_tier0_text(&format!("{good}trailing garbage\n")).is_err());
        let truncated = &good[..good.len() - 2];
        assert!(parse_tier0_text(truncated).is_err());

        // (b) Provenance tamper: flip one byte of the row's SMT2 while
        // keeping the framing valid. The file still parses, but the row's
        // DERIVED key changes, so the ORIGINAL obligation misses and
        // re-proves live. A tampered row can never mint Verified for the
        // query it used to answer.
        let tampered_text = good.replace("(assert true)", "(assert trux)");
        let tampered = parse_tier0_text(&tampered_text).unwrap().unwrap();
        let tampered_db = Tier0Db::from_parsed(&tampered);
        let original_key = verdict_cache_key_v2(&identity, smt2);
        assert!(!tier0_candidate_in(&tampered_db, &solver, &original_key));

        // (c) Empty file = no DB, silently disabled (not an error).
        assert_eq!(parse_tier0_text(""), Ok(None));
        assert_eq!(parse_tier0_text("  \n \n"), Ok(None));

        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn recorder_keeps_verified_only_never_timeout() {
        let _guard = recorder_test_lock();
        record_begin();
        // Negative / inconclusive verdicts are NEVER recorded (and can
        // therefore never become committed rows): a Timeout is a scheduling
        // fact, not a proof fact.
        record_live_result("t0-timeout", "(q1)", &AYResult::Timeout);
        record_live_result(
            "t0-cex",
            "(q2)",
            &AYResult::CounterExample(vec![("x".to_string(), 1)]),
        );
        record_live_result(
            "t0-unknown",
            "(q3)",
            &AYResult::Unknown("gave up".to_string()),
        );
        record_live_result("t0-error", "(q4)", &AYResult::Error("io".to_string()));
        record_live_result("t0-solver-unsat", "(q4b)", &AYResult::SolverUnsat);
        record_live_result("t0-verified", "(q5)", &AYResult::Verified);
        let entries = record_take();
        assert!(!recording_active());

        assert!(
            entries
                .iter()
                .all(|e| !e.name.starts_with("t0-") || e.name == "t0-verified"),
            "only the Verified observation may be recorded, got {entries:?}"
        );
        assert!(
            entries
                .iter()
                .any(|e| e.name == "t0-verified" && e.smt2 == "(q5)"),
            "the Verified observation must be recorded"
        );

        // Disarmed recorder drops everything (no stray global growth).
        record_live_result("t0-after", "(q6)", &AYResult::Verified);
        assert!(record_take().is_empty());
    }

    #[test]
    fn render_is_deterministic_and_round_trips() {
        let identity = "ab".repeat(32);
        let entries = vec![
            Tier0Entry {
                name: "b-second".to_string(),
                smt2: "(assert b)\n(check-sat)".to_string(),
            },
            Tier0Entry {
                name: "a-first".to_string(),
                smt2: "(assert a)".to_string(),
            },
            // Duplicate row collapses.
            Tier0Entry {
                name: "a-first".to_string(),
                smt2: "(assert a)".to_string(),
            },
        ];
        let text1 = render_tier0_db(&identity, Some("ay 1.2.3"), Some("test"), &entries).unwrap();
        let mut reversed = entries.clone();
        reversed.reverse();
        let text2 = render_tier0_db(&identity, Some("ay 1.2.3"), Some("test"), &reversed).unwrap();
        assert_eq!(text1, text2, "row order must not affect the output");

        let parsed = parse_tier0_text(&text1).unwrap().unwrap();
        assert_eq!(parsed.solver_identity, identity);
        assert_eq!(parsed.solver_version.as_deref(), Some("ay 1.2.3"));
        assert_eq!(parsed.provenance.as_deref(), Some("test"));
        assert_eq!(parsed.entries.len(), 2, "dupes collapse");
        assert_eq!(parsed.entries[0].name, "a-first");
        assert_eq!(parsed.entries[1].name, "b-second");
        assert_eq!(parsed.entries[1].smt2, "(assert b)\n(check-sat)");

        // Invalid identities / multiline metadata are rejected.
        assert!(render_tier0_db("deadbeef", None, None, &entries).is_err());
        assert!(render_tier0_db(&identity, Some("a\nb"), None, &entries).is_err());
    }

    /// Timing probe for the popcnt width-32 canary (historically ~16 s/live
    /// solve). The persistent row is only a candidate, so this measures the
    /// mandatory live revalidation path:
    ///
    /// ```text
    /// TRUST_CG_RUN_MEASUREMENT_TESTS=1 cargo test --release \
    ///     -p trust-cg-verify tier0_popcnt_canary_timing_probe -- --nocapture
    /// ```
    #[test]
    fn tier0_popcnt_canary_timing_probe() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_MEASUREMENT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "measurement campaign not requested; \
                 set TRUST_CG_RUN_MEASUREMENT_TESTS=1 to run"
            );
            return;
        }

        use crate::pass_validators::{PassValidator, PopcntSwarExpansionValidator};
        let validator = PopcntSwarExpansionValidator::x86_generic("x86-popcnt-expand", 32);
        let started = std::time::Instant::now();
        let validation = validator.validate();
        println!(
            "popcnt width-32 canary discharge took {:.3}s (result: {validation:?})",
            started.elapsed().as_secs_f64()
        );
    }

    /// The header-only identity read MUST agree with the full parse.
    ///
    /// `tier0_candidate_verified` now self-disables against the header before
    /// materializing the DB, so if these two ever disagreed a host could either
    /// skip a DB it should have used (lost reuse) or parse one it should not
    /// have. Both are caught here.
    #[test]
    fn header_only_identity_agrees_with_the_full_parse() {
        let quick = super::embedded_tier0_identity();
        match parse_tier0_text(EMBEDDED_TIER0_VDB) {
            Ok(Some(parsed)) => assert_eq!(
                quick,
                Some(parsed.solver_identity.as_str()),
                "header-only identity must equal the fully-parsed one"
            ),
            // Empty or malformed: the tier is disabled either way, and the
            // header read must not claim an identity the parse rejects.
            Ok(None) | Err(_) => assert_eq!(
                quick, None,
                "no usable DB => the header read must not report an identity"
            ),
        }
    }

    #[test]
    fn embedded_tier0_parses_or_disables_cleanly() {
        // The COMMITTED file must never be in the "malformed" state: either
        // it is empty (tier disabled quietly) or it parses strictly.
        match parse_tier0_text(EMBEDDED_TIER0_VDB) {
            Ok(_) => {}
            Err(e) => panic!("committed tier0.vdb is malformed: {e}"),
        }
    }

    /// PROOF-4 B1: a REAL registry obligation resolves via a tier-0 verdict
    /// LOOKUP (a byte-for-byte content-key match), not by a statistical sweep.
    /// Runs WITHOUT a live solver by building a synthetic DB from the
    /// obligation's own regen SMT2 under a fake solver identity, then asserting
    /// the per-compile lookup derivation reproduces the same key (a HIT) and a
    /// different obligation MISSES. This is the drift guard: if the lookup SMT2
    /// ever diverges from what regen records, the HIT flips to a miss and this
    /// test fails.
    #[test]
    fn registry_obligation_resolves_via_tier0_lookup_not_sampling() {
        let dir = temp_dir("registry_lookup");
        let (solver, identity) = fake_solver(&dir, b"registry-lookup fake ay bytes");

        // Two distinct eligible registry obligations from the REAL database.
        let eligible = super::enumerate_regen_eligible().expect("enumerate eligible");
        assert!(
            eligible.len() >= 2,
            "expected multiple eligible registry obligations, got {}",
            eligible.len()
        );
        let ob_a = &eligible[0].obligation;
        let ob_b = eligible
            .iter()
            .map(|r| &r.obligation)
            .find(|o| super::db_obligation_smt2(o) != super::db_obligation_smt2(ob_a))
            .expect("two obligations with distinct SMT2");

        // Commit ONLY ob_a's regen SMT2 into a synthetic tier-0 DB.
        let db = db_with(
            &identity,
            &[Tier0Entry {
                name: ob_a.name.clone(),
                smt2: super::db_obligation_smt2(ob_a),
            }],
        );

        // ob_a: the lookup re-derives the identical content key -> HIT.
        assert!(
            super::tier0_candidate_obligation_in(&db, &solver, ob_a),
            "committed registry obligation must resolve via tier-0 lookup"
        );
        // ob_b: never committed -> MISS (falls back to the statistical sweep).
        assert!(
            !super::tier0_candidate_obligation_in(&db, &solver, ob_b),
            "an un-committed registry obligation must miss (sound fallback)"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Compile-time probe (PROOF-4 B1): discharge a batch of REAL registry
    /// obligations through [`crate::lowering_proof::discharge_registry_obligation`]
    /// and report how many resolved via live-revalidated tier-0 candidates
    /// (Formal) vs a 100k statistical sweep, plus wall time:
    ///
    /// ```text
    /// # tier-0 candidates ON: matching rows are revalidated live
    /// TRUST_CG_RUN_MEASUREMENT_TESTS=1 cargo test -p trust-cg-verify \
    ///     --lib tier0_registry_discharge_timing_probe -- --nocapture
    /// # tier-0 OFF (sweeps): expect all Statistical, seconds
    /// TCG_NO_VERDICT_DB=1 TRUST_CG_RUN_MEASUREMENT_TESTS=1 \
    ///     cargo test -p trust-cg-verify --lib \
    ///     tier0_registry_discharge_timing_probe -- --nocapture
    /// ```
    #[test]
    fn tier0_registry_discharge_timing_probe() {
        if !matches!(
            std::env::var("TRUST_CG_RUN_MEASUREMENT_TESTS").as_deref(),
            Ok("1")
        ) {
            eprintln!(
                "measurement campaign not requested; \
                 set TRUST_CG_RUN_MEASUREMENT_TESTS=1 to run"
            );
            return;
        }

        let eligible = super::enumerate_regen_eligible().expect("enumerate eligible");
        let config = VerificationConfig::default();
        // A fixed batch (distinct obligations so the per-obligation memo does
        // not mask the sweep cost in the OFF lane).
        let batch: Vec<ProofObligation> = eligible
            .iter()
            .take(40)
            .map(|r| r.obligation.clone())
            .collect();
        let started = std::time::Instant::now();
        let (mut formal, mut statistical) = (0usize, 0usize);
        for ob in &batch {
            let (result, strength) =
                crate::lowering_proof::discharge_registry_obligation(ob, &config);
            assert!(matches!(result, crate::verify::VerificationResult::Valid));
            match strength {
                VerificationStrength::Formal => formal += 1,
                VerificationStrength::Statistical { .. } => statistical += 1,
                VerificationStrength::Exhaustive => {}
            }
        }
        println!(
            "tier0_registry_discharge_timing_probe: discharged {} registry obligation(s) in \
             {:.3}s — {} via tier-0 candidate + live revalidation (Formal), \
             {} via statistical SWEEP; \
             TCG_NO_VERDICT_DB={}",
            batch.len(),
            started.elapsed().as_secs_f64(),
            formal,
            statistical,
            std::env::var_os("TCG_NO_VERDICT_DB").is_some(),
        );
    }

    #[test]
    fn exemptions_render_parse_roundtrip_is_deterministic() {
        let identity = "cd".repeat(32);
        let exemptions = vec![
            Tier0Exemption {
                reason: "Timeout".to_string(),
                category: "NEON Lowering".to_string(),
                name: "z-last obligation".to_string(),
            },
            Tier0Exemption {
                reason: "Timeout".to_string(),
                category: "NEON Lowering".to_string(),
                name: "a-first obligation".to_string(),
            },
            // Duplicate collapses.
            Tier0Exemption {
                reason: "Timeout".to_string(),
                category: "NEON Lowering".to_string(),
                name: "a-first obligation".to_string(),
            },
        ];
        let text1 = render_exemptions(&identity, Some("ay 0.11"), None, &exemptions);
        let mut rev = exemptions.clone();
        rev.reverse();
        let text2 = render_exemptions(&identity, Some("ay 0.11"), None, &rev);
        assert_eq!(text1, text2, "exemption row order must not affect output");

        let parsed = parse_exemptions(&text1).unwrap();
        assert_eq!(parsed.len(), 2, "dupes collapse");
        assert_eq!(parsed[0].name, "a-first obligation");
        assert_eq!(parsed[1].name, "z-last obligation");

        // Empty parses to no exemptions; a bad schema line errors.
        assert_eq!(parse_exemptions("").unwrap(), Vec::new());
        assert!(parse_exemptions("bogus-schema\ncount: 0\n").is_err());
    }

    /// The COMMITTED exemption list must (a) parse, (b) name only obligations
    /// that are GENUINELY absent from the committed tier-0 DB (an exempted
    /// obligation is precisely one with no committed verdict), and (c) justify
    /// every entry against a known solver-incompleteness class. Non-empty iff
    /// there are genuinely solver-incomplete obligations.
    #[test]
    fn committed_exemptions_are_consistent_and_justified() {
        let path = concat!(env!("CARGO_MANIFEST_DIR"), "/verdict_db/exemptions.txt");
        let text = std::fs::read_to_string(path).unwrap_or_default();
        let exemptions = parse_exemptions(&text).expect("committed exemptions.txt must parse");

        // Committed tier-0 row NAMES (informational field, but sufficient to
        // assert an exemption is not ALSO committed as verified).
        let committed_names: std::collections::HashSet<String> =
            match parse_tier0_text(EMBEDDED_TIER0_VDB) {
                Ok(Some(parsed)) => parsed.entries.iter().map(|e| e.name.clone()).collect(),
                _ => std::collections::HashSet::new(),
            };

        for e in &exemptions {
            // The exemption `name` may carry a "(reason)" suffix for Unknown/
            // Error rows; strip it for the membership check.
            let base = e.name.split(" (").next().unwrap_or(&e.name).to_string();
            assert!(
                !committed_names.contains(&base),
                "exempted obligation {base:?} is ALSO committed as a verified row — \
                 an obligation cannot be both proven and exempt"
            );
            assert!(
                super::EXPECTED_EXEMPTION_MARKERS
                    .iter()
                    .any(|m| e.name.contains(m) || e.category.contains(m)),
                "exempted obligation {:?} (category {:?}) matches no justified \
                 solver-incompleteness marker in EXPECTED_EXEMPTION_MARKERS — every \
                 exemption must be justified, not silently accepted",
                e.name,
                e.category
            );
        }
    }

    // -----------------------------------------------------------------------
    // PROOF-5 / TV-9 (B2): parametric reconstruction credit flip
    // -----------------------------------------------------------------------

    use crate::verify::{VerificationResult, VerificationStrength};
    use trust_cg_ir::RegClass as X86RegClass;
    use trust_cg_ir::X86Opcode;
    use trust_cg_ir::regs::VReg as X86VReg;
    use trust_cg_lower::x86_64_isel::{X86ISelInst, X86ISelOperand};

    fn g32(id: u32) -> X86ISelOperand {
        X86ISelOperand::VReg(X86VReg::new(id, X86RegClass::Gpr32))
    }

    /// PART A drift guard: the PARAMETRIC (free-immediate) canonical obligation is
    /// INDEPENDENT of the baked immediate and byte-identical (in the
    /// key-determining SMT2) to its RR sibling — so ONE committed tier-0 row is
    /// the parametric proof for the whole width family (RR + every RI immediate).
    /// The RAW per-instance obligations differ per immediate, which is exactly
    /// why the parametric canonicalization is needed.
    #[test]
    fn reconstructed_ri_canonicalizes_to_rr_family_row() {
        use crate::x86_64_function_verifier::{
            canonical_reconstruct_obligation, reconstruct_alu_obligation,
        };
        let addri = X86ISelInst::new(
            X86Opcode::AddRI,
            vec![g32(0), g32(1), X86ISelOperand::Imm(7)],
        );
        let addri2 = X86ISelInst::new(
            X86Opcode::AddRI,
            vec![g32(0), g32(1), X86ISelOperand::Imm(0x5abc)],
        );
        let addrr = X86ISelInst::new(X86Opcode::AddRR, vec![g32(0), g32(1), g32(2)]);
        let can_ri = canonical_reconstruct_obligation(&addri).unwrap();
        let can_ri2 = canonical_reconstruct_obligation(&addri2).unwrap();
        let can_rr = canonical_reconstruct_obligation(&addrr).unwrap();
        assert_eq!(
            db_obligation_smt2(&can_ri),
            db_obligation_smt2(&can_ri2),
            "the parametric canonical must not depend on the immediate value"
        );
        assert_eq!(
            db_obligation_smt2(&can_ri),
            db_obligation_smt2(&can_rr),
            "the RI canonical must share its RR sibling's single tier-0 row"
        );
        let raw_ri = reconstruct_alu_obligation(&addri).unwrap();
        let raw_ri2 = reconstruct_alu_obligation(&addri2).unwrap();
        assert_ne!(
            db_obligation_smt2(&raw_ri),
            db_obligation_smt2(&raw_ri2),
            "raw per-instance reconstruction obligations differ by baked immediate"
        );
    }

    /// PART A drift guard + refutation (ImulRRI — the mul-heavy compile-parity
    /// lever): the 3-operand `IMUL r,r,imm` per-immediate obligations COLLAPSE onto
    /// the ONE committed `Imul_{32,64} -> ImulRR` tier-0 row (the canonical is
    /// immediate-free and byte-identical to its RR sibling), while the RAW instances
    /// still differ per baked immediate. The CRITICAL check ties the two multiply
    /// encoders: the machine SMT2 the ImulRRI INSTANCE bakes (`encode_imul_rri`) is
    /// byte-identical to `encode_imul_rr(size, src, bv_const(imm))` — i.e.
    /// `encode_imul_rri == encode_imul_rr∘subst`. That identity is the SOLE theorem
    /// the Formal credit rests on: the canonical proves the reg*reg multiply, and
    /// crediting the constant-operand instance is sound ONLY because it reduces to
    /// the same encoder. If a future edit decouples the two multiply encoders (so
    /// the credit would vouch for an unchecked encoder) THIS test fails — instead of
    /// the lookup silently HITting the stale ImulRR row and over-crediting Formal.
    #[test]
    fn reconstructed_imul_rri_canonicalizes_to_rr_and_encoders_agree() {
        use crate::smt::SmtExpr;
        use crate::x86_64_function_verifier::{
            canonical_reconstruct_obligation, reconstruct_alu_obligation,
        };
        use crate::x86_64_semantics::{
            X86OperandSize, encode_imul_rr, encode_imul_rri, x86_operand_size_bits,
        };

        // (1) The per-immediate canonicals collapse onto the ONE committed ImulRR
        // row (byte-identical key => tier-0 HIT, no new row, no regen).
        let a = X86ISelInst::new(
            X86Opcode::ImulRRI,
            vec![g32(0), g32(1), X86ISelOperand::Imm(1000003)],
        );
        let b = X86ISelInst::new(
            X86Opcode::ImulRRI,
            vec![g32(0), g32(1), X86ISelOperand::Imm(0x5abc)],
        );
        let rr = X86ISelInst::new(X86Opcode::ImulRR, vec![g32(0), g32(1), g32(2)]);
        let can_a = db_obligation_smt2(&canonical_reconstruct_obligation(&a).unwrap());
        let can_b = db_obligation_smt2(&canonical_reconstruct_obligation(&b).unwrap());
        let can_rr = db_obligation_smt2(&canonical_reconstruct_obligation(&rr).unwrap());
        assert_eq!(
            can_a, can_rr,
            "the ImulRRI canonical must share the ImulRR tier-0 row (no new row, no regen)"
        );
        assert_eq!(
            can_a, can_b,
            "the ImulRRI canonical must not depend on the baked immediate"
        );

        // (2) The RAW per-instance obligations DO differ by baked immediate (pre-
        // canonicalization) — proving the collapse is doing real work (each distinct
        // immediate would otherwise be its own tier-0 miss + statistical sweep).
        let raw_a = reconstruct_alu_obligation(&a).unwrap();
        let raw_b = reconstruct_alu_obligation(&b).unwrap();
        assert_ne!(
            db_obligation_smt2(&raw_a),
            db_obligation_smt2(&raw_b),
            "raw ImulRRI instance obligations must differ by baked immediate"
        );

        // (3) CRITICAL drift check: the ImulRRI INSTANCE's machine encoder is
        // byte-identical to encode_imul_rr with the immediate materialized as a
        // same-width bv const — i.e. `encode_imul_rri == encode_imul_rr∘subst`. This
        // is the sole theorem the Formal credit depends on; a future decoupling of
        // the two multiply encoders fails HERE, not by silent over-credit. Cover
        // both widths and the sign-extend / all-ones / INT_MIN edges.
        for (size, imm) in [
            (X86OperandSize::S32, 1000003i64),
            (X86OperandSize::S32, 0x5abc_i64),
            (X86OperandSize::S64, -1i64),
            (X86OperandSize::S64, i32::MIN as i64),
        ] {
            let width = x86_operand_size_bits(size);
            let src = SmtExpr::var("recon_src", width);
            let rri_machine = encode_imul_rri(size, src.clone(), imm);
            let rr_subst = encode_imul_rr(size, src.clone(), SmtExpr::bv_const(imm as u64, width));
            assert_eq!(
                rri_machine.to_smt2_expr(),
                rr_subst.to_smt2_expr(),
                "encode_imul_rri must be byte-identical to encode_imul_rr∘subst \
                 (imm={imm}, width={width}); a decoupled multiply encoder would make \
                 the ImulRRI Formal credit unsound"
            );
        }

        // (3b) And the INSTANCE obligation actually bakes that same machine encoder,
        // tying reconstruct_x86_imul_imm's machine side to the encoder under test:
        // raw ImulRRI(1000003) machine side == encode_imul_rr∘subst(1000003).
        let w32 = x86_operand_size_bits(X86OperandSize::S32);
        let src32 = SmtExpr::var("recon_src", w32);
        let expected_machine = encode_imul_rr(
            X86OperandSize::S32,
            src32.clone(),
            SmtExpr::bv_const(1000003u64, w32),
        );
        assert_eq!(
            raw_a.aarch64_expr.to_smt2_expr(),
            expected_machine.to_smt2_expr(),
            "the ImulRRI instance obligation's machine side must be encode_imul_rr∘subst"
        );
    }

    /// PART A refutation: the parametric shift rule's `count < width` precondition
    /// is LOAD-BEARING (#57) — the free-immediate rule discharges `Valid` WITH it
    /// and REFUTES without it (the masked machine side diverges from the clamp-to-0
    /// source at `count == width`), proving the parametric proof has genuine
    /// content (a wrong shift-mask wiring is caught).
    #[test]
    fn parametric_shift_rule_precondition_is_load_bearing() {
        use crate::x86_64_function_verifier::canonical_reconstruct_obligation;
        let shlri = X86ISelInst::new(
            X86Opcode::ShlRI,
            vec![g32(0), g32(1), X86ISelOperand::Imm(3)],
        );
        let mut ob = canonical_reconstruct_obligation(&shlri).unwrap();
        assert_eq!(
            ob.inputs.len(),
            2,
            "the freed shift count must be a declared free input (forall-imm)"
        );
        assert!(
            !ob.preconditions.is_empty(),
            "the parametric shift rule must carry the count<width precondition"
        );
        assert!(matches!(
            crate::lowering_proof::verify_by_evaluation(&ob),
            VerificationResult::Valid
        ));
        ob.preconditions.clear();
        assert!(
            matches!(
                crate::lowering_proof::verify_by_evaluation(&ob),
                VerificationResult::Invalid { .. }
            ),
            "stripping count<width must REFUTE the parametric shift rule"
        );
    }

    /// PART A drift guard (synthetic DB, no live solver): a committed canonical
    /// reconstruction obligation resolves via a tier-0 LOOKUP (byte-for-byte
    /// content-key match), and a distinct family MISSES.
    #[test]
    fn reconstructed_canonical_resolves_via_tier0_lookup_not_sampling() {
        let dir = temp_dir("recon_tier0");
        let (solver, identity) = fake_solver(&dir, b"recon-tier0 fake ay bytes");
        let obs =
            super::enumerate_reconstruct_regen_obligations().expect("enumerate reconstructed");
        assert!(
            obs.len() >= 20,
            "expected the integer reconstruction surface, got {}",
            obs.len()
        );
        let ob0 = &obs[0];
        let db = db_with(
            &identity,
            &[Tier0Entry {
                name: ob0.name.clone(),
                smt2: db_obligation_smt2(ob0),
            }],
        );
        assert!(
            tier0_candidate_obligation_in(&db, &solver, ob0),
            "a committed canonical reconstruction obligation must resolve via tier-0 lookup"
        );
        let ob1 = obs
            .iter()
            .find(|o| db_obligation_smt2(o) != db_obligation_smt2(ob0))
            .expect("a distinct reconstruction obligation");
        assert!(
            !tier0_candidate_obligation_in(&db, &solver, ob1),
            "an un-committed reconstruction obligation must MISS (sound fallback)"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// Regen determinism: the reconstruction enumeration is byte-stable (so a
    /// re-regen is diff-clean). Cross-arch families whose bitvector semantics
    /// coincide (e.g. `Iadd` → `bvadd` on both x86 and aarch64) legitimately
    /// SHARE one tier-0 key, so the distinct-key count is `<=` the obligation
    /// count — a proof reused across arches, not a bug.
    #[test]
    fn reconstructed_enumeration_is_deterministic() {
        let a = super::enumerate_reconstruct_regen_obligations().unwrap();
        let b = super::enumerate_reconstruct_regen_obligations().unwrap();
        assert_eq!(a, b, "reconstruction enumeration must be deterministic");
        let mut keys: Vec<String> = a.iter().map(db_obligation_smt2).collect();
        keys.sort();
        keys.dedup();
        assert!(
            keys.len() >= 20 && keys.len() <= a.len(),
            "expected a broad reconstruction surface: {} distinct keys from {} obligations",
            keys.len(),
            a.len()
        );
    }

    /// PART A landed: the COMMITTED tier-0 DB holds the parametric candidate for
    /// EVERY enumerated reconstruction obligation. Only meaningful with the
    /// manifest solver present (tier-0 self-disables under a foreign/absent
    /// solver), so it is a no-op on such hosts rather than a false failure.
    #[test]
    fn committed_tier0_covers_enumerated_reconstruction_families() {
        let Some((path, identity)) = tier0_solver() else {
            return;
        };
        let Some(db) = embedded_tier0() else {
            return;
        };
        if identity != &db.solver_identity {
            return;
        }
        let obs = super::enumerate_reconstruct_regen_obligations().unwrap();
        for ob in &obs {
            assert!(
                tier0_candidate_obligation_in(db, path, ob),
                "committed tier-0 must hold the parametric verdict for {:?} — run regen_verdict_db",
                ob.name
            );
        }
    }

    /// PART B / M3 criterion (d): with the manifest solver present, ZERO
    /// tier-0-covered reconstructed obligations are credited via
    /// `method=Statistical` — every one is `Formal` (SolverProven) via the
    /// committed PARAMETRIC candidate after a live solver result. No-op on a
    /// solver-absent / foreign-solver host (tier-0 self-disables there; the
    /// `Statistical` fallback is legitimate — see the next test).
    #[test]
    fn reconstructed_discharge_zero_statistical_when_solver_present() {
        let Some((_, identity)) = tier0_solver() else {
            return;
        };
        let Some(db) = embedded_tier0() else {
            return;
        };
        if identity != &db.solver_identity {
            return;
        }
        let cfg = VerificationConfig::default();
        let obs = super::enumerate_reconstruct_regen_obligations().unwrap();
        let mut statistical = 0usize;
        for ob in &obs {
            // instance == canonical for the enumerated (already-free) forms.
            let (res, strength) =
                crate::lowering_proof::discharge_reconstructed_obligation(ob, ob, &cfg);
            assert!(
                matches!(res, VerificationResult::Valid),
                "{:?} must discharge Valid",
                ob.name
            );
            if matches!(strength, VerificationStrength::Statistical { .. }) {
                statistical += 1;
            }
        }
        assert_eq!(
            statistical,
            0,
            "M3: with a solver present, 0 of {} tier-0-covered reconstructed obligations \
             may be credited Statistical (all must be Formal/SolverProven)",
            obs.len()
        );
    }

    /// PART B: a reconstructed family NOT in the offline tier-0 DB (a DIVISION
    /// obligation — the solver-hard INT_MIN/-1 exemption class) keeps a
    /// clearly-labeled `Statistical` fallback in the DEFAULT lane (the opt-in
    /// live-solver route is off), and the build is NEVER failed closed. This is
    /// exactly the solver-absent posture: no tier-0 hit, no live solve, honest
    /// Statistical label, still `Valid`.
    #[test]
    fn reconstructed_discharge_falls_back_to_statistical_for_uncovered_family() {
        let idiv = X86ISelInst::new(X86Opcode::Idiv, vec![g32(0)]);
        let Some(ob) = crate::x86_64_function_verifier::reconstruct_alu_obligation(&idiv) else {
            return;
        };
        let cfg = VerificationConfig::default();
        // >8-bit (Statistical base tier) and absent from tier-0.
        assert!(matches!(
            VerificationStrength::for_obligation_with_config(&ob, &cfg),
            VerificationStrength::Statistical { .. }
        ));
        // Default lane: the opt-in live route is OFF, so this must not spawn a
        // solver and must not fail closed.
        assert!(!reconstructed_live_solver_enabled());
        let (res, strength) =
            crate::lowering_proof::discharge_reconstructed_obligation(&ob, &ob, &cfg);
        assert!(
            matches!(res, VerificationResult::Valid),
            "an uncovered family must still compile (no fail-closed), got {res:?}"
        );
        assert!(
            matches!(strength, VerificationStrength::Statistical { .. }),
            "an uncovered family must keep the honest Statistical label, got {strength:?}"
        );
    }
}
