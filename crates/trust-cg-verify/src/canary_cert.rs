// trust-cg-verify/canary_cert.rs - portable, independently replayed canary certs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Portable certificate skip for fixed, program-independent proof obligations.
//!
//! A hit is selected by the exact SMT-LIB query bytes, not by a locally
//! installed AY binary.  AY is the offline producer recorded in each artifact;
//! it is deliberately not an online checker or a prerequisite for consuming a
//! committed certificate.  Authority comes from all of the following:
//!
//! * a source-embedded manifest binds every expected filename to the SHA-256
//!   of its complete certificate bytes and to a domain-separated hash of its
//!   exact SMT-LIB query;
//! * schema-v3 certificates carry those exact query bytes and bind them to the
//!   producer AY identity and exported CNF;
//! * the vendored, independent `drat-trim` executable replays the DRAT proof;
//! * the executable is hashed before and after replay, and the successful
//!   process memo is keyed by that checker identity as well as certificate and
//!   query identity.
//!
//! Any missing/malformed/mutated artifact selected for the exact query, query
//! miss, checker failure, or identity change returns `false`; the caller then
//! uses the ordinary live proof path, which remains fail closed. Offline
//! publication/audit still validates the complete embedded set.
//!
//! Here "portable" means independent of an installed AY producer. It does not
//! authorize arbitrary `drat-trim` builds: the current checker executable must
//! match a reviewed host-plus-byte identity, so a different platform or
//! toolchain build misses until separately qualified by complete-set replay.
//! One explicitly named legacy unqualified byte identity retains its previous
//! authorization; its original host was not recorded and is not invented here.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{Mutex, OnceLock};

use crate::lrat_cert::{
    LratCert, checker_binary_sha256, parse_cert, recheck_cert_with_expected_checker, sha256_hex,
};
use trust_cg_process_env::SanitizedChildEnv;

#[path = "canary_cert_bound_memory.rs"]
pub(crate) mod bound_memory;
pub use bound_memory::{
    BoundMemoryCertRegenReport, BoundMemoryCertRow, regen_atomic_memory_certs,
    regen_bound_memory_certs, regen_neon_memory_certs,
};

const MANIFEST_SCHEMA: &str = "tcg-canary-cert-manifest-v2";
// The sole grandfathered v1 authorization. New authorizations must be host
// qualified. Do not turn this migration exception into an unqualified list.
const LEGACY_UNQUALIFIED_CHECKER_SHA256: &str =
    "0f634db2aed73a915aa0c0f76258d84801385b15416ee608219df01af6962d20";
const PORTABLE_QUERY_DOMAIN: &[u8] = b"tcg-portable-canary-query-v1\0";
const EXPECTED_CERT_COUNT: usize = 33;

const EMBEDDED_MANIFEST: &str = include_str!("../verdict_db/canary_certs/manifest.v1");

const EMBEDDED_CERTS: &[(&str, &str)] = &[
    (
        "popcnt_swar_32.lratcert",
        include_str!("../verdict_db/canary_certs/popcnt_swar_32.lratcert"),
    ),
    (
        "recon_shl_32.lratcert",
        include_str!("../verdict_db/canary_certs/recon_shl_32.lratcert"),
    ),
    (
        "recon_shl_64.lratcert",
        include_str!("../verdict_db/canary_certs/recon_shl_64.lratcert"),
    ),
    (
        "recon_shr_32.lratcert",
        include_str!("../verdict_db/canary_certs/recon_shr_32.lratcert"),
    ),
    (
        "recon_shr_64.lratcert",
        include_str!("../verdict_db/canary_certs/recon_shr_64.lratcert"),
    ),
    (
        "recon_sar_32.lratcert",
        include_str!("../verdict_db/canary_certs/recon_sar_32.lratcert"),
    ),
    (
        "recon_sar_64.lratcert",
        include_str!("../verdict_db/canary_certs/recon_sar_64.lratcert"),
    ),
    (
        "aarch64_udiv_32.lratcert",
        include_str!("../verdict_db/canary_certs/aarch64_udiv_32.lratcert"),
    ),
    (
        "aarch64_udiv_64.lratcert",
        include_str!("../verdict_db/canary_certs/aarch64_udiv_64.lratcert"),
    ),
    (
        "icmp_eq_32.lratcert",
        include_str!("../verdict_db/canary_certs/icmp_eq_32.lratcert"),
    ),
    (
        "guard_bounds_32.lratcert",
        include_str!("../verdict_db/canary_certs/guard_bounds_32.lratcert"),
    ),
    (
        "guard_bounds_64.lratcert",
        include_str!("../verdict_db/canary_certs/guard_bounds_64.lratcert"),
    ),
    (
        "guard_shift_range_32.lratcert",
        include_str!("../verdict_db/canary_certs/guard_shift_range_32.lratcert"),
    ),
    (
        "guard_shift_range_64.lratcert",
        include_str!("../verdict_db/canary_certs/guard_shift_range_64.lratcert"),
    ),
    (
        "guard_null_if_zero_32.lratcert",
        include_str!("../verdict_db/canary_certs/guard_null_if_zero_32.lratcert"),
    ),
    (
        "guard_null_if_zero_64.lratcert",
        include_str!("../verdict_db/canary_certs/guard_null_if_zero_64.lratcert"),
    ),
    (
        "guard_div_zero_32.lratcert",
        include_str!("../verdict_db/canary_certs/guard_div_zero_32.lratcert"),
    ),
    (
        "guard_div_zero_64.lratcert",
        include_str!("../verdict_db/canary_certs/guard_div_zero_64.lratcert"),
    ),
    (
        "frame_sp_alignment_16.lratcert",
        include_str!("../verdict_db/canary_certs/frame_sp_alignment_16.lratcert"),
    ),
    (
        "macho_pageoff12_add.lratcert",
        include_str!("../verdict_db/canary_certs/macho_pageoff12_add.lratcert"),
    ),
    (
        "macho_got_load_pageoff12.lratcert",
        include_str!("../verdict_db/canary_certs/macho_got_load_pageoff12.lratcert"),
    ),
    (
        "macho_branch26.lratcert",
        include_str!("../verdict_db/canary_certs/macho_branch26.lratcert"),
    ),
    (
        "macho_page21.lratcert",
        include_str!("../verdict_db/canary_certs/macho_page21.lratcert"),
    ),
    (
        "movz_x_0.lratcert",
        include_str!("../verdict_db/canary_certs/movz_x_0.lratcert"),
    ),
    (
        "frame_callee_save_no_overlap.lratcert",
        include_str!("../verdict_db/canary_certs/frame_callee_save_no_overlap.lratcert"),
    ),
    (
        "frame_callee_save_restore.lratcert",
        include_str!("../verdict_db/canary_certs/frame_callee_save_restore.lratcert"),
    ),
    (
        "ldp_i32_offset0.lratcert",
        include_str!("../verdict_db/canary_certs/ldp_i32_offset0.lratcert"),
    ),
    (
        "roundtrip_i8.lratcert",
        include_str!("../verdict_db/canary_certs/roundtrip_i8.lratcert"),
    ),
    (
        "movk_x_16.lratcert",
        include_str!("../verdict_db/canary_certs/movk_x_16.lratcert"),
    ),
    (
        "movk_x_32.lratcert",
        include_str!("../verdict_db/canary_certs/movk_x_32.lratcert"),
    ),
    (
        "movk_x_48.lratcert",
        include_str!("../verdict_db/canary_certs/movk_x_48.lratcert"),
    ),
    (
        "checked_sadd_64.lratcert",
        include_str!("../verdict_db/canary_certs/checked_sadd_64.lratcert"),
    ),
    (
        "checked_umul_64.lratcert",
        include_str!("../verdict_db/canary_certs/checked_umul_64.lratcert"),
    ),
];

#[derive(Debug, Clone, PartialEq, Eq)]
struct ManifestEntry {
    file: String,
    cert_sha256: String,
    query_sha256: String,
    producer_ay_sha256: String,
}

#[derive(Debug)]
struct CertManifest {
    checkers: CheckerAuthorizations,
    entries: Vec<ManifestEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct HostChecker {
    target: String,
    sha256: String,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct CheckerAuthorizations {
    legacy_unqualified: bool,
    hosts: Vec<HostChecker>,
}

impl CheckerAuthorizations {
    fn authorizes(&self, target: &str, sha256: &str) -> bool {
        (self.legacy_unqualified && sha256 == LEGACY_UNQUALIFIED_CHECKER_SHA256)
            || self
                .hosts
                .iter()
                .any(|entry| entry.target == target && entry.sha256 == sha256)
    }

    /// The identity manifest.v1 authorizes for `target`, if it names one — what
    /// a drift message must show beside the checker this process actually built.
    fn authorized_for(&self, target: &str) -> Option<&str> {
        self.hosts
            .iter()
            .find(|entry| entry.target == target)
            .map(|entry| entry.sha256.as_str())
    }
}

#[derive(Debug)]
struct PortableCert {
    cert: LratCert,
}

#[derive(Debug, Clone)]
struct PortableCertIndexEntry<'a> {
    file: String,
    cert_file_sha256: String,
    query_sha256: String,
    producer_ay_sha256: String,
    text: &'a str,
}

#[derive(Debug)]
struct PortableCertSet<'a> {
    /// Every manifest entry, including the separately named semantic aliases.
    entries: Vec<PortableCertIndexEntry<'a>>,
    /// One representative per exact query. Some separately named guard lanes
    /// are intentional semantic aliases and therefore share a query key.
    by_query: HashMap<String, PortableCertIndexEntry<'a>>,
    checkers: CheckerAuthorizations,
    manifest_sha256: String,
}

fn is_lower_hex_256(value: &str) -> bool {
    value.len() == 64
        && value
            .bytes()
            .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
}

/// A solver-independent identity for the exact query bytes being certified.
pub(crate) fn portable_query_key(smt2: &str) -> String {
    use sha2::{Digest, Sha256};
    let mut hasher = Sha256::new();
    hasher.update(PORTABLE_QUERY_DOMAIN);
    hasher.update(smt2.as_bytes());
    format!("{:x}", hasher.finalize())
}

fn parse_manifest(text: &str) -> Result<CertManifest, String> {
    if !text.ends_with('\n') {
        return Err("manifest must end with a newline".to_string());
    }
    let mut lines = text.lines();
    if lines.next() != Some(MANIFEST_SCHEMA) {
        return Err(format!("manifest must start with {MANIFEST_SCHEMA:?}"));
    }
    let field = |line: Option<&str>, prefix: &str| -> Result<String, String> {
        line.and_then(|line| line.strip_prefix(prefix))
            .map(str::to_string)
            .ok_or_else(|| format!("manifest missing {prefix:?} field"))
    };
    let legacy_count = field(lines.next(), "legacy-checker-count: ")?;
    let legacy_unqualified = match legacy_count.as_str() {
        "0" => false,
        "1" => {
            if field(lines.next(), "legacy-checker-sha256: ")? != LEGACY_UNQUALIFIED_CHECKER_SHA256
            {
                return Err("only the exact grandfathered v1 checker may be unqualified".into());
            }
            true
        }
        _ => return Err("legacy-checker-count must be zero or one".into()),
    };
    let host_count: usize = field(lines.next(), "host-checker-count: ")?
        .parse()
        .map_err(|_| "invalid host-checker-count")?;
    if host_count > 64 || (host_count == 0 && !legacy_unqualified) {
        return Err("manifest requires one to 64 reviewed checker authorizations".into());
    }
    let mut hosts = Vec::new();
    let mut seen = HashSet::new();
    for _ in 0..host_count {
        let row = field(lines.next(), "host-checker: ")?;
        let fields: Vec<_> = row.split_ascii_whitespace().collect();
        if fields.len() != 2 || !valid_target_triple(fields[0]) || !is_lower_hex_256(fields[1]) {
            return Err(format!("malformed host-qualified checker {row:?}"));
        }
        if !seen.insert((fields[0].to_owned(), fields[1].to_owned())) {
            return Err("duplicate host-qualified checker authorization".into());
        }
        hosts.push(HostChecker {
            target: fields[0].into(),
            sha256: fields[1].into(),
        });
    }
    let declared: usize = field(lines.next(), "cert-count: ")?
        .parse()
        .map_err(|_| "manifest cert-count is not an integer".to_string())?;
    let mut entries = Vec::new();
    for line in lines {
        let fields: Vec<&str> = line.split_ascii_whitespace().collect();
        if fields.len() != 5 || fields[0] != "cert:" {
            return Err(format!("malformed manifest entry {line:?}"));
        }
        if fields[1].contains('/') || fields[1].contains('\\') {
            return Err(format!(
                "manifest cert filename is not a basename: {:?}",
                fields[1]
            ));
        }
        if !is_lower_hex_256(fields[2])
            || !is_lower_hex_256(fields[3])
            || !is_lower_hex_256(fields[4])
        {
            return Err(format!("manifest entry has malformed digest: {line:?}"));
        }
        entries.push(ManifestEntry {
            file: fields[1].to_string(),
            cert_sha256: fields[2].to_string(),
            query_sha256: fields[3].to_string(),
            producer_ay_sha256: fields[4].to_string(),
        });
    }
    if entries.len() != declared {
        return Err(format!(
            "manifest declares {declared} certs but carries {} entries",
            entries.len()
        ));
    }
    Ok(CertManifest {
        checkers: CheckerAuthorizations {
            legacy_unqualified,
            hosts,
        },
        entries,
    })
}

fn valid_target_triple(target: &str) -> bool {
    // Exact nonempty identifiers only: no wildcard, path, whitespace, pattern,
    // or case-folding. A syntactically valid other host never matches this host.
    target.len() <= 128
        && target.split('-').count() >= 3
        && target.split('-').all(|part| !part.is_empty())
        && target.bytes().all(|byte| {
            byte.is_ascii_lowercase() || byte.is_ascii_digit() || byte == b'-' || byte == b'_'
        })
}

fn alias_group(file: &str) -> Option<(&'static str, &'static str)> {
    let width = if file.ends_with("_32.lratcert") {
        "32"
    } else if file.ends_with("_64.lratcert") {
        "64"
    } else {
        return None;
    };
    let semantics = if file.starts_with("guard_bounds_") || file.starts_with("guard_shift_range_") {
        "unsigned-ge"
    } else if file.starts_with("guard_null_if_zero_") || file.starts_with("guard_div_zero_") {
        "zero"
    } else {
        return None;
    };
    Some((semantics, width))
}

fn allowed_exact_semantic_alias(left: &str, right: &str) -> bool {
    left != right && alias_group(left).is_some_and(|group| Some(group) == alias_group(right))
}

/// Build the cheap, source-embedded lookup index.
///
/// This validates the complete manifest shape, count, filename set, digest
/// syntax, and duplicate-query alias policy without touching any certificate
/// body.  A consumer validates the one exact-query-selected body before it can
/// grant authority; offline publication additionally calls [`build_cert_set`]
/// to validate every body.
fn build_cert_index<'a>(
    manifest_text: &str,
    cert_texts: &[(&str, &'a str)],
    expected_count: usize,
) -> Result<PortableCertSet<'a>, String> {
    let manifest = parse_manifest(manifest_text)?;
    if manifest.entries.len() != expected_count || cert_texts.len() != expected_count {
        return Err(format!(
            "portable set must contain exactly {expected_count} certs (manifest {}, embedded {})",
            manifest.entries.len(),
            cert_texts.len()
        ));
    }
    let texts: HashMap<&str, &str> = cert_texts.iter().copied().collect();
    if texts.len() != cert_texts.len() {
        return Err("duplicate embedded certificate filename".to_string());
    }
    let manifest_files: HashSet<&str> = manifest.entries.iter().map(|e| e.file.as_str()).collect();
    if manifest_files.len() != manifest.entries.len() {
        return Err("duplicate filename in certificate manifest".to_string());
    }
    let embedded_files: HashSet<&str> = texts.keys().copied().collect();
    if manifest_files != embedded_files {
        return Err("manifest and embedded certificate filename sets differ".to_string());
    }

    let mut entries = Vec::with_capacity(manifest.entries.len());
    let mut by_query: HashMap<String, PortableCertIndexEntry<'a>> = HashMap::new();
    for entry in manifest.entries {
        let text = texts[entry.file.as_str()];
        let indexed = PortableCertIndexEntry {
            file: entry.file,
            cert_file_sha256: entry.cert_sha256,
            query_sha256: entry.query_sha256,
            producer_ay_sha256: entry.producer_ay_sha256,
            text,
        };
        if let Some(previous) = by_query.get(&indexed.query_sha256) {
            if !allowed_exact_semantic_alias(&previous.file, &indexed.file) {
                return Err(format!(
                    "{} and {} unexpectedly share an exact query",
                    previous.file, indexed.file
                ));
            }
        } else {
            // Preserve the first representative. Full-set validation below
            // still checks every separately named alias body.
            by_query.insert(indexed.query_sha256.clone(), indexed.clone());
        }
        entries.push(indexed);
    }
    Ok(PortableCertSet {
        entries,
        by_query,
        checkers: manifest.checkers,
        manifest_sha256: sha256_hex(manifest_text.as_bytes()),
    })
}

/// Validate and parse one body selected by its exact manifest query key.
fn validate_cert_index_entry(entry: &PortableCertIndexEntry<'_>) -> Result<LratCert, String> {
    let actual_file_sha = sha256_hex(entry.text.as_bytes());
    if actual_file_sha != entry.cert_file_sha256 {
        return Err(format!(
            "{} complete-file digest mismatch: manifest {}, embedded {}",
            entry.file, entry.cert_file_sha256, actual_file_sha
        ));
    }
    let cert = parse_cert(entry.text).map_err(|e| format!("{}: {e}", entry.file))?;
    if !cert.carries_obligation_binding() {
        return Err(format!(
            "{} uses legacy schema v2 and cannot authorize portable lookup",
            entry.file
        ));
    }
    if cert.solver_identity != entry.producer_ay_sha256 {
        return Err(format!(
            "{} producer AY identity differs from manifest",
            entry.file
        ));
    }
    if portable_query_key(&cert.smt2) != entry.query_sha256 {
        return Err(format!("{} exact-query digest mismatch", entry.file));
    }
    let internal_key = crate::ay_bridge::verdict_cache_key_v2(&cert.solver_identity, &cert.smt2);
    if cert.verdict_key != internal_key {
        return Err(format!("{} producer/query binding is invalid", entry.file));
    }
    Ok(cert)
}

/// Validate every embedded body. This is the publication/audit path; the
/// compile-time consumer uses [`build_cert_index`] and validates only the body
/// selected by the exact query.
fn build_cert_set<'a>(
    manifest_text: &str,
    cert_texts: &[(&str, &'a str)],
    expected_count: usize,
) -> Result<PortableCertSet<'a>, String> {
    let set = build_cert_index(manifest_text, cert_texts, expected_count)?;
    for entry in &set.entries {
        validate_cert_index_entry(entry)?;
    }
    Ok(set)
}

/// The set of `query_sha256` values the embedded manifest declares, parsed from
/// the small manifest alone — no certificate body is hashed or parsed.
///
/// `None` means the manifest did not parse; callers must then fall through to
/// the indexed path rather than declining, so the existing invalid-index
/// diagnostic is still emitted exactly once.
fn manifest_query_keys() -> Option<&'static HashSet<String>> {
    static KEYS: OnceLock<Option<HashSet<String>>> = OnceLock::new();
    KEYS.get_or_init(|| {
        parse_manifest(EMBEDDED_MANIFEST).ok().map(|manifest| {
            manifest
                .entries
                .into_iter()
                .map(|e| e.query_sha256)
                .collect()
        })
    })
    .as_ref()
}

fn embedded_cert_index() -> Option<&'static PortableCertSet<'static>> {
    static CERTS: OnceLock<Option<PortableCertSet<'static>>> = OnceLock::new();
    CERTS
        .get_or_init(|| match build_cert_index(EMBEDDED_MANIFEST, EMBEDDED_CERTS, EXPECTED_CERT_COUNT) {
            Ok(set) => Some(set),
            Err(error) => {
                eprintln!(
                    "trust-cg-verify::canary_cert: WARNING: portable certificate index is invalid; \
                     CERT-SKIP disabled and live discharge retained: {error}"
                );
                None
            }
        })
        .as_ref()
}

pub(crate) fn cert_skip_enabled() -> bool {
    crate::env_lock::var_os("TCG_CANARY_NO_CACHE").is_none()
        && crate::env_lock::var_os("TCG_NO_PROOF_CACHE").is_none()
}

/// Process memo key = exact query + complete cert bytes + captured portable
/// authority (checker path/bytes, manifest, sanitized environment and CWD).
///
/// Each key owns a compute-once cell. Distinct certificate replays may run in
/// parallel, while concurrent aliases for the same exact query wait for the
/// first independent checker result instead of spawning duplicate checkers.
fn check_memo() -> &'static Mutex<HashMap<String, std::sync::Arc<Mutex<bool>>>> {
    static MEMO: OnceLock<Mutex<HashMap<String, std::sync::Arc<Mutex<bool>>>>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

fn memoize_success(cell: &Mutex<bool>, replay: impl FnOnce() -> bool) -> bool {
    let mut verified = cell.lock().unwrap_or_else(|poison| poison.into_inner());
    if !*verified {
        // A failed or interrupted replay can be transient. Only a successful
        // independently checked result may survive the current attempt.
        *verified = replay();
    }
    *verified
}

fn checker_identity_is_authorized(
    certs: &PortableCertSet<'_>,
    target: &str,
    actual_sha256: &str,
) -> bool {
    certs.checkers.authorizes(target, actual_sha256)
}

/// Owned portable proof authority, independent of AY discovery or identity.
/// Only the captured checker and sanitized child environment perform replay;
/// later ambient overrides cannot change the launch and then borrow this ID.
#[derive(Clone, Debug)]
pub(crate) struct PortableVerificationAuthority {
    enabled: bool,
    checker: Option<PathBuf>,
    checker_sha256: Option<String>,
    authorized_checker_sha256: Option<String>,
    checker_target: String,
    manifest_sha256: String,
    child_env: SanitizedChildEnv,
}

impl PortableVerificationAuthority {
    pub(crate) fn capture(child_env: SanitizedChildEnv, enabled: bool) -> Self {
        Self::capture_in(
            child_env,
            enabled,
            trust_cg_drat_trim::drat_trim_executable_path(),
            EMBEDDED_MANIFEST,
        )
    }

    fn capture_in(
        child_env: SanitizedChildEnv,
        enabled: bool,
        checker: &Path,
        manifest: &str,
    ) -> Self {
        Self::capture_for_target(
            child_env,
            enabled,
            checker,
            manifest,
            trust_cg_drat_trim::drat_trim_target_triple(),
        )
    }

    fn capture_for_target(
        child_env: SanitizedChildEnv,
        enabled: bool,
        checker: &Path,
        manifest: &str,
        target: &str,
    ) -> Self {
        let checker = child_env.anchor_path(checker);
        let checker_sha256 = enabled
            .then(|| checker.as_deref().and_then(checker_binary_sha256))
            .flatten();
        // MISSING: no bytes at the checker's path (a deleted build directory,
        // an unreadable file). Every portable replay declines, and before this
        // was announced the miss read as the live solver's verdict (a "solver
        // timeout" for the 30 s canary, 2026-11-03).
        if enabled && checker_sha256.is_none() {
            announce_checker_missing_once(checker.as_deref(), target);
        }
        let authorized_checker_sha256 = parse_manifest(manifest).ok().and_then(|parsed| {
            let authorized = checker_sha256
                .as_ref()
                .filter(|sha| parsed.checkers.authorizes(target, sha))
                .cloned();
            // DRIFT: this process built a checker manifest.v1 does not authorize
            // for this target. Every portable replay will now decline, and before
            // this was announced that read exactly like a cache miss — a whole red
            // subsystem hidden for a week. Say so once, with the fix.
            if authorized.is_none()
                && let (Some(actual), Some(path)) = (checker_sha256.as_deref(), checker.as_deref())
            {
                announce_checker_identity_drift_once(
                    manifest,
                    path,
                    parsed
                        .checkers
                        .authorized_for(target)
                        .unwrap_or("<manifest.v1 names no checker for this target>"),
                    actual,
                );
            }
            authorized
        });
        Self {
            enabled,
            checker,
            checker_sha256,
            authorized_checker_sha256,
            checker_target: target.to_owned(),
            manifest_sha256: sha256_hex(manifest.as_bytes()),
            child_env,
        }
    }

    fn current_checker(&self) -> Option<(&Path, &str)> {
        if !self.enabled {
            return None;
        }
        let checker = self.checker.as_deref()?;
        let captured_sha = self.checker_sha256.as_deref()?;
        if self.authorized_checker_sha256.as_deref() != Some(captured_sha)
            || checker_binary_sha256(checker).as_deref() != Some(captured_sha)
        {
            return None;
        }
        Some((checker, captured_sha))
    }

    /// Why this authority can consume no committed certificate at all, or
    /// `None` when the checker is authorized or the tier is disabled. Two
    /// causes are named: the checker is missing or cannot be read at its
    /// path, so there are no bytes to hash ([`missing_checker_message`]); or
    /// its bytes are not a reviewed `(target, SHA-256)` pair in the manifest.
    fn unqualified_host_reason(&self) -> Option<String> {
        if !self.enabled || self.authorized_checker_sha256.is_some() {
            return None;
        }
        let Some(sha) = self.checker_sha256.as_deref() else {
            return Some(missing_checker_message(
                self.checker.as_deref(),
                &self.checker_target,
            ));
        };
        Some(format!(
            "a committed portable certificate exists for this exact query, but this host's \
             bundled checker identity {}/{} is not authorized by \
             verdict_db/canary_certs/manifest.v1 — qualify the host \
             (docs/portable-checker-host-qualification.md); this is a checker-identity miss, \
             not a solver-capability gap",
            self.checker_target, sha
        ))
    }

    /// Reusable identity requires a complete launch snapshot and still-matching
    /// checker bytes. Endpoint file checks are not immutable executable-image
    /// binding; arbitrary filesystem A-to-B-to-A replacement remains separate.
    pub(crate) fn reusable_identity(&self) -> Option<[u8; 32]> {
        use sha2::{Digest, Sha256};
        self.child_env.working_dir()?;
        let (checker, checker_sha) = self.current_checker()?;
        let mut digest = Sha256::new();
        digest.update(b"trust-cg/portable-verification-authority/v2\0");
        for field in [
            checker.as_os_str().as_encoded_bytes(),
            checker_sha.as_bytes(),
            self.checker_target.as_bytes(),
            self.manifest_sha256.as_bytes(),
        ] {
            digest.update((field.len() as u64).to_le_bytes());
            digest.update(field);
        }
        digest.update(self.child_env.digest());
        Some(digest.finalize().into())
    }

    /// A true result means the exact selected certificate was independently
    /// replayed under this portable authority, or reuses its own successful
    /// replay. It must never be relabeled as an AY authority receipt.
    pub(crate) fn verify(&self, smt2: &str) -> bool {
        if !self.enabled || !manifest_may_contain(smt2) {
            return false;
        }
        let Some(certs) = embedded_cert_index() else {
            return false;
        };
        self.verify_in(smt2, certs)
    }

    fn verify_in(&self, smt2: &str, certs: &PortableCertSet<'_>) -> bool {
        self.verify_selected(smt2, certs, true)
    }

    /// [`Self::verify_in`] without the successful-replay memo: the selected
    /// body is validated and replayed on every call. For controls that swap a
    /// body under an unchanged manifest entry, whose memo key (the manifest's
    /// digest of the body, not the body's own) the swapped body would
    /// otherwise share with an earlier successful replay. Production reads
    /// each body once per process, so it never swaps one.
    #[cfg(test)]
    fn verify_in_without_memo(&self, smt2: &str, certs: &PortableCertSet<'_>) -> bool {
        self.verify_selected(smt2, certs, false)
    }

    fn verify_selected(&self, smt2: &str, certs: &PortableCertSet<'_>, memoize: bool) -> bool {
        if certs.manifest_sha256 != self.manifest_sha256 {
            return false;
        }
        let Some((checker, checker_sha)) = self.current_checker() else {
            return false;
        };
        if !checker_identity_is_authorized(certs, &self.checker_target, checker_sha) {
            return false;
        }
        let query_sha = portable_query_key(smt2);
        let Some(cert) = certs.by_query.get(&query_sha) else {
            return false;
        };
        let replay = || match validate_cert_index_entry(cert) {
            Ok(parsed) => cert_skip_verified_in_environment(
                &PortableCert { cert: parsed },
                smt2,
                checker,
                checker_sha,
                &self.child_env,
            ),
            Err(error) => {
                eprintln!(
                    "trust-cg-verify::canary_cert: WARNING: selected portable certificate is invalid; \
                     CERT-SKIP declined and live discharge retained: {error}"
                );
                false
            }
        };
        let Some(identity) = self.reusable_identity().filter(|_| memoize) else {
            // A missing captured CWD may still permit diagnostic replay with
            // an absolute checker path, but cannot seed reusable authority.
            return replay();
        };
        let memo_key = format!("{query_sha}:{}:{identity:02x?}", cert.cert_file_sha256);
        let cell = {
            let mut memo = check_memo()
                .lock()
                .unwrap_or_else(|poison| poison.into_inner());
            std::sync::Arc::clone(memo.entry(memo_key).or_default())
        };
        memoize_success(&cell, replay)
    }
}

/// The maintained way to re-authorize a changed checker build: replays every
/// committed payload with the current checker bytes and re-mints the manifest
/// binding (fresh AY production only for payloads that no longer replay).
const CHECKER_REAUTHORIZATION_COMMAND: &str =
    "scripts/trust_cargo.sh run --release -p trust-cg-verify --bin regen_canary_certs";

#[cfg(test)]
fn checker_identity_drift_message(checker: &Path, authorized: &str, actual: &str) -> String {
    format!(
        "the vendored drat-trim checker {} hashes to {actual} but manifest.v1 authorizes \
         {authorized}; the checker's bytes follow the host C toolchain (compiler, SDK, and \
         the deployment target pinned in crates/trust-cg-drat-trim/build.rs). Options: \
         restore the toolchain the manifest was minted against, or review the toolchain \
         change and re-authorize the complete set with `{CHECKER_REAUTHORIZATION_COMMAND}`",
        checker.display()
    )
}

/// Why a checker with no readable bytes can replay no portable certificate:
/// `checker` names the path it was looked for at (`None`: a relative path with
/// no captured working directory to anchor it). It starts with `checker not
/// found at <path>` so a refusal that carries it names the cause first.
fn missing_checker_message(checker: Option<&Path>, target: &str) -> String {
    let at = checker.map_or_else(
        || {
            format!(
                "{} (relative, and no working directory was captured to anchor it)",
                trust_cg_drat_trim::drat_trim_executable_path().display()
            )
        },
        |path| path.display().to_string(),
    );
    format!(
        "checker not found at {at}: a committed portable certificate exists for this exact \
         query, but this host's bundled {target} DRAT checker is missing or cannot be read \
         there, so the certificate cannot be replayed. The path is fixed when \
         trust-cg-drat-trim is built (DRAT_TRIM_BUILT_EXE, inside that build's target \
         directory): rebuild, or restore the directory it names. This is a missing-checker \
         miss, not a solver timeout or a solver-capability gap"
    )
}

/// One loud line, once per process, when the vendored checker cannot be read
/// at its path: the whole portable set is disabled, as on identity drift.
fn announce_checker_missing_once(checker: Option<&Path>, target: &str) {
    static ANNOUNCED: OnceLock<()> = OnceLock::new();
    ANNOUNCED.get_or_init(|| {
        eprintln!(
            "trust-cg-verify::canary_cert: WARNING: portable certificate set is DISABLED; \
             CERT-SKIP declined for every query and live discharge retained: {}",
            missing_checker_message(checker, target)
        );
    });
}

/// Which committed portable certificate set `manifest` is: its label, its
/// committed directory, and the command that re-authorizes a checker for it.
/// The canary set and the three form-certificate sets
/// ([`bound_memory::FormCertSet`]) share one checker and one capture, so a
/// line that names no set misattributes: on a host whose checker only the
/// canary set authorizes (Darwin x86-64, 2026-11-03), the bound-memory set's
/// drift line read "portable certificate set is DISABLED" while every canary
/// query was served.
fn portable_set_identity(manifest: &str) -> (&'static str, &'static str, &'static str) {
    if manifest == EMBEDDED_MANIFEST {
        return (
            "canary",
            "verdict_db/canary_certs",
            CHECKER_REAUTHORIZATION_COMMAND,
        );
    }
    for set in [
        &bound_memory::BOUND_MEMORY_SET,
        &bound_memory::ATOMIC_MEMORY_SET,
        &bound_memory::NEON_MEMORY_SET,
    ] {
        if manifest == set.manifest_text {
            return (set.label, set.rel_dir, set.qualification_command);
        }
    }
    (
        "unregistered",
        "<a manifest no committed set embeds>",
        CHECKER_REAUTHORIZATION_COMMAND,
    )
}

/// One loud line, once per process and certificate set, when the vendored
/// checker's bytes are not the ones that set's `manifest.v1` authorizes.
///
/// This gate disables the ENTIRE portable set — every query misses and pays
/// live discharge — and it used to do so in silence: the lane read as an
/// ordinary cache miss. The checker bytes are a function of the host C
/// toolchain, and on 2026-09-13 a CommandLineTools update moved only the
/// `cc`-inferred `-mmacosx-version-min` (26.5 -> 27.0) and re-keyed the
/// checker with nothing in the repository changed (measured 2026-09-20; the
/// input is pinned in `trust-cg-drat-trim`'s build script now). The decision
/// is unchanged — still fail closed — only the silence is gone, and the line
/// names the set ([`portable_set_identity`]) and carries its fix.
fn announce_checker_identity_drift_once(
    manifest: &str,
    checker: &Path,
    authorized: &str,
    actual: &str,
) {
    static ANNOUNCED: OnceLock<Mutex<std::collections::BTreeSet<&'static str>>> = OnceLock::new();
    let (label, dir, command) = portable_set_identity(manifest);
    let first = ANNOUNCED
        .get_or_init(Default::default)
        .lock()
        .unwrap_or_else(|poison| poison.into_inner())
        .insert(label);
    if first {
        eprintln!(
            "trust-cg-verify::canary_cert: WARNING: portable certificate set `{label}` ({dir}) \
             is DISABLED; CERT-SKIP declined for every query of that set and live discharge \
             retained: the vendored drat-trim checker {} hashes to {actual} but \
             {dir}/manifest.v1 authorizes {authorized}; the checker's bytes follow the host C \
             toolchain (compiler, SDK, and the deployment target pinned in \
             crates/trust-cg-drat-trim/build.rs). Options: restore the toolchain the manifest \
             was minted against, or review the toolchain change and re-authorize the set with \
             `{command}`",
            checker.display()
        );
    }
}

/// Why [`cert_skip_verified`] declines `smt2` right now, as one sentence that
/// names the gate and its fix — or `None` when a replay is servable.
///
/// Walks the consume path gate by gate (kill switches, recording, manifest
/// pre-filter, index validity, checker identity, selected body, exact-query
/// replay) so a test whose PRECONDITION is a portable hit can fail with the
/// cause instead of a bare `false`. Diagnosis only: it grants nothing, and the
/// final arm replays the selected certificate exactly as the consumer would.
#[cfg(test)]
pub(crate) fn describe_cert_skip_miss(smt2: &str) -> Option<String> {
    if !cert_skip_enabled() {
        return Some(
            "TCG_CANARY_NO_CACHE or TCG_NO_PROOF_CACHE is set (unset it to allow portable replay)"
                .to_string(),
        );
    }
    if crate::verdict_db::recording_active() {
        return Some("verdict-DB recording is active, which bypasses portable replay".to_string());
    }
    let query_sha = portable_query_key(smt2);
    if let Some(keys) = manifest_query_keys()
        && !keys.contains(&query_sha)
    {
        return Some(format!(
            "manifest.v1 names no certificate for query key {query_sha}: the live query bytes \
             drifted from the committed set; re-mint with `{CHECKER_REAUTHORIZATION_COMMAND}`"
        ));
    }
    let Some(certs) = embedded_cert_index() else {
        return Some(
            "the embedded portable certificate index is invalid (see the WARNING it printed)"
                .to_string(),
        );
    };
    let checker = trust_cg_drat_trim::drat_trim_executable_path();
    let Some(checker_sha) = checker_binary_sha256(checker) else {
        return Some(format!(
            "cannot read/hash the vendored checker {}",
            checker.display()
        ));
    };
    let target = trust_cg_drat_trim::drat_trim_target_triple();
    if !checker_identity_is_authorized(certs, target, &checker_sha) {
        return Some(checker_identity_drift_message(
            checker,
            certs
                .checkers
                .authorized_for(target)
                .unwrap_or("<manifest.v1 names no checker for this target>"),
            &checker_sha,
        ));
    }
    let Some(entry) = certs.by_query.get(&query_sha) else {
        return Some(format!(
            "the validated index carries no entry for query key {query_sha}"
        ));
    };
    match validate_cert_index_entry(entry) {
        Err(error) => Some(format!(
            "selected certificate {} is invalid: {error}",
            entry.file
        )),
        Ok(parsed) => {
            if cert_skip_verified_in(&PortableCert { cert: parsed }, smt2, checker, &checker_sha) {
                None
            } else {
                Some(format!(
                    "selected certificate {} failed exact-query binding or independent replay",
                    entry.file
                ))
            }
        }
    }
}

/// Consume a portable committed certificate for these exact SMT-LIB bytes.
/// This intentionally performs no AY lookup, version probe, or binary hash.
pub(crate) fn cert_skip_verified(smt2: &str) -> bool {
    let enabled = cert_skip_enabled() && !crate::verdict_db::recording_active();
    if !enabled || !manifest_may_contain(smt2) {
        return false;
    }
    PortableVerificationAuthority::capture(SanitizedChildEnv::capture_verifier(), enabled)
        .verify(smt2)
}

/// Provenance only: the offline producer AY (SHA-256) the embedded manifest
/// names for the portable certificate of this exact query. Grants nothing.
pub(crate) fn portable_cert_producer_ay_sha256(smt2: &str) -> Option<String> {
    embedded_cert_index()?
        .by_query
        .get(&portable_query_key(smt2))
        .map(|entry| entry.producer_ay_sha256.clone())
}

/// Why a committed portable certificate that EXISTS for these exact query
/// bytes was not consumed on this host — a checker that is missing or cannot
/// be read at its path, or checker bytes the manifest does not authorize — or
/// `None` when no certificate is indexed for the query (an ordinary live-lane
/// obligation), when the tier is disabled, or when this host's checker is
/// authorized (a replay outcome is then the replay's own to report).
///
/// The distinction this names is "the solver could not prove it" versus "a
/// checked proof exists but this host's checker identity is not reviewed".
/// The 2026-09-21 Linux x86-64 `core` census could not make it: 27 roots were
/// filed as a solver-capability gap (`[TCG-PASSVAL-067]`, `solver unknown`)
/// when `manifest.v1` simply had no x86-64 row. Naming the miss changes no
/// verdict — the live lane still runs and still fails closed.
pub(crate) fn cert_skip_miss_reason(smt2: &str) -> Option<String> {
    let enabled = cert_skip_enabled() && !crate::verdict_db::recording_active();
    if !enabled {
        return None;
    }
    // Unlike `manifest_may_contain`, an unparsable manifest is NOT a hit here:
    // the claim "a certificate exists for this query" must be read off a
    // parsed manifest, never assumed.
    let indexed =
        manifest_query_keys().is_some_and(|keys| keys.contains(&portable_query_key(smt2)));
    if !indexed {
        return None;
    }
    PortableVerificationAuthority::capture(SanitizedChildEnv::capture_verifier(), enabled)
        .unqualified_host_reason()
}

fn manifest_may_contain(smt2: &str) -> bool {
    let query_sha = portable_query_key(smt2);
    // Manifest-only pre-filter. `popcnt_swar_32.lratcert` alone is 15.1 MB, so
    // touching certificate bodies for a query that cannot match would add a
    // large fixed first-use cost. The small manifest already carries every
    // artifact's `query_sha256`; the indexed path below binds a selected entry
    // back to that key before it can grant authority.
    //
    // This cannot weaken the tier: a miss here declines the skip and falls back
    // to live discharge, while a hit validates the selected artifact's complete
    // digest, schema, producer/query binding and verdict key before independent
    // replay. The pre-filter can only make the consumer MORE conservative.
    //
    // If the manifest itself does not parse we deliberately fall through, so
    // `embedded_cert_index()` still reports the invalid index on its usual path.
    if let Some(keys) = manifest_query_keys()
        && !keys.contains(&query_sha)
    {
        return false;
    }
    true
}

#[cfg(test)]
fn cert_skip_verified_in(
    portable: &PortableCert,
    smt2: &str,
    checker: &Path,
    checker_sha256: &str,
) -> bool {
    cert_skip_verified_in_environment(
        portable,
        smt2,
        checker,
        checker_sha256,
        &SanitizedChildEnv::capture_verifier(),
    )
}

fn cert_skip_verified_in_environment(
    portable: &PortableCert,
    smt2: &str,
    checker: &Path,
    checker_sha256: &str,
    child_env: &SanitizedChildEnv,
) -> bool {
    if portable_query_key(smt2) != portable_query_key(&portable.cert.smt2)
        || smt2.as_bytes() != portable.cert.smt2.as_bytes()
    {
        return false;
    }
    let Ok(workdir) = tempfile::tempdir() else {
        return false;
    };
    // Temp files are absolute, so applying the captured checker CWD cannot
    // redirect its CNF/proof arguments to another directory.
    let Ok(workdir_path) = std::fs::canonicalize(workdir.path()) else {
        return false;
    };
    crate::lrat_cert::recheck_cert_with_expected_checker_and_env(
        &portable.cert,
        checker,
        checker_sha256,
        &workdir_path,
        child_env,
    )
    .is_verified()
}

#[derive(Debug)]
pub struct CanaryCertRegenReport {
    pub solver_path: String,
    /// The admission record of the producer AY (route, path, SHA-256, build).
    pub solver_admission: String,
    pub solver_identity: String,
    pub checker_identity: String,
    pub certs: Vec<(String, usize)>,
}

#[derive(Debug)]
struct NamedObligation {
    file: &'static str,
    obligation: crate::lowering_proof::ProofObligation,
}

fn certifiable_named_obligations() -> Vec<NamedObligation> {
    use crate::pass_validators::{
        GuardCarrierExpansionValidator, GuardCarrierKind, PassValidator,
        PopcntSwarExpansionValidator,
    };
    use trust_cg_ir::x86_64_ops::X86CondCode;

    let mut out = vec![NamedObligation {
        file: "popcnt_swar_32.lratcert",
        obligation: PopcntSwarExpansionValidator::x86_generic("x86-popcnt-expand", 32).obligation(),
    }];
    for obligation in crate::x86_64_function_verifier::enumerate_reconstruct_tier0_obligations()
        .into_iter()
        .filter(|obligation| is_certifiable_shift_reconstruction(&obligation.name))
    {
        out.push(NamedObligation {
            file: reconstruction_file_name(&obligation.name),
            obligation,
        });
    }
    for (class, file) in [
        (trust_cg_ir::RegClass::Gpr32, "aarch64_udiv_32.lratcert"),
        (trust_cg_ir::RegClass::Gpr64, "aarch64_udiv_64.lratcert"),
    ] {
        let r = |id| trust_cg_ir::MachOperand::VReg(trust_cg_ir::regs::VReg::new(id, class));
        let inst =
            trust_cg_ir::MachInst::new(trust_cg_ir::AArch64Opcode::UDiv, vec![r(0), r(1), r(2)]);
        let obligation = crate::function_verifier::reconstruct_alu_obligation(&inst)
            .expect("typed AArch64 UDIV reconstruction obligation");
        out.push(NamedObligation { file, obligation });
    }
    out.push(NamedObligation {
        file: "icmp_eq_32.lratcert",
        obligation: crate::x86_64_lowering_proofs::proof_x86_icmp_eq_i32(),
    });
    for (kind, cond, stem) in [
        (GuardCarrierKind::Bounds, X86CondCode::AE, "guard_bounds"),
        (
            GuardCarrierKind::ShiftRange,
            X86CondCode::AE,
            "guard_shift_range",
        ),
        (
            GuardCarrierKind::NullIfZero,
            X86CondCode::E,
            "guard_null_if_zero",
        ),
        (GuardCarrierKind::DivZero, X86CondCode::E, "guard_div_zero"),
    ] {
        for (width, suffix) in [(32, "32"), (64, "64")] {
            let file = match (stem, suffix) {
                ("guard_bounds", "32") => "guard_bounds_32.lratcert",
                ("guard_bounds", "64") => "guard_bounds_64.lratcert",
                ("guard_shift_range", "32") => "guard_shift_range_32.lratcert",
                ("guard_shift_range", "64") => "guard_shift_range_64.lratcert",
                ("guard_null_if_zero", "32") => "guard_null_if_zero_32.lratcert",
                ("guard_null_if_zero", "64") => "guard_null_if_zero_64.lratcert",
                ("guard_div_zero", "32") => "guard_div_zero_32.lratcert",
                ("guard_div_zero", "64") => "guard_div_zero_64.lratcert",
                _ => unreachable!(),
            };
            out.push(NamedObligation {
                file,
                obligation: GuardCarrierExpansionValidator::new(
                    "x86-guard-carrier-expand",
                    kind,
                    cond,
                    width,
                )
                .obligation(),
            });
        }
    }
    out.extend([
        NamedObligation {
            file: "frame_sp_alignment_16.lratcert",
            obligation: crate::frame_proofs::proof_frame_sp_alignment(),
        },
        NamedObligation {
            file: "macho_pageoff12_add.lratcert",
            obligation: crate::aarch64_macho_data_reloc_proofs::proof_pageoff12_add_full(),
        },
        NamedObligation {
            file: "macho_got_load_pageoff12.lratcert",
            obligation: crate::aarch64_macho_data_reloc_proofs::proof_got_load_pageoff12(),
        },
        NamedObligation {
            file: "macho_branch26.lratcert",
            obligation: crate::aarch64_macho_call_reloc_proofs::proof_branch26_call_target(),
        },
        NamedObligation {
            file: "macho_page21.lratcert",
            obligation: crate::aarch64_macho_data_reloc_proofs::proof_page21_adrp_page(),
        },
        NamedObligation {
            file: "movz_x_0.lratcert",
            obligation: crate::const_materialize_proofs::proof_movz_hw0(),
        },
        NamedObligation {
            file: "frame_callee_save_no_overlap.lratcert",
            obligation: crate::frame_proofs::proof_frame_callee_save_no_overlap(),
        },
        NamedObligation {
            file: "frame_callee_save_restore.lratcert",
            obligation: crate::frame_proofs::proof_frame_callee_save_restore_identity(),
        },
        NamedObligation {
            file: "ldp_i32_offset0.lratcert",
            obligation: crate::memory_proofs::proof_ldp_qf_abv_i32_offset0(),
        },
        NamedObligation {
            file: "roundtrip_i8.lratcert",
            obligation: crate::memory_proofs::proof_roundtrip_i8(),
        },
        NamedObligation {
            file: "movk_x_16.lratcert",
            obligation: crate::const_materialize_proofs::proof_movk_halfword_insert(16, 64),
        },
        NamedObligation {
            file: "movk_x_32.lratcert",
            obligation: crate::const_materialize_proofs::proof_movk_halfword_insert(32, 64),
        },
        NamedObligation {
            file: "movk_x_48.lratcert",
            obligation: crate::const_materialize_proofs::proof_movk_halfword_insert(48, 64),
        },
        NamedObligation {
            file: "checked_sadd_64.lratcert",
            obligation: crate::checked_overflow_proofs::proof_checked_sadd_i64(),
        },
        NamedObligation {
            file: "checked_umul_64.lratcert",
            obligation: crate::checked_overflow_proofs::proof_checked_umul_i64(),
        },
    ]);
    assert_eq!(out.len(), EXPECTED_CERT_COUNT);
    out
}

fn is_certifiable_shift_reconstruction(name: &str) -> bool {
    name.contains(" -> ShlRR ") || name.contains(" -> ShrRR ") || name.contains(" -> SarRR ")
}

fn reconstruction_file_name(name: &str) -> &'static str {
    for (needle, file) in [
        ("_32 -> ShlRR", "recon_shl_32.lratcert"),
        ("_64 -> ShlRR", "recon_shl_64.lratcert"),
        ("_32 -> ShrRR", "recon_shr_32.lratcert"),
        ("_64 -> ShrRR", "recon_shr_64.lratcert"),
        ("_32 -> SarRR", "recon_sar_32.lratcert"),
        ("_64 -> SarRR", "recon_sar_64.lratcert"),
    ] {
        if name.contains(needle) {
            return file;
        }
    }
    unreachable!("unmapped certified reconstruction obligation: {name:?}")
}

#[cfg(test)]
fn render_manifest(checker_sha: &str, entries: &[ManifestEntry]) -> String {
    render_manifest_with_checkers(
        &CheckerAuthorizations {
            legacy_unqualified: false,
            hosts: vec![HostChecker {
                target: trust_cg_drat_trim::drat_trim_target_triple().into(),
                sha256: checker_sha.into(),
            }],
        },
        entries,
    )
}

fn render_manifest_with_checkers(
    checkers: &CheckerAuthorizations,
    entries: &[ManifestEntry],
) -> String {
    let mut out = format!(
        "{MANIFEST_SCHEMA}\nlegacy-checker-count: {}\n",
        usize::from(checkers.legacy_unqualified)
    );
    if checkers.legacy_unqualified {
        out.push_str(&format!(
            "legacy-checker-sha256: {LEGACY_UNQUALIFIED_CHECKER_SHA256}\n"
        ));
    }
    out.push_str(&format!("host-checker-count: {}\n", checkers.hosts.len()));
    for checker in &checkers.hosts {
        out.push_str(&format!(
            "host-checker: {} {}\n",
            checker.target, checker.sha256
        ));
    }
    out.push_str(&format!("cert-count: {}\n", entries.len()));
    for entry in entries {
        out.push_str(&format!(
            "cert: {} {} {} {}\n",
            entry.file, entry.cert_sha256, entry.query_sha256, entry.producer_ay_sha256
        ));
    }
    out
}

fn regeneration_checkers(
    previous: &str,
    entries: &[ManifestEntry],
    target: &str,
    sha256: &str,
) -> CheckerAuthorizations {
    let mut checkers = parse_manifest(previous)
        .ok()
        .filter(|old| old.entries == entries)
        .map(|old| old.checkers)
        .unwrap_or_default();
    let current = HostChecker {
        target: target.into(),
        sha256: sha256.into(),
    };
    if !checkers.hosts.contains(&current) {
        checkers.hosts.push(current);
    }
    checkers
}

fn replace_file(source: &Path, destination: &Path) -> Result<(), String> {
    match std::fs::rename(source, destination) {
        Ok(()) => Ok(()),
        Err(first) if destination.exists() => {
            std::fs::remove_file(destination)
                .map_err(|e| format!("cannot replace {}: {e}", destination.display()))?;
            std::fs::rename(source, destination).map_err(|e| {
                format!(
                    "cannot publish {} after replacement (first error: {first}): {e}",
                    destination.display()
                )
            })
        }
        Err(error) => Err(format!("cannot publish {}: {error}", destination.display())),
    }
}

/// Upgrade an already-committed proof payload to the portable v3 envelope
/// without asking AY to rediscover the same refutation. This is admissible
/// only when the old producer identity plus the exact current SMT2 reproduce
/// the cert's existing verdict key, and the current authorized drat-trim bytes
/// independently replay the unchanged CNF/DRAT payload. A stale query is a
/// normal cache miss; a bound proof that no longer checks is a hard error.
fn upgrade_replayable_existing_cert(
    path: &Path,
    obligation_name: &str,
    smt2: &str,
    checker: &Path,
    checker_identity: &str,
    workdir: &Path,
) -> Result<Option<LratCert>, String> {
    let Ok(text) = std::fs::read_to_string(path) else {
        return Ok(None);
    };
    let Ok(existing) = parse_cert(&text) else {
        return Ok(None);
    };
    if existing.carries_obligation_binding() && existing.smt2 != smt2 {
        return Ok(None);
    }
    let expected_key = crate::ay_bridge::verdict_cache_key_v2(&existing.solver_identity, smt2);
    if existing.verdict_key != expected_key {
        eprintln!(
            "regen_canary_certs: {} is stale for the current exact query \
             (recorded key {}, current key {}); regenerating",
            path.display(),
            existing.verdict_key,
            expected_key,
        );
        return Ok(None);
    }
    let upgraded = LratCert::new(
        existing.verdict_key,
        existing.solver_identity,
        obligation_name,
        existing.cnf,
        existing.drat,
        smt2,
    );
    match recheck_cert_with_expected_checker(&upgraded, checker, checker_identity, workdir) {
        outcome if outcome.is_verified() => Ok(Some(upgraded)),
        outcome => Err(format!(
            "existing exact-query certificate {} failed independent replay: {outcome:?}",
            path.display()
        )),
    }
}

/// Offline regeneration. All 33 certificates are checked in a sibling staging
/// directory. Existing proof payloads are reused only after their historical
/// producer+exact-current-query key matches and the current checker replays
/// them; missing/stale payloads are freshly generated. Set
/// `TCG_CANARY_REGEN_ALL=1` to force fresh AY production for every entry.
/// Certificate files are published first and the manifest last, so a
/// crash/partial update can only disable consumption.
pub fn regen_canary_certs(out_dir: &Path) -> Result<CanaryCertRegenReport, String> {
    let solver = crate::ay_bridge::resolved_certificate_producer()
        .map_err(|refusal| format!("no AY producer admitted: {refusal}"))?;
    let solver_identity = solver.sha256().to_owned();
    let checker = trust_cg_drat_trim::drat_trim_executable_path();
    let checker_identity = checker_binary_sha256(checker)
        .ok_or_else(|| format!("cannot read/hash checker {}", checker.display()))?;
    let parent = out_dir
        .parent()
        .ok_or_else(|| format!("certificate output has no parent: {}", out_dir.display()))?;
    std::fs::create_dir_all(parent)
        .map_err(|e| format!("cannot create {}: {e}", parent.display()))?;
    let staging = tempfile::Builder::new()
        .prefix(".canary-cert-staging-")
        .tempdir_in(parent)
        .map_err(|e| format!("cannot create certificate staging directory: {e}"))?;

    let mut report = Vec::new();
    let mut manifest_entries = Vec::new();
    let mut generated_texts: Vec<(String, String)> = Vec::new();
    let mut checked_by_query: HashMap<String, LratCert> = HashMap::new();
    let force_all = crate::env_lock::var_os("TCG_CANARY_REGEN_ALL").is_some();
    for named in certifiable_named_obligations() {
        let workdir = tempfile::tempdir_in(staging.path())
            .map_err(|e| format!("cannot create proof workdir: {e}"))?;
        let exact_smt2 = crate::verdict_db::db_obligation_smt2(&named.obligation);
        let exact_query_key = portable_query_key(&exact_smt2);
        let cert = if let Some(cert) = checked_by_query.get(&exact_query_key) {
            // Bounds/ShiftRange and NullIfZero/DivZero are explicitly audited
            // exact-query aliases. Reuse the already checked proof bytes; the
            // manifest still carries one complete-file entry per semantic lane.
            cert.clone()
        } else {
            let reusable = if force_all {
                None
            } else {
                upgrade_replayable_existing_cert(
                    &out_dir.join(named.file),
                    &named.obligation.name,
                    &exact_smt2,
                    checker,
                    &checker_identity,
                    workdir.path(),
                )?
            };
            let cert = match reusable {
                Some(cert) => cert,
                None => {
                    let raw = crate::lrat_cert::generate_cert_for_obligation(
                        &named.obligation,
                        &solver,
                        checker,
                        workdir.path(),
                    )?;
                    crate::lrat_cert::trim_cert(&raw, checker, workdir.path())?
                }
            };
            checked_by_query.insert(exact_query_key, cert.clone());
            cert
        };
        let text = crate::lrat_cert::render_cert(&cert)?;
        let path = staging.path().join(named.file);
        std::fs::write(&path, text.as_bytes())
            .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
        manifest_entries.push(ManifestEntry {
            file: named.file.to_string(),
            cert_sha256: sha256_hex(text.as_bytes()),
            query_sha256: portable_query_key(&cert.smt2),
            producer_ay_sha256: cert.solver_identity.clone(),
        });
        report.push((named.obligation.name, text.len()));
        generated_texts.push((named.file.to_string(), text));
    }
    // Prior qualification is for exact certificate files and queries, not all
    // future payloads. Preserve it only when the complete corpus is unchanged.
    let checkers = regeneration_checkers(
        EMBEDDED_MANIFEST,
        &manifest_entries,
        trust_cg_drat_trim::drat_trim_target_triple(),
        &checker_identity,
    );
    let manifest = render_manifest_with_checkers(&checkers, &manifest_entries);
    std::fs::write(staging.path().join("manifest.v1"), manifest.as_bytes())
        .map_err(|e| format!("cannot write staged manifest: {e}"))?;

    // Validate exactly what is about to be published, including the explicit
    // duplicate-query alias policy.
    let borrowed: Vec<(&str, &str)> = generated_texts
        .iter()
        .map(|(file, text)| (file.as_str(), text.as_str()))
        .collect();
    build_cert_set(&manifest, &borrowed, EXPECTED_CERT_COUNT)
        .map_err(|e| format!("staged portable certificate set is invalid: {e}"))?;

    // Re-establish every distinct staged proof with the EXACT checker bytes
    // named by the manifest immediately before publication. Generation and
    // trimming also check their outputs, but those APIs accept a path; a
    // checker replacement during a long regeneration must not let different
    // bytes inherit the initial manifest identity. The expected-checker replay
    // hashes the executable on both sides of each subprocess. Semantic aliases
    // carry byte-identical certs, so replay each complete-file digest once.
    let mut replayed_files = HashSet::new();
    for (file, text) in &generated_texts {
        let file_sha = sha256_hex(text.as_bytes());
        if !replayed_files.insert(file_sha) {
            continue;
        }
        let cert = parse_cert(text).map_err(|e| format!("staged {file}: {e}"))?;
        let workdir = tempfile::tempdir_in(staging.path())
            .map_err(|e| format!("cannot create final replay workdir for {file}: {e}"))?;
        let outcome =
            recheck_cert_with_expected_checker(&cert, checker, &checker_identity, workdir.path());
        if !outcome.is_verified() {
            return Err(format!(
                "staged portable certificate {file} failed final exact-checker replay: \
                 {outcome:?}"
            ));
        }
    }

    std::fs::create_dir_all(out_dir)
        .map_err(|e| format!("cannot create {}: {e}", out_dir.display()))?;
    for entry in &manifest_entries {
        replace_file(
            &staging.path().join(&entry.file),
            &out_dir.join(&entry.file),
        )?;
    }
    replace_file(
        &staging.path().join("manifest.v1"),
        &out_dir.join("manifest.v1"),
    )?;

    Ok(CanaryCertRegenReport {
        solver_path: solver.path().display().to_string(),
        solver_admission: solver.describe(),
        solver_identity,
        checker_identity,
        certs: report,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const GOLDEN_CNF: &str = include_str!("../lrat_fixtures/repr_qfbv.cnf");
    const GOLDEN_DRAT: &str = include_str!("../lrat_fixtures/repr_qfbv.drat");
    const GOLDEN_SMT2: &str = include_str!("../lrat_fixtures/repr_qfbv.smt2");

    fn golden_portable(_file: &str) -> PortableCert {
        let producer = "11".repeat(32);
        let key = crate::ay_bridge::verdict_cache_key_v2(&producer, GOLDEN_SMT2);
        let cert = LratCert::new(
            key,
            producer,
            "portable golden",
            GOLDEN_CNF,
            GOLDEN_DRAT,
            GOLDEN_SMT2,
        );
        PortableCert { cert }
    }

    fn render_legacy_v2(cert: &LratCert) -> String {
        format!(
            "{}\nverdict-sha256: {}\nsolver-sha256: {}\ncnf-sha256: {}\n\
             obligation: {}\ncnf {}\n{}\ndrat {}\n{}\n",
            crate::lrat_cert::LRAT_CERT_SCHEMA_LINE_V2,
            cert.verdict_key,
            cert.solver_identity,
            cert.cnf_sha256,
            cert.obligation_name,
            cert.cnf.len(),
            cert.cnf,
            cert.drat.len(),
            cert.drat,
        )
    }

    #[test]
    fn legacy_upgrade_requires_exact_query_key_and_independent_replay() {
        let portable = golden_portable("golden.lratcert");
        let dir = tempfile::tempdir().unwrap();
        let cert_path = dir.path().join("golden.lratcert");
        std::fs::write(&cert_path, render_legacy_v2(&portable.cert)).unwrap();
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).unwrap();
        let replay_dir = tempfile::tempdir().unwrap();
        let upgraded = upgrade_replayable_existing_cert(
            &cert_path,
            "portable golden",
            GOLDEN_SMT2,
            checker,
            &checker_sha,
            replay_dir.path(),
        )
        .unwrap()
        .expect("exact legacy cert upgrades");
        assert!(upgraded.carries_obligation_binding());
        assert_eq!(upgraded.smt2, GOLDEN_SMT2);

        let replay_dir = tempfile::tempdir().unwrap();
        assert!(
            upgrade_replayable_existing_cert(
                &cert_path,
                "portable golden",
                &format!("{GOLDEN_SMT2}\n; mutation"),
                checker,
                &checker_sha,
                replay_dir.path(),
            )
            .unwrap()
            .is_none(),
            "a changed exact query must regenerate rather than inherit the old proof"
        );

        let mut bad = portable.cert;
        bad.drat.clear();
        std::fs::write(&cert_path, render_legacy_v2(&bad)).unwrap();
        let replay_dir = tempfile::tempdir().unwrap();
        assert!(
            upgrade_replayable_existing_cert(
                &cert_path,
                "portable golden",
                GOLDEN_SMT2,
                checker,
                &checker_sha,
                replay_dir.path(),
            )
            .is_err(),
            "a bound but invalid proof is a hard regeneration error"
        );
    }

    #[test]
    fn portable_key_is_solver_independent_and_content_sensitive() {
        assert_eq!(
            portable_query_key(GOLDEN_SMT2),
            portable_query_key(GOLDEN_SMT2)
        );
        assert_ne!(
            portable_query_key(GOLDEN_SMT2),
            portable_query_key(&format!("{GOLDEN_SMT2}\n; mutation"))
        );
    }

    #[test]
    fn exact_query_hit_needs_no_ay_but_replays_checker() {
        let cert = golden_portable("golden.lratcert");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).unwrap();
        assert!(cert_skip_verified_in(
            &cert,
            GOLDEN_SMT2,
            checker,
            &checker_sha
        ));
        assert!(!cert_skip_verified_in(
            &cert,
            &format!("{GOLDEN_SMT2}\n; mutation"),
            checker,
            &checker_sha
        ));
    }

    #[test]
    fn checker_identity_and_proof_mutations_fail_closed() {
        let mut cert = golden_portable("golden.lratcert");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        assert!(!cert_skip_verified_in(
            &cert,
            GOLDEN_SMT2,
            checker,
            &"00".repeat(32)
        ));
        cert.cert.drat.clear();
        let checker_sha = checker_binary_sha256(checker).unwrap();
        assert!(!cert_skip_verified_in(
            &cert,
            GOLDEN_SMT2,
            checker,
            &checker_sha
        ));
    }

    #[test]
    fn producer_identity_is_provenance_and_cannot_replace_authority_bindings() {
        let mut portable = golden_portable("golden.lratcert");
        // Change producer provenance consistently, including the legacy
        // producer/query key. No live AY identity participates in replay.
        portable.cert.solver_identity = "99".repeat(32);
        portable.cert.verdict_key = crate::ay_bridge::verdict_cache_key_v2(
            &portable.cert.solver_identity,
            &portable.cert.smt2,
        );
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).unwrap();
        assert!(cert_skip_verified_in(
            &portable,
            GOLDEN_SMT2,
            checker,
            &checker_sha,
        ));

        // That provenance edit grants no authority: it cannot compensate for
        // a changed query, a missing proof, or different checker bytes.
        assert!(!cert_skip_verified_in(
            &portable,
            &format!("{GOLDEN_SMT2}\n; different query"),
            checker,
            &checker_sha,
        ));
        portable.cert.drat.clear();
        assert!(!cert_skip_verified_in(
            &portable,
            GOLDEN_SMT2,
            checker,
            &checker_sha,
        ));
        assert!(!cert_skip_verified_in(
            &portable,
            GOLDEN_SMT2,
            checker,
            &"88".repeat(32),
        ));
    }

    #[test]
    fn manifest_rejects_file_query_and_producer_mutations() {
        let portable = golden_portable("golden.lratcert");
        let text = crate::lrat_cert::render_cert(&portable.cert).unwrap();
        let producer = portable.cert.solver_identity.clone();
        let checker = "22".repeat(32);
        let entry = ManifestEntry {
            file: "golden.lratcert".to_string(),
            cert_sha256: sha256_hex(text.as_bytes()),
            query_sha256: portable_query_key(GOLDEN_SMT2),
            producer_ay_sha256: producer.clone(),
        };
        let manifest = render_manifest(&checker, std::slice::from_ref(&entry));
        assert!(build_cert_set(&manifest, &[("golden.lratcert", &text)], 1).is_ok());

        let file_tamper = format!("{text}\n");
        assert!(build_cert_set(&manifest, &[("golden.lratcert", &file_tamper)], 1).is_err());

        let bad_query = manifest.replace(&entry.query_sha256, &"33".repeat(32));
        assert!(build_cert_set(&bad_query, &[("golden.lratcert", &text)], 1).is_err());

        let bad_producer = manifest.replace(&producer, &"44".repeat(32));
        assert!(build_cert_set(&bad_producer, &[("golden.lratcert", &text)], 1).is_err());
    }

    #[test]
    fn runtime_index_validates_only_the_exact_query_selected_body() {
        let first = golden_portable("first.lratcert").cert;
        let mut second = first.clone();
        second.obligation_name = "unrelated portable theorem".to_string();
        second.smt2.push_str("; distinct exact query\n");
        second.verdict_key =
            crate::ay_bridge::verdict_cache_key_v2(&second.solver_identity, &second.smt2);
        let first_text = crate::lrat_cert::render_cert(&first).unwrap();
        let second_text = crate::lrat_cert::render_cert(&second).unwrap();
        let entries = [
            ManifestEntry {
                file: "first.lratcert".to_string(),
                cert_sha256: sha256_hex(first_text.as_bytes()),
                query_sha256: portable_query_key(&first.smt2),
                producer_ay_sha256: first.solver_identity.clone(),
            },
            ManifestEntry {
                file: "second.lratcert".to_string(),
                cert_sha256: sha256_hex(second_text.as_bytes()),
                query_sha256: portable_query_key(&second.smt2),
                producer_ay_sha256: second.solver_identity.clone(),
            },
        ];
        let manifest = render_manifest(&"22".repeat(32), &entries);
        let tampered_second = format!("{second_text}\n");
        let index = build_cert_index(
            &manifest,
            &[
                ("first.lratcert", &first_text),
                ("second.lratcert", &tampered_second),
            ],
            2,
        )
        .expect("unselected bodies are deliberately lazy");

        let selected = &index.by_query[&portable_query_key(&first.smt2)];
        assert!(validate_cert_index_entry(selected).is_ok());
        let unrelated = &index.by_query[&portable_query_key(&second.smt2)];
        assert!(validate_cert_index_entry(unrelated).is_err());
        assert!(
            build_cert_set(
                &manifest,
                &[
                    ("first.lratcert", &first_text),
                    ("second.lratcert", &tampered_second),
                ],
                2,
            )
            .is_err(),
            "offline publication/audit must still validate the complete set"
        );
    }

    #[test]
    fn replay_memo_is_compute_once_per_exact_authority_key() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let key = format!(
            "canary-cert-compute-once-test:{:?}",
            std::thread::current().id()
        );
        let cell = {
            let mut memo = check_memo()
                .lock()
                .unwrap_or_else(|poison| poison.into_inner());
            std::sync::Arc::clone(memo.entry(key).or_default())
        };
        let calls = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..8 {
                let cell = std::sync::Arc::clone(&cell);
                let calls = &calls;
                scope.spawn(move || {
                    assert!(memoize_success(&cell, || {
                        calls.fetch_add(1, Ordering::SeqCst);
                        true
                    }));
                });
            }
        });
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    #[test]
    fn replay_memo_retries_false_without_poisoning_later_success() {
        let cell = Mutex::new(false);
        assert!(!memoize_success(&cell, || false));
        assert!(memoize_success(&cell, || true));
        assert!(memoize_success(&cell, || {
            panic!("successful replay must be reused")
        }));
    }

    /// The child is an isolated one-test process so changing CWD cannot race
    /// unrelated tests. The wrapper logs only an allowlisted resource value
    /// and its directory, then executes the actual bundled DRAT checker on the
    /// exact golden CNF/proof. It does not print a fake success transcript.
    #[cfg(unix)]
    #[test]
    fn portable_authority_preserves_captured_environment_cwd_and_replay_identity() {
        use std::os::unix::fs::PermissionsExt;
        use std::process::Command;

        const CHILD: &str = "TCG_PORTABLE_CAPTURE_TEST_CHILD";
        if std::env::var_os(CHILD).is_none() {
            let root = tempfile::tempdir().unwrap();
            let mut child = Command::new(std::env::current_exe().unwrap());
            child
                .args([
                    "canary_cert::tests::portable_authority_preserves_captured_environment_cwd_and_replay_identity",
                    "--exact",
                    "--show-output",
                    "--test-threads=1",
                ])
                .current_dir(root.path())
                .env(CHILD, "1");
            let output =
                crate::subprocess::run(&mut child, Some(std::time::Duration::from_secs(20)))
                    .expect("bounded isolated portable authority control");
            assert!(
                output.status.success(),
                "child stdout={} stderr={}",
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr),
            );
            let stdout = String::from_utf8_lossy(&output.stdout);
            assert!(stdout.contains("portable capture: 8 checker launches; original environment/CWD and independent DRAT replay observed"));
            print!("{stdout}");
            return;
        }

        fn capture_env(value: &str) -> SanitizedChildEnv {
            crate::env_lock::with_env_overrides(&[("GOVERN_AY_MB", value)], || {
                SanitizedChildEnv::capture_verifier()
            })
        }
        fn fixture_manifest(text: &str, checker_sha: &str, file: &str) -> String {
            let cert = parse_cert(text).unwrap();
            render_manifest(
                checker_sha,
                &[ManifestEntry {
                    file: file.to_owned(),
                    cert_sha256: sha256_hex(text.as_bytes()),
                    query_sha256: portable_query_key(&cert.smt2),
                    producer_ay_sha256: cert.solver_identity,
                }],
            )
        }
        fn quoted(path: &Path) -> String {
            format!("'{}'", path.to_str().unwrap().replace('\'', "'\\''"))
        }

        let root = std::env::current_dir().unwrap();
        let directory_b = root.join("directory-b");
        std::fs::create_dir(&directory_b).unwrap();
        let checker = root.join("checker");
        let counter = root.join("checker-calls");
        let retry_flag = root.join("retry-observed");
        let actual_checker = trust_cg_drat_trim::drat_trim_executable_path();
        let wrapper = format!(
            "#!/bin/sh\nset -eu\nprintf '%s|%s\\n' \"${{GOVERN_AY_MB-unset}}\" \"$PWD\" >> {}\n\
             if [ \"${{GOVERN_AY_MB-unset}}\" = retry ] && [ ! -e {} ]; then\n\
               : > {}\n  printf 's NOT VERIFIED\\n'\n  exit 1\nfi\nexec {} \"$@\"\n",
            quoted(&counter),
            quoted(&retry_flag),
            quoted(&retry_flag),
            quoted(actual_checker),
        );
        std::fs::write(&checker, &wrapper).unwrap();
        std::fs::set_permissions(&checker, std::fs::Permissions::from_mode(0o755)).unwrap();
        let checker_sha = checker_binary_sha256(&checker).unwrap();
        let text = crate::lrat_cert::render_cert(&golden_portable("golden.lratcert").cert).unwrap();
        let manifest = fixture_manifest(&text, &checker_sha, "golden.lratcert");
        let index = build_cert_index(&manifest, &[("golden.lratcert", &text)], 1).unwrap();
        let env_a = capture_env("128");
        let authority_a = PortableVerificationAuthority::capture_in(
            env_a.clone(),
            true,
            Path::new("checker"),
            &manifest,
        );
        assert_eq!(authority_a.checker.as_deref(), Some(checker.as_path()));
        let identity_a = authority_a.reusable_identity().unwrap();
        let authority_b = PortableVerificationAuthority::capture_in(
            capture_env("256"),
            true,
            &checker,
            &manifest,
        );
        assert_ne!(authority_b.reusable_identity(), Some(identity_a));
        std::env::set_current_dir(&directory_b).unwrap();
        let authority_cwd_b = PortableVerificationAuthority::capture_in(
            capture_env("128"),
            true,
            &checker,
            &manifest,
        );
        assert_ne!(authority_cwd_b.reusable_identity(), Some(identity_a));

        std::thread::scope(|scope| {
            let authority = authority_a.clone();
            let index = &index;
            scope
                .spawn(move || {
                    crate::env_lock::with_env_overrides(&[("GOVERN_AY_MB", "512")], || {
                        assert!(authority.verify_in(GOLDEN_SMT2, index));
                    });
                })
                .join()
                .unwrap();
        });
        assert!(authority_a.verify_in(GOLDEN_SMT2, &index));
        assert_eq!(
            std::fs::read_to_string(&counter).unwrap(),
            format!("128|{}\n", root.display())
        );
        assert!(authority_b.verify_in(GOLDEN_SMT2, &index));
        assert!(authority_cwd_b.verify_in(GOLDEN_SMT2, &index));
        assert_eq!(
            std::fs::read_to_string(&counter).unwrap(),
            format!(
                "128|{}\n256|{}\n128|{}\n",
                root.display(),
                root.display(),
                directory_b.display()
            )
        );

        let alias = root.join("checker-alias");
        std::fs::copy(&checker, &alias).unwrap();
        let alias_authority =
            PortableVerificationAuthority::capture_in(env_a.clone(), true, &alias, &manifest);
        assert_eq!(checker_binary_sha256(&alias), Some(checker_sha.clone()));
        assert_ne!(alias_authority.reusable_identity(), Some(identity_a));
        assert!(alias_authority.verify_in(GOLDEN_SMT2, &index));
        assert!(!authority_a.verify_in(&format!("{GOLDEN_SMT2}\n; another query"), &index));
        let disabled =
            PortableVerificationAuthority::capture_in(env_a.clone(), false, &checker, &manifest);
        assert!(disabled.reusable_identity().is_none());
        assert!(!disabled.verify_in(GOLDEN_SMT2, &index));

        let other_manifest = fixture_manifest(&text, &checker_sha, "other.lratcert");
        let other_index =
            build_cert_index(&other_manifest, &[("other.lratcert", &text)], 1).unwrap();
        let other_authority = PortableVerificationAuthority::capture_in(
            env_a.clone(),
            true,
            &checker,
            &other_manifest,
        );
        assert_ne!(other_authority.reusable_identity(), Some(identity_a));
        assert!(!authority_a.verify_in(GOLDEN_SMT2, &other_index));
        let damaged_text = format!("{text}\n");
        let damaged_index =
            build_cert_index(&manifest, &[("golden.lratcert", &damaged_text)], 1).unwrap();
        // Production bodies are source-embedded and immutable; exercise
        // selected-body validation on a fresh authority, before any memo hit.
        let damaged_authority = PortableVerificationAuthority::capture_in(
            capture_env("damaged"),
            true,
            &checker,
            &manifest,
        );
        assert!(!damaged_authority.verify_in(GOLDEN_SMT2, &damaged_index));

        let mut bad = golden_portable("bad.lratcert").cert;
        bad.drat.clear();
        let bad_text = crate::lrat_cert::render_cert(&bad).unwrap();
        let bad_manifest = fixture_manifest(&bad_text, &checker_sha, "bad.lratcert");
        let bad_index = build_cert_index(&bad_manifest, &[("bad.lratcert", &bad_text)], 1).unwrap();
        let bad_authority =
            PortableVerificationAuthority::capture_in(env_a.clone(), true, &checker, &bad_manifest);
        assert!(!bad_authority.verify_in(GOLDEN_SMT2, &bad_index));
        assert!(!bad_authority.verify_in(GOLDEN_SMT2, &bad_index));
        let retry = PortableVerificationAuthority::capture_in(
            capture_env("retry"),
            true,
            &checker,
            &manifest,
        );
        assert!(!retry.verify_in(GOLDEN_SMT2, &index));
        assert!(retry.verify_in(GOLDEN_SMT2, &index));
        assert!(retry.verify_in(GOLDEN_SMT2, &index));
        assert_eq!(
            std::fs::read_to_string(&counter).unwrap().lines().count(),
            8
        );

        std::fs::write(&checker, format!("{wrapper}\n# new bytes\n")).unwrap();
        assert!(authority_a.reusable_identity().is_none());
        assert!(!authority_a.verify_in(GOLDEN_SMT2, &index));
        assert_eq!(
            std::fs::read_to_string(&counter).unwrap().lines().count(),
            8
        );
        // Missing current-directory capture is explicitly non-reusable.
        let gone = root.join("gone");
        std::fs::create_dir(&gone).unwrap();
        std::env::set_current_dir(&gone).unwrap();
        std::fs::remove_dir(&gone).unwrap();
        let missing_cwd = capture_env("128");
        assert!(missing_cwd.working_dir().is_none());
        let no_cwd =
            PortableVerificationAuthority::capture_in(missing_cwd, true, &alias, &manifest);
        assert!(no_cwd.reusable_identity().is_none());
        std::env::set_current_dir(&root).unwrap();
        println!(
            "portable capture: 8 checker launches; original environment/CWD and independent DRAT replay observed"
        );
    }

    /// The manifest-only pre-filter in `cert_skip_verified` short-circuits on a
    /// query the manifest does not declare, so it must never exclude a key the
    /// shape-validated index can actually serve — otherwise it would silently
    /// disable the tier instead of skipping index/checker setup. This is the
    /// invariant that makes the pre-filter conservative rather than lossy.
    #[test]
    fn manifest_prefilter_covers_every_servable_query() {
        let set = build_cert_set(EMBEDDED_MANIFEST, EMBEDDED_CERTS, EXPECTED_CERT_COUNT)
            .expect("committed portable certificate set");
        let keys = manifest_query_keys().expect("committed manifest parses");
        for query in set.by_query.keys() {
            assert!(
                keys.contains(query),
                "pre-filter would hide servable query {query}"
            );
        }
    }

    #[test]
    fn committed_set_binds_the_exact_runtime_checker_bytes() {
        let set = build_cert_set(EMBEDDED_MANIFEST, EMBEDDED_CERTS, EXPECTED_CERT_COUNT)
            .expect("committed portable certificate set");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).expect("hash vendored checker");
        let target = trust_cg_drat_trim::drat_trim_target_triple();
        assert!(
            checker_identity_is_authorized(&set, target, &checker_sha),
            "host/checker-byte drift must disable the portable set until full qualification: {target}/{checker_sha}"
        );

        let drifted_manifest = EMBEDDED_MANIFEST.replacen(&checker_sha, &"77".repeat(32), 1);
        assert!(checker_identity_is_authorized(&set, target, &checker_sha));
        assert!(
            build_cert_set(&drifted_manifest, EMBEDDED_CERTS, EXPECTED_CERT_COUNT)
                .ok()
                .is_none_or(|drifted| !checker_identity_is_authorized(
                    &drifted,
                    target,
                    &checker_sha
                )),
            "checker SHA drift must be a portable-cache miss"
        );
    }

    #[test]
    fn host_qualified_schema_is_strict_and_preserves_only_the_recorded_legacy_exception() {
        let parsed = parse_manifest(EMBEDDED_MANIFEST).unwrap();
        assert!(parsed.checkers.legacy_unqualified);
        assert_eq!(
            parsed.checkers.hosts,
            vec![
                HostChecker {
                    target: "aarch64-apple-darwin".into(),
                    sha256: "f075353bccb02de692091e97cc35493266f6119a9b7546bff95dde0ecc52a226"
                        .into(),
                },
                HostChecker {
                    target: "aarch64-unknown-linux-gnu".into(),
                    sha256: "2aeaf98d78db430ebe805b6457d2d6016b1b18aa9ede74234eea0a1f3f1b8722"
                        .into(),
                },
                HostChecker {
                    target: "x86_64-apple-darwin".into(),
                    sha256: "beb09303142ba179a6cdce34eb42a9f3c4f7146bab32bf881dfcce09e6423a6d"
                        .into(),
                },
                HostChecker {
                    target: "x86_64-unknown-linux-gnu".into(),
                    sha256: "6bd14b38eac39bff41450ebac9e3c9436009ec478ffca537c47dae214bdb83ca"
                        .into(),
                },
                HostChecker {
                    target: "aarch64-apple-darwin".into(),
                    sha256: "7f1fae25ed6163aeb454c8a615c2b4d47530a3c7db0c9b645b6da22853e6a603"
                        .into(),
                },
            ]
        );
        let linux = parsed
            .checkers
            .hosts
            .iter()
            .find(|checker| checker.target == "aarch64-unknown-linux-gnu")
            .unwrap();
        let darwin = parsed
            .checkers
            .hosts
            .iter()
            .find(|checker| checker.target == "aarch64-apple-darwin")
            .unwrap();
        let darwin_x86 = parsed
            .checkers
            .hosts
            .iter()
            .find(|checker| checker.target == "x86_64-apple-darwin")
            .unwrap();
        let linux_x86 = parsed
            .checkers
            .hosts
            .iter()
            .find(|checker| checker.target == "x86_64-unknown-linux-gnu")
            .unwrap();
        assert!(parsed.checkers.authorizes(&linux.target, &linux.sha256));
        assert!(parsed.checkers.authorizes(&darwin.target, &darwin.sha256));
        assert!(
            parsed
                .checkers
                .authorizes(&darwin_x86.target, &darwin_x86.sha256)
        );
        assert!(
            parsed
                .checkers
                .authorizes(&linux_x86.target, &linux_x86.sha256)
        );
        assert!(!parsed.checkers.authorizes(&linux.target, &darwin.sha256));
        for other in ["x86_64-unknown-linux-gnu", "aarch64-apple-darwin"] {
            assert!(
                !parsed.checkers.authorizes(other, &darwin_x86.sha256),
                "x86-64 Darwin bytes borrowed another host: {other}"
            );
        }
        for other in ["aarch64-unknown-linux-gnu", "x86_64-apple-darwin"] {
            assert!(
                !parsed.checkers.authorizes(other, &linux_x86.sha256),
                "x86-64 Linux bytes borrowed another host: {other}"
            );
        }
        for other in [
            "x86_64-unknown-linux-gnu",
            "aarch64-apple-darwin",
            "unreviewed-unknown-host",
            "",
            "*",
        ] {
            assert!(
                !parsed.checkers.authorizes(other, &linux.sha256),
                "new Linux bytes borrowed another host: {other}"
            );
        }
        let darwin_sdk_27_2 = parsed
            .checkers
            .hosts
            .iter()
            .find(|checker| {
                checker.sha256 == "7f1fae25ed6163aeb454c8a615c2b4d47530a3c7db0c9b645b6da22853e6a603"
            })
            .unwrap();
        assert!(
            parsed
                .checkers
                .authorizes(&darwin_sdk_27_2.target, &darwin_sdk_27_2.sha256)
        );
        for other in [
            "aarch64-unknown-linux-gnu",
            "x86_64-apple-darwin",
            "x86_64-unknown-linux-gnu",
            "unreviewed-unknown-host",
            "",
            "*",
        ] {
            assert!(
                !parsed.checkers.authorizes(other, &darwin_sdk_27_2.sha256),
                "Darwin SDK 27.2 checker bytes borrowed another host: {other}"
            );
        }
        // This is the exact old one-hash policy, with no guessed host attached.
        assert!(
            parsed
                .checkers
                .authorizes("aarch64-apple-darwin", LEGACY_UNQUALIFIED_CHECKER_SHA256)
        );
        assert!(!parsed.checkers.authorizes(&linux.target, &"66".repeat(32)));
        let malformed = [
            EMBEDDED_MANIFEST.replacen(MANIFEST_SCHEMA, "tcg-canary-cert-manifest-v1", 1),
            EMBEDDED_MANIFEST.replacen(MANIFEST_SCHEMA, "tcg-canary-cert-manifest-v3", 1),
            EMBEDDED_MANIFEST.trim_end().to_owned(),
            EMBEDDED_MANIFEST.replacen("legacy-checker-count: 1", "legacy-checker-count: 2", 1),
            EMBEDDED_MANIFEST.replacen(LEGACY_UNQUALIFIED_CHECKER_SHA256, &"33".repeat(32), 1),
            EMBEDDED_MANIFEST.replacen("host-checker-count: 5", "host-checker-count: 4", 1),
            EMBEDDED_MANIFEST.replacen("host-checker-count: 5", "host-checker-count: 6", 1),
            EMBEDDED_MANIFEST.replacen("host-checker-count: 5", "host-checker-count: 65", 1),
            EMBEDDED_MANIFEST.replacen("aarch64-unknown-linux-gnu", "*", 1),
            EMBEDDED_MANIFEST.replacen("aarch64-unknown-linux-gnu", "aarch64-*-linux-gnu", 1),
            EMBEDDED_MANIFEST.replacen("aarch64-unknown-linux-gnu", "AArch64-unknown-linux-gnu", 1),
            EMBEDDED_MANIFEST.replacen("aarch64-unknown-linux-gnu", "aarch64--linux-gnu", 1),
            EMBEDDED_MANIFEST.replacen(&linux.sha256, &linux.sha256.to_uppercase(), 1),
            EMBEDDED_MANIFEST
                .replacen(
                    "cert-count: 33",
                    &format!(
                        "host-checker: {} {}\ncert-count: 33",
                        linux.target, linux.sha256
                    ),
                    1,
                )
                .replacen("host-checker-count: 5", "host-checker-count: 6", 1),
        ];
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        for (index, manifest) in malformed.into_iter().enumerate() {
            assert_ne!(manifest, EMBEDDED_MANIFEST, "no-op schema mutation {index}");
            assert!(
                parse_manifest(&manifest).is_err(),
                "malformed schema case {index}"
            );
            let authority = PortableVerificationAuthority::capture_in(
                SanitizedChildEnv::capture_verifier(),
                true,
                checker,
                &manifest,
            );
            assert!(
                authority.reusable_identity().is_none(),
                "malformed schema minted authority: {index}"
            );
        }
        println!(
            "HOST_SCHEMA_CENSUS malformed_refusals=14 wrong_host_refusals=16 legacy_preserved=1"
        );
    }

    /// A portable-certificate MISS is named, never mistaken for a solver gap:
    /// the reason carries the unqualified host and this checker's real bytes,
    /// is silent for the qualified host or a disabled tier, and is never
    /// produced for a query that no committed certificate indexes.
    #[test]
    fn cert_skip_miss_is_named_for_an_unqualified_host_only() {
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let sha = checker_binary_sha256(checker).unwrap();
        let host = trust_cg_drat_trim::drat_trim_target_triple();
        let other = if host == "aarch64-apple-darwin" {
            "x86_64-unknown-linux-gnu"
        } else {
            "aarch64-apple-darwin"
        };
        let portable = golden_portable("golden.lratcert");
        let text = crate::lrat_cert::render_cert(&portable.cert).unwrap();
        let entry = ManifestEntry {
            file: "golden.lratcert".into(),
            cert_sha256: sha256_hex(text.as_bytes()),
            query_sha256: portable_query_key(GOLDEN_SMT2),
            producer_ay_sha256: portable.cert.solver_identity,
        };
        let manifest = render_manifest(&sha, std::slice::from_ref(&entry));
        let env = SanitizedChildEnv::capture_verifier();
        let capture = |enabled: bool, target: &str| {
            PortableVerificationAuthority::capture_for_target(
                env.clone(),
                enabled,
                checker,
                &manifest,
                target,
            )
        };
        let reason = capture(true, other)
            .unqualified_host_reason()
            .expect("an unqualified host must be named");
        assert!(reason.contains(other), "{reason}");
        assert!(reason.contains(&sha), "{reason}");
        assert!(reason.contains("not a solver-capability gap"), "{reason}");
        assert!(
            !reason.contains(host),
            "the reason must not name a host it did not measure: {reason}"
        );
        assert_eq!(capture(true, host).unqualified_host_reason(), None);
        assert_eq!(capture(false, other).unqualified_host_reason(), None);
        // The committed manifest indexes no certificate for the golden query,
        // so the production entry point stays silent for it whatever this
        // host's qualification is.
        assert_eq!(cert_skip_miss_reason(GOLDEN_SMT2), None);
    }

    /// Each committed set's manifest names its own set, so a drift line is
    /// never attributed to the canary set when another set is the one that
    /// does not authorize this host's checker.
    #[test]
    fn a_drift_announcement_names_its_certificate_set() {
        assert_eq!(portable_set_identity(EMBEDDED_MANIFEST).0, "canary");
        for set in [
            &bound_memory::BOUND_MEMORY_SET,
            &bound_memory::ATOMIC_MEMORY_SET,
            &bound_memory::NEON_MEMORY_SET,
        ] {
            let (label, dir, command) = portable_set_identity(set.manifest_text);
            assert_eq!(
                (label, dir, command),
                (set.label, set.rel_dir, set.qualification_command)
            );
            assert_ne!(label, "canary");
        }
        assert_eq!(portable_set_identity("not a manifest").0, "unregistered");
    }

    /// A checker that is missing or cannot be read is named as such, with
    /// its path: the 2026-11-03 Darwin x86-64 O2 census filed 17 roots as a
    /// solver timeout (`[TCG-PASSVAL-067]`) because the build-embedded
    /// checker path pointed into a deleted worktree, the CERT-SKIP tier
    /// missed in silence and the live solver ran out its deadline. The
    /// manifest authorizes this host's real checker, so the only fault is the
    /// missing file; a disabled tier stays silent.
    #[test]
    fn a_missing_checker_is_named_with_its_path_never_as_a_solver_gap() {
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let sha = checker_binary_sha256(checker).unwrap();
        let host = trust_cg_drat_trim::drat_trim_target_triple();
        let portable = golden_portable("golden.lratcert");
        let text = crate::lrat_cert::render_cert(&portable.cert).unwrap();
        let entry = ManifestEntry {
            file: "golden.lratcert".into(),
            cert_sha256: sha256_hex(text.as_bytes()),
            query_sha256: portable_query_key(GOLDEN_SMT2),
            producer_ay_sha256: portable.cert.solver_identity,
        };
        let manifest = render_manifest(&sha, std::slice::from_ref(&entry));
        let directory = tempfile::tempdir().unwrap();
        let missing = directory.path().join("deleted-worktree/out/drat-trim");
        let unreadable = directory.path().join("not-a-file");
        std::fs::create_dir(&unreadable).unwrap();
        let env = SanitizedChildEnv::capture_verifier();
        for absent in [&missing, &unreadable] {
            let capture = |enabled: bool| {
                PortableVerificationAuthority::capture_for_target(
                    env.clone(),
                    enabled,
                    absent,
                    &manifest,
                    host,
                )
            };
            let reason = capture(true)
                .unqualified_host_reason()
                .expect("a missing checker must be named");
            assert!(
                reason.starts_with(&format!("checker not found at {}", absent.display())),
                "{reason}"
            );
            assert!(reason.contains("not a solver timeout"), "{reason}");
            assert!(
                !reason.contains(&sha),
                "it names no bytes it did not read: {reason}"
            );
            assert_eq!(capture(false).unqualified_host_reason(), None);
            // The real checker, at its real path, is authorized: no miss.
            assert_eq!(
                PortableVerificationAuthority::capture_for_target(
                    env.clone(),
                    true,
                    checker,
                    &manifest,
                    host,
                )
                .unqualified_host_reason(),
                None
            );
        }
    }

    #[test]
    fn host_binding_is_checked_before_replay_and_is_in_the_owned_memo_identity() {
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let sha = checker_binary_sha256(checker).unwrap();
        let host = trust_cg_drat_trim::drat_trim_target_triple();
        let other = if host == "aarch64-apple-darwin" {
            "x86_64-unknown-linux-gnu"
        } else {
            "aarch64-apple-darwin"
        };
        let portable = golden_portable("golden.lratcert");
        let text = crate::lrat_cert::render_cert(&portable.cert).unwrap();
        let entry = ManifestEntry {
            file: "golden.lratcert".into(),
            cert_sha256: sha256_hex(text.as_bytes()),
            query_sha256: portable_query_key(GOLDEN_SMT2),
            producer_ay_sha256: portable.cert.solver_identity,
        };
        let manifest = render_manifest(&sha, std::slice::from_ref(&entry));
        let index = build_cert_index(&manifest, &[("golden.lratcert", &text)], 1).unwrap();
        let env = SanitizedChildEnv::capture_verifier();
        let capture = |target: &str, manifest: &str| {
            PortableVerificationAuthority::capture_for_target(
                env.clone(),
                true,
                checker,
                manifest,
                target,
            )
        };
        let actual = capture(host, &manifest);
        assert!(actual.reusable_identity().is_some());
        assert!(actual.verify_in(GOLDEN_SMT2, &index));
        let wrong_host = capture(other, &manifest);
        assert!(wrong_host.reusable_identity().is_none());
        assert!(!wrong_host.verify_in(GOLDEN_SMT2, &index));
        let wrong_hash_manifest = manifest.replacen(&sha, &"77".repeat(32), 1);
        let wrong_hash = capture(host, &wrong_hash_manifest);
        assert!(wrong_hash.reusable_identity().is_none());
        assert!(!wrong_hash.verify_in(GOLDEN_SMT2, &index));
        let mut dual = parse_manifest(&manifest).unwrap().checkers;
        dual.hosts.push(HostChecker {
            target: other.into(),
            sha256: sha.clone(),
        });
        let dual_manifest = render_manifest_with_checkers(&dual, std::slice::from_ref(&entry));
        let first = capture(host, &dual_manifest);
        let second = capture(other, &dual_manifest);
        // A test-only two-host fixture proves identity separation. It adds no
        // production authorization and does not claim cross-host execution.
        assert!(first.reusable_identity().is_some());
        assert!(second.reusable_identity().is_some());
        assert_ne!(first.reusable_identity(), second.reusable_identity());
        assert_ne!(actual.reusable_identity(), first.reusable_identity());
        assert!(!actual.verify_in(
            GOLDEN_SMT2,
            &build_cert_index(&dual_manifest, &[("golden.lratcert", &text)], 1).unwrap()
        ));
    }

    #[test]
    fn regeneration_retains_host_authorization_only_for_the_same_complete_corpus() {
        let parsed = parse_manifest(EMBEDDED_MANIFEST).unwrap();
        let target = trust_cg_drat_trim::drat_trim_target_triple();
        let sha = "55".repeat(32);
        let preserved = regeneration_checkers(EMBEDDED_MANIFEST, &parsed.entries, target, &sha);
        assert!(preserved.legacy_unqualified);
        assert_eq!(
            &preserved.hosts[..parsed.checkers.hosts.len()],
            parsed.checkers.hosts.as_slice()
        );
        assert!(preserved.authorizes(target, &sha));
        for mutation in 0..4 {
            let mut changed = parsed.entries.clone();
            match mutation {
                0 => changed[0].cert_sha256 = "11".repeat(32),
                1 => changed[0].query_sha256 = "22".repeat(32),
                2 => changed[0].producer_ay_sha256 = "33".repeat(32),
                3 => {
                    changed.pop();
                }
                _ => unreachable!(),
            }
            let fresh = regeneration_checkers(EMBEDDED_MANIFEST, &changed, target, &sha);
            assert!(!fresh.legacy_unqualified);
            assert_eq!(
                fresh.hosts,
                vec![HostChecker {
                    target: target.into(),
                    sha256: sha.clone()
                }]
            );
        }
    }

    #[test]
    fn every_committed_query_reaches_the_host_qualified_production_authority() {
        let authority =
            PortableVerificationAuthority::capture(SanitizedChildEnv::capture_verifier(), true);
        assert!(
            authority.reusable_identity().is_some(),
            "actual host/checker bytes are not authorized"
        );
        let mut count = 0;
        for (file, text) in EMBEDDED_CERTS {
            let cert = parse_cert(text).unwrap();
            assert!(
                authority.verify(&cert.smt2),
                "actual portable authority refused {file}"
            );
            count += 1;
        }
        assert_eq!(count, 33);
        assert!(!authority.verify(&format!("{GOLDEN_SMT2}\n; changed exact request\n")));
        println!(
            "HOST_AUTHORITY_CENSUS certificate_queries={count} qualified_target={}",
            trust_cg_drat_trim::drat_trim_target_triple()
        );
    }

    #[test]
    fn only_declared_guard_aliases_may_share_an_exact_query() {
        assert!(allowed_exact_semantic_alias(
            "guard_bounds_32.lratcert",
            "guard_shift_range_32.lratcert"
        ));
        assert!(allowed_exact_semantic_alias(
            "guard_null_if_zero_64.lratcert",
            "guard_div_zero_64.lratcert"
        ));
        assert!(!allowed_exact_semantic_alias(
            "guard_bounds_32.lratcert",
            "guard_shift_range_64.lratcert"
        ));
        assert!(!allowed_exact_semantic_alias(
            "recon_shl_32.lratcert",
            "recon_shr_32.lratcert"
        ));
    }

    #[test]
    fn store_enforces_alias_policy_instead_of_overwriting_duplicate_queries() {
        let first = golden_portable("guard_bounds_32.lratcert");
        let mut second_cert = first.cert.clone();
        second_cert.obligation_name = "same semantics, separately named lane".to_string();
        let first_text = crate::lrat_cert::render_cert(&first.cert).unwrap();
        let second_text = crate::lrat_cert::render_cert(&second_cert).unwrap();
        let entries = [
            ManifestEntry {
                file: "guard_bounds_32.lratcert".to_string(),
                cert_sha256: sha256_hex(first_text.as_bytes()),
                query_sha256: portable_query_key(GOLDEN_SMT2),
                producer_ay_sha256: first.cert.solver_identity.clone(),
            },
            ManifestEntry {
                file: "guard_shift_range_32.lratcert".to_string(),
                cert_sha256: sha256_hex(second_text.as_bytes()),
                query_sha256: portable_query_key(GOLDEN_SMT2),
                producer_ay_sha256: second_cert.solver_identity.clone(),
            },
        ];
        let manifest = render_manifest(&"22".repeat(32), &entries);
        assert!(
            build_cert_set(
                &manifest,
                &[
                    ("guard_bounds_32.lratcert", &first_text),
                    ("guard_shift_range_32.lratcert", &second_text),
                ],
                2,
            )
            .is_ok()
        );

        let forbidden = manifest
            .replace("guard_bounds_32", "recon_shl_32")
            .replace("guard_shift_range_32", "recon_shr_32");
        assert!(
            build_cert_set(
                &forbidden,
                &[
                    ("recon_shl_32.lratcert", &first_text),
                    ("recon_shr_32.lratcert", &second_text),
                ],
                2,
            )
            .is_err()
        );
    }

    #[test]
    fn committed_set_is_exactly_thirty_three_v3_certs_and_rechecks() {
        // `build_cert_set` rejects any manifest/embedded count other than
        // `EXPECTED_CERT_COUNT`, so a successful build is the count check.
        build_cert_set(EMBEDDED_MANIFEST, EMBEDDED_CERTS, EXPECTED_CERT_COUNT)
            .expect("committed portable certificate set");
        assert_eq!(EMBEDDED_CERTS.len(), EXPECTED_CERT_COUNT);
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).unwrap();
        for (file, text) in EMBEDDED_CERTS {
            let cert = parse_cert(text).unwrap_or_else(|e| panic!("{file}: {e}"));
            assert!(
                cert.carries_obligation_binding(),
                "{file} must be schema v3"
            );
            let portable = PortableCert { cert: cert.clone() };
            assert!(
                cert_skip_verified_in(&portable, &cert.smt2, checker, &checker_sha),
                "{file} failed independent replay"
            );
            println!(
                "PORTABLE_REPLAY file={file} checker_target={} checker_sha256={checker_sha} verified=true",
                trust_cg_drat_trim::drat_trim_target_triple()
            );
        }
        println!("PORTABLE_REPLAY_CENSUS certificates={EXPECTED_CERT_COUNT}");
    }

    #[test]
    fn committed_queries_match_all_current_obligations() {
        let expected: HashMap<&str, String> = certifiable_named_obligations()
            .iter()
            .map(|named| {
                (
                    named.file,
                    crate::verdict_db::db_obligation_smt2(&named.obligation),
                )
            })
            .collect();
        assert_eq!(expected.len(), EXPECTED_CERT_COUNT);
        for (file, text) in EMBEDDED_CERTS {
            let cert = parse_cert(text).unwrap();
            assert_eq!(
                cert.smt2, expected[*file],
                "{file} does not bind the current live query"
            );
        }
    }

    #[test]
    fn aarch64_consumers_match_their_portable_certificate_queries() {
        let embedded_query = |file: &str| {
            let (_, text) = EMBEDDED_CERTS
                .iter()
                .find(|(candidate, _)| *candidate == file)
                .unwrap_or_else(|| panic!("missing embedded certificate {file}"));
            parse_cert(text)
                .unwrap_or_else(|error| panic!("parse {file}: {error}"))
                .smt2
        };

        let icmp_query = embedded_query("icmp_eq_32.lratcert");
        assert_eq!(
            crate::verdict_db::db_obligation_smt2(&crate::lowering_proof::proof_icmp_eq_i32()),
            icmp_query,
            "AArch64 Icmp Eq must remain an exact-query consumer of the portable proof"
        );
        assert_eq!(
            crate::verdict_db::db_obligation_smt2(&crate::lowering_proof::proof_condbr_eq_i32()),
            icmp_query,
            "AArch64 CondBr Eq must remain an exact-query consumer of the portable proof"
        );

        let aarch64_ushr64 = crate::function_verifier::enumerate_reconstruct_tier0_obligations()
            .into_iter()
            .find(|obligation| obligation.name.contains("Ushr_64 -> LsrRR"))
            .expect("AArch64 Ushr64 canonical reconstruction obligation");
        assert_eq!(
            crate::verdict_db::db_obligation_smt2(&aarch64_ushr64),
            embedded_query("recon_shr_64.lratcert"),
            "AArch64 Ushr64 canonical reconstruction must remain an exact-query consumer"
        );

        for (class, file) in [
            (trust_cg_ir::RegClass::Gpr32, "aarch64_udiv_32.lratcert"),
            (trust_cg_ir::RegClass::Gpr64, "aarch64_udiv_64.lratcert"),
        ] {
            let r = |id| trust_cg_ir::MachOperand::VReg(trust_cg_ir::regs::VReg::new(id, class));
            let inst = trust_cg_ir::MachInst::new(
                trust_cg_ir::AArch64Opcode::UDiv,
                vec![r(0), r(1), r(2)],
            );
            let obligation = crate::function_verifier::reconstruct_alu_obligation(&inst)
                .expect("typed AArch64 UDIV reconstruction obligation");
            assert_eq!(
                crate::verdict_db::db_obligation_smt2(&obligation),
                embedded_query(file),
                "AArch64 {class:?} UDIV reconstruction must remain an exact-query consumer"
            );
        }
    }

    #[test]
    fn kill_switches_disable_portable_reuse() {
        crate::env_lock::with_env_edits(|env| {
            env.set("TCG_CANARY_NO_CACHE", "1");
            assert!(!cert_skip_enabled());
            env.remove("TCG_CANARY_NO_CACHE");
            env.set("TCG_NO_PROOF_CACHE", "1");
            assert!(!cert_skip_enabled());
            env.remove("TCG_NO_PROOF_CACHE");
            assert!(cert_skip_enabled());
        });
    }
}
