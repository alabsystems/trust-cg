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
//! Any missing/malformed/mutated artifact, query miss, checker failure, or
//! identity change returns `false`; the caller then uses the ordinary live
//! proof path, which remains fail closed.
//!
//! Here "portable" means independent of an installed AY producer. It does not
//! authorize arbitrary `drat-trim` builds: the current checker executable must
//! match the manifest's reviewed byte identity, so a different platform or
//! toolchain build deliberately misses until that checker is separately
//! authorized and the certificate set is replayed.

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::{Mutex, OnceLock};

use crate::lrat_cert::{
    LratCert, checker_binary_sha256, parse_cert, recheck_cert_with_expected_checker, sha256_hex,
};

const MANIFEST_SCHEMA: &str = "tcg-canary-cert-manifest-v1";
const PORTABLE_QUERY_DOMAIN: &[u8] = b"tcg-portable-canary-query-v1\0";
const EXPECTED_CERT_COUNT: usize = 16;

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
];

#[derive(Debug, Clone)]
struct ManifestEntry {
    file: String,
    cert_sha256: String,
    query_sha256: String,
    producer_ay_sha256: String,
}

#[derive(Debug)]
struct CertManifest {
    drat_trim_checker_sha256: String,
    entries: Vec<ManifestEntry>,
}

#[derive(Debug)]
struct PortableCert {
    cert: LratCert,
}

#[derive(Debug)]
struct PortableCertIndexEntry<'a> {
    file: String,
    cert_file_sha256: String,
    text: &'a str,
}

#[derive(Debug)]
struct PortableCertSet<'a> {
    /// One representative per exact query. Some separately named guard lanes
    /// are intentional semantic aliases and therefore share a query key.
    by_query: HashMap<String, PortableCertIndexEntry<'a>>,
    #[allow(dead_code)]
    file_count: usize,
    drat_trim_checker_sha256: String,
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
    let drat_trim_checker_sha256 = field(lines.next(), "drat-trim-checker-sha256: ")?;
    if !is_lower_hex_256(&drat_trim_checker_sha256) {
        return Err("DRAT checker identity is not 64 lowercase hex".to_string());
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
        drat_trim_checker_sha256,
        entries,
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

fn build_cert_set<'a>(
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

    let mut by_query: HashMap<String, PortableCertIndexEntry<'a>> = HashMap::new();
    for entry in manifest.entries {
        let text = texts[entry.file.as_str()];
        let actual_file_sha = sha256_hex(text.as_bytes());
        if actual_file_sha != entry.cert_sha256 {
            return Err(format!(
                "{} complete-file digest mismatch: manifest {}, embedded {}",
                entry.file, entry.cert_sha256, actual_file_sha
            ));
        }
        let cert = parse_cert(text).map_err(|e| format!("{}: {e}", entry.file))?;
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
        let query_sha = portable_query_key(&cert.smt2);
        if query_sha != entry.query_sha256 {
            return Err(format!("{} exact-query digest mismatch", entry.file));
        }
        let internal_key =
            crate::ay_bridge::verdict_cache_key_v2(&cert.solver_identity, &cert.smt2);
        if cert.verdict_key != internal_key {
            return Err(format!("{} producer/query binding is invalid", entry.file));
        }
        if let Some(previous) = by_query.get(&query_sha) {
            if !allowed_exact_semantic_alias(&previous.file, &entry.file) {
                return Err(format!(
                    "{} and {} unexpectedly share an exact query",
                    previous.file, entry.file
                ));
            }
            // Preserve the first representative. Both complete artifacts were
            // nevertheless parsed and hash-checked above.
            continue;
        }
        by_query.insert(
            query_sha,
            PortableCertIndexEntry {
                file: entry.file,
                cert_file_sha256: entry.cert_sha256,
                text,
            },
        );
    }
    Ok(PortableCertSet {
        by_query,
        file_count: expected_count,
        drat_trim_checker_sha256: manifest.drat_trim_checker_sha256,
    })
}

fn embedded_certs() -> Option<&'static PortableCertSet<'static>> {
    static CERTS: OnceLock<Option<PortableCertSet<'static>>> = OnceLock::new();
    CERTS
        .get_or_init(|| match build_cert_set(EMBEDDED_MANIFEST, EMBEDDED_CERTS, EXPECTED_CERT_COUNT) {
            Ok(set) => Some(set),
            Err(error) => {
                eprintln!(
                    "trust-cg-verify::canary_cert: WARNING: portable certificate set is invalid; \
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

/// Process memo key = exact query + complete cert bytes + exact checker bytes.
fn check_memo() -> &'static Mutex<HashMap<String, bool>> {
    static MEMO: OnceLock<Mutex<HashMap<String, bool>>> = OnceLock::new();
    MEMO.get_or_init(|| Mutex::new(HashMap::new()))
}

fn checker_identity_is_authorized(certs: &PortableCertSet<'_>, actual_sha256: &str) -> bool {
    certs.drat_trim_checker_sha256 == actual_sha256
}

/// Consume a portable committed certificate for these exact SMT-LIB bytes.
/// This intentionally performs no AY lookup, version probe, or binary hash.
pub(crate) fn cert_skip_verified(smt2: &str) -> bool {
    if !cert_skip_enabled() || crate::verdict_db::recording_active() {
        return false;
    }
    let Some(certs) = embedded_certs() else {
        return false;
    };
    let checker = trust_cg_drat_trim::drat_trim_executable_path();
    let Some(checker_sha) = checker_binary_sha256(checker) else {
        return false;
    };
    // The proof was independently checked at regeneration by the executable
    // recorded in the signed-by-source manifest.  Requiring the same bytes at
    // consume time prevents an upgraded, downgraded, or replaced checker from
    // silently inheriting that authority.  A checker change requires an
    // explicit full regeneration and review of all sixteen artifacts.
    if !checker_identity_is_authorized(certs, &checker_sha) {
        return false;
    }
    let query_sha = portable_query_key(smt2);
    let Some(cert) = certs.by_query.get(&query_sha) else {
        return false;
    };
    let memo_key = format!("{}:{}:{}", query_sha, cert.cert_file_sha256, checker_sha);
    if let Some(hit) = check_memo()
        .lock()
        .unwrap_or_else(|poison| poison.into_inner())
        .get(&memo_key)
        .copied()
    {
        return hit;
    }
    let hit = parse_cert(cert.text).is_ok_and(|parsed| {
        cert_skip_verified_in(&PortableCert { cert: parsed }, smt2, checker, &checker_sha)
    });
    check_memo()
        .lock()
        .unwrap_or_else(|poison| poison.into_inner())
        .insert(memo_key, hit);
    hit
}

fn cert_skip_verified_in(
    portable: &PortableCert,
    smt2: &str,
    checker: &Path,
    checker_sha256: &str,
) -> bool {
    if portable_query_key(smt2) != portable_query_key(&portable.cert.smt2)
        || smt2.as_bytes() != portable.cert.smt2.as_bytes()
    {
        return false;
    }
    let Ok(workdir) = tempfile::tempdir() else {
        return false;
    };
    recheck_cert_with_expected_checker(&portable.cert, checker, checker_sha256, workdir.path())
        .is_verified()
}

#[derive(Debug)]
pub struct CanaryCertRegenReport {
    pub solver_path: String,
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

fn render_manifest(checker_sha: &str, entries: &[ManifestEntry]) -> String {
    let mut out = format!(
        "{MANIFEST_SCHEMA}\ndrat-trim-checker-sha256: {checker_sha}\ncert-count: {}\n",
        entries.len()
    );
    for entry in entries {
        out.push_str(&format!(
            "cert: {} {} {} {}\n",
            entry.file, entry.cert_sha256, entry.query_sha256, entry.producer_ay_sha256
        ));
    }
    out
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

/// Offline regeneration. All 16 certificates are checked in a sibling staging
/// directory. Existing proof payloads are reused only after their historical
/// producer+exact-current-query key matches and the current checker replays
/// them; missing/stale payloads are freshly generated. Set
/// `TCG_CANARY_REGEN_ALL=1` to force fresh AY production for every entry.
/// Certificate files are published first and the manifest last, so a
/// crash/partial update can only disable consumption.
pub fn regen_canary_certs(out_dir: &Path) -> Result<CanaryCertRegenReport, String> {
    let solver_path = crate::ay_bridge::resolved_certificate_producer_path()
        .ok_or_else(|| "no AY producer found (build AY or set AY_SOLVER_PATH)".to_string())?;
    let solver_identity = crate::ay_bridge::solver_identity_hash(&solver_path)
        .ok_or_else(|| format!("cannot read/hash AY producer {solver_path}"))?;
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
                        Path::new(&solver_path),
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
    let manifest = render_manifest(&checker_identity, &manifest_entries);
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
        solver_path,
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
    fn committed_set_binds_the_exact_runtime_checker_bytes() {
        let set = build_cert_set(EMBEDDED_MANIFEST, EMBEDDED_CERTS, EXPECTED_CERT_COUNT)
            .expect("committed portable certificate set");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).expect("hash vendored checker");
        assert_eq!(
            set.drat_trim_checker_sha256, checker_sha,
            "checker-byte drift must disable the portable set until full regeneration"
        );

        let drifted_manifest = EMBEDDED_MANIFEST.replacen(
            &format!("drat-trim-checker-sha256: {checker_sha}"),
            &format!("drat-trim-checker-sha256: {}", "77".repeat(32)),
            1,
        );
        let drifted = build_cert_set(&drifted_manifest, EMBEDDED_CERTS, EXPECTED_CERT_COUNT)
            .expect("a well-formed manifest can describe a different checker build");
        assert!(checker_identity_is_authorized(&set, &checker_sha));
        assert!(
            !checker_identity_is_authorized(&drifted, &checker_sha),
            "checker SHA drift must be a portable-cache miss"
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
    fn committed_set_is_exactly_sixteen_v3_certs_and_rechecks() {
        let set = build_cert_set(EMBEDDED_MANIFEST, EMBEDDED_CERTS, EXPECTED_CERT_COUNT)
            .expect("committed portable certificate set");
        assert_eq!(set.file_count, EXPECTED_CERT_COUNT);
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
        }
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
