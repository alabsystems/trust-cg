// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

//! The committed certificate set for the AArch64 bound-memory FORM theorems
//! (`verdict_db/bound_memory_certs/`).
//!
//! Owner ruling 2026-09-29: pair `LDP`/`STP` and scalar `LDR`/`STR` rows are
//! credited only by a formal proof. [`crate::bound_memory_authority`] credits a
//! row only when the exact query of its form theorem has a certificate in
//! this set that the vendored, independent `drat-trim` replays in this
//! process.
//!
//! The set follows the portable canary conventions (the parent module):
//! schema-v3 `.lratcert` files carrying the exact SMT2, its bit-blasted CNF
//! and a trimmed DRAT refutation; a `manifest.v1` in the
//! `tcg-canary-cert-manifest-v2` schema binding every filename to its complete
//! file SHA-256, domain-separated exact-query SHA-256, producer AY SHA-256 and
//! the reviewed `(target, checker SHA-256)` authorizations; the same
//! exact-query lookup, body validation, checker-identity gate, per-process
//! replay memo and kill switches (`TCG_CANARY_NO_CACHE`, `TCG_NO_PROOF_CACHE`).
//! One deliberate difference: the manifest is embedded but the bodies are
//! committed zstd-compressed and read from the committed directory
//! ([`BOUND_MEMORY_CERT_DIR`]), and only the body an exact query selects.
//!
//! It is a SEPARATE set with its own manifest, not rows appended to the 33
//! canaries, for one reason: regenerating the canary manifest over a changed
//! corpus drops every checker qualification the committed canary manifest
//! carries for hosts this machine cannot replay on (see
//! `regeneration_checkers`). A separate manifest records only the checker that
//! actually replayed THIS set, and leaves the canary qualifications untouched.
//!
//! A form theorem that AY cannot refute into a checkable DRAT proof gets no
//! file: its rows stay unverified. Nothing here downgrades to sampling.
//!
//! # Two sets, one mechanism
//!
//! [`FormCertSet`] is one committed set: its embedded manifest, its committed
//! directory and its per-process body cache. [`BOUND_MEMORY_SET`] holds the
//! pair and scalar memory forms; [`ATOMIC_MEMORY_SET`]
//! (`verdict_db/atomic_memory_certs/`) holds the single-instruction atomic
//! forms of [`crate::aarch64_atomic_forms`] (ledger `X-OPCODES-P2`). The atomic
//! forms are a set of their own for the same reason the bound-memory set is
//! not part of the canary set: adding them to the bound-memory corpus would
//! drop every host qualification its manifest carries for hosts this machine
//! cannot replay on.
//! [`NEON_MEMORY_SET`] (`verdict_db/neon_memory_certs/`) holds the NEON
//! `LD1`/`ST1` (one register, immediate post-index) forms of
//! [`crate::aarch64_neon_structure_forms`] (ledger `L04-P1`), a set of its own
//! for the same reason.

use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::{Mutex, OnceLock};

use super::{
    CheckerAuthorizations, ManifestEntry, PortableCertSet, PortableVerificationAuthority,
    build_cert_set, cert_skip_enabled, parse_manifest, portable_query_key, regeneration_checkers,
    render_manifest_with_checkers, replace_file, upgrade_replayable_existing_cert,
};
use crate::lrat_cert::{
    checker_binary_sha256, parse_cert, recheck_cert_with_expected_checker, sha256_hex,
};
use trust_cg_process_env::SanitizedChildEnv;

/// Committed manifest of the bound-memory set, embedded at build time.
pub(crate) const BOUND_MEMORY_MANIFEST: &str =
    include_str!("../verdict_db/bound_memory_certs/manifest.v1");

/// The committed directory the certificate BODIES are read from.
///
/// Unlike the 33 canaries, the bodies are not embedded: the set is 409 MB of
/// certificate text (57 MB committed zstd-compressed; measured 2026-09-29),
/// and embedding it would add that to every binary that links this crate. The
/// manifest IS embedded, and a body is used only after the SHA-256 of its
/// complete decompressed text equals the embedded manifest's, so a body read
/// here carries exactly the authority an embedded one would: the same bytes,
/// bound by source. The difference is availability only: a binary run away
/// from its source tree finds no body and credits nothing (fail closed).
pub(crate) const BOUND_MEMORY_CERT_DIR: &str =
    concat!(env!("CARGO_MANIFEST_DIR"), "/verdict_db/bound_memory_certs");

/// Committed manifest of the atomic-memory set, embedded at build time.
pub(crate) const ATOMIC_MEMORY_MANIFEST: &str =
    include_str!("../verdict_db/atomic_memory_certs/manifest.v1");

/// The committed directory the atomic-memory certificate bodies are read from
/// (bodies committed zstd-compressed, exactly as for the bound-memory set).
pub(crate) const ATOMIC_MEMORY_CERT_DIR: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/verdict_db/atomic_memory_certs"
);

/// Committed manifest of the NEON structure-memory set, embedded at build time.
pub(crate) const NEON_MEMORY_MANIFEST: &str =
    include_str!("../verdict_db/neon_memory_certs/manifest.v1");

/// The committed directory the NEON structure-memory certificate bodies are
/// read from (bodies committed zstd-compressed).
pub(crate) const NEON_MEMORY_CERT_DIR: &str =
    concat!(env!("CARGO_MANIFEST_DIR"), "/verdict_db/neon_memory_certs");

/// One committed form-certificate set: its embedded manifest, committed body
/// directory and per-process caches.
pub(crate) struct FormCertSet {
    /// Short name used in diagnostics (`bound-memory`, `atomic-memory`).
    pub(crate) label: &'static str,
    /// The embedded manifest text.
    pub(crate) manifest_text: &'static str,
    /// The committed directory (absolute).
    pub(crate) dir: &'static str,
    /// The committed directory relative to the crate, for messages.
    pub(crate) rel_dir: &'static str,
    /// The maintained command that qualifies a host's checker for this set.
    pub(crate) qualification_command: &'static str,
    parsed: OnceLock<Option<super::CertManifest>>,
    keys: OnceLock<Option<HashSet<String>>>,
    bodies: OnceLock<Mutex<HashMap<String, &'static str>>>,
}

/// The committed bound-memory set (pair and scalar memory forms).
pub(crate) static BOUND_MEMORY_SET: FormCertSet = FormCertSet {
    label: "bound-memory",
    manifest_text: BOUND_MEMORY_MANIFEST,
    dir: BOUND_MEMORY_CERT_DIR,
    rel_dir: "verdict_db/bound_memory_certs",
    qualification_command: BOUND_MEMORY_QUALIFICATION_COMMAND,
    parsed: OnceLock::new(),
    keys: OnceLock::new(),
    bodies: OnceLock::new(),
};

/// The committed atomic-memory set (single-instruction atomic forms).
pub(crate) static ATOMIC_MEMORY_SET: FormCertSet = FormCertSet {
    label: "atomic-memory",
    manifest_text: ATOMIC_MEMORY_MANIFEST,
    dir: ATOMIC_MEMORY_CERT_DIR,
    rel_dir: "verdict_db/atomic_memory_certs",
    qualification_command: ATOMIC_MEMORY_QUALIFICATION_COMMAND,
    parsed: OnceLock::new(),
    keys: OnceLock::new(),
    bodies: OnceLock::new(),
};

/// The committed NEON structure-memory set (`LD1`/`ST1` post-index forms).
pub(crate) static NEON_MEMORY_SET: FormCertSet = FormCertSet {
    label: "neon-memory",
    manifest_text: NEON_MEMORY_MANIFEST,
    dir: NEON_MEMORY_CERT_DIR,
    rel_dir: "verdict_db/neon_memory_certs",
    qualification_command: NEON_MEMORY_QUALIFICATION_COMMAND,
    parsed: OnceLock::new(),
    keys: OnceLock::new(),
    bodies: OnceLock::new(),
};

impl FormCertSet {
    fn manifest(&'static self) -> Option<&'static super::CertManifest> {
        self.parsed
            .get_or_init(|| match parse_manifest(self.manifest_text) {
                Ok(manifest) => Some(manifest),
                Err(error) => {
                    eprintln!(
                        "trust-cg-verify::canary_cert: WARNING: {label} manifest is invalid; no \
                         {label} row can be credited: {error}",
                        label = self.label
                    );
                    None
                }
            })
            .as_ref()
    }

    fn query_keys(&'static self) -> Option<&'static HashSet<String>> {
        self.keys
            .get_or_init(|| {
                self.manifest().map(|manifest| {
                    manifest
                        .entries
                        .iter()
                        .map(|entry| entry.query_sha256.clone())
                        .collect()
                })
            })
            .as_ref()
    }

    /// The committed body of `file`, read once per process and kept. `None`
    /// when it cannot be read; its digest is checked by the consumer, never
    /// here.
    fn body(&'static self, file: &str) -> Option<&'static str> {
        let bodies = self.bodies.get_or_init(|| Mutex::new(HashMap::new()));
        if let Some(text) = bodies.lock().unwrap_or_else(|p| p.into_inner()).get(file) {
            return Some(text);
        }
        let text = read_body(Path::new(self.dir), file).ok()?;
        let text: &'static str = Box::leak(text.into_boxed_str());
        bodies
            .lock()
            .unwrap_or_else(|p| p.into_inner())
            .insert(file.to_string(), text);
        Some(text)
    }

    /// A one-entry portable set for the manifest entry of this exact query,
    /// with its body read from the committed directory.
    fn selected_set(&'static self, query_sha: &str) -> Option<PortableCertSet<'static>> {
        let manifest = self.manifest()?;
        let entry = manifest
            .entries
            .iter()
            .find(|entry| entry.query_sha256 == query_sha)?;
        let text = self.body(&entry.file)?;
        let indexed = super::PortableCertIndexEntry {
            file: entry.file.clone(),
            cert_file_sha256: entry.cert_sha256.clone(),
            query_sha256: entry.query_sha256.clone(),
            producer_ay_sha256: entry.producer_ay_sha256.clone(),
            text,
        };
        Some(PortableCertSet {
            entries: vec![indexed.clone()],
            by_query: HashMap::from([(query_sha.to_string(), indexed)]),
            checkers: manifest.checkers.clone(),
            manifest_sha256: sha256_hex(self.manifest_text.as_bytes()),
        })
    }

    /// Whether the committed certificate for these EXACT query bytes replays
    /// with its BODY read from `dir` (bypassing the body cache and the replay
    /// memo): the on-disk corruption controls.
    #[cfg(test)]
    pub(crate) fn replays_from_dir(&'static self, smt2: &str, dir: &Path) -> Result<(), String> {
        let manifest = self
            .manifest()
            .ok_or_else(|| format!("the {} manifest is invalid", self.label))?;
        let query_sha = portable_query_key(smt2);
        let entry = manifest
            .entries
            .iter()
            .find(|entry| entry.query_sha256 == query_sha)
            .ok_or("no committed certificate names this exact query")?;
        let text = read_body(dir, &entry.file)?;
        let indexed = super::PortableCertIndexEntry {
            file: entry.file.clone(),
            cert_file_sha256: entry.cert_sha256.clone(),
            query_sha256: entry.query_sha256.clone(),
            producer_ay_sha256: entry.producer_ay_sha256.clone(),
            text: &text,
        };
        super::validate_cert_index_entry(&indexed)?;
        let selected = PortableCertSet {
            entries: vec![indexed.clone()],
            by_query: HashMap::from([(query_sha, indexed)]),
            checkers: manifest.checkers.clone(),
            manifest_sha256: sha256_hex(self.manifest_text.as_bytes()),
        };
        let authority = self.capture_authority(SanitizedChildEnv::capture_verifier(), true);
        if authority.verify_in_without_memo(smt2, &selected) {
            Ok(())
        } else {
            Err("the body validated but its independent replay was refused".to_string())
        }
    }

    /// Every committed body, read from disk (the audit path).
    #[cfg(test)]
    pub(crate) fn committed_bodies(&'static self) -> Result<Vec<(String, String)>, String> {
        let manifest = self
            .manifest()
            .ok_or_else(|| format!("the {} manifest is invalid", self.label))?;
        manifest
            .entries
            .iter()
            .map(|entry| {
                read_body(Path::new(self.dir), &entry.file).map(|text| (entry.file.clone(), text))
            })
            .collect()
    }

    /// Capture the replay authority for this set: the vendored checker and the
    /// sanitized child environment, bound to THIS set's manifest.
    pub(crate) fn capture_authority(
        &self,
        child_env: SanitizedChildEnv,
        enabled: bool,
    ) -> PortableVerificationAuthority {
        PortableVerificationAuthority::capture_in(
            child_env,
            enabled,
            trust_cg_drat_trim::drat_trim_executable_path(),
            self.manifest_text,
        )
    }

    /// True iff a committed certificate of this set for these EXACT query
    /// bytes was independently replayed under `authority`.
    pub(crate) fn cert_verified_with(
        &'static self,
        authority: &PortableVerificationAuthority,
        smt2: &str,
    ) -> bool {
        let query_sha = portable_query_key(smt2);
        if !self
            .query_keys()
            .is_some_and(|keys| keys.contains(&query_sha))
        {
            return false;
        }
        let Some(selected) = self.selected_set(&query_sha) else {
            return false;
        };
        authority.verify_in(smt2, &selected)
    }

    /// [`Self::cert_verified_with`] under an authority captured now.
    pub(crate) fn cert_verified(&'static self, smt2: &str) -> bool {
        let enabled = enabled();
        enabled
            && self.cert_verified_with(
                &self.capture_authority(SanitizedChildEnv::capture_verifier(), enabled),
                smt2,
            )
    }

    /// Why no committed certificate of this set credits these query bytes, as
    /// one clause. Diagnostic only: it grants nothing.
    pub(crate) fn cert_miss_reason(&'static self, smt2: &str) -> String {
        if !cert_skip_enabled() {
            return "committed certificates are disabled by TCG_CANARY_NO_CACHE or \
                    TCG_NO_PROOF_CACHE"
                .to_string();
        }
        if crate::verdict_db::recording_active() {
            return "verdict-DB recording is active, which bypasses committed certificates"
                .to_string();
        }
        let indexed = self
            .query_keys()
            .is_some_and(|keys| keys.contains(&portable_query_key(smt2)));
        if !indexed {
            return format!(
                "no committed certificate names its exact query ({}/manifest.v1)",
                self.rel_dir
            );
        }
        if self.selected_set(&portable_query_key(smt2)).is_none() {
            return format!(
                "the committed certificate body is not readable under {} (a binary run away \
                 from its source tree credits no {} row)",
                self.dir, self.label
            );
        }
        match self.checker_qualification() {
            Err(unqualified) => format!("a committed certificate exists, but {unqualified}"),
            Ok(()) => {
                "the committed certificate failed its exact-query binding or independent replay"
                    .to_string()
            }
        }
    }

    /// Whether the vendored checker of THIS build is one this set's manifest
    /// authorizes (target and exact bytes).
    pub(crate) fn checker_qualification(&'static self) -> Result<(), String> {
        let manifest = self
            .manifest()
            .ok_or_else(|| format!("the {} manifest is invalid", self.label))?;
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let target = trust_cg_drat_trim::drat_trim_target_triple();
        let sha = checker_binary_sha256(checker)
            .ok_or_else(|| format!("cannot hash the vendored checker {}", checker.display()))?;
        checker_qualification_in(self, &manifest.checkers, target, &sha)
    }
}

/// Suffix of a committed body on disk: the certificate text, zstd-compressed.
/// The manifest names (and hashes) the DECOMPRESSED `.lratcert` text.
const BODY_SUFFIX: &str = ".zst";
/// Largest decompressed body accepted (the largest committed one is ~45 MB).
const MAX_BODY_BYTES: u64 = 256 << 20;
/// zstd long-distance window used to write, and the most accepted to read.
const ZSTD_WINDOW_LOG: u32 = 27;

fn decompress_body(bytes: &[u8]) -> Result<String, String> {
    use std::io::Read;
    let mut decoder = zstd::stream::read::Decoder::new(bytes)
        .map_err(|e| format!("cannot start zstd decoder: {e}"))?;
    decoder
        .window_log_max(ZSTD_WINDOW_LOG)
        .map_err(|e| format!("cannot bound the zstd window: {e}"))?;
    let mut out = Vec::new();
    decoder
        .take(MAX_BODY_BYTES + 1)
        .read_to_end(&mut out)
        .map_err(|e| format!("cannot decompress: {e}"))?;
    if out.len() as u64 > MAX_BODY_BYTES {
        return Err(format!("decompressed body exceeds {MAX_BODY_BYTES} bytes"));
    }
    String::from_utf8(out).map_err(|_| "decompressed body is not UTF-8".to_string())
}

fn compress_body(text: &str) -> Result<Vec<u8>, String> {
    use std::io::Write;
    let mut encoder = zstd::stream::write::Encoder::new(Vec::new(), 19)
        .map_err(|e| format!("cannot start zstd encoder: {e}"))?;
    encoder
        .long_distance_matching(true)
        .and_then(|()| encoder.window_log(ZSTD_WINDOW_LOG))
        .map_err(|e| format!("cannot configure zstd encoder: {e}"))?;
    encoder
        .write_all(text.as_bytes())
        .map_err(|e| format!("cannot compress: {e}"))?;
    encoder
        .finish()
        .map_err(|e| format!("cannot finish zstd stream: {e}"))
}

/// Read and decompress the committed body of manifest file `file` from `dir`.
fn read_body(dir: &Path, file: &str) -> Result<String, String> {
    let path = dir.join(format!("{file}{BODY_SUFFIX}"));
    let bytes = std::fs::read(&path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    decompress_body(&bytes).map_err(|e| format!("{}: {e}", path.display()))
}

/// Whether the committed bound-memory certificate for these EXACT query
/// bytes replays with its BODY read from `dir` instead of the committed
/// directory, under an authority captured now: `Ok(())`, or the reason it is
/// refused. The on-disk controls use it: a corrupted, truncated or
/// substituted `*.lratcert.zst` must credit nothing. It bypasses the
/// per-process body cache and the successful-replay memo.
#[cfg(test)]
pub(crate) fn bound_memory_cert_replays_from_dir(smt2: &str, dir: &Path) -> Result<(), String> {
    BOUND_MEMORY_SET.replays_from_dir(smt2, dir)
}

/// Every committed bound-memory body, read from disk (the audit path:
/// offline tests and regeneration validate the COMPLETE set; a compile reads
/// only the body its query selects).
#[cfg(test)]
pub(crate) fn bound_memory_committed_bodies() -> Result<Vec<(String, String)>, String> {
    BOUND_MEMORY_SET.committed_bodies()
}

fn enabled() -> bool {
    cert_skip_enabled() && !crate::verdict_db::recording_active()
}

/// Capture the replay authority for the bound-memory set: the vendored checker
/// and the sanitized child environment, bound to THIS set's manifest. A
/// verification request captures one alongside its canary authority, so a
/// reused report's bound-memory credit was granted under the same checker,
/// manifest and environment identity.
pub(crate) fn capture_bound_memory_authority(
    child_env: SanitizedChildEnv,
    enabled: bool,
) -> PortableVerificationAuthority {
    BOUND_MEMORY_SET.capture_authority(child_env, enabled)
}

/// True iff a committed bound-memory certificate for these EXACT query bytes
/// was independently replayed under `authority` (in this process, or by this
/// process's memoized successful replay of the same bytes under the same
/// authority identity).
pub(crate) fn bound_memory_cert_verified_with(
    authority: &PortableVerificationAuthority,
    smt2: &str,
) -> bool {
    BOUND_MEMORY_SET.cert_verified_with(authority, smt2)
}

/// The maintained way to qualify another host's checker for this set: it
/// replays every committed payload with that host's checker bytes (fresh AY
/// production only for a payload that no longer replays) and, the corpus being
/// unchanged, keeps every existing authorization and adds this one.
const BOUND_MEMORY_QUALIFICATION_COMMAND: &str = "scripts/trust_cargo.sh run --release -p \
     trust-cg-verify --bin regen_bound_memory_certs";

/// The maintained way to qualify another host's checker for the atomic set.
const ATOMIC_MEMORY_QUALIFICATION_COMMAND: &str = "scripts/trust_cargo.sh run --release -p \
     trust-cg-verify --bin regen_bound_memory_certs -- --set atomic";

/// The maintained way to qualify another host's checker for the NEON set.
const NEON_MEMORY_QUALIFICATION_COMMAND: &str = "scripts/trust_cargo.sh run --release -p \
     trust-cg-verify --bin regen_bound_memory_certs -- --set neon";

/// Whether the vendored checker of THIS build is one the bound-memory
/// `manifest.v1` authorizes (target and exact bytes): `Ok(())`, or one clause
/// naming the actual identity, the authorized ones and the fix.
///
/// The set is qualified per host, exactly as the canary set is: a checker is
/// authorized only after it replayed the complete set. On a host it does not
/// authorize every bound-memory row misses fail closed (it stays unverified,
/// its reason carrying [`crate::bound_memory_authority::CHECKER_IDENTITY_MISS`]),
/// and exactly one test says so by name
/// (`bound_memory_set_binds_the_exact_runtime_checker_bytes`); every test that
/// observes bound-memory credit asks this function which outcome to expect.
pub(crate) fn bound_memory_checker_qualification() -> Result<(), String> {
    BOUND_MEMORY_SET.checker_qualification()
}

fn checker_qualification_in(
    set: &FormCertSet,
    checkers: &CheckerAuthorizations,
    target: &str,
    sha: &str,
) -> Result<(), String> {
    if checkers.authorizes(target, sha) {
        return Ok(());
    }
    Err(format!(
        "this host's checker {target}/{sha} is not authorized by {}/manifest.v1, which \
         authorizes [{}] ({}); qualify this host by replaying the complete set with its \
         checker: `{}`",
        set.rel_dir,
        checker_labels(checkers).join(", "),
        crate::bound_memory_authority::CHECKER_IDENTITY_MISS,
        set.qualification_command
    ))
}

/// One regenerated (or measured) bound-memory form.
#[derive(Debug, Clone)]
pub struct BoundMemoryCertRow {
    /// Certificate filename (one per exact query).
    pub file: String,
    /// Form theorem names sharing this exact query.
    pub forms: Vec<String>,
    /// `Ok((cnf bytes, trimmed drat bytes, cert bytes))`, or why no
    /// checker-accepted certificate was produced.
    pub outcome: Result<(usize, usize, usize), String>,
    /// Wall time of production (or reuse) plus trimming, in milliseconds.
    pub millis: u128,
    /// The payload was reused from an existing query-bound certificate.
    pub reused: bool,
}

/// Result of [`regen_bound_memory_certs`].
#[derive(Debug)]
pub struct BoundMemoryCertRegenReport {
    pub solver_path: String,
    pub solver_admission: String,
    pub solver_identity: String,
    pub checker_target: String,
    pub checker_identity: String,
    /// Checker authorizations the published manifest carries.
    pub checkers: Vec<String>,
    pub rows: Vec<BoundMemoryCertRow>,
    /// True when the set was written to `out_dir` (false for a failed
    /// staging validation, which publishes nothing).
    pub published: bool,
}

fn checker_labels(checkers: &CheckerAuthorizations) -> Vec<String> {
    let mut labels = Vec::new();
    if checkers.legacy_unqualified {
        labels.push(format!(
            "legacy-unqualified {}",
            super::LEGACY_UNQUALIFIED_CHECKER_SHA256
        ));
    }
    for host in &checkers.hosts {
        labels.push(format!("{} {}", host.target, host.sha256));
    }
    labels
}

/// Offline regeneration of the committed bound-memory set.
///
/// Every DISTINCT exact form query ([`crate::bound_memory_authority`]) is
/// certified at most once: an existing query-bound payload in `out_dir` is
/// reused only when its producer+exact-current-query key matches and the
/// current checker replays it (set `TCG_BOUND_MEMORY_REGEN_ALL=1` to force
/// fresh production); otherwise AY bit-blasts the exact query to CNF, emits a
/// DRAT refutation, `drat-trim -l` trims it and the trimmed proof is checked
/// again. A query that yields no checker-accepted certificate is REPORTED and
/// gets no file; its rows stay unverified.
///
/// The complete staged set is validated as the consumer will read it and
/// every distinct payload is replayed once more by the exact checker bytes the
/// manifest names. Certificate files publish before the manifest, and files
/// the new manifest does not name are removed last, so an interrupted
/// publication can only disable consumption.
///
/// `only` restricts production to files whose name contains it; a restricted
/// run never publishes (it writes the staged set into `out_dir` only when
/// `out_dir` is not the committed directory).
pub fn regen_bound_memory_certs(
    out_dir: &Path,
    jobs: usize,
    only: Option<&str>,
) -> Result<BoundMemoryCertRegenReport, String> {
    let named = crate::bound_memory_authority::certifiable_bound_memory_queries()
        .into_iter()
        .map(|query| RegenQuery {
            file: query.file,
            forms: query.forms,
            obligation: query.obligation,
        })
        .collect();
    regen_form_certs(
        &BOUND_MEMORY_SET,
        named,
        crate::bound_memory_authority::representative_wrong_pair_theorem(),
        out_dir,
        jobs,
        only,
    )
}

/// Offline regeneration of the committed atomic-memory set
/// (`verdict_db/atomic_memory_certs/`), with exactly the production, reuse,
/// validation and publication protocol of [`regen_bound_memory_certs`], over
/// the 48 atomic form theorems of [`crate::aarch64_atomic_forms`].
pub fn regen_atomic_memory_certs(
    out_dir: &Path,
    jobs: usize,
    only: Option<&str>,
) -> Result<BoundMemoryCertRegenReport, String> {
    let named = crate::aarch64_atomic_forms::certifiable_atomic_queries()
        .into_iter()
        .map(|query| RegenQuery {
            file: query.file,
            forms: vec![query.form],
            obligation: query.obligation,
        })
        .collect();
    regen_form_certs(
        &ATOMIC_MEMORY_SET,
        named,
        crate::aarch64_atomic_forms::representative_wrong_atomic_theorem(),
        out_dir,
        jobs,
        only,
    )
}

/// Offline regeneration of the committed NEON structure-memory set
/// (`verdict_db/neon_memory_certs/`), with exactly the production, reuse,
/// validation and publication protocol of [`regen_bound_memory_certs`], over
/// the 14 `LD1`/`ST1` form theorems of
/// [`crate::aarch64_neon_structure_forms`].
pub fn regen_neon_memory_certs(
    out_dir: &Path,
    jobs: usize,
    only: Option<&str>,
) -> Result<BoundMemoryCertRegenReport, String> {
    let named = crate::aarch64_neon_structure_forms::certifiable_neon_queries()
        .into_iter()
        .map(|query| RegenQuery {
            file: query.file,
            forms: vec![query.form],
            obligation: query.obligation,
        })
        .collect();
    regen_form_certs(
        &NEON_MEMORY_SET,
        named,
        crate::aarch64_neon_structure_forms::representative_wrong_neon_theorem(),
        out_dir,
        jobs,
        only,
    )
}

/// One distinct exact form query a set regeneration certifies.
struct RegenQuery {
    file: String,
    forms: Vec<String>,
    obligation: crate::lowering_proof::ProofObligation,
}

fn regen_form_certs(
    set: &'static FormCertSet,
    named: Vec<RegenQuery>,
    mutant: crate::lowering_proof::ProofObligation,
    out_dir: &Path,
    jobs: usize,
    only: Option<&str>,
) -> Result<BoundMemoryCertRegenReport, String> {
    let committed = Path::new(set.dir);
    std::fs::create_dir_all(out_dir)
        .map_err(|e| format!("cannot create {}: {e}", out_dir.display()))?;
    let into_committed = std::fs::canonicalize(committed)
        .ok()
        .zip(std::fs::canonicalize(out_dir).ok())
        .is_some_and(|(a, b)| a == b);
    if only.is_some() && into_committed {
        return Err(
            "a partial (--only) run cannot publish into the committed directory: every \
             unselected certificate would be dropped"
                .into(),
        );
    }
    let solver = crate::ay_bridge::resolved_certificate_producer()
        .map_err(|refusal| format!("no AY producer admitted: {refusal}"))?;
    let solver_identity = solver.sha256().to_owned();
    let checker = trust_cg_drat_trim::drat_trim_executable_path();
    let checker_identity = checker_binary_sha256(checker)
        .ok_or_else(|| format!("cannot read/hash checker {}", checker.display()))?;
    let checker_target = trust_cg_drat_trim::drat_trim_target_triple().to_string();

    let named: Vec<RegenQuery> = named
        .into_iter()
        .filter(|query| only.is_none_or(|needle| query.file.contains(needle)))
        .collect();
    if named.is_empty() {
        return Err(format!("no {} form query matches {only:?}", set.label));
    }

    let staging = tempfile::Builder::new()
        .prefix(".bound-memory-cert-staging-")
        .tempdir_in(out_dir)
        .map_err(|e| format!("cannot create certificate staging directory: {e}"))?;
    let force_all = crate::env_lock::var_os("TCG_BOUND_MEMORY_REGEN_ALL").is_some();

    // 1. Produce (or reuse) and check each distinct query, bounded parallelism.
    let next = std::sync::atomic::AtomicUsize::new(0);
    type Produced = (BoundMemoryCertRow, Option<String>);
    let results: Mutex<Vec<Option<Produced>>> = Mutex::new(vec![None; named.len()]);
    std::thread::scope(|scope| {
        for _ in 0..jobs.max(1) {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                    let Some(query) = named.get(index) else { break };
                    let started = std::time::Instant::now();
                    let smt2 = crate::verdict_db::db_obligation_smt2(&query.obligation);
                    let produced = tempfile::tempdir_in(staging.path())
                        .map_err(|e| format!("cannot create proof workdir: {e}"))
                        .and_then(|workdir| {
                            let existing = (!force_all)
                                .then(|| read_body(out_dir, &query.file).ok())
                                .flatten();
                            let reused = match existing {
                                None => None,
                                Some(text) => {
                                    let path = workdir.path().join("existing.lratcert");
                                    std::fs::write(&path, text.as_bytes()).map_err(|e| {
                                        format!("cannot stage existing {}: {e}", query.file)
                                    })?;
                                    upgrade_replayable_existing_cert(
                                        &path,
                                        &query.obligation.name,
                                        &smt2,
                                        checker,
                                        &checker_identity,
                                        workdir.path(),
                                    )?
                                }
                            };
                            let (cert, was_reused) = match reused {
                                Some(cert) => (cert, true),
                                None => {
                                    let raw = crate::lrat_cert::generate_cert_for_obligation(
                                        &query.obligation,
                                        &solver,
                                        checker,
                                        workdir.path(),
                                    )?;
                                    (
                                        crate::lrat_cert::trim_cert(&raw, checker, workdir.path())?,
                                        false,
                                    )
                                }
                            };
                            let text = crate::lrat_cert::render_cert(&cert)?;
                            Ok((cert.cnf.len(), cert.drat.len(), text, was_reused))
                        });
                    let millis = started.elapsed().as_millis();
                    let (outcome, text, reused) = match produced {
                        Ok((cnf, drat, text, reused)) => {
                            (Ok((cnf, drat, text.len())), Some(text), reused)
                        }
                        Err(error) => (Err(error), None, false),
                    };
                    eprintln!(
                        "regen_form_certs[{}]: {} {} ({millis} ms{})",
                        set.label,
                        query.file,
                        match &outcome {
                            Ok((cnf, drat, cert)) =>
                                format!("ok cnf={cnf} drat={drat} cert={cert}"),
                            Err(error) => format!("NO CERTIFICATE: {error}"),
                        },
                        if reused { ", reused" } else { "" }
                    );
                    let row = BoundMemoryCertRow {
                        file: query.file.clone(),
                        forms: query.forms.clone(),
                        outcome,
                        millis,
                        reused,
                    };
                    results.lock().unwrap_or_else(|p| p.into_inner())[index] = Some((row, text));
                }
            });
        }
    });
    let produced: Vec<Produced> = results
        .into_inner()
        .unwrap_or_else(|p| p.into_inner())
        .into_iter()
        .map(|slot| slot.expect("every query was attempted"))
        .collect();

    // 2. Assemble the staged set from the queries that certified.
    let mut entries = Vec::new();
    let mut texts: Vec<(String, String)> = Vec::new();
    for (row, text) in &produced {
        let Some(text) = text else { continue };
        let cert = parse_cert(text).map_err(|e| format!("staged {}: {e}", row.file))?;
        entries.push(ManifestEntry {
            file: row.file.clone(),
            cert_sha256: sha256_hex(text.as_bytes()),
            query_sha256: portable_query_key(&cert.smt2),
            producer_ay_sha256: cert.solver_identity.clone(),
        });
        texts.push((row.file.clone(), text.clone()));
    }
    if entries.is_empty() {
        return Err(format!(
            "no {} form query produced a checker-accepted certificate",
            set.label
        ));
    }
    let previous = std::fs::read_to_string(out_dir.join("manifest.v1"))
        .unwrap_or_else(|_| set.manifest_text.to_string());
    let checkers = regeneration_checkers(&previous, &entries, &checker_target, &checker_identity);
    let manifest = render_manifest_with_checkers(&checkers, &entries);
    let borrowed: Vec<(&str, &str)> = texts
        .iter()
        .map(|(file, text)| (file.as_str(), text.as_str()))
        .collect();
    let staged_set = build_cert_set(&manifest, &borrowed, texts.len())
        .map_err(|e| format!("staged {} certificate set is invalid: {e}", set.label))?;

    // 3. Replay every distinct staged payload with the exact manifest checker.
    let mut replayed = HashMap::new();
    for (file, text) in &texts {
        let digest = sha256_hex(text.as_bytes());
        if replayed.contains_key(&digest) {
            continue;
        }
        let cert = parse_cert(text).map_err(|e| format!("staged {file}: {e}"))?;
        let workdir = tempfile::tempdir_in(staging.path())
            .map_err(|e| format!("cannot create final replay workdir for {file}: {e}"))?;
        let outcome =
            recheck_cert_with_expected_checker(&cert, checker, &checker_identity, workdir.path());
        if !outcome.is_verified() {
            return Err(format!(
                "staged {} certificate {file} failed final exact-checker replay: {outcome:?}",
                set.label
            ));
        }
        replayed.insert(digest, file.clone());
    }

    // 4. The staged set must credit every staged query and refuse a mutant.
    let authority = PortableVerificationAuthority::capture_in(
        SanitizedChildEnv::capture_verifier(),
        true,
        checker,
        &manifest,
    );
    for query in &named {
        let staged = texts.iter().any(|(file, _)| *file == query.file);
        let credited = authority.verify_in(
            &crate::verdict_db::db_obligation_smt2(&query.obligation),
            &staged_set,
        );
        if staged != credited {
            return Err(format!(
                "staged consumer disagrees for {}: staged={staged} credited={credited}",
                query.file
            ));
        }
    }
    if authority.verify_in(&crate::verdict_db::db_obligation_smt2(&mutant), &staged_set) {
        return Err(format!(
            "staged consumer credited a deliberately wrong theorem: {}",
            mutant.name
        ));
    }

    // 5. Publish: certificates, then the manifest, then prune.
    let files: Vec<String> = entries.iter().map(|entry| entry.file.clone()).collect();
    let compressed: Vec<Result<Vec<u8>, String>> = {
        use rayon::prelude::*;
        texts
            .par_iter()
            .map(|(file, text)| {
                let compressed = compress_body(text).map_err(|e| format!("{file}: {e}"))?;
                if decompress_body(&compressed).as_deref() != Ok(text.as_str()) {
                    return Err(format!("{file}: the compressed body does not round-trip"));
                }
                Ok(compressed)
            })
            .collect()
    };
    for ((file, _), compressed) in texts.iter().zip(compressed) {
        let compressed = compressed?;
        let name = format!("{file}{BODY_SUFFIX}");
        let path = staging.path().join(&name);
        std::fs::write(&path, &compressed)
            .map_err(|e| format!("cannot write {}: {e}", path.display()))?;
        replace_file(&path, &out_dir.join(&name))?;
    }
    let manifest_path = staging.path().join("manifest.v1");
    std::fs::write(&manifest_path, manifest.as_bytes())
        .map_err(|e| format!("cannot write staged manifest: {e}"))?;
    replace_file(&manifest_path, &out_dir.join("manifest.v1"))?;
    let keep: HashSet<&str> = files.iter().map(String::as_str).collect();
    if let Ok(listing) = std::fs::read_dir(out_dir) {
        for entry in listing.flatten() {
            let name = entry.file_name().to_string_lossy().into_owned();
            let logical = name.strip_suffix(BODY_SUFFIX).unwrap_or(&name);
            if logical.ends_with(".lratcert") && !(keep.contains(logical) && name != logical) {
                std::fs::remove_file(entry.path())
                    .map_err(|e| format!("cannot remove stale {name}: {e}"))?;
            }
        }
    }

    Ok(BoundMemoryCertRegenReport {
        solver_path: solver.path().display().to_string(),
        solver_admission: solver.describe(),
        solver_identity,
        checker_target,
        checker_identity,
        checkers: checker_labels(&checkers),
        rows: produced.into_iter().map(|(row, _)| row).collect(),
        published: true,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    /// THE host-qualification pin of the bound-memory set: red on exactly the
    /// hosts whose checker bytes the manifest does not authorize, naming the
    /// identity and the fix. Every other test that observes bound-memory
    /// credit branches on [`bound_memory_checker_qualification`] and asserts
    /// the fail-closed outcome there, so an unqualified host shows ONE red
    /// test for its one cause (as the canary set's
    /// `committed_set_binds_the_exact_runtime_checker_bytes` does).
    #[test]
    fn bound_memory_set_binds_the_exact_runtime_checker_bytes() {
        if let Err(unqualified) = bound_memory_checker_qualification() {
            panic!("the bound-memory certificate set credits nothing on this host: {unqualified}");
        }
        let manifest = parse_manifest(BOUND_MEMORY_MANIFEST).expect("committed manifest parses");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let sha = checker_binary_sha256(checker).expect("checker hash");
        let target = trust_cg_drat_trim::drat_trim_target_triple();
        assert_eq!(
            checker_qualification_in(&BOUND_MEMORY_SET, &manifest.checkers, target, &sha),
            Ok(())
        );

        // Other bytes on this target, and these bytes under another target,
        // are misses that name the identity and the qualification command.
        let other_bytes = checker_qualification_in(
            &BOUND_MEMORY_SET,
            &manifest.checkers,
            target,
            &"77".repeat(32),
        )
        .expect_err("changed checker bytes must not borrow the authorization");
        // The "other target" must be one NO host can be. Naming a real triple
        // here made the control host-dependent: it was spelled
        // `x86_64-unknown-linux-gnu`, and the day that host qualified its own
        // checker the lookup correctly SUCCEEDED and this control panicked on
        // its own `expect_err` — a green qualification reported as a red test.
        // A synthetic triple tests the same thing on every host.
        let other_target = checker_qualification_in(
            &BOUND_MEMORY_SET,
            &manifest.checkers,
            "nohost-unknown-none-elf",
            &sha,
        )
        .expect_err("a host qualification must not cover another target");
        for miss in [other_bytes, other_target] {
            assert!(
                miss.contains(crate::bound_memory_authority::CHECKER_IDENTITY_MISS)
                    && miss.contains(BOUND_MEMORY_QUALIFICATION_COMMAND)
                    && miss.contains(&format!("{target} {sha}")),
                "{miss}"
            );
        }
    }

    /// The committed bound-memory set is well formed, every body its manifest
    /// names is present and replays, it never shares an exact query with the
    /// canary set, and
    /// every committed query is the query of a current bound-memory form (a
    /// stale certificate would credit nothing and hide a regression).
    #[test]
    fn committed_bound_memory_set_is_exact_and_current() {
        let bodies = bound_memory_committed_bodies().expect("committed bodies");
        let borrowed: Vec<(&str, &str)> = bodies
            .iter()
            .map(|(file, text)| (file.as_str(), text.as_str()))
            .collect();
        let set = build_cert_set(BOUND_MEMORY_MANIFEST, &borrowed, borrowed.len())
            .expect("committed bound-memory set must validate");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).expect("checker hash");
        for (file, text) in &bodies {
            let cert = parse_cert(text).expect("committed body parses");
            let workdir = tempfile::tempdir().expect("workdir");
            assert!(
                recheck_cert_with_expected_checker(&cert, checker, &checker_sha, workdir.path())
                    .is_verified(),
                "{file} does not replay"
            );
        }
        let current: HashMap<String, String> =
            crate::bound_memory_authority::certifiable_bound_memory_queries()
                .into_iter()
                .map(|query| {
                    (
                        portable_query_key(&crate::verdict_db::db_obligation_smt2(
                            &query.obligation,
                        )),
                        query.file,
                    )
                })
                .collect();
        let canary = parse_manifest(super::super::EMBEDDED_MANIFEST).expect("canary manifest");
        let canary_queries: HashSet<&str> = canary
            .entries
            .iter()
            .map(|entry| entry.query_sha256.as_str())
            .collect();
        for entry in &set.entries {
            assert_eq!(
                current.get(&entry.query_sha256),
                Some(&entry.file),
                "{} is not the certificate of a current bound-memory form query",
                entry.file
            );
            assert!(
                !canary_queries.contains(entry.query_sha256.as_str()),
                "{} duplicates a canary query",
                entry.file
            );
        }
        assert_eq!(set.by_query.len(), set.entries.len(), "one file per query");
        eprintln!(
            "BOUND_MEMORY_CERT_REPLAY bodies={} checker={}/{}",
            bodies.len(),
            trust_cg_drat_trim::drat_trim_target_triple(),
            checker_sha
        );
    }

    /// THE host-qualification pin of the atomic-memory set (the analogue of
    /// `bound_memory_set_binds_the_exact_runtime_checker_bytes`): red on
    /// exactly the hosts whose checker bytes its manifest does not authorize.
    #[test]
    fn atomic_memory_set_binds_the_exact_runtime_checker_bytes() {
        if let Err(unqualified) = ATOMIC_MEMORY_SET.checker_qualification() {
            panic!("the atomic-memory certificate set credits nothing on this host: {unqualified}");
        }
        let manifest = parse_manifest(ATOMIC_MEMORY_MANIFEST).expect("committed manifest parses");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let sha = checker_binary_sha256(checker).expect("checker hash");
        let target = trust_cg_drat_trim::drat_trim_target_triple();
        let miss = checker_qualification_in(
            &ATOMIC_MEMORY_SET,
            &manifest.checkers,
            target,
            &"77".repeat(32),
        )
        .expect_err("changed checker bytes must not borrow the authorization");
        assert!(
            miss.contains(crate::bound_memory_authority::CHECKER_IDENTITY_MISS)
                && miss.contains(ATOMIC_MEMORY_QUALIFICATION_COMMAND)
                && miss.contains("verdict_db/atomic_memory_certs/manifest.v1")
                && miss.contains(&format!("{target} {sha}")),
            "{miss}"
        );
    }

    /// The committed atomic-memory set is well formed, every body replays,
    /// it shares no exact query with the canary or bound-memory sets, and
    /// every committed query is the query of a current atomic form theorem.
    /// Every one of the 48 forms has a certificate.
    #[test]
    fn committed_atomic_memory_set_is_exact_current_and_complete() {
        let bodies = ATOMIC_MEMORY_SET
            .committed_bodies()
            .expect("committed bodies");
        let borrowed: Vec<(&str, &str)> = bodies
            .iter()
            .map(|(file, text)| (file.as_str(), text.as_str()))
            .collect();
        let set = build_cert_set(ATOMIC_MEMORY_MANIFEST, &borrowed, borrowed.len())
            .expect("committed atomic-memory set must validate");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).expect("checker hash");
        for (file, text) in &bodies {
            let cert = parse_cert(text).expect("committed body parses");
            let workdir = tempfile::tempdir().expect("workdir");
            assert!(
                recheck_cert_with_expected_checker(&cert, checker, &checker_sha, workdir.path())
                    .is_verified(),
                "{file} does not replay"
            );
        }
        let current: HashMap<String, String> =
            crate::aarch64_atomic_forms::certifiable_atomic_queries()
                .into_iter()
                .map(|query| {
                    (
                        portable_query_key(&crate::verdict_db::db_obligation_smt2(
                            &query.obligation,
                        )),
                        query.file,
                    )
                })
                .collect();
        let others: HashSet<String> = [super::super::EMBEDDED_MANIFEST, BOUND_MEMORY_MANIFEST]
            .into_iter()
            .flat_map(|text| parse_manifest(text).expect("manifest").entries)
            .map(|entry| entry.query_sha256)
            .collect();
        for entry in &set.entries {
            assert_eq!(
                current.get(&entry.query_sha256),
                Some(&entry.file),
                "{} is not the certificate of a current atomic form query",
                entry.file
            );
            assert!(
                !others.contains(&entry.query_sha256),
                "{} duplicates another set's query",
                entry.file
            );
        }
        assert_eq!(set.by_query.len(), set.entries.len(), "one file per query");
        assert_eq!(
            set.entries.len(),
            current.len(),
            "every atomic form theorem must have a committed certificate"
        );
        eprintln!(
            "ATOMIC_MEMORY_CERT_REPLAY bodies={} checker={}/{}",
            bodies.len(),
            trust_cg_drat_trim::drat_trim_target_triple(),
            checker_sha
        );
    }

    /// THE host-qualification pin of the NEON structure-memory set: red on
    /// exactly the hosts whose checker bytes its manifest does not authorize.
    #[test]
    fn neon_memory_set_binds_the_exact_runtime_checker_bytes() {
        if let Err(unqualified) = NEON_MEMORY_SET.checker_qualification() {
            panic!("the NEON memory certificate set credits nothing on this host: {unqualified}");
        }
        let manifest = parse_manifest(NEON_MEMORY_MANIFEST).expect("committed manifest parses");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let sha = checker_binary_sha256(checker).expect("checker hash");
        let target = trust_cg_drat_trim::drat_trim_target_triple();
        let miss = checker_qualification_in(
            &NEON_MEMORY_SET,
            &manifest.checkers,
            target,
            &"77".repeat(32),
        )
        .expect_err("changed checker bytes must not borrow the authorization");
        assert!(
            miss.contains(crate::bound_memory_authority::CHECKER_IDENTITY_MISS)
                && miss.contains(NEON_MEMORY_QUALIFICATION_COMMAND)
                && miss.contains("verdict_db/neon_memory_certs/manifest.v1")
                && miss.contains(&format!("{target} {sha}")),
            "{miss}"
        );
    }

    /// The committed NEON structure-memory set is well formed, every body
    /// replays, it shares no exact query with the other sets, every committed
    /// query is the query of a current `LD1`/`ST1` form theorem, and every one
    /// of the 14 forms has a certificate.
    #[test]
    fn committed_neon_memory_set_is_exact_current_and_complete() {
        let bodies = NEON_MEMORY_SET
            .committed_bodies()
            .expect("committed bodies");
        let borrowed: Vec<(&str, &str)> = bodies
            .iter()
            .map(|(file, text)| (file.as_str(), text.as_str()))
            .collect();
        let set = build_cert_set(NEON_MEMORY_MANIFEST, &borrowed, borrowed.len())
            .expect("committed NEON memory set must validate");
        let checker = trust_cg_drat_trim::drat_trim_executable_path();
        let checker_sha = checker_binary_sha256(checker).expect("checker hash");
        for (file, text) in &bodies {
            let cert = parse_cert(text).expect("committed body parses");
            let workdir = tempfile::tempdir().expect("workdir");
            assert!(
                recheck_cert_with_expected_checker(&cert, checker, &checker_sha, workdir.path())
                    .is_verified(),
                "{file} does not replay"
            );
        }
        let current: HashMap<String, String> =
            crate::aarch64_neon_structure_forms::certifiable_neon_queries()
                .into_iter()
                .map(|query| {
                    (
                        portable_query_key(&crate::verdict_db::db_obligation_smt2(
                            &query.obligation,
                        )),
                        query.file,
                    )
                })
                .collect();
        let others: HashSet<String> = [
            super::super::EMBEDDED_MANIFEST,
            BOUND_MEMORY_MANIFEST,
            ATOMIC_MEMORY_MANIFEST,
        ]
        .into_iter()
        .flat_map(|text| parse_manifest(text).expect("manifest").entries)
        .map(|entry| entry.query_sha256)
        .collect();
        for entry in &set.entries {
            assert_eq!(
                current.get(&entry.query_sha256),
                Some(&entry.file),
                "{} is not the certificate of a current NEON form query",
                entry.file
            );
            assert!(
                !others.contains(&entry.query_sha256),
                "{} duplicates another set's query",
                entry.file
            );
        }
        assert_eq!(set.by_query.len(), set.entries.len(), "one file per query");
        assert_eq!(
            set.entries.len(),
            current.len(),
            "every NEON form theorem must have a committed certificate"
        );
    }
}
