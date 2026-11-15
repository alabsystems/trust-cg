// trust-cg-verify - immutable external-verifier authority
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! Exact, request-local identity for proof-producing subprocesses.
//!
//! A solver/query digest alone is not enough to reuse `Verified`: promotion
//! also depends on the independent checker and on the environment under which
//! both executables ran. This module captures those inputs once and supplies
//! compact keys to every positive in-process memo. It deliberately remains
//! frontend-neutral; TY, rustc, and any other TrustIR producer share the same
//! authority boundary.

use std::path::{Path, PathBuf};
use std::sync::Arc;

use sha2::{Digest, Sha256};

use trust_cg_process_env::SanitizedChildEnv;

use crate::ay_identity::PinnedAy;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ExecutableAuthority {
    path: Arc<PathBuf>,
    sha256: Arc<str>,
}

impl ExecutableAuthority {
    fn new(path: PathBuf, sha256: String) -> Option<Self> {
        if sha256.len() != 64
            || !sha256
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return None;
        }
        Some(Self {
            // Execute the exact path that was capability-probed. A symlink or
            // wrapper may intentionally depend on its spelling/argv[0]; using
            // a canonical target here would silently change the authority
            // between probe and replay.
            path: Arc::new(path),
            sha256: Arc::from(sha256),
        })
    }

    pub(crate) fn path(&self) -> &Path {
        self.path.as_path()
    }

    pub(crate) fn sha256(&self) -> &str {
        &self.sha256
    }
}

/// One immutable request's solver/checker/process environment.
///
/// Solver content is supplied only when constructing a positive-cache key.
/// This preserves the existing non-blocking hot path: a default AY binary is
/// large, so an unresolved background content hash makes reuse decline rather
/// than forcing compilation to wait merely to attempt a cache lookup.
#[derive(Clone, Debug)]
pub(crate) struct VerificationAuthority {
    // The admitted AY. Every solver process for this request is started from
    // it (`PinnedAy::command`), never from a path.
    solver: Arc<PinnedAy>,
    solver_path_text: Arc<str>,
    checker: Option<ExecutableAuthority>,
    checker_error: Option<crate::obligation_cert_store::CheckerResolutionError>,
    child_env: SanitizedChildEnv,
    proof_context_id: [u8; 32],
    solver_process_id: [u8; 32],
}

impl VerificationAuthority {
    /// Capture the exact checker and hermetic child environment for the AY
    /// admitted for this request. The solver's digest was computed when it was
    /// admitted; nothing here hashes it again.
    pub(crate) fn capture(solver: &PinnedAy) -> Self {
        Self::capture_with_timeout(solver, crate::ay_bridge::AYConfig::default().timeout_ms)
    }

    /// Transport-only test adapters need process identity, but must not probe
    /// an independent checker outside the transport deadline or gain proof authority.
    #[cfg(test)]
    pub(crate) fn capture_solver_process(solver: &PinnedAy) -> Self {
        Self::from_parts(solver.clone(), None, SanitizedChildEnv::capture_verifier())
    }

    pub(crate) fn capture_with_timeout(solver: &PinnedAy, timeout_ms: u64) -> Self {
        Self::capture_with_environment(solver, SanitizedChildEnv::capture_verifier(), timeout_ms)
    }

    pub(crate) fn capture_with_environment(
        solver: &PinnedAy,
        child_env: SanitizedChildEnv,
        timeout_ms: u64,
    ) -> Self {
        // An admitted AY is always an absolute, identity-checked path: there
        // is no bare name to resolve against PATH and no relative path to
        // anchor to the working directory.
        let resolution = crate::obligation_cert_store::clean_checker_path_and_identity_with_env(
            &child_env, timeout_ms,
        );
        let (checker, error) = match resolution {
            Ok((path, identity)) => (ExecutableAuthority::new(path, identity), None),
            Err(error) => (None, Some(error)),
        };
        let mut authority = Self::from_parts(solver.clone(), checker, child_env);
        authority.checker_error = error;
        authority
    }

    fn from_parts(
        solver: PinnedAy,
        checker: Option<ExecutableAuthority>,
        child_env: SanitizedChildEnv,
    ) -> Self {
        crate::ay_bridge::seed_admitted_solver_identity(&solver);
        let solver_path = solver.path().to_path_buf();
        let solver_path_text: Arc<str> = Arc::from(solver_path.to_string_lossy().into_owned());
        let mut checker_env = Sha256::new();
        checker_env.update(b"trust-cg.verification-authority.checker-env.v1\0");
        hash_digest_part(&mut checker_env, b"child-env", &child_env.digest());
        match &checker {
            Some(checker) => {
                hash_part(&mut checker_env, b"checker-present", b"1");
                hash_path_part(&mut checker_env, b"checker-path", checker.path());
                hash_part(
                    &mut checker_env,
                    b"checker-sha256",
                    checker.sha256().as_bytes(),
                );
            }
            None => hash_part(&mut checker_env, b"checker-present", b"0"),
        }
        let checker_env_id = checker_env.finalize().into();

        // A byte-identical executable at another path is not necessarily the
        // same program execution: argv[0], sibling-resource lookup, wrappers,
        // and platform loader policy can all be path-dependent. Positive
        // solver-result reuse therefore binds the canonical solver path in
        // addition to its separately supplied content digest.
        let mut proof_context = Sha256::new();
        proof_context.update(b"trust-cg.verification-authority.proof-context.v1\0");
        hash_path_part(&mut proof_context, b"solver-path", &solver_path);
        hash_digest_part(&mut proof_context, b"checker-env", &checker_env_id);
        let proof_context_id = proof_context.finalize().into();

        let mut process = Sha256::new();
        process.update(b"trust-cg.verification-authority.solver-process.v1\0");
        hash_path_part(&mut process, b"solver-path", &solver_path);
        hash_digest_part(&mut process, b"child-env", &child_env.digest());
        hash_solver_metadata(&mut process, &solver_path);
        let solver_process_id = process.finalize().into();

        Self {
            solver: Arc::new(solver),
            solver_path_text,
            checker,
            checker_error: None,
            child_env,
            proof_context_id,
            solver_process_id,
        }
    }

    /// The admitted AY every solver process of this request is started from.
    pub(crate) fn solver(&self) -> &PinnedAy {
        &self.solver
    }

    pub(crate) fn solver_path(&self) -> &Path {
        self.solver.path()
    }

    pub(crate) fn solver_path_text(&self) -> &str {
        &self.solver_path_text
    }

    pub(crate) fn checker(&self) -> Option<&ExecutableAuthority> {
        self.checker.as_ref()
    }

    pub(crate) fn checker_resolution_error(
        &self,
    ) -> Option<&crate::obligation_cert_store::CheckerResolutionError> {
        self.checker_error.as_ref()
    }

    pub(crate) fn child_env(&self) -> &SanitizedChildEnv {
        &self.child_env
    }

    /// Identity used to decide whether a resident solver process can serve the
    /// request. It binds execution path, stable file metadata, and the exact
    /// child environment without synchronously hashing solver contents. The
    /// independent checker is deliberately excluded because changing it does
    /// not change an already-running AY process.
    pub(crate) fn solver_process_id(&self) -> [u8; 32] {
        self.solver_process_id
    }

    /// Solver-path + checker-path/content + child-environment identity used by
    /// positive replay memos whose existing key already binds solver content.
    pub(crate) fn positive_reuse_context_id(&self) -> Option<[u8; 32]> {
        self.checker.as_ref()?;
        Some(self.proof_context_id)
    }

    /// Full positive-reuse authority. `None` means no capable independent
    /// checker exists, so no solver result may enter a `Verified` memo.
    pub(crate) fn cache_id_with_solver_identity(&self, solver_identity: &str) -> Option<[u8; 32]> {
        self.checker.as_ref()?;
        if solver_identity.len() != 64
            || !solver_identity
                .bytes()
                .all(|b| b.is_ascii_hexdigit() && !b.is_ascii_uppercase())
        {
            return None;
        }
        let mut hasher = Sha256::new();
        hasher.update(b"trust-cg.verification-authority.full.v1\0");
        hash_part(&mut hasher, b"solver-sha256", solver_identity.as_bytes());
        hash_digest_part(&mut hasher, b"proof-context", &self.proof_context_id);
        Some(hasher.finalize().into())
    }

    /// Bind an existing solver+query key to the exact checker/environment that
    /// promoted it. The legacy key already binds solver content and SMT2.
    pub(crate) fn session_key(&self, legacy_query_key: &str) -> Option<SessionProofKey> {
        self.checker.as_ref()?;
        Some(SessionProofKey::new(
            legacy_query_key.as_bytes(),
            &self.proof_context_id,
        ))
    }
}

/// In-process solver memo key: shared by the positive `Verified` memo and the
/// negative certification-gap memo (`ay_bridge::SessionNegativeVerdictMemo`),
/// so both bind the same solver + query + checker + environment identity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SessionProofKey {
    digest: [u8; 32],
}

impl SessionProofKey {
    fn new(legacy_query_key: &[u8], proof_context_id: &[u8; 32]) -> Self {
        let mut hasher = Sha256::new();
        hasher.update(b"trust-cg.verification-authority.session-proof.v1\0");
        hash_part(&mut hasher, b"legacy-query-key", legacy_query_key);
        hash_digest_part(&mut hasher, b"proof-context", proof_context_id);
        Self {
            digest: hasher.finalize().into(),
        }
    }

    #[cfg(test)]
    pub(crate) fn for_test(legacy_query_key: String, proof_context_id: [u8; 32]) -> Self {
        Self::new(legacy_query_key.as_bytes(), &proof_context_id)
    }
}

fn hash_part(hasher: &mut Sha256, label: &[u8], bytes: &[u8]) {
    hasher.update((label.len() as u64).to_be_bytes());
    hasher.update(label);
    hasher.update((bytes.len() as u64).to_be_bytes());
    hasher.update(bytes);
}

fn hash_digest_part(hasher: &mut Sha256, label: &[u8], digest: &[u8; 32]) {
    hash_part(hasher, label, digest);
}

fn hash_path_part(hasher: &mut Sha256, label: &[u8], path: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        hash_part(hasher, label, path.as_os_str().as_bytes());
    }
    #[cfg(windows)]
    {
        use std::os::windows::ffi::OsStrExt;
        let mut bytes = Vec::new();
        for unit in path.as_os_str().encode_wide() {
            bytes.extend_from_slice(&unit.to_le_bytes());
        }
        hash_part(hasher, label, &bytes);
    }
    #[cfg(not(any(unix, windows)))]
    hash_part(hasher, label, path.as_os_str().to_string_lossy().as_bytes());
}

fn hash_solver_metadata(hasher: &mut Sha256, path: &Path) {
    let Ok(metadata) = std::fs::metadata(path) else {
        hash_part(hasher, b"solver-metadata", b"unavailable");
        return;
    };
    hash_part(hasher, b"solver-size", &metadata.len().to_be_bytes());
    if let Ok(modified) = metadata.modified()
        && let Ok(delta) = modified.duration_since(std::time::UNIX_EPOCH)
    {
        hash_part(hasher, b"solver-mtime-secs", &delta.as_secs().to_be_bytes());
        hash_part(
            hasher,
            b"solver-mtime-nanos",
            &delta.subsec_nanos().to_be_bytes(),
        );
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        hash_part(hasher, b"solver-dev", &metadata.dev().to_be_bytes());
        hash_part(hasher, b"solver-ino", &metadata.ino().to_be_bytes());
        hash_part(hasher, b"solver-ctime", &metadata.ctime().to_be_bytes());
        hash_part(
            hasher,
            b"solver-ctime-nanos",
            &metadata.ctime_nsec().to_be_bytes(),
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn checker(path: &str, byte: &str) -> ExecutableAuthority {
        ExecutableAuthority::new(PathBuf::from(path), byte.repeat(32))
            .expect("test checker identity is canonical lowercase SHA-256")
    }

    fn child_env_with_governance(megabytes: &str) -> SanitizedChildEnv {
        trust_cg_process_env::with_env_edits(|environment| {
            environment.set("GOVERN_AY_MB", megabytes);
            SanitizedChildEnv::capture_verifier()
        })
    }

    /// An executable fixture admitted through the identity rule (it is never
    /// run by these key-derivation tests).
    #[cfg(unix)]
    fn inert_solver(directory: &Path, name: &str) -> PinnedAy {
        use std::os::unix::fs::PermissionsExt;
        let path = directory.join(name);
        std::fs::write(&path, format!("#!/bin/sh\n# {name}\nexit 97\n")).unwrap();
        std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
        crate::ay_identity::test_fixtures::pin(&path)
    }

    fn authority(
        checker: Option<ExecutableAuthority>,
        child_env: SanitizedChildEnv,
    ) -> VerificationAuthority {
        authority_at(
            crate::ay_identity::test_fixtures::inert(),
            checker,
            child_env,
        )
    }

    fn authority_at(
        solver: PinnedAy,
        checker: Option<ExecutableAuthority>,
        child_env: SanitizedChildEnv,
    ) -> VerificationAuthority {
        VerificationAuthority::from_parts(solver, checker, child_env)
    }

    #[cfg(unix)]
    #[test]
    fn session_key_binds_checker_and_child_environment() {
        let directory = tempfile::tempdir().unwrap();
        let environment_a = child_env_with_governance("128");
        let environment_b = child_env_with_governance("256");
        let checker_a = checker("/test/clean-a", "11");
        let checker_b = checker("/test/clean-b", "22");

        let base = authority(Some(checker_a.clone()), environment_a.clone());
        let changed_checker = authority(Some(checker_b), environment_a);
        let changed_environment = authority(Some(checker_a.clone()), environment_b);
        let changed_solver_path = authority_at(
            inert_solver(directory.path(), "other-ay"),
            Some(checker_a),
            child_env_with_governance("128"),
        );
        let legacy = "solver-and-query-v2".to_string();

        assert_ne!(
            base.session_key(&legacy),
            changed_checker.session_key(&legacy)
        );
        assert_ne!(
            base.session_key(&legacy),
            changed_environment.session_key(&legacy)
        );
        assert_ne!(
            base.session_key("solver-and-query-v2"),
            changed_solver_path.session_key("solver-and-query-v2")
        );
    }

    #[cfg(unix)]
    #[test]
    fn full_cache_id_binds_solver_checker_and_child_environment() {
        let directory = tempfile::tempdir().unwrap();
        let environment_a = child_env_with_governance("128");
        let environment_b = child_env_with_governance("256");
        let checker_a = checker("/test/clean-a", "11");
        let checker_b = checker("/test/clean-b", "22");
        let base = authority(Some(checker_a.clone()), environment_a.clone());
        let changed_checker = authority(Some(checker_b), environment_a);
        let changed_environment = authority(Some(checker_a.clone()), environment_b);
        let changed_solver_path = authority_at(
            inert_solver(directory.path(), "other-ay"),
            Some(checker_a),
            child_env_with_governance("128"),
        );
        let solver_a = "aa".repeat(32);
        let solver_b = "bb".repeat(32);

        let base_id = base
            .cache_id_with_solver_identity(&solver_a)
            .expect("checker makes the authority cacheable");
        assert_ne!(
            base_id,
            base.cache_id_with_solver_identity(&solver_b)
                .expect("alternate solver identity is valid")
        );
        assert_ne!(
            base_id,
            changed_checker
                .cache_id_with_solver_identity(&solver_a)
                .expect("alternate checker is capable")
        );
        assert_ne!(
            base_id,
            changed_environment
                .cache_id_with_solver_identity(&solver_a)
                .expect("alternate environment is cacheable")
        );
        assert_ne!(
            base_id,
            changed_solver_path
                .cache_id_with_solver_identity(&solver_a)
                .expect("alternate execution path is cacheable")
        );
    }

    #[cfg(unix)]
    #[test]
    fn resident_solver_identity_ignores_checker_but_binds_environment_and_metadata() {
        let directory = tempfile::tempdir().unwrap();
        let solver = inert_solver(directory.path(), "ay");
        let environment_a = child_env_with_governance("128");
        let environment_b = child_env_with_governance("256");
        let checker_a = checker("/test/clean-a", "11");
        let checker_b = checker("/test/clean-b", "22");

        let base = authority_at(solver.clone(), Some(checker_a), environment_a.clone());
        let changed_checker = authority_at(solver.clone(), Some(checker_b), environment_a.clone());
        assert_eq!(
            base.solver_process_id(),
            changed_checker.solver_process_id()
        );

        let changed_environment = authority_at(solver.clone(), None, environment_b);
        assert_ne!(
            base.solver_process_id(),
            changed_environment.solver_process_id()
        );

        std::fs::write(solver.path(), b"solver-with-different-size")
            .expect("replace solver fixture");
        let changed_metadata = authority_at(solver.clone(), None, environment_a);
        assert_ne!(
            base.solver_process_id(),
            changed_metadata.solver_process_id()
        );
        // And the replaced file is no longer startable from the old admission.
        assert_eq!(
            changed_metadata.solver().command().unwrap_err().code(),
            "TCG-AY-IDENTITY-CHANGED"
        );
    }

    /// `capture("ay")` used to resolve a bare name against the request PATH.
    /// An authority now exists only for an admitted AY, and admission never
    /// searches: a bare name is refused even when a PATH entry holds bytes the
    /// rule would admit, and the absolute path of those bytes is captured as is.
    #[cfg(unix)]
    #[test]
    fn a_bare_solver_name_yields_no_authority_even_with_a_matching_path_entry() {
        use std::os::unix::fs::PermissionsExt;

        let root = tempfile::tempdir().unwrap();
        let bin = root.path().join("bin");
        let solver = bin.join("ay");
        std::fs::create_dir_all(&bin).expect("create PATH fixture directory");
        std::fs::write(&solver, b"#!/bin/sh\nexit 0\n").expect("write solver fixture");
        std::fs::set_permissions(&solver, std::fs::Permissions::from_mode(0o755))
            .expect("make solver fixture executable");
        let fixture_digest = crate::ay_identity::test_fixtures::declare(&[&solver]);

        trust_cg_process_env::with_env_edits(|environment| {
            environment.set("PATH", bin.as_os_str());
            environment.set(
                crate::ay_identity::test_fixtures::FIXTURE_DIGESTS_ENV,
                &fixture_digest,
            );
            environment.set(
                "TCG_EXTERNAL_CLEAN_CHECKER",
                root.path().join("missing-clean").as_os_str(),
            );
            let refusal = crate::ay_identity::resolve_explicit_path("ay").unwrap_err();
            assert_eq!(refusal.code(), "TCG-AY-IDENTITY-OVERRIDE-NOT-ABSOLUTE");
            let admitted = crate::ay_identity::resolve_explicit_path(&solver).unwrap();
            let captured = VerificationAuthority::capture(&admitted);
            assert_eq!(captured.solver_path(), solver);
            assert_eq!(captured.solver_path_text(), solver.to_string_lossy());
        });
    }

    #[test]
    fn missing_checker_or_malformed_solver_identity_disables_positive_reuse() {
        let without_checker = authority(None, child_env_with_governance("128"));
        assert!(without_checker.session_key("legacy").is_none());
        assert!(
            without_checker
                .cache_id_with_solver_identity(&"aa".repeat(32))
                .is_none()
        );

        let with_checker = authority(
            Some(checker("/test/clean", "11")),
            child_env_with_governance("128"),
        );
        assert!(
            with_checker
                .cache_id_with_solver_identity("not-a-sha256")
                .is_none()
        );
    }
}
