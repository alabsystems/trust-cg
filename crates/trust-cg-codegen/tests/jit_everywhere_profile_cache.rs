// trust-cg-codegen/tests/jit_everywhere_profile_cache.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::{
    JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA, JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA_VERSION,
    ProfileCacheCostData, ProfileCacheEntry, ProfileCacheInstallRejection, ProfileCacheKey,
    ProfileCacheOutcome, ProfileCacheProofDiagnostic, ProfileCacheReplayReference,
    ProfileOnlyArtifactMetadata, ProfileOnlySpeculativeCache, Target,
};

fn ay_key() -> ProfileCacheKey {
    ProfileCacheKey::new(
        "sha256:source-ay-sparse-substitute",
        "sha256:trust_ir-ay-sparse-substitute",
        "pipeline:o3-profile-only:v1",
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "profile-schema:block-counters:v1",
        "proof-policy:v1:require-certificates",
        "ay",
        "ay_sparse_substitute:generation:7",
    )
}

fn ty_key() -> ProfileCacheKey {
    ProfileCacheKey::new(
        "sha256:source-ty-action",
        "sha256:trust_ir-ty-action",
        "pipeline:o3-profile-only:v1",
        Target::Aarch64,
        "sha256:target-facts-aarch64-darwin",
        "profile-schema:block-counters:v1",
        "proof-policy:v1:require-certificates",
        "ty",
        "ty_action:generation:11",
    )
}

fn profile_only_artifact_entry(key: ProfileCacheKey) -> ProfileCacheEntry {
    ProfileCacheEntry::new(
        key,
        ProfileCacheOutcome::ProfileOnlyArtifact,
        Some(ProfileOnlyArtifactMetadata::new(
            "sha256:native-profile-only-ay-sparse-substitute",
            4096,
            "ay_sparse_substitute_entry",
        )),
        Some(ProfileCacheProofDiagnostic::new(
            "trust_cg_verify",
            "profile_only_unverified",
            Some("profile_only_non_installable".to_owned()),
            Some("sha256:proof-report-ay-sparse-substitute".to_owned()),
            Some(1_000),
        )),
        ProfileCacheCostData::new(1_200, 900, 90_000, 21_000),
        ProfileCacheReplayReference::new(
            "sha256:replay-root-ay-sparse-substitute",
            "sha256:replay-record-ay-sparse-substitute",
            Some("sha256:reducer-ay-sparse-substitute".to_owned()),
        ),
    )
}

fn negative_entry(key: ProfileCacheKey, outcome: ProfileCacheOutcome) -> ProfileCacheEntry {
    ProfileCacheEntry::new(
        key,
        outcome,
        None,
        Some(ProfileCacheProofDiagnostic::new(
            "trust_cg_verify",
            outcome.as_str(),
            Some(outcome.as_str().to_owned()),
            Some(format!("sha256:proof-report-{}", outcome.as_str())),
            Some(250),
        )),
        ProfileCacheCostData::new(400, 250, 33_000, 0),
        ProfileCacheReplayReference::new(
            format!("sha256:replay-root-{}", outcome.as_str()),
            format!("sha256:replay-record-{}", outcome.as_str()),
            None,
        ),
    )
}

#[test]
fn jit_everywhere_profile_cache_stores_replayable_profile_only_artifact() {
    let key = ay_key();
    let entry = profile_only_artifact_entry(key.clone());

    assert_eq!(entry.schema, JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA);
    assert_eq!(
        entry.schema_version,
        JIT_EVERYWHERE_PROFILE_CACHE_SCHEMA_VERSION
    );
    assert_eq!(entry.issue, 737);
    assert_eq!(entry.outcome, ProfileCacheOutcome::ProfileOnlyArtifact);
    // Golden refreshed to match the committed `canonical_key_sha256` /
    // `canonical_entry_sha256` serialization (jit_profile_cache.rs): SHA-256 of
    // a length-prefixed framing of the schema tag, the digests,
    // `Target::Aarch64.name()` ("aarch64", a static string), profile schema,
    // proof policy, consumer, and generation domain — all host/arch-independent.
    // The key value was re-derived from first principles (pure SHA-256 of that
    // byte framing) on the x86-64 host; both values equal the code's own
    // `canonical_*` outputs asserted just below. The previous literals were
    // baked from an older framing and were stale, not platform drift.
    assert_eq!(
        entry.key.key_sha256,
        "sha256:acd9a13002102df929b621ca19084de4b13309d2c56b4e8fa9f4bba8e9320c33"
    );
    assert_eq!(
        entry.entry_sha256,
        "sha256:b648ac2f3e25af40b9c47d036b3e8d3d47123eabc640bd41971b396ba4e34e30"
    );
    assert_eq!(entry.key.key_sha256, entry.key.canonical_key_sha256());
    assert_eq!(entry.entry_sha256, entry.canonical_entry_sha256());
    assert!(entry.is_replayable_learning());
    assert!(entry.baseline_authoritative);
    assert!(entry.side_effects.all_install_authority_blocked());

    let mut cache = ProfileOnlySpeculativeCache::new();
    cache.insert_learning_entry(entry.clone()).unwrap();

    let stored = cache
        .get_learning_entry(&key)
        .expect("stored profile entry");
    assert_eq!(stored, &entry);
    assert_eq!(
        cache.replay_reference(&key),
        Some(&entry.replay),
        "profile-only entries remain replayable learning data"
    );
}

#[test]
fn jit_everywhere_profile_cache_cannot_feed_callable_install_lookup() {
    let mut cache = ProfileOnlySpeculativeCache::new();
    let ay_entry = profile_only_artifact_entry(ay_key());
    let ty_entry = profile_only_artifact_entry(ty_key());
    cache.insert_learning_entry(ay_entry.clone()).unwrap();
    cache.insert_learning_entry(ty_entry.clone()).unwrap();

    for key in [&ay_entry.key, &ty_entry.key] {
        let lookup = cache.lookup_callable_install(key);
        assert!(lookup.entry_present);
        assert_eq!(
            lookup.rejection,
            ProfileCacheInstallRejection::ProfileOnlyNonInstallable
        );
        assert!(lookup.denied_without_install_authority());
        assert!(lookup.callable_handle_id.is_none());
        assert!(!lookup.installable_cache_hit_accepted);
        assert_eq!(lookup.useful_native_delta, 0);
    }
}

#[test]
fn jit_everywhere_profile_cache_preserves_negative_outcomes_as_learning() {
    let outcomes = [
        ProfileCacheOutcome::Fallback,
        ProfileCacheOutcome::VerifierTimeout,
        ProfileCacheOutcome::UnsupportedTarget,
        ProfileCacheOutcome::StaleEvidence,
        ProfileCacheOutcome::ProofRejected,
    ];

    let mut cache = ProfileOnlySpeculativeCache::new();
    for (index, outcome) in outcomes.into_iter().enumerate() {
        let mut key = ay_key();
        key.generation_domain = format!("ay_negative_case:generation:{index}");
        key.key_sha256 = key.canonical_key_sha256();
        let entry = negative_entry(key.clone(), outcome);
        assert!(entry.is_replayable_learning());
        assert_eq!(entry.outcome, outcome);
        assert!(entry.artifact.is_none());
        cache.insert_learning_entry(entry).unwrap();

        let lookup = cache.lookup_callable_install(&key);
        assert_eq!(
            lookup.rejection,
            ProfileCacheInstallRejection::ProfileOnlyNonInstallable
        );
        assert!(lookup.denied_without_install_authority());
    }

    assert_eq!(cache.len(), outcomes.len());
}

#[test]
fn jit_everywhere_profile_cache_key_binds_profile_schema_and_generation() {
    let base = ay_key();
    let mut changed_profile_schema = ay_key();
    changed_profile_schema.profile_schema = "profile-schema:block-counters:v2".to_owned();
    changed_profile_schema.key_sha256 = changed_profile_schema.canonical_key_sha256();

    let mut changed_generation = ay_key();
    changed_generation.generation_domain = "ay_sparse_substitute:generation:8".to_owned();
    changed_generation.key_sha256 = changed_generation.canonical_key_sha256();

    assert_ne!(base.key_sha256, changed_profile_schema.key_sha256);
    assert_ne!(base.key_sha256, changed_generation.key_sha256);
    assert_ne!(
        changed_profile_schema.key_sha256,
        changed_generation.key_sha256
    );
}

#[test]
fn jit_everywhere_profile_cache_rejects_invalid_learning_entries() {
    let mut entry = profile_only_artifact_entry(ay_key());
    entry.replay.replay_root_sha256.clear();
    entry.entry_sha256 = entry.canonical_entry_sha256();

    let mut cache = ProfileOnlySpeculativeCache::new();
    let result = cache.insert_learning_entry(entry);

    assert_eq!(
        result,
        Err(ProfileCacheInstallRejection::InvalidProfileEntry)
    );
    assert!(cache.is_empty());

    let lookup = cache.lookup_callable_install(&ay_key());
    assert!(!lookup.entry_present);
    assert_eq!(
        lookup.rejection,
        ProfileCacheInstallRejection::MissingProfileEntry
    );
    assert!(lookup.denied_without_install_authority());
}
