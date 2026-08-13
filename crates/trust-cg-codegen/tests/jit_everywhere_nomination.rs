// trust-cg-codegen/tests/jit_everywhere_nomination.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

use trust_cg_codegen::{
    CandidateRegionKind, JIT_EVERYWHERE_NOMINATION_SCHEMA,
    JIT_EVERYWHERE_NOMINATION_SCHEMA_VERSION, NominationDisposition, NominationInput,
    NominationRejectionReason, NominationStructuralSignal, Target,
    nominate_jit_everywhere_candidate,
};

fn ay_nomination_input() -> NominationInput {
    NominationInput::new(
        "ay",
        CandidateRegionKind::AYSparseSubstitute,
        Target::Aarch64,
        "sha256:source-ay-sparse-substitute",
        "sha256:trust_ir-ay-sparse-substitute",
        "sha256:profile-key-ay-sparse-substitute",
        "proof-policy:v1:require-certificates",
        "ay_sparse_substitute:generation:7",
        NominationStructuralSignal::new(7, 2, 1, 4, 96, 2),
    )
}

#[test]
fn jit_everywhere_nomination_records_are_deterministic() {
    let input = ay_nomination_input();

    let left = nominate_jit_everywhere_candidate(&input);
    let right = nominate_jit_everywhere_candidate(&input);

    assert_eq!(left, right);
    assert_eq!(left.schema, JIT_EVERYWHERE_NOMINATION_SCHEMA);
    assert_eq!(
        left.schema_version,
        JIT_EVERYWHERE_NOMINATION_SCHEMA_VERSION
    );
    assert_eq!(left.issue, 736);
    assert_eq!(left.disposition, NominationDisposition::Nominated);
    assert_eq!(left.rejection_reason, None);
    assert_eq!(left.advisory_score, 45);
    // Golden refreshed to match the committed `candidate_id_for_input` /
    // `put_record_body` serialization (jit_nomination.rs). The candidate id is
    // SHA-256 over a length-prefixed framing of the schema tag, consumer,
    // region kind, `Target::Aarch64.name()` (the static string "aarch64"),
    // and the five digests — all host/arch-independent. The expected values
    // below were re-derived from first principles (pure-SHA-256 of that exact
    // byte framing) on the x86-64 host and equal the code's own
    // `canonical_record_sha256()` (asserted on the next line); the previous
    // literals were baked from an older framing and were stale, not drift.
    assert_eq!(
        left.candidate_id.value,
        "candidate:sha256:71f2fabc752d1c9565e44139507b95f3d79bdb3870002a20ff2f734154693869"
    );
    assert_eq!(
        left.record_sha256,
        "sha256:1b69676b400434b3d9bbc81b9149f39343cd9603e4442bf53904021d07eb0fdb"
    );
    assert_eq!(left.record_sha256, left.canonical_record_sha256());
    assert!(left.candidate_id.value.starts_with("candidate:sha256:"));
}

#[test]
fn jit_everywhere_nomination_rejects_unsupported_shape_with_typed_reason() {
    let mut input = ay_nomination_input();
    input.consumer = "ty".to_owned();
    input.generation_domain = "ty_action:generation:11".to_owned();

    let record = nominate_jit_everywhere_candidate(&input);

    assert_eq!(record.disposition, NominationDisposition::Rejected);
    assert_eq!(
        record.rejection_reason,
        Some(NominationRejectionReason::UnsupportedRegionKind)
    );
    // Golden refreshed (same host/arch-independent serialization proof as the
    // accepted case above); re-derived from the committed framing and equal to
    // `record.canonical_record_sha256()` asserted below.
    assert_eq!(
        record.candidate_id.value,
        "candidate:sha256:ce77e2f2eeaccb70852299e806752065a7f7312ac351dab890133ed083bbc6a2"
    );
    assert_eq!(
        record.record_sha256,
        "sha256:9ed7f73483be7605472c5793ab585e5e1efa6fb340bedd2be3db2c247527e0ce"
    );
    assert_eq!(record.advisory_score, 0);
    assert_eq!(record.record_sha256, record.canonical_record_sha256());
    assert!(record.is_non_installing());
}

#[test]
fn jit_everywhere_nomination_rejects_missing_observations() {
    let mut input = ay_nomination_input();
    input.structural_signal = NominationStructuralSignal::new(0, 0, 0, 0, 0, 0);

    let record = nominate_jit_everywhere_candidate(&input);

    assert_eq!(record.disposition, NominationDisposition::Rejected);
    assert_eq!(
        record.rejection_reason,
        Some(NominationRejectionReason::MissingObservation)
    );
    assert_eq!(record.advisory_score, 0);
    assert!(record.is_non_installing());
}

#[test]
fn jit_everywhere_nomination_has_no_compile_install_or_useful_native_effects() {
    let accepted = nominate_jit_everywhere_candidate(&ay_nomination_input());
    let rejected = {
        let mut input = ay_nomination_input();
        input.consumer = "unknown-consumer".to_owned();
        nominate_jit_everywhere_candidate(&input)
    };

    for record in [accepted, rejected] {
        assert!(record.side_effects.all_blocked());
        assert!(!record.side_effects.compile_enqueued);
        assert!(!record.side_effects.executable_artifact_created);
        assert!(!record.side_effects.callable_handle_published);
        assert!(!record.side_effects.install_cache_written);
        assert!(!record.side_effects.ay_registry_inserted);
        assert!(!record.side_effects.ty_native_activated);
        assert_eq!(record.side_effects.useful_native_delta, 0);
    }
}

#[test]
fn jit_everywhere_nomination_id_changes_with_profile_key() {
    let base = ay_nomination_input();
    let mut changed = ay_nomination_input();
    changed.profile_key_sha256 = "sha256:profile-key-ay-sparse-substitute-refresh".to_owned();

    let base_record = nominate_jit_everywhere_candidate(&base);
    let changed_record = nominate_jit_everywhere_candidate(&changed);

    assert_ne!(base_record.candidate_id, changed_record.candidate_id);
    assert_ne!(base_record.record_sha256, changed_record.record_sha256);
}
