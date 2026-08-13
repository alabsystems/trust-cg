// trust-cg-codegen/tests/wp0_artifact_bytes_unchanged.rs
//
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Copyright 2026 Andrew Yates | License: Apache-2.0

//! WP-0 no-drift pin: adding the proof-evidence honesty channel moved **no**
//! artifact bytes.
//!
//! `ProofPolicy` gained a `required_strength` field and `ProofEvidenceSummary`
//! gained `strength` + `accepted_assumptions`. Both are encoded as a
//! *conditional tail*: the bytes are emitted only when the field carries
//! information. Every value below is therefore the same one the encoder
//! produced before the fields existed — the constants were captured by running
//! this file against the pre-change tree and are pinned here so a future edit
//! to either encoder cannot silently reprice an existing artifact identity,
//! invalidation key, or cache key.
//!
//! A failure here means an artifact that used to hash one way now hashes
//! another. That is a cache-invalidation and install-authority event, not a
//! cosmetic one.

use trust_cg_codegen::jit_contract::{
    AbiDescriptor, ArtifactChecksum, DeterministicArtifactManifest, Endianness, EvidenceStrength,
    InvalidationKey, JitArtifactKind, LayoutManifest, ProofEvidenceSummary, ProofPolicy,
    RequiredEvidenceStrength, TargetDescriptor,
};
use trust_cg_codegen::target::{Target, TargetSpec};

/// Checksums recorded against the tree as it stood before WP-0 landed.
const BASELINE_POLICY_DISABLED: u128 = 188_175_227_438_436_940_693_294_818_867_197_489_380;
const BASELINE_POLICY_REQUIRE_CERTIFICATES: u128 =
    15_751_963_069_922_002_482_968_147_802_358_872_553;
const BASELINE_MANIFEST: u128 = 216_325_943_387_089_859_475_006_568_335_973_231_168;
const BASELINE_SYMBOL_MANIFEST: u128 = 184_028_644_154_682_221_136_123_563_136_064_730_661;
const BASELINE_EVIDENCE_VERIFIED: u128 = 331_260_594_645_473_797_617_340_197_945_955_168_427;
const BASELINE_EVIDENCE_BOUND_TO_ARTIFACT: u128 =
    322_893_251_667_028_946_565_986_559_259_782_392_818;

fn manifest(policy: ProofPolicy) -> DeterministicArtifactManifest {
    // The baseline was captured for this exact target. Using
    // `default_for_architecture` makes the supposedly stable golden depend on
    // the test host's OS (`aarch64-unknown-linux-gnu` versus
    // `aarch64-apple-darwin`).
    let spec =
        TargetSpec::parse("aarch64-unknown-linux-gnu").expect("pinned WP-0 target must parse");
    let target = TargetDescriptor::for_trust_cg_target_spec(spec);
    let abi =
        AbiDescriptor::for_trust_cg_target_os(Target::Aarch64, target.operating_system.clone());
    let layout = LayoutManifest::lp64(Endianness::Little, 16);
    let invalidation = InvalidationKey::new(
        "sha256:wp0-probe-source",
        "trust-cg-codegen:probe",
        target.checksum(),
        abi.checksum(),
        layout.checksum(),
        policy.checksum(),
        7,
    );
    DeterministicArtifactManifest::new(
        "wp0-probe-artifact",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        policy,
    )
}

#[test]
fn proof_policy_checksums_are_unchanged_by_the_required_strength_field() {
    let disabled = ProofPolicy::disabled();
    let certificates = ProofPolicy::require_certificates(["ay"]);

    assert_eq!(disabled.required_strength, RequiredEvidenceStrength::Any);
    assert_eq!(
        certificates.required_strength,
        RequiredEvidenceStrength::Any
    );
    assert_eq!(disabled.checksum().get(), BASELINE_POLICY_DISABLED);
    assert_eq!(
        certificates.checksum().get(),
        BASELINE_POLICY_REQUIRE_CERTIFICATES
    );
}

#[test]
fn manifest_and_symbol_manifest_checksums_are_unchanged() {
    let manifest = manifest(ProofPolicy::disabled());
    assert_eq!(manifest.checksum().get(), BASELINE_MANIFEST);
    assert_eq!(
        manifest.symbol_manifest_checksum().get(),
        BASELINE_SYMBOL_MANIFEST
    );
}

#[test]
fn proof_evidence_checksums_are_unchanged_by_the_honesty_channel() {
    let evidence = ProofEvidenceSummary::verified(
        "probe",
        ArtifactChecksum::new(11),
        ArtifactChecksum::new(22),
        ArtifactChecksum::new(33),
        ArtifactChecksum::new(44),
        ArtifactChecksum::new(55),
    );
    assert_eq!(evidence.strength, EvidenceStrength::NotReported);
    assert!(evidence.accepted_assumptions.is_empty());
    assert_eq!(evidence.checksum().get(), BASELINE_EVIDENCE_VERIFIED);

    let bound = ProofEvidenceSummary::verified_for_artifact(
        "probe",
        &manifest(ProofPolicy::disabled()),
        "sha256:payload",
        "sha256:report",
    );
    assert_eq!(bound.checksum().get(), BASELINE_EVIDENCE_BOUND_TO_ARTIFACT);
}

/// The tail is conditional, not dead: once a policy or a summary actually
/// carries the new information, the checksum *must* move, or the channel would
/// not be covered by artifact identity at all.
#[test]
fn the_new_fields_are_covered_by_the_checksum_once_they_carry_information() {
    let stronger = ProofPolicy::require_certificates(["ay"])
        .with_required_strength(RequiredEvidenceStrength::Formal);
    assert_ne!(
        stronger.checksum().get(),
        BASELINE_POLICY_REQUIRE_CERTIFICATES,
        "a policy demanding formal strength must not hash as a policy that does not"
    );

    let reported = ProofEvidenceSummary::verified(
        "probe",
        ArtifactChecksum::new(11),
        ArtifactChecksum::new(22),
        ArtifactChecksum::new(33),
        ArtifactChecksum::new(44),
        ArtifactChecksum::new(55),
    )
    .with_strength(EvidenceStrength::Statistical {
        sample_count: 100_000,
    });
    assert_ne!(
        reported.checksum().get(),
        BASELINE_EVIDENCE_VERIFIED,
        "a summary reporting a real strength must not hash as one reporting nothing"
    );
}
