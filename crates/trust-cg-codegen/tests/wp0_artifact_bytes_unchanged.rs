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
//! The ABI input is frozen explicitly at the WP-0-era descriptor. It is an
//! encoder fixture, not a valid current Linux ABI or an installable artifact.
//! The corrected current ABI must produce a different identity; this file
//! checks that transition separately without changing the historical goldens.
//!
//! A failure here means an artifact that used to hash one way now hashes
//! another. That is a cache-invalidation and install-authority event, not a
//! cosmetic one.
//!
//! Two such events are deliberate: manifest schema v2 (`trust-cg.artifact/v2`)
//! added the executable-memory protection record, and manifest schema v3
//! (`trust-cg.artifact/v3`) added that record's page-protection witness. Each
//! moved the two manifest-derived goldens. The v1 and v2 values are kept as
//! historical constants and the v3 values are pinned; every policy,
//! symbol-manifest and unbound evidence golden is still the pre-WP-0 value.

use trust_cg_codegen::jit_contract::{
    AbiDescriptor, AbiVarargsPolicy, ArtifactChecksum, DeterministicArtifactManifest, Endianness,
    EvidenceStrength, ExecutableMemoryOwner, ExecutableMemoryProtection, InvalidationKey,
    JIT_ARTIFACT_MANIFEST_SCHEMA, JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION, JitArtifactKind,
    LayoutManifest, PageProtectionWitness, PageProtectionWitnessSource, ProofEvidenceSummary,
    ProofPolicy, RequiredEvidenceStrength,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY,
    TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY, TargetDescriptor, TargetOperatingSystem,
    TeardownPolicy, trust_ir_hardware_vector_contract_manifest_row_count,
    trust_ir_hardware_vector_contract_manifest_sha256,
};
use trust_cg_codegen::target::{Target, TargetSpec};

/// Checksums recorded against the tree as it stood before WP-0 landed.
const BASELINE_POLICY_DISABLED: u128 = 188_175_227_438_436_940_693_294_818_867_197_489_380;
const BASELINE_POLICY_REQUIRE_CERTIFICATES: u128 =
    15_751_963_069_922_002_482_968_147_802_358_872_553;
/// Manifest-level WP-0 goldens under manifest schema v1 (`trust-cg.artifact/v1`).
/// The v2 schema deliberately moved them; see the v2 constants below.
const V1_BASELINE_MANIFEST: u128 = 216_325_943_387_089_859_475_006_568_335_973_231_168;
const BASELINE_SYMBOL_MANIFEST: u128 = 184_028_644_154_682_221_136_123_563_136_064_730_661;
const BASELINE_EVIDENCE_VERIFIED: u128 = 331_260_594_645_473_797_617_340_197_945_955_168_427;
const V1_BASELINE_EVIDENCE_BOUND_TO_ARTIFACT: u128 =
    322_893_251_667_028_946_565_986_559_259_782_392_818;
/// The same WP-0 probe under manifest schema v2 (`trust-cg.artifact/v2`),
/// which added the executable-memory protection record. Historical since v3.
const V2_MANIFEST: u128 = 130_236_844_368_833_394_274_478_215_509_145_710_519;
const V2_EVIDENCE_BOUND_TO_ARTIFACT: u128 = 26_800_311_325_190_312_049_936_713_716_777_106_288;
/// The same WP-0 probe under manifest schema v3 (`trust-cg.artifact/v3`),
/// which adds the protection record's page-protection witness. The v2 and v3
/// bumps are the only intended identity moves since WP-0: the proof-evidence
/// honesty channel still contributes no bytes when it carries no information,
/// and the symbol-manifest checksum (which excludes the protection record) is
/// unchanged.
const V3_MANIFEST: u128 = 337_816_001_306_970_612_074_377_269_579_833_110_315;
const V3_EVIDENCE_BOUND_TO_ARTIFACT: u128 = 51_399_134_916_935_157_512_005_253_208_317_942_086;

/// Exact ABI fields produced at 5cdbab23, before 18e1ab69 corrected the
/// AArch64 callee saves, Linux red zone, and OS-specific descriptor name.
/// Never use this obsolete descriptor to admit or execute generated code.
fn historical_abi() -> AbiDescriptor {
    fn strings<const N: usize>(names: [&str; N]) -> Vec<String> {
        names.map(str::to_owned).to_vec()
    }
    AbiDescriptor {
        name: "trust-cg-aarch64".into(),
        calling_convention: "aapcs64".into(),
        pointer_width_bits: 64,
        stack_alignment_bytes: 16,
        red_zone_bytes: 128,
        shadow_space_bytes: 0,
        integer_argument_registers: strings(["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]),
        float_argument_registers: strings(["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7"]),
        integer_return_registers: strings(["x0", "x1", "x2", "x3", "x4", "x5", "x6", "x7"]),
        float_return_registers: strings(["v0", "v1", "v2", "v3", "v4", "v5", "v6", "v7"]),
        callee_saved_registers: strings([
            "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28",
        ]),
        executable_memory_owner: ExecutableMemoryOwner::TrustCg,
        teardown_policy: TeardownPolicy::RefCounted,
        varargs: AbiVarargsPolicy::Unsupported,
    }
}

fn manifest(policy: ProofPolicy) -> DeterministicArtifactManifest {
    manifest_with_abi(policy, historical_abi())
}

fn manifest_with_abi(policy: ProofPolicy, abi: AbiDescriptor) -> DeterministicArtifactManifest {
    // The baseline was captured for this exact target. Using
    // `default_for_architecture` makes the supposedly stable golden depend on
    // the test host's OS (`aarch64-unknown-linux-gnu` versus
    // `aarch64-apple-darwin`).
    let spec =
        TargetSpec::parse("aarch64-unknown-linux-gnu").expect("pinned WP-0 target must parse");
    let target = TargetDescriptor::for_trust_cg_target_spec(spec);
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
    let mut manifest = DeterministicArtifactManifest::new(
        "wp0-probe-artifact",
        JitArtifactKind::ExecutableMemory,
        target,
        abi,
        layout,
        invalidation,
        policy,
    );
    // The manifest binds the pinned trust-ir's CHC x86 vector-contract
    // manifest (row count and digest), so its identity moves with that
    // contract by design; `the_live_manifest_binds_the_pinned_trust_ir_vector_contract`
    // checks that binding. These goldens pin trust-cg's own encoders, so the
    // probe carries the contract as it stood when they were captured.
    for (key, value) in [
        (
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY,
            WP0_TRUST_IR_VECTOR_CONTRACT_ROWS,
        ),
        (
            TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY,
            WP0_TRUST_IR_VECTOR_CONTRACT_SHA256,
        ),
    ] {
        let previous = manifest.metadata.insert(key.to_owned(), value.to_owned());
        assert!(previous.is_some(), "the manifest binds `{key}`");
    }
    manifest
}

/// The pinned trust-ir CHC x86 vector contract when the v3 goldens were
/// captured (trust-ir 7b9146ba, the pin at trust-cg 2130afa58).
const WP0_TRUST_IR_VECTOR_CONTRACT_ROWS: &str = "561";
const WP0_TRUST_IR_VECTOR_CONTRACT_SHA256: &str =
    "sha256:ef4832c95c113fdbad970c086771a0c875f64965e0948541e51407be80622b1f";

/// The live manifest binds the CURRENT pinned contract, so an artifact built
/// against a different trust-ir contract has a different identity: the
/// goldens above freeze only that input, never the binding.
#[test]
fn the_live_manifest_binds_the_pinned_trust_ir_vector_contract() {
    let spec =
        TargetSpec::parse("aarch64-unknown-linux-gnu").expect("pinned WP-0 target must parse");
    let target = TargetDescriptor::for_trust_cg_target_spec(spec);
    let probe = manifest(ProofPolicy::disabled());
    let live = DeterministicArtifactManifest::new(
        "wp0-probe-artifact",
        JitArtifactKind::ExecutableMemory,
        target,
        probe.abi.clone(),
        probe.layout.clone(),
        probe.invalidation.clone(),
        ProofPolicy::disabled(),
    );
    assert_eq!(
        live.metadata
            .get(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY)
            .map(String::as_str),
        Some(
            trust_ir_hardware_vector_contract_manifest_row_count()
                .to_string()
                .as_str()
        )
    );
    assert_eq!(
        live.metadata
            .get(TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY),
        Some(&trust_ir_hardware_vector_contract_manifest_sha256())
    );
    // Only the contract differs between the live manifest and the probe.
    let mut frozen = live.clone();
    for key in [
        TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_ROW_COUNT_KEY,
        TRUST_IR_HARDWARE_VECTOR_CONTRACT_MANIFEST_SHA256_KEY,
    ] {
        frozen
            .metadata
            .insert(key.to_owned(), probe.metadata[key].clone());
    }
    assert_eq!(frozen.checksum().get(), probe.checksum().get());
    assert_eq!(
        live.checksum().get() == probe.checksum().get(),
        trust_ir_hardware_vector_contract_manifest_sha256() == WP0_TRUST_IR_VECTOR_CONTRACT_SHA256,
        "the manifest identity moves exactly when the pinned contract does"
    );
}

#[test]
fn corrected_abi_fields_change_artifact_and_bound_evidence_identity() {
    let old = historical_abi();
    let current =
        AbiDescriptor::for_trust_cg_target_os(Target::Aarch64, TargetOperatingSystem::Linux);
    assert_eq!(current.name, "trust-cg-aarch64-linux");
    assert_eq!(current.red_zone_bytes, 0);
    let expected_saves: Vec<_> = [
        "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29", "d8", "d9",
        "d10", "d11", "d12", "d13", "d14", "d15",
    ]
    .map(str::to_owned)
    .into();
    assert_eq!(current.callee_saved_registers, expected_saves);

    // Check each correction independently as well as their combined result.
    let mut renamed = old.clone();
    renamed.name.clone_from(&current.name);
    let mut red_zone = old.clone();
    red_zone.red_zone_bytes = current.red_zone_bytes;
    let mut saves = old.clone();
    saves
        .callee_saved_registers
        .clone_from(&current.callee_saved_registers);
    for abi in [renamed, red_zone, saves, current] {
        assert_ne!(abi.checksum(), old.checksum());
        let changed = manifest_with_abi(ProofPolicy::disabled(), abi);
        assert_ne!(changed.checksum().get(), V3_MANIFEST);
        assert_ne!(changed.checksum().get(), V2_MANIFEST);
        assert_ne!(changed.checksum().get(), V1_BASELINE_MANIFEST);
        let bound = ProofEvidenceSummary::verified_for_artifact(
            "probe",
            &changed,
            "sha256:payload",
            "sha256:report",
        );
        assert_ne!(bound.checksum().get(), V3_EVIDENCE_BOUND_TO_ARTIFACT);
        assert_ne!(bound.checksum().get(), V2_EVIDENCE_BOUND_TO_ARTIFACT);
        assert_ne!(
            bound.checksum().get(),
            V1_BASELINE_EVIDENCE_BOUND_TO_ARTIFACT
        );
    }
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
    assert_eq!(manifest.checksum().get(), V3_MANIFEST);
    assert_ne!(
        manifest.checksum().get(),
        V2_MANIFEST,
        "the v3 schema must not collide with the v2 identity it replaced"
    );
    assert_ne!(
        manifest.checksum().get(),
        V1_BASELINE_MANIFEST,
        "the v3 schema must not collide with the v1 identity"
    );
    assert_eq!(
        manifest.symbol_manifest_checksum().get(),
        BASELINE_SYMBOL_MANIFEST
    );
}

/// Schema v3 carries the executable-memory protection contract for the
/// manifest's own target (never the test host's), including its
/// page-protection witness, and every field of it is covered by the manifest
/// identity.
#[test]
fn manifest_schema_v3_binds_the_target_executable_memory_protection() {
    let manifest = manifest(ProofPolicy::disabled());
    assert_eq!(manifest.schema, JIT_ARTIFACT_MANIFEST_SCHEMA);
    assert_eq!(manifest.schema, "trust-cg.artifact/v3");
    assert_eq!(
        manifest.schema_version,
        JIT_ARTIFACT_MANIFEST_SCHEMA_VERSION
    );
    assert_eq!(manifest.schema_version, 3);
    let protection = manifest
        .executable_memory
        .clone()
        .expect("executable manifests declare their protection");
    assert_eq!(
        protection,
        ExecutableMemoryProtection {
            allocator: "mmap".to_owned(),
            // MAP_PRIVATE | MAP_ANONYMOUS
            allocation_flags: 0x22,
            allocation_granule_bytes: 4096,
            // PROT_READ | PROT_WRITE, then PROT_READ | PROT_EXEC
            write_phase_protection: 0x3,
            published_protection: 0x5,
            map_jit: false,
            write_protect_supported: false,
            published_rx: true,
            mprotect_rx_ok: true,
            // Linux targets promise a kernel observation equal to the
            // recorded read-execute private mapping.
            page_protection_witness: PageProtectionWitness {
                source: PageProtectionWitnessSource::KernelProcSelfMaps,
                recorded_permissions: "r-xp".to_owned(),
                observed_permissions: Some("r-xp".to_owned()),
            },
        }
    );
    assert_eq!(
        ExecutableMemoryProtection::for_trust_cg_target(&manifest.target),
        Some(protection.clone())
    );
    // A macOS target promises only its recorded state.
    let darwin = TargetDescriptor::for_trust_cg_target_spec(
        TargetSpec::parse("aarch64-apple-darwin").expect("pinned Darwin target must parse"),
    );
    assert_eq!(
        ExecutableMemoryProtection::for_trust_cg_target(&darwin)
            .expect("macOS AArch64 publishes in process")
            .page_protection_witness,
        PageProtectionWitness {
            source: PageProtectionWitnessSource::RecordedOnly,
            recorded_permissions: "r-xp".to_owned(),
            observed_permissions: None,
        }
    );

    let mut absent = manifest.clone();
    absent.executable_memory = None;
    assert_ne!(absent.checksum(), manifest.checksum());
    for mutate in [
        (|p: &mut ExecutableMemoryProtection| p.map_jit = true) as fn(&mut _),
        |p| p.write_protect_supported = true,
        |p| p.published_rx = false,
        |p| p.mprotect_rx_ok = false,
        |p| p.allocation_flags |= 0x800,
        |p| p.allocation_granule_bytes = 16 * 1024,
        |p| p.write_phase_protection = 0x7,
        |p| p.published_protection = 0x7,
        |p| p.allocator = "virtual_alloc".to_owned(),
        |p| p.page_protection_witness.source = PageProtectionWitnessSource::RecordedOnly,
        |p| p.page_protection_witness.recorded_permissions = "rwxp".to_owned(),
        |p| p.page_protection_witness.observed_permissions = Some("rw-p".to_owned()),
        |p| p.page_protection_witness.observed_permissions = None,
    ] {
        let mut changed = manifest.clone();
        mutate(changed.executable_memory.as_mut().unwrap());
        assert_ne!(changed.checksum(), manifest.checksum());
    }
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
    assert_eq!(bound.checksum().get(), V3_EVIDENCE_BOUND_TO_ARTIFACT);
    assert_ne!(bound.checksum().get(), V2_EVIDENCE_BOUND_TO_ARTIFACT);
    assert_ne!(
        bound.checksum().get(),
        V1_BASELINE_EVIDENCE_BOUND_TO_ARTIFACT
    );
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
